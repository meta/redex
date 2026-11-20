#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Rank sets of reachability roots by the DEX bytes the reachability graph
shows dying with them.

NOT A BYTE PRICE. The result is what one reachability graph of one Redex run
shows becoming unreachable when the roots' edges are cut, joined to the run's
final DEX. It ranks candidates and bounds the real change in neither
direction. What it counts as deleted is deleted, but the net change differs:
removing roots in source can remove more (other registrations of the same key,
generated tables); later passes react (inlining, class merging, DEX packing,
renaming), which can move bytes instead of freeing them; and the graph does not
record Redex's conditional marking, so removing an entry point that leaves a
type uninstantiable or a call never returning can free far more than the graph
shows. Claim bytes only from a real removal (Redex rerun or a build size
measurement of the source change).

Reachability roots only: registrations and entry points, given as anchor rows
(`root_ranking/anchors.py` defines the format). Value roots are refused.

Inputs:
  --run-dir   a Redex output directory: `reachability-graph` (emitted with
              `-J <pass>.emit_graph_on_run=<n>` on an early reachability pass,
              before class merging, and `-J record_keep_reasons=true`),
              `redex-full-rename-map.txt`, `redex-line-number-map-v2` and
              `redex-debug-line-map-v2`, and `redex.py-invocation.txt`.
  --bundle    the same run's output .apk or .aab.
  --anchors   anchor rows, JSON lines, for every registration of the
              registries the roots belong to: an edge that several keys
              register is cut only when the set holds all of them.
  --sets      optional JSON {"<set name>": ["<coordinate>", ...]}; default:
              one set of every rankable coordinate.

Each set is cut as a whole and each of its roots alone. Roots can overlap, so
what they free alone can overlap too; `shared_in_set` is what dies only when
several of them go: the set's bytes minus the bytes of everything that dies
with some root alone.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import logging
import multiprocessing
import os
import shlex
import sys
import time
from collections.abc import Iterator, Mapping, Sequence, Set
from dataclasses import dataclass
from typing import NamedTuple, TypedDict

from debug_line_map import DebugLineMap
from lib.core import ReachableObjectType
from lib.set_cut import Cut, SetCut, SetCutGraph
from line_unmap import PositionMap
from root_ranking.anchors import Anchor, cut_for, EDGE_KINDS, read_anchors, refusal
from root_ranking.dex_bundle import inventory, read_dex, store_of
from root_ranking.dex_pricing import DexReferences, Release
from root_ranking.final_join import (
    dead_code,
    DeadCode,
    DEBUG_LINE_MAP,
    FinalJoin,
    LINE_NUMBER_MAP,
    Overloads,
    read_rename_map,
    RENAME_MAP,
)

GRAPH = "reachability-graph"
# The seed Redex records when it keeps something without a recorded reason
GENERIC_SEED = "<SEED>"
INVOCATION = "redex.py-invocation.txt"
DEXVT_EXPORT = ("redex-dexvt.ndjson", "redex-dexvt.callersets.tsv")
NOT_A_PRICE = (
    "Ranking signal, not a byte price: what the reachability graph shows dying "
    "in this run; the real change can be larger or smaller. Claim bytes only "
    "from a real removal."
)

# The group of a set's edges that several of its roots register; not a root.
SHARED_EDGES = "registered by several roots"

logger: logging.Logger = logging.getLogger(__name__)


class Label(NamedTuple):
    """One priced cut: a whole set, one of its roots alone, or everything that
    goes with some root of the set alone."""

    set_name: str
    part: str  # WHOLE, ANY_ALONE, or a coordinate


WHOLE = "set"
ANY_ALONE = "any alone"


class Summary(TypedDict):
    total: int
    code: int
    bytes: dict[str, int]
    by_store: dict[str, int]


class SetReport(Summary):
    graph_cut: dict[str, int]
    roots: dict[str, Summary]
    # Members with no bytes: refused; without an anchor; with anchors that
    # match no edge, or only entry-point rows whose keep reason the graph holds
    # twice or that name no reason while several hold the class; or whose every
    # edge a key outside the set or a refused key also registers. `refused` and
    # `problems` say which.
    not_ranked: list[str]
    shared_in_set: int
    join: dict[str, int]


class Report(TypedDict):
    meaning: str
    provenance: dict[str, object]
    sets: dict[str, SetReport]
    refused: dict[str, str]
    problems: list[str]
    elapsed_s: float


@dataclass(frozen=True)
class _Job:
    bundle: str
    dead: Mapping[Label, DeadCode]
    renames: Mapping[str, frozenset[str]]
    known: frozenset[str]  # reachable field and method names
    lines: Mapping[int, Sequence[tuple[int, int]]]


# Worker inputs, set before the pool forks.
_job: _Job | None = None


def _j_options(words: Sequence[str]) -> Iterator[str]:
    """The values of `-J key=value` and `-Jkey=value` options."""
    for i, word in enumerate(words):
        if word == "-J" and i + 1 < len(words):
            yield words[i + 1]
        elif word.startswith("-J") and len(word) > 2:
            yield word[2:]


def _graph_kind(run_dir: str) -> dict[str, object]:
    """Which pass emitted the graph and whether keep reasons were recorded, from
    the `-J` options of the run's redex.py invocation."""
    kind: dict[str, object] = {"pass": None, "run": None, "keep_reasons": False}
    path = os.path.join(run_dir, INVOCATION)
    if not os.path.exists(path):
        kind["unknown"] = f"no {INVOCATION}"
        return kind
    with open(path) as f:
        words = shlex.split(f.read())
    for option in _j_options(words):
        key, _, setting = option.partition("=")
        if key == "record_keep_reasons":
            kind["keep_reasons"] = setting.lower() == "true"
        elif key.endswith(".emit_graph_on_run"):
            kind["pass"], kind["run"] = key.rsplit(".", 1)[0], int(setting)
        elif key.endswith(".emit_graph_on_last_run") and setting.lower() == "true":
            kind["pass"], kind["run"] = key.rsplit(".", 1)[0], "last"
    return kind


def _sha256(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 24), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _provenance(
    run_dir: str, graph_file: str, bundle: str, kind: dict[str, object]
) -> dict[str, object]:
    maps = (RENAME_MAP, LINE_NUMBER_MAP, DEBUG_LINE_MAP)
    dexvt = {
        name: _sha256(os.path.join(run_dir, name))
        for name in DEXVT_EXPORT
        if os.path.exists(os.path.join(run_dir, name))
    }
    return {
        "bundle": {"file": os.path.abspath(bundle), "sha256": _sha256(bundle)},
        "graph": {
            "file": os.path.abspath(graph_file),
            "sha256": _sha256(graph_file),
            "kind": kind,
        },
        "maps": {name: _sha256(os.path.join(run_dir, name)) for name in maps},
        "dexvt_export": dexvt or None,
    }


def _claims(
    graph: SetCutGraph,
    anchors: Mapping[str, Sequence[Anchor]],
    refused: Mapping[str, str],
    wanted: Set[str],
) -> tuple[dict[str, Cut], dict[tuple[int, int], set[str]], list[str]]:
    """Each rankable coordinate's cut, the coordinates that register each
    edge, and the problems of the anchors of the `wanted` coordinates. A
    refused coordinate is never cut, but the edges its registration and
    entry-point rows name stay registered."""
    cuts, problems = {}, []
    claimants: dict[tuple[int, int], set[str]] = collections.defaultdict(set)
    for c, rows in anchors.items():
        edge_rows = [a for a in rows if a.how in EDGE_KINDS]
        cut, found = cut_for(graph, edge_rows)
        if c not in refused:
            cuts[c] = cut
            if c in wanted:
                problems += found
        for edge in cut.edges:
            claimants[edge].add(c)
    return cuts, claimants, problems


def _cut_sets(
    graph: SetCutGraph,
    anchors: Mapping[str, Sequence[Anchor]],
    sets: Mapping[str, Sequence[str]],
    refused: Mapping[str, str],
) -> tuple[dict[str, SetCut], list[str], dict[str, list[str]]]:
    """Cuts each set, and names the members each set ranks: those with an edge
    the set can cut.
    An edge several coordinates delete, such as one handler two dispatch keys
    register, is cut only when the set holds all of them: a key alone does
    not free what another key still registers. A refused key is never cut, so
    the edges it registers always stay."""
    wanted = {c for members in sets.values() for c in members}
    cuts, claimants, problems = _claims(graph, anchors, refused, wanted)
    problems += [
        f"set {name}: no anchor for {c}"
        for name, members in sets.items()
        for c in members
        if c not in cuts and c not in refused
    ]
    results, ranked = {}, {}
    for name, members in sets.items():
        in_set = set(members) - refused.keys()
        groups, shared = {}, set()
        ranked[name] = []
        for c in members:
            if c not in cuts:
                continue
            edges = {e for e in cuts[c].edges if claimants[e] <= in_set}
            # A root whose anchors match no edge, or whose every edge a root
            # outside the set also registers, is not ranked, not a 0 B root.
            if edges:
                ranked[name].append(c)
            if len(edges) < len(cuts[c].edges):
                others = set().union(*(claimants[e] for e in cuts[c].edges)) - in_set
                problems.append(
                    f"set {name}: {c} shares registrations with {sorted(others)[:3]}"
                    f"{' ...' if len(others) > 3 else ''}, which stay"
                )
            own = frozenset(e for e in edges if claimants[e] == {c})
            shared |= edges - own
            if own:
                groups[c] = Cut(own)
        if shared:
            # Cut with the set, never with one of its roots alone.
            groups[SHARED_EDGES] = Cut(frozenset(shared))
        if groups:
            results[name] = graph.cut(groups)
        else:
            problems.append(f"set {name}: no edge to cut; not ranked")
    return results, problems, ranked


def _dead_codes(
    graph: SetCutGraph, results: Mapping[str, SetCut], run_dir: str
) -> dict[Label, DeadCode]:
    """What each set and each of its roots alone delete, by original name and
    by line-number map row."""
    cuts: dict[Label, Sequence[int]] = {}
    for name, result in results.items():
        cuts[Label(name, WHOLE)] = result.dead
        if not _only_root(result):
            for c, nodes in result.alone.items():
                if c != SHARED_EDGES:
                    cuts[Label(name, c)] = nodes
    methods = ReachableObjectType.METHOD
    overloads = Overloads(graph.reachable_names(methods))
    every_cut = {
        i for r in results.values() for i in r.dead if graph.kinds[i] == methods
    }
    positions = PositionMap.read_from(
        os.path.join(run_dir, LINE_NUMBER_MAP), with_unreliable=True
    )
    rows = positions.rows_naming(overloads.removed(graph.names[i] for i in every_cut))
    return {
        label: dead_code(graph, nodes, overloads, rows) for label, nodes in cuts.items()
    }


def _price_dex(
    dex_name: str,
) -> tuple[str, dict[Label, dict[str, int]], dict[str, dict[str, int]]]:
    """Bytes per label in one dex. ANY_ALONE is the union of what each root
    of a set releases alone, deduplicated item by item."""
    job = _job
    if job is None:
        raise RuntimeError("pricing worker started without a job")
    dex = DexReferences(read_dex(job.bundle, dex_name))
    join = FinalJoin(dex, job.renames, job.known, job.lines)
    stats: dict[str, dict[str, int]] = {}
    releases: dict[Label, Release] = {}
    for label, dead in job.dead.items():
        # Join statistics describe each set; per-root joins would repeat them.
        deletion, counts = join.deletion(dead)
        releases[label] = dex.release(deletion)
        if label.part == WHOLE:
            stats[label.set_name] = counts
    alone: dict[str, list[Release]] = collections.defaultdict(list)
    for label, release in releases.items():
        if label.part != WHOLE:
            alone[label.set_name].append(release)
    for set_name, parts in alone.items():
        releases[Label(set_name, ANY_ALONE)] = parts[0].union(*parts[1:])
    sizes = {label: dict(dex.size(r)) for label, r in releases.items()}
    sizes = {label: size for label, size in sizes.items() if size}
    return dex_name, sizes, stats


def _price(
    job: _Job, dex_names: Sequence[str], jobs: int
) -> tuple[dict[Label, dict[str, dict[str, int]]], dict[str, collections.Counter[str]]]:
    """Bytes per label and dex, and join statistics per set, over the
    bundle's dexes."""
    global _job
    _job = job
    by_label: dict[Label, dict[str, dict[str, int]]] = collections.defaultdict(dict)
    joins: dict[str, collections.Counter[str]] = collections.defaultdict(
        collections.Counter
    )
    # fork, so workers share the parsed maps instead of copying them.
    with multiprocessing.get_context("fork").Pool(jobs) as pool:
        # A DEX that fails to parse ends the run: a report that left it out
        # would undercount every set it touches.
        for dex_name, freed, stats in pool.imap_unordered(_price_dex, dex_names):
            for label, sections in freed.items():
                by_label[label][dex_name] = sections
            for set_name, counts in stats.items():
                joins[set_name].update(counts)
    return by_label, joins


def _summarize(bytes_by_dex: Mapping[str, Mapping[str, int]]) -> Summary:
    sections: collections.Counter[str] = collections.Counter()
    stores: collections.Counter[str] = collections.Counter()
    for dex_name, freed in bytes_by_dex.items():
        sections.update(freed)
        stores[store_of(dex_name)] += sum(freed.values())
    return Summary(
        total=sum(sections.values()),
        code=sections["code"],
        bytes=dict(sections),
        by_store=dict(stores),
    )


def _only_root(result: SetCut) -> bool:
    """Whether the set is one root that registers all of its edges alone, so
    that what the root frees alone is what the set frees."""
    return len(result.alone) == 1 and SHARED_EDGES not in result.alone


def _set_report(
    graph: SetCutGraph,
    name: str,
    result: SetCut,
    members: Sequence[str],
    not_ranked: Sequence[str],
    by_label: Mapping[Label, Mapping[str, Mapping[str, int]]],
    join: Mapping[str, int],
) -> SetReport:
    whole = _summarize(by_label.get(Label(name, WHOLE), {}))
    if _only_root(result):
        roots = {c: whole for c in result.alone}
        any_alone = whole
    else:
        # A root whose every edge another root also registers frees 0 B alone.
        roots = {c: _summarize(by_label.get(Label(name, c), {})) for c in members}
        any_alone = _summarize(by_label.get(Label(name, ANY_ALONE), {}))
    counts = collections.Counter(graph.kinds[i] for i in result.dead)
    return SetReport(
        **whole,
        graph_cut={
            "classes": counts[ReachableObjectType.CLASS],
            "methods": counts[ReachableObjectType.METHOD],
            "fields": counts[ReachableObjectType.FIELD],
        },
        roots=roots,
        not_ranked=list(not_ranked),
        shared_in_set=whole["total"] - any_alone["total"],
        join=dict(join),
    )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--run-dir", required=True)
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--graph", help=f"default: <run-dir>/{GRAPH}")
    parser.add_argument("--anchors", required=True)
    parser.add_argument("--sets")
    parser.add_argument("--out", required=True, help="JSON report")
    parser.add_argument("-j", "--jobs", type=int, default=8)
    return parser.parse_args(argv)


def _anchor_sets(
    args: argparse.Namespace,
) -> tuple[dict[str, list[Anchor]], dict[str, str], dict[str, list[str]]]:
    """Every coordinate's anchors, refused coordinates with the reason, and
    the sets."""
    anchors = read_anchors(args.anchors)
    refused = {c: r for c, rows in anchors.items() if (r := refusal(rows))}
    rankable = {c: rows for c, rows in anchors.items() if c not in refused}
    if not rankable:
        raise ValueError("no reachability roots to rank: " + json.dumps(refused))
    if not args.sets:
        return anchors, refused, {"all": sorted(rankable)}
    with open(args.sets) as f:
        sets = json.load(f)
    if not isinstance(sets, dict) or not all(
        isinstance(members, list) and all(isinstance(c, str) for c in members)
        for members in sets.values()
    ):
        raise ValueError(f"{args.sets}: not a JSON object of coordinate lists")
    for name, members in sets.items():
        if not any(c in rankable for c in members):
            raise ValueError(f"set {name} has no reachability roots to rank")
    return anchors, refused, sets


def _load_graph(graph_file: str, kind: Mapping[str, object]) -> SetCutGraph:
    if kind.get("run") == "last":
        logger.warning(
            "a graph from the last reachability run misses code that class "
            "merging and inlining already folded into survivors"
        )
    graph = SetCutGraph.load(graph_file)
    # Without recorded keep reasons, every seed hangs off the generic one.
    if not any(
        k == ReachableObjectType.SEED and name != GENERIC_SEED
        for k, name in zip(graph.kinds, graph.names)
    ):
        raise ValueError(
            f"{graph_file} records no keep reasons: rerun with "
            "-J record_keep_reasons=true"
        )
    return graph


def _require_inputs(run_dir: str, graph_file: str) -> None:
    """Refuses before any work when the graph or a map the join needs is not
    there, naming every missing file."""
    required = [graph_file] + [
        os.path.join(run_dir, name)
        for name in (RENAME_MAP, LINE_NUMBER_MAP, DEBUG_LINE_MAP)
    ]
    missing = [path for path in required if not os.path.exists(path)]
    if missing:
        raise ValueError(
            "missing " + ", ".join(missing) + ": --run-dir must be the directory "
            "the Redex run wrote its graph and maps to"
        )


def rank(args: argparse.Namespace) -> Report:
    started = time.time()
    graph_file = args.graph or os.path.join(args.run_dir, GRAPH)
    _require_inputs(args.run_dir, graph_file)
    kind = _graph_kind(args.run_dir)
    anchors, refused, sets = _anchor_sets(args)
    dexes = inventory(args.bundle)
    for store in dexes.unread:
        logger.warning("not reading DEX store %s: its bytes are not counted", store)
    graph = _load_graph(graph_file, kind)
    results, problems, ranked = _cut_sets(graph, anchors, sets, refused)
    dead = _dead_codes(graph, results, args.run_dir)
    renames = read_rename_map(os.path.join(args.run_dir, RENAME_MAP))
    lines = DebugLineMap.read_from(os.path.join(args.run_dir, DEBUG_LINE_MAP))
    known = frozenset(
        graph.reachable_names(ReachableObjectType.FIELD, ReachableObjectType.METHOD)
    )
    job = _Job(args.bundle, dead, renames, known, lines.method_id_map)
    by_label, joins = _price(job, dexes.dexes, args.jobs)
    return Report(
        meaning=NOT_A_PRICE,
        provenance={
            **_provenance(args.run_dir, graph_file, args.bundle, kind),
            "unread_dex_stores": dexes.unread,
        },
        sets={
            name: _set_report(
                graph,
                name,
                result,
                ranked[name],
                [c for c in sets[name] if c not in ranked[name]],
                by_label,
                joins[name],
            )
            for name, result in results.items()
        },
        refused=refused,
        problems=problems,
        elapsed_s=round(time.time() - started, 1),
    )


def main(argv: Sequence[str] | None = None) -> int:
    logging.basicConfig(level=logging.INFO)
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = rank(args)
    except ValueError as error:
        logger.error("%s", error)
        return 1
    with open(args.out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    for name, summary in report["sets"].items():
        logger.info(
            "%s: graph shows %d B (%d B code) dying; ranking signal, not a byte "
            "price",
            name,
            summary["total"],
            summary["code"],
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
