# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Anchor rows: the reachability edges that removing a key deletes.

One JSON object per line, keyed by the shared coordinate
`bk:<system>/<namespace>/<key>[#variant]`. A key may have several rows, one
per edge:

  {"c": "bk:actions/app/example.Decrypt", "how": "switch-arm",
   "registrar": "Lcom/example/ActionRegistry;.dispatch:(I)Ljava/lang/Object;",
   "handler": "Lcom/example/DecryptAction;"}
  {"c": "bk:routes/app/settings", "how": "entry-point",
   "class": "Lcom/example/SettingsActivity;", "seed": "MANIFEST"}

`switch-arm` and `registry-row` name a registration: the edges from the
registrar (a class, or one of its methods) into the handler class and its
members. `any-handler` names a registration whose handler the reader could
not tell: it holds every edge out of the registrar, so nothing the registrar
references dies without it, and its key is not ranked, since what removing it
frees is unknown. `entry-point` names the seed edges a keep reason gives a class and its
members; `seed` is that reason as the graph names it (`MANIFEST`,
`KEEP: <rule>`), and may be left out only when one reason holds the class. A
row whose class several seeds of that name hold, such as one rule repeated in
two files, is not ranked: the graph cannot tell which one the change removes.
Names are the graph's original descriptors.

Value roots (`read`, `literal-arg`: a flag read or a returned value) are
accepted in the file but refused for ranking: changing a value lets constant
propagation, unused-argument removal and inlining delete code that no
reachability graph shows.
"""

from __future__ import annotations

import collections
import json
import re
from collections.abc import Callable, Sequence
from dataclasses import dataclass

from lib.core import INSTANCE_TYPES, ReachableObjectType
from lib.set_cut import Cut, SetCutGraph

REGISTRATIONS = ("switch-arm", "registry-row")
ANY_HANDLER = "any-handler"
ENTRY_POINTS = ("entry-point",)
# The kinds that name edges
EDGE_KINDS = (*REGISTRATIONS, ANY_HANDLER, *ENTRY_POINTS)
VALUE_ROOTS = ("read", "literal-arg")
# The coordinate grammar of dexvt's boundary tables: a system of a lowercase
# letter and at most 31 more lowercase letters, digits or `-`, and non-empty
# parts in which `%` only escapes `%`, `/` or `#` (`%25`, `%2F`, `%23`). A
# system without namespaces writes `-` (`bk:qpl/-/<marker id>`).
_COORDINATE = re.compile(r"bk:[a-z][a-z0-9-]{0,31}/([^/#]+)/([^/#]+)(?:#([^/#]+))?")
_ESCAPE = re.compile(r"%(25|2[Ff]|23)")
# JSON key -> Anchor field; other keys, such as an alias, are ignored
_FIELDS = {
    "c": "coordinate",
    "how": "how",
    "registrar": "registrar",
    "handler": "handler",
    "class": "entry_class",
    "seed": "seed",
}


@dataclass(frozen=True)
class Anchor:
    coordinate: str
    how: str
    registrar: str = ""
    handler: str = ""
    entry_class: str = ""
    seed: str = ""


def read_anchors(filename: str) -> dict[str, list[Anchor]]:
    """Anchor rows by coordinate. Malformed rows raise ValueError."""
    by_coordinate: dict[str, list[Anchor]] = collections.defaultdict(list)
    with open(filename) as f:
        for number, line in enumerate(f, 1):
            if line.strip():
                anchor = _parse(json.loads(line), f"{filename}:{number}")
                by_coordinate[anchor.coordinate].append(anchor)
    return by_coordinate


def _parse(row: object, where: str) -> Anchor:
    if not isinstance(row, dict):
        raise ValueError(f"{where}: not a JSON object: {row!r}")
    values = {field: row.get(key, "") for key, field in _FIELDS.items()}
    if not all(isinstance(v, str) for v in values.values()):
        raise ValueError(f"{where}: anchor fields must be strings: {row}")
    anchor = Anchor(**values)
    if not is_coordinate(anchor.coordinate):
        raise ValueError(f"{where}: not a bk: coordinate: {row}")
    if anchor.how in REGISTRATIONS and not (anchor.registrar and anchor.handler):
        raise ValueError(f"{where}: {anchor.how} needs registrar and handler")
    if anchor.how == ANY_HANDLER and not anchor.registrar:
        raise ValueError(f"{where}: {ANY_HANDLER} needs registrar")
    if anchor.how in ENTRY_POINTS and not anchor.entry_class:
        raise ValueError(f"{where}: entry-point needs class")
    return anchor


def is_coordinate(text: str) -> bool:
    match = _COORDINATE.fullmatch(text)
    return match is not None and all(
        "%" not in _ESCAPE.sub("", part) for part in match.groups("")
    )


def refusal(anchors: Sequence[Anchor]) -> str | None:
    """Why a key cannot be ranked by its reachability edges, or None."""
    for anchor in anchors:
        if anchor.how in VALUE_ROOTS:
            return (
                "value root: changing a value removes code the reachability "
                "graph cannot see; price it by a real removal"
            )
        if anchor.how == ANY_HANDLER:
            return (
                f"handler unknown: it holds every edge out of {anchor.registrar}, "
                "so what removing it frees cannot be told"
            )
        if anchor.how not in EDGE_KINDS:
            return f"unknown anchor kind {anchor.how!r}"
    return None


def cut_for(graph: SetCutGraph, anchors: Sequence[Anchor]) -> tuple[Cut, list[str]]:
    """The edges a key's anchors delete, and the anchors that match no edge.
    Raises ValueError for an anchor `refusal` rejects."""
    edges: set[tuple[int, int]] = set()
    problems: list[str] = []
    for anchor in anchors:
        if anchor.how in REGISTRATIONS:
            found = _edges_into(
                graph, anchor.handler, _is_registrar(graph, anchor.registrar)
            )
            target = f"from {anchor.registrar} into {anchor.handler}"
        elif anchor.how == ANY_HANDLER:
            found = {
                (u, v)
                for u in _registrar_nodes(graph, anchor.registrar)
                for v in graph.retained(u)
            }
            target = f"from {anchor.registrar}"
        elif anchor.how in ENTRY_POINTS:
            found = _edges_into(graph, anchor.entry_class, _is_seed(graph, anchor.seed))
            target = f"from {anchor.seed or 'a seed'} into {anchor.entry_class}"
            seeds = {u for u, _ in found}
            if len(seeds) > 1:
                # Cutting every seed would claim what the others still hold.
                # Identical rule text in two files is two seeds of one name.
                problems.append(
                    f"{anchor.coordinate}: {len(seeds)} keep reasons hold "
                    f"{anchor.entry_class} "
                    + (
                        f"(several read `{anchor.seed}`)"
                        if anchor.seed
                        else "(name the removed one in `seed`)"
                    )
                )
                continue
        else:
            raise ValueError(f"{anchor.coordinate}: {refusal([anchor])}")
        if not found:
            problems.append(f"{anchor.coordinate}: no edge {target}")
        edges |= found
    return Cut(frozenset(edges)), problems


def _edges_into(
    graph: SetCutGraph, class_name: str, from_source: Callable[[int], bool]
) -> set[tuple[int, int]]:
    """Edges into a class and its members from the nodes `from_source` picks."""
    cls = graph.node(ReachableObjectType.CLASS, class_name)
    targets = ([] if cls is None else [cls]) + list(graph.members(class_name))
    return {(u, v) for v in targets for u in graph.retainers(v) if from_source(u)}


def _is_registrar(graph: SetCutGraph, registrar: str) -> Callable[[int], bool]:
    """Picks the registrar class and its members, or the registrar method.
    Annotation and seed nodes carry type and rule names, never a registrar."""
    return lambda u: graph.kinds[u] not in INSTANCE_TYPES and registrar in (
        graph.names[u],
        graph.declaring_class(u),
    )


def _registrar_nodes(graph: SetCutGraph, registrar: str) -> list[int]:
    """The registrar method, or the registrar class and its members: the
    nodes `_is_registrar` picks."""
    method = graph.node(ReachableObjectType.METHOD, registrar)
    if method is not None:
        return [method]
    cls = graph.node(ReachableObjectType.CLASS, registrar)
    return ([] if cls is None else [cls]) + list(graph.members(registrar))


def _is_seed(graph: SetCutGraph, seed: str) -> Callable[[int], bool]:
    """Picks the seeds of one keep reason, or every seed when `seed` is empty."""
    return lambda u: graph.kinds[u] == ReachableObjectType.SEED and (
        not seed or graph.names[u] == seed
    )
