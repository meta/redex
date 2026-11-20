#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Joins a set cut to the final DEX of the same Redex run.

The graph names code as it was at the graph's pass; the final DEX holds what
later passes made of it. Two maps of the same run connect them:

  * `redex-full-rename-map.txt` names every surviving class, method and field
    of the final DEX by its original name. A final holder dies whole when all
    of its original names are cut.
  * The line-number map and the debug line map give each instruction of a
    final method its position stack: the method it was written in, then the
    methods it was inlined into. Code inlined or merged after the graph's pass
    survives in other methods; an instruction range dies when its stack names
    a cut method. Position names carry no prototype, so a cut claims a name
    only when it removes every reachable overload of it.
"""

from __future__ import annotations

import collections
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass

from debug_line_map import method_key
from lib.core import ReachableObjectType
from lib.set_cut import SetCutGraph

from .dex_pricing import Deletion, DexReferences

RENAME_MAP = "redex-full-rename-map.txt"
LINE_NUMBER_MAP = "redex-line-number-map-v2"
DEBUG_LINE_MAP = "redex-debug-line-map-v2"


def read_rename_map(filename: str) -> dict[str, frozenset[str]]:
    """Final name -> original names, for types, methods and fields. Lines read
    `<kind> <original> -> <final>`. A holder with no original name, such as
    one a later pass synthesized, maps to no names: no cut removes it."""
    final_to_original: dict[str, set[str]] = collections.defaultdict(set)
    with open(filename, encoding="utf-8", errors="replace") as f:
        for line in f:
            kind, _, rest = line.rstrip("\n").partition(" ")
            original, arrow, final = rest.partition(" -> ")
            if arrow and kind != "store":
                names = final_to_original[final]
                if original:
                    names.add(original)
    return {final: frozenset(names) for final, names in final_to_original.items()}


def position_name(method_name: str) -> str | None:
    """`Lcom/a/B;.m:(I)V` -> `com.a.B.m`, the form position stacks use."""
    end = method_name.find(";.")
    colon = method_name.find(":", end)
    if end <= 0 or colon < 0:
        return None
    cls = method_name[1:end].replace("/", ".")
    return cls + "." + method_name[end + 2 : colon]


class Overloads:
    """Reachable methods per position name, so that each cut can tell which of
    its position names it removes entirely."""

    def __init__(self, reachable_methods: Iterable[str]) -> None:
        self._live: collections.Counter[str | None] = collections.Counter(
            map(position_name, reachable_methods)
        )

    def removed(self, cut_methods: Iterable[str]) -> frozenset[str]:
        """Position names whose every reachable overload is in the cut."""
        cut = collections.Counter(map(position_name, cut_methods))
        return frozenset(
            name for name, count in cut.items() if name and count == self._live[name]
        )


@dataclass(frozen=True)
class DeadCode:
    """A cut, by original name, plus the line-number map rows whose stack
    names a method the cut removes entirely."""

    classes: frozenset[str]
    methods: frozenset[str]
    fields: frozenset[str]
    rows: frozenset[int]


def dead_code(
    graph: SetCutGraph,
    nodes: Iterable[int],
    overloads: Overloads,
    rows: Mapping[str, frozenset[int]],
) -> DeadCode:
    """What a cut's dead graph nodes delete, by original name and by row."""
    by_kind: dict[int, set[str]] = collections.defaultdict(set)
    for i in nodes:
        by_kind[graph.kinds[i]].add(graph.names[i])
    methods = by_kind[ReachableObjectType.METHOD]
    dead_rows = frozenset().union(
        *(rows.get(name, ()) for name in overloads.removed(methods))
    )
    return DeadCode(
        frozenset(by_kind[ReachableObjectType.CLASS]),
        frozenset(methods),
        frozenset(by_kind[ReachableObjectType.FIELD]),
        dead_rows,
    )


class FinalJoin:
    """One final dex, its holders named by their original names and indexed
    by them, so that a cut costs time in proportion to what it names.

    `known` holds the graph's reachable field and method names: a member whose
    original names the graph does not know, such as one a later pass
    synthesized, goes with its class. `debug_lines` maps each method to the
    line-number map rows of its instructions."""

    def __init__(
        self,
        dex: DexReferences,
        final_to_original: Mapping[str, frozenset[str]],
        known: frozenset[str],
        debug_lines: Mapping[int, Sequence[tuple[int, int]]],
    ) -> None:
        self.dex = dex
        self._known = known
        self._classes: list[frozenset[str]] = []
        self._fields: list[list[frozenset[str]]] = []
        self._methods: list[list[frozenset[str]]] = []
        self._by_name: dict[str, set[int]] = collections.defaultdict(set)
        self._by_row: dict[int, set[tuple[int, int]]] = collections.defaultdict(set)
        self._lines: dict[tuple[int, int], Sequence[tuple[int, int]]] = {}
        self.methods_without_lines = 0
        for c, cls in enumerate(dex.classes):
            final_cls = dex.type_name(cls.type_index)
            originals = final_to_original.get(final_cls, frozenset({final_cls}))
            fields = [dex.field_name(f.index) for f in cls.fields]
            methods = [dex.method_name(m.index) for m in cls.methods]
            self._classes.append(originals)
            self._fields.append(
                [_originals(n, final_cls, originals, final_to_original) for n in fields]
            )
            self._methods.append(
                [
                    _originals(n, final_cls, originals, final_to_original)
                    for n in methods
                ]
            )
            for names in [originals, *self._fields[c], *self._methods[c]]:
                for name in names:
                    self._by_name[name].add(c)
            self._index_lines(c, debug_lines)

    def _index_lines(
        self, c: int, debug_lines: Mapping[int, Sequence[tuple[int, int]]]
    ) -> None:
        for m, method in enumerate(self.dex.classes[c].methods):
            if not method.insn_units:
                continue
            lines = debug_lines.get(method_key(method.index, self.dex.signature4))
            if not lines:
                self.methods_without_lines += 1
                continue
            self._lines[(c, m)] = lines
            for _, row in lines:
                self._by_row[row].add((c, m))

    def deletion(self, dead: DeadCode) -> tuple[Deletion, dict[str, int]]:
        """What `dead` deletes. A holder goes when all of its original names
        are dead; a class goes whole only when none of its members is still
        reachable in the graph. Also returns how much went which way."""
        touched_rows = {cm for row in dead.rows for cm in self._by_row.get(row, ())}
        touched = {
            c
            for names in (dead.classes, dead.fields, dead.methods)
            for name in names
            for c in self._by_name.get(name, ())
        } | {c for c, _ in touched_rows}
        classes, fields, methods = set(), set(), set()
        ranges: dict[tuple[int, int], list[tuple[int, int]]] = {}
        for c in touched:
            dead_fields = [
                f for f, names in enumerate(self._fields[c]) if _cut(names, dead.fields)
            ]
            dead_methods, dead_ranges = self._dead_methods(c, dead, touched_rows)
            if _cut(self._classes[c], dead.classes) and not self._live_member(c, dead):
                classes.add(c)
                continue
            fields.update((c, f) for f in dead_fields)
            methods.update((c, m) for m in dead_methods)
            ranges.update(((c, m), r) for m, r in dead_ranges.items())
        stats = {
            "classes_whole": len(classes),
            "methods_whole": len(methods),
            "methods_partial": len(ranges),
            "partial_units": sum(e - s for r in ranges.values() for s, e in r),
            "methods_without_lines": self.methods_without_lines,
        }
        deletion = Deletion(
            frozenset(classes), frozenset(methods), frozenset(fields), ranges
        )
        return deletion, stats

    def _live_member(self, c: int, dead: DeadCode) -> bool:
        return any(
            (names & self._known) - dead.fields for names in self._fields[c]
        ) or any((names & self._known) - dead.methods for names in self._methods[c])

    def _dead_methods(
        self, c: int, dead: DeadCode, touched_rows: set[tuple[int, int]]
    ) -> tuple[list[int], dict[int, list[tuple[int, int]]]]:
        """Methods of class `c` that go whole, because all of their original
        names are cut, and the dead code-unit ranges of the others. Positions
        show which code goes, not that its method does: a method whose every
        instruction came from cut methods stays, with a return."""
        whole: list[int] = []
        partial: dict[int, list[tuple[int, int]]] = {}
        for m, method in enumerate(self.dex.classes[c].methods):
            names = self._methods[c][m]
            if _cut(names, dead.methods):
                whole.append(m)
            elif (c, m) in touched_rows:
                method_ranges = _dead_ranges(
                    self._lines[(c, m)], method.insn_units, dead.rows
                )
                if method_ranges:
                    partial[m] = method_ranges
        return whole, partial


def _cut(names: frozenset[str], dead: frozenset[str]) -> bool:
    """Whether a holder with these original names is cut: all of them are
    dead. A holder without original names is never cut."""
    return bool(names) and names <= dead


def _originals(
    final_name: str,
    final_cls: str,
    original_cls: frozenset[str],
    final_to_original: Mapping[str, frozenset[str]],
) -> frozenset[str]:
    originals = final_to_original.get(final_name)
    if originals is not None:
        return originals
    # A member the map leaves out kept its name in its (possibly renamed) class.
    if final_name.startswith(final_cls + "."):
        member = final_name[len(final_cls) :]
        return frozenset(cls + member for cls in original_cls)
    return frozenset({final_name})


def _dead_ranges(
    lines: Sequence[tuple[int, int]], n_units: int, rows: frozenset[int]
) -> list[tuple[int, int]]:
    """[start, end) code-unit ranges whose position row is in `rows`. Each
    (pc, row) entry covers the code up to the next entry's pc."""
    # Redex writes a method's entries in increasing pc order: its debug
    # program walks the code by address. An out-of-order map is broken input
    # and ends the run, like a DEX that fails to parse.
    out: list[tuple[int, int]] = []
    for i, (pc, row) in enumerate(lines):
        end = lines[i + 1][0] if i + 1 < len(lines) else n_units
        if end < pc:
            raise ValueError(f"debug line map entries out of pc order at pc {pc}")
        if end == pc or row not in rows:
            continue
        if out and out[-1][1] == pc:
            out[-1] = (out[-1][0], end)
        else:
            out.append((pc, end))
    return out
