#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""What a reachability graph loses when a set of retaining edges is cut.

The graph Redex dumps names each node by (kind, name) and stores, per node,
the nodes that retain it. Its roots are the nodes nothing retains: seeds, one
per keep reason, and the generic `<SEED>` for what Redex keeps without a
recorded reason. Annotation and seed nodes may repeat a name: each is one
annotation instance or one keep reason, retaining only what that instance
names, so they stay separate nodes. Classes, fields and methods have unique
names.

A cut removes edges, such as a registration in a dispatch table. The set cut
is everything reachable before and unreachable after. Each group of a set is
also cut alone; groups may overlap, so what dies with each group alone can
overlap too. What dies only when two or more groups go is shared in the set.
"""

from __future__ import annotations

import array
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field

from .core import INSTANCE_TYPES, ReachabilityGraph, ReachableObjectType


@dataclass(frozen=True)
class Cut:
    """Edges (retainer, retained) of one root, as node ids."""

    edges: frozenset[tuple[int, int]] = frozenset()


@dataclass(frozen=True)
class SetCut:
    """Node ids that die with the whole set, with each group cut alone, and
    only when several groups go together."""

    dead: Sequence[int]
    alone: Mapping[str, Sequence[int]] = field(default_factory=dict)
    shared: Sequence[int] = ()


def _owner_class(kind: int, name: str) -> str | None:
    if kind not in (ReachableObjectType.FIELD, ReachableObjectType.METHOD):
        return None
    # An array method such as `[LFoo;.clone` belongs to no class definition.
    if name.startswith("["):
        return None
    end = name.find(";.")
    return name[: end + 1] if end > 0 else None


class SetCutGraph:
    """Logical reachability graph in compressed sparse rows, both directions."""

    def __init__(
        self,
        kinds: array.array,
        names: list[str],
        retained_by: list[array.array],
    ) -> None:
        """Takes ownership of its arguments."""
        self.kinds = kinds
        self.names = names
        self._ids: dict[tuple[int, str], int] = {
            (kinds[i], name): i
            for i, name in enumerate(names)
            if kinds[i] not in INSTANCE_TYPES
        }
        self._members: dict[str, list[int]] = {}
        for i, name in enumerate(names):
            owner = _owner_class(kinds[i], name)
            if owner is not None:
                self._members.setdefault(owner, []).append(i)
        self._pred_offsets, self._preds = _compress(retained_by)
        self._succ_offsets, self._succs = _invert(self._pred_offsets, self._preds)
        self.roots: list[int] = [
            i for i, retainers in enumerate(retained_by) if not retainers
        ]
        self.reachable_before: bytearray = self.reachable()

    @staticmethod
    def load(filename: str) -> SetCutGraph:
        kinds = array.array("B")
        names: list[str] = []
        retained_by: list[array.array] = []
        for _, node, retainers in ReachabilityGraph().iter_serialized_records(filename):
            kinds.append(node.type)
            names.append(node.name)
            retained_by.append(retainers)
        return SetCutGraph(kinds, names, retained_by)

    def node(self, kind: int, name: str) -> int | None:
        """The class, field or method node of that name; annotation and seed
        instances are not addressable by name."""
        return self._ids.get((kind, name))

    def members(self, class_name: str) -> Sequence[int]:
        """The field and method nodes whose names put them in that class."""
        return self._members.get(class_name, ())

    def reachable_names(self, *kinds: int) -> Iterator[str]:
        """Names of the nodes of these kinds that are reachable before any cut."""
        return (
            name
            for i, name in enumerate(self.names)
            if self.reachable_before[i] and self.kinds[i] in kinds
        )

    def declaring_class(self, node: int) -> str | None:
        """The class a field or method node's name puts it in, else None."""
        return _owner_class(self.kinds[node], self.names[node])

    def retainers(self, node: int) -> Sequence[int]:
        return self._preds[self._pred_offsets[node] : self._pred_offsets[node + 1]]

    def retained(self, node: int) -> Sequence[int]:
        return self._succs[self._succ_offsets[node] : self._succ_offsets[node + 1]]

    def reachable(
        self,
        cut: Cut | None = None,
        seen: bytearray | None = None,
        starts: Iterable[int] | None = None,
    ) -> bytearray:
        """Marks what is reachable from the roots (or from `starts`, on top of
        an existing `seen`) without the cut's edges."""
        if seen is None:
            seen = bytearray(len(self.names))
        if cut is None:
            cut = Cut()
        sources = {u for u, _ in cut.edges}
        stack = []
        for node in self.roots if starts is None else starts:
            if not seen[node]:
                seen[node] = 1
                stack.append(node)
        while stack:
            u = stack.pop()
            check = u in sources
            for v in self.retained(u):
                if seen[v] or (check and (u, v) in cut.edges):
                    continue
                seen[v] = 1
                stack.append(v)
        return seen

    def cut(self, groups: Mapping[str, Cut]) -> SetCut:
        """Raises ValueError for a cut edge the graph does not have."""
        whole = Cut(frozenset().union(*(g.edges for g in groups.values())))
        for u, v in whole.edges:
            if v not in self.retained(u):
                raise ValueError(f"no edge {self.names[u]} -> {self.names[v]}")
        after = self.reachable(whole)
        before = self.reachable_before
        dead = [i for i in range(len(self.names)) if before[i] and not after[i]]
        alone: dict[str, Sequence[int]] = {}
        if len(groups) > 1:
            for name, group in groups.items():
                alone[name] = self._dead_alone(group, whole, after, dead)
        else:
            alone = {name: dead for name in groups}
        any_alone = set().union(*(set(v) for v in alone.values()))
        shared = [i for i in dead if i not in any_alone]
        return SetCut(dead, alone, shared)

    def _dead_alone(
        self, group: Cut, whole: Cut, after: bytearray, dead: Sequence[int]
    ) -> list[int]:
        # Restoring the other groups' edges can only add nodes to `after`:
        # start from it and follow just those edges.
        seen = bytearray(after)
        starts = [v for u, v in whole.edges - group.edges if seen[u]]
        self.reachable(group, seen, starts)
        return [i for i in dead if not seen[i]]


def _compress(rows: list[array.array]) -> tuple[array.array, array.array]:
    offsets = array.array("Q", [0])
    flat = array.array("I")
    for row in rows:
        flat.extend(row)
        offsets.append(len(flat))
    return offsets, flat


def _invert(offsets: array.array, flat: array.array) -> tuple[array.array, array.array]:
    n = len(offsets) - 1
    degree = array.array("Q", [0]) * (n + 1)
    for v in flat:
        degree[v + 1] += 1
    for i in range(n):
        degree[i + 1] += degree[i]
    fill = array.array("Q", degree)
    out = array.array("I", [0]) * len(flat)
    for retained in range(n):
        for j in range(offsets[retained], offsets[retained + 1]):
            u = flat[j]
            out[fill[u]] = retained
            fill[u] += 1
    return degree, out
