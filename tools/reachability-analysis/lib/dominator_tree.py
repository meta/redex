#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

import array
import sqlite3
from collections.abc import Iterator

from .core import instance_kind_names, ReachabilityGraph


_KINDS = ("ANNO", "CLASS", "FIELD", "METHOD", "SEED")
_KIND_CODES = {kind: code for code, kind in enumerate(_KINDS)}
_NO_NODE = 0xFFFFFFFF


def _zeros(typecode: str, size: int) -> array.array:
    return array.array(typecode, [0]) * size


def _logical_nodes(
    connection: sqlite3.Connection,
) -> tuple[array.array, array.array, array.array]:
    raw_node_count = connection.execute("SELECT COUNT(*) FROM nodes").fetchone()[0]
    raw_to_logical = _zeros("I", raw_node_count)
    representative_ids = array.array("I")
    kind_codes = array.array("B")
    previous: tuple[str, str] | None = None
    instance_kinds = instance_kind_names()
    logical_id = -1
    for raw_id, kind, name in connection.execute(
        "SELECT id, kind, name FROM nodes INDEXED BY nodes_by_kind_name "
        "ORDER BY kind, name, id"
    ):
        identity = kind, name
        if identity != previous or kind in instance_kinds:
            logical_id += 1
            representative_ids.append(raw_id)
            kind_codes.append(_KIND_CODES[kind])
            previous = identity
        raw_to_logical[raw_id] = logical_id
    if logical_id >= _NO_NODE:
        raise ValueError("Too many logical nodes for dominator materialization")
    return raw_to_logical, representative_ids, kind_codes


def _prefix_offsets(degrees: array.array) -> array.array:
    offsets = array.array("I", [0])
    total = 0
    for degree in degrees:
        total += degree
        if total >= _NO_NODE:
            raise ValueError("Too many logical edges for dominator materialization")
        offsets.append(total)
    return offsets


def _logical_graph(
    graph: ReachabilityGraph,
    input_filename: str,
    raw_to_logical: array.array,
    logical_node_count: int,
) -> tuple[array.array, array.array, array.array, array.array]:
    virtual_root = logical_node_count
    node_count = logical_node_count + 1
    successor_degrees = _zeros("I", node_count)
    predecessor_degrees = _zeros("I", node_count)
    for raw_retained, _, raw_retainers in graph.iter_serialized_records(input_filename):
        retained = raw_to_logical[raw_retained]
        for raw_retainer in raw_retainers:
            retainer = raw_to_logical[raw_retainer]
            successor_degrees[retainer] += 1
            predecessor_degrees[retained] += 1

    roots = array.array(
        "I",
        (
            logical_id
            for logical_id in range(logical_node_count)
            if predecessor_degrees[logical_id] == 0
        ),
    )
    successor_degrees[virtual_root] = len(roots)
    for root in roots:
        predecessor_degrees[root] += 1

    successor_offsets = _prefix_offsets(successor_degrees)
    predecessor_offsets = _prefix_offsets(predecessor_degrees)
    edge_count = successor_offsets[-1]
    successors = array.array("I", [_NO_NODE]) * edge_count
    predecessors = array.array("I", [_NO_NODE]) * edge_count
    successor_cursors = successor_offsets[:-1]
    predecessor_cursors = predecessor_offsets[:-1]

    for raw_retained, _, raw_retainers in graph.iter_serialized_records(input_filename):
        retained = raw_to_logical[raw_retained]
        for raw_retainer in raw_retainers:
            retainer = raw_to_logical[raw_retainer]
            successors[successor_cursors[retainer]] = retained
            successor_cursors[retainer] += 1
            predecessors[predecessor_cursors[retained]] = retainer
            predecessor_cursors[retained] += 1
    for root in roots:
        successors[successor_cursors[virtual_root]] = root
        successor_cursors[virtual_root] += 1
        predecessors[predecessor_cursors[root]] = virtual_root
        predecessor_cursors[root] += 1
    return successor_offsets, successors, predecessor_offsets, predecessors


def _reverse_postorder(
    successor_offsets: array.array,
    successors: array.array,
    virtual_root: int,
) -> array.array:
    visited = _zeros("B", len(successor_offsets) - 1)
    visited[virtual_root] = 1
    nodes = array.array("I", [virtual_root])
    cursors = array.array("I", [successor_offsets[virtual_root]])
    postorder = array.array("I")
    while nodes:
        node = nodes[-1]
        cursor = cursors[-1]
        if cursor == successor_offsets[node + 1]:
            postorder.append(node)
            nodes.pop()
            cursors.pop()
            continue
        successor = successors[cursor]
        cursors[-1] += 1
        if visited[successor]:
            continue
        visited[successor] = 1
        nodes.append(successor)
        cursors.append(successor_offsets[successor])
    postorder.reverse()
    return postorder


def _intersect(
    left: int,
    right: int,
    immediate_dominators: array.array,
    positions: array.array,
) -> int:
    while left != right:
        while positions[left] > positions[right]:
            left = immediate_dominators[left]
        while positions[right] > positions[left]:
            right = immediate_dominators[right]
    return left


def _immediate_dominators(
    successor_offsets: array.array,
    successors: array.array,
    predecessor_offsets: array.array,
    predecessors: array.array,
    virtual_root: int,
) -> array.array:
    reverse_postorder = _reverse_postorder(successor_offsets, successors, virtual_root)
    positions = array.array("I", [_NO_NODE]) * (virtual_root + 1)
    for position, node in enumerate(reverse_postorder):
        positions[node] = position

    immediate_dominators = array.array("I", [_NO_NODE]) * len(positions)
    immediate_dominators[virtual_root] = virtual_root
    changed = True
    while changed:
        changed = False
        for node in reverse_postorder[1:]:
            new_dominator = _NO_NODE
            for edge in range(predecessor_offsets[node], predecessor_offsets[node + 1]):
                predecessor = predecessors[edge]
                if immediate_dominators[predecessor] == _NO_NODE:
                    continue
                if new_dominator == _NO_NODE:
                    new_dominator = predecessor
                else:
                    new_dominator = _intersect(
                        predecessor,
                        new_dominator,
                        immediate_dominators,
                        positions,
                    )
            if immediate_dominators[node] != new_dominator:
                immediate_dominators[node] = new_dominator
                changed = True
    return immediate_dominators


def _subtree_stats(
    immediate_dominators: array.array,
    logical_node_count: int,
    virtual_root: int,
) -> tuple[array.array, array.array]:
    materialized_idoms = array.array("I", [_NO_NODE]) * logical_node_count
    retained_counts = _zeros("Q", logical_node_count + 1)
    remaining_children = _zeros("I", logical_node_count + 1)
    for node in range(logical_node_count):
        idom = immediate_dominators[node]
        if idom == _NO_NODE:
            continue
        retained_counts[node] = 1
        remaining_children[idom] += 1
        if idom != virtual_root:
            materialized_idoms[node] = idom

    leaves = array.array(
        "I",
        (
            node
            for node in range(logical_node_count)
            if retained_counts[node] != 0 and remaining_children[node] == 0
        ),
    )
    cursor = 0
    while cursor < len(leaves):
        node = leaves[cursor]
        cursor += 1
        idom = immediate_dominators[node]
        retained_counts[idom] += retained_counts[node]
        remaining_children[idom] -= 1
        if idom != virtual_root and remaining_children[idom] == 0:
            leaves.append(idom)
    return materialized_idoms, retained_counts[:-1]


def compute_dominator_stats(
    connection: sqlite3.Connection,
    graph: ReachabilityGraph,
    input_filename: str,
) -> tuple[array.array, array.array, array.array, array.array]:
    raw_to_logical, representative_ids, kind_codes = _logical_nodes(connection)
    logical_node_count = len(representative_ids)
    virtual_root = logical_node_count
    successor_offsets, successors, predecessor_offsets, predecessors = _logical_graph(
        graph,
        input_filename,
        raw_to_logical,
        logical_node_count,
    )
    del raw_to_logical
    immediate_dominators = _immediate_dominators(
        successor_offsets,
        successors,
        predecessor_offsets,
        predecessors,
        virtual_root,
    )
    del successor_offsets, successors, predecessor_offsets, predecessors
    materialized_idoms, retained_counts = _subtree_stats(
        immediate_dominators,
        logical_node_count,
        virtual_root,
    )
    return representative_ids, kind_codes, materialized_idoms, retained_counts


def iter_dominator_rows(
    representative_ids: array.array,
    kind_codes: array.array,
    immediate_dominators: array.array,
    retained_counts: array.array,
) -> Iterator[tuple[int, int | None, str, int]]:
    for logical_id, retained_count in enumerate(retained_counts):
        if retained_count == 0:
            continue
        idom = immediate_dominators[logical_id]
        yield (
            representative_ids[logical_id],
            None if idom == _NO_NODE else representative_ids[idom],
            _KINDS[kind_codes[logical_id]],
            retained_count,
        )
