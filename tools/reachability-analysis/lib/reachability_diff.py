#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

from collections import Counter
from collections.abc import Hashable, Mapping, Set

from .core import (
    INSTANCE_TYPES,
    ReachabilityGraph,
    ReachableObject,
    ReachableObjectType,
)

NEW_NODE_MARKER = "<NEW>"

# A node of the diff. A class, field or method is one node per name:
# (type, name, -1). Each annotation or seed instance is its own node:
# (type, name, its index in `node_records`).
NodeKey = tuple[int, str, int]


def _node_keys(graph: ReachabilityGraph) -> dict[ReachableObject, NodeKey]:
    return {
        node: (node.type, node.name, index if node.type in INSTANCE_TYPES else -1)
        for index, node in enumerate(graph.node_records)
    }


def _identity(node: ReachableObject) -> Hashable:
    """What matches a node across graphs. A class, field or method is its
    name. An annotation or seed instance is its name and the names of its
    retainers: an annotation instance is retained by the class that carries
    it, and a seed by nothing."""
    if node.type not in INSTANCE_TYPES:
        return node.type, node.name
    return (
        node.type,
        node.name,
        frozenset((retainer.type, retainer.name) for retainer in node.preds),
    )


def newly_retained_keys(
    old_graph: ReachabilityGraph, new_graph: ReachabilityGraph
) -> set[NodeKey]:
    """The new graph's nodes that match no old node. Each old node matches
    one new node: of several instances with one identity, as many as the old
    graph has count as old, the first in record order, and the rest as new.
    Such instances are indistinguishable, so which of them is new is
    arbitrary."""
    unmatched = Counter(_identity(node) for node in old_graph.node_records)
    new_keys = set()
    for node, key in _node_keys(new_graph).items():
        identity = _identity(node)
        if unmatched[identity]:
            unmatched[identity] -= 1
        else:
            new_keys.add(key)
    return new_keys


def _logical_adjacency(
    keys: Mapping[ReachableObject, NodeKey],
) -> tuple[dict[NodeKey, set[NodeKey]], dict[NodeKey, set[NodeKey]]]:
    predecessors = {key: set() for key in keys.values()}
    successors = {key: set() for key in keys.values()}

    for node, node_key in keys.items():
        for predecessor in node.preds:
            predecessor_key = keys.get(predecessor)
            if predecessor_key is None:
                continue
            predecessors[node_key].add(predecessor_key)
            successors[predecessor_key].add(node_key)
    return predecessors, successors


def _closure(
    starts: Set[NodeKey],
    adjacency: Mapping[NodeKey, Set[NodeKey]],
    allowed: Set[NodeKey] | None = None,
) -> set[NodeKey]:
    visited = set()
    pending = list(starts)
    while pending:
        node = pending.pop()
        if node in visited or (allowed is not None and node not in allowed):
            continue
        visited.add(node)
        pending.extend(adjacency[node])
    return visited


def build_diff_graph(
    old_graph: ReachabilityGraph, new_graph: ReachabilityGraph
) -> ReachabilityGraph:
    new_keys = newly_retained_keys(old_graph, new_graph)
    output = ReachabilityGraph()
    if not new_keys:
        return output

    marker_key = (ReachableObjectType.ANNO, NEW_NODE_MARKER)
    if marker_key in new_graph.nodes:
        raise ValueError(f"Input graph already contains marker node {marker_key}")

    predecessors, successors = _logical_adjacency(_node_keys(new_graph))
    ancestor_candidates = _closure(new_keys, predecessors)
    roots = {key for key in ancestor_candidates if not predecessors[key]}
    rooted_ancestors = _closure(roots, successors, ancestor_candidates)
    descendants = _closure(new_keys, successors)
    kept_keys = rooted_ancestors | descendants

    copied_nodes = {}
    for key in sorted(kept_keys):
        copied = ReachableObject(key[0], key[1])
        output.add_node(copied)
        copied_nodes[key] = copied

    for predecessor_key in sorted(kept_keys):
        for successor_key in sorted(successors[predecessor_key] & kept_keys):
            output.add_edge(copied_nodes[successor_key], copied_nodes[predecessor_key])

    marker = ReachableObject(ReachableObjectType.ANNO, NEW_NODE_MARKER)
    output.add_node(marker)
    for key in sorted(new_keys):
        output.add_edge(marker, copied_nodes[key])
    return output
