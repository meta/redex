#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from collections import defaultdict, deque

from . import core  # noqa F401
from .core import ReachableObjectType


"""
Just a kitchen sink of methods that may be useful when analyzing the
reachability graph. We may want to refine / prune this file in the future.
"""


def classify_nodes(nodes):
    """
    Return a summary count of the number of each kind of node.
    """
    ctr = defaultdict(int)
    for node in nodes:
        ctr[ReachableObjectType.to_string(node.type)] += 1
    return ctr


def group_by_common_keys(d):
    """
    The input :d should be a dict whose values are sets. Suppose we had

      k1 -> set(v1, v2, v3)
      k2 -> set(v1, v2)
      k3 -> set(v1, v2)

    The output will be

      frozenset(k1, k2, k3) -> set(v1, v2)
      frozenset(k1) -> set(v3)

    This can be useful for finding keep rules which overlap a lot in their
    matched classes.
    """
    value_to_keys = defaultdict(set)
    for k, values in list(d.items()):
        for v in values:
            value_to_keys[v].add(k)

    grouped_keys = defaultdict(set)
    for value, keys in list(value_to_keys.items()):
        grouped_keys[frozenset(keys)].add(value)

    return grouped_keys


def _all_nodes(graph):
    for nodes in graph.nodes.values():
        yield from nodes


def find_nodes(graph, filter_fn):
    """
    Find all nodes whose names pass the predicate :filter_fn.
    """
    nodes = set()
    for node in _all_nodes(graph):
        if filter_fn(node.name):
            nodes.add(node)
    return nodes


def find_nodes_in_packages(graph, pkg_prefixes):
    """
    Find all nodes that fall under the list of :pkg_prefixes.
    """
    nodes = set()
    for node in _all_nodes(graph):
        for pkg_prefix in pkg_prefixes:
            # If we have an array, use its base type
            base_type = node.name.lstrip("[")
            if base_type.startswith(pkg_prefix):
                nodes.add(node)
    return nodes


def find_boundary(graph, query_set):
    """
    Find all the nodes that retain (i.e. point into) :query_set.

    If we encounter an annotation node, we look for its retainers. Frequently,
    they are members of the set itself. E.g. we have many instances of

        @JsonSerialize(Foo.class)
        public Foo { ... }

    We don't want to mark JsonSerialize as a retainer of Foo.

    Return a dictionary of

      <retaining node> -> <set of retained nodes>

    where the set of retained nodes are the immediate successors of the
    retaining node that are inside :query_set.
    """
    boundary = defaultdict(set)
    to_visit = set(query_set)
    visited = set()
    while len(to_visit) > 0:
        node = to_visit.pop()
        if node in visited:
            continue
        visited.add(node)

        for pred in node.preds:
            if pred not in query_set:
                if not pred.type == ReachableObjectType.ANNO:
                    boundary[pred].add(node)
                else:
                    to_visit.add(pred)
    return boundary


def group_members_by_class(graph):
    """
    Return a map of class -> set of members in that class.
    """
    grouped_members = defaultdict(set)
    for node in _all_nodes(graph):
        if node.type in [ReachableObjectType.FIELD, ReachableObjectType.METHOD]:
            cls, sep, _ = node.name.partition(";")
            cls += ";"
            # An owner outside the app has no class node.
            cls_nodes = graph.nodes.get((ReachableObjectType.CLASS, cls))
            if cls_nodes is None:
                continue
            # A class has one node per name; only annotation and seed nodes are
            # per instance.
            [cls_node] = cls_nodes
            grouped_members[cls_node].add(node)
    return grouped_members


def find_package_references(graph, pkg_prefixes):
    """
    Find all nodes that retain classes under the list of :pkg_prefixes.
    """
    query_set = find_nodes_in_packages(graph, pkg_prefixes)
    return find_boundary(graph, query_set)


def get_dominated(graph, query_set):
    """
    Find all nodes in the graph that cannot be reached from a root without
    passing through :query_set.
    """
    visited = set()

    def mark(start):
        to_visit = {start}
        while to_visit:
            node = to_visit.pop()
            if node in visited or node in query_set:
                continue
            visited.add(node)
            to_visit.update(
                successor
                for successor in node.succs
                if successor not in visited and successor not in query_set
            )

    seeds = [node for node in _all_nodes(graph) if len(node.preds) == 0]

    for seed in seeds:
        mark(seed)

    closure = set()
    for node in _all_nodes(graph):
        if node not in visited:
            closure.add(node)

    return closure


def _get_ancestors(target):
    ancestors = set()
    queue = deque([target])
    while queue:
        node = queue.popleft()
        if node in ancestors:
            continue
        ancestors.add(node)
        queue.extend(node.preds)
    return ancestors


def _reverse_postorder(roots, ancestors, virtual_root):
    visited = {virtual_root}
    postorder = []
    stack = [(virtual_root, iter(roots))]
    while stack:
        node, successors = stack[-1]
        try:
            successor = next(successors)
        except StopIteration:
            postorder.append(node)
            stack.pop()
            continue
        if successor in visited or successor not in ancestors:
            continue
        visited.add(successor)
        stack.append((successor, iter(successor.succs)))
    return list(reversed(postorder))


def _intersect_idoms(left, right, immediate_dominators, positions):
    while left is not right:
        while positions[left] > positions[right]:
            left = immediate_dominators[left]
        while positions[right] > positions[left]:
            right = immediate_dominators[right]
    return left


def get_dominators(graph, target):
    """Return target's proper dominators, ordered from nearest to root."""
    ancestors = _get_ancestors(target)
    roots = [
        node for node in _all_nodes(graph) if node in ancestors and len(node.preds) == 0
    ]

    virtual_root = object()
    reverse_postorder = _reverse_postorder(roots, ancestors, virtual_root)
    positions = {node: position for position, node in enumerate(reverse_postorder)}
    if target not in positions:
        raise ValueError(f"Node {target.name!r} is not reachable from any root")

    immediate_dominators = {virtual_root: virtual_root}
    changed = True
    while changed:
        changed = False
        for node in reverse_postorder[1:]:
            predecessors = [
                predecessor
                for predecessor in node.preds
                if predecessor in immediate_dominators
            ]
            if len(node.preds) == 0:
                predecessors.append(virtual_root)
            if not predecessors:
                continue
            new_dominator = predecessors[0]
            for predecessor in predecessors[1:]:
                new_dominator = _intersect_idoms(
                    predecessor,
                    new_dominator,
                    immediate_dominators,
                    positions,
                )
            if immediate_dominators.get(node) is not new_dominator:
                immediate_dominators[node] = new_dominator
                changed = True

    dominators = []
    node = target
    while immediate_dominators[node] is not virtual_root:
        node = immediate_dominators[node]
        dominators.append(node)
    return dominators


def shortest_path(start, end):
    """Return a shortest path from start to end following successor edges."""
    queue = deque([start])
    parents = {start: None}
    while queue:
        node = queue.popleft()
        if node is end:
            path = []
            while node is not None:
                path.append(node)
                node = parents[node]
            return list(reversed(path))
        for successor in node.succs:
            if successor not in parents:
                parents[successor] = node
                queue.append(successor)
    return None


class Ranker(object):
    """
    Given a list of leak roots and leaked methods, rank the roots in order of
    classes that they retain. We do this by making a weighted count of the
    number of nodes reachable from each root. Methods are weighted most heavily
    and fields least. For a given node reachable from N roots, we divide its
    weight by N when calculating its contribution to each root's score. This is
    similar to the LeakShare metric described in "BLeak: Automatically Debugging
    Memory Leaks in Web Applications" by Vilk and Berger.

    While calculating the ranking, we also record the set of leaked nodes
    dominated by each root, i.e. the set of nodes that are only reachable via
    that root.
    """

    def __init__(self, roots, leaked_set):
        self.counts = defaultdict(int)
        self.leaked_set = leaked_set
        for root in roots:
            self.mark(root)

    def mark(self, root):
        """
        Populate self.counts so that it contains, for each leaked node, the
        number of leak roots that it can be reached from.
        """
        visited = set()

        # Recursive solution does not work well for deep graphs
        def mark_iter(node):
            queue = deque([node])

            while queue:
                node = queue.popleft()
                if node in visited or node not in self.leaked_set:
                    continue

                visited.add(node)
                self.counts[node] += 1
                queue.extend(node.succs)

        for succ in root.succs:
            mark_iter(succ)

    def get_rank(self, root):
        rank = 0.0
        dominated = set()
        visited = set()

        # Recursive solution does not work well for deep graphs
        def visit_iter(node):
            nonlocal rank
            nonlocal dominated

            queue = deque([node])

            while queue:
                node = queue.popleft()

                if node in visited or node not in self.leaked_set:
                    continue
                visited.add(node)

                if self.counts[node] == 1:
                    dominated.add(node)
                if node.type == ReachableObjectType.METHOD:
                    rank += 1.0 / self.counts[node]

                queue.extend(node.succs)

        for succ in root.succs:
            visit_iter(succ)

        return (rank, dominated)


def rank(roots, leaked_set):
    ranker = Ranker(roots, leaked_set)
    results = [(root, ranker.get_rank(root)) for root in roots]
    return sorted(results, key=lambda t: t[1][0], reverse=True)
