# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import tempfile
import unittest

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType
from lib.set_cut import Cut, SetCutGraph

CLASS = ReachableObjectType.CLASS
METHOD = ReachableObjectType.METHOD
SEED = ReachableObjectType.SEED
ANNO = ReachableObjectType.ANNO


def _load(edges, extra_nodes=()):
    graph = ReachabilityGraph()
    nodes = {}

    def node(key):
        if key not in nodes:
            nodes[key] = ReachableObject(*key)
            graph.add_node(nodes[key])
        return nodes[key]

    for key in extra_nodes:
        node(key)
    for retainer, retained in edges:
        ReachabilityGraph.add_edge(node(retained), node(retainer))
    with tempfile.TemporaryDirectory() as temp_dir:
        filename = os.path.join(temp_dir, "graph")
        graph.dump(filename)
        return SetCutGraph.load(filename)


def _names(graph, ids):
    return sorted(graph.names[i] for i in ids)


class SetCutTest(unittest.TestCase):
    def setUp(self):
        # A dispatch method registers two handlers; both use a shared library
        # that nothing else uses. As Redex records it, every used method
        # retains its class.
        seed = (SEED, "<SEED>")
        dispatch = (METHOD, "LDispatch;.evaluate:(I)V")
        methods = [
            dispatch,
            (METHOD, "LA;.evaluate:()V"),
            (METHOD, "LB;.evaluate:()V"),
            (METHOD, "LLib;.run:()V"),
            (METHOD, "LAOnly;.run:()V"),
        ]
        self.graph = _load(
            [
                (seed, dispatch),
                (dispatch, (METHOD, "LA;.evaluate:()V")),
                (dispatch, (METHOD, "LB;.evaluate:()V")),
                ((METHOD, "LA;.evaluate:()V"), (METHOD, "LLib;.run:()V")),
                ((METHOD, "LB;.evaluate:()V"), (METHOD, "LLib;.run:()V")),
                ((METHOD, "LA;.evaluate:()V"), (METHOD, "LAOnly;.run:()V")),
            ]
            + [(m, (CLASS, m[1].split(".")[0])) for m in methods]
        )

    def _registration(self, handler):
        graph = self.graph
        dispatch = graph.node(METHOD, "LDispatch;.evaluate:(I)V")
        target = graph.node(METHOD, handler + ".evaluate:()V")
        return Cut(edges=frozenset({(dispatch, target)}))

    def test_members_are_found_by_name(self):
        graph = self.graph
        cls = graph.node(CLASS, "LA;")
        self.assertEqual(_names(graph, graph.retainers(cls)), ["LA;.evaluate:()V"])
        self.assertTrue(graph.reachable_before[cls])
        method = graph.node(METHOD, "LA;.evaluate:()V")
        self.assertEqual(graph.declaring_class(method), "LA;")
        self.assertEqual(list(graph.members("LA;")), [method])
        self.assertIsNone(graph.declaring_class(cls))
        self.assertEqual(
            sorted(graph.reachable_names(CLASS)),
            ["LA;", "LAOnly;", "LB;", "LDispatch;", "LLib;"],
        )

    def test_set_singles_and_shared(self):
        graph = self.graph
        result = graph.cut(
            {"a": self._registration("LA;"), "b": self._registration("LB;")}
        )
        self.assertEqual(
            _names(graph, result.dead),
            [
                "LA;",
                "LA;.evaluate:()V",
                "LAOnly;",
                "LAOnly;.run:()V",
                "LB;",
                "LB;.evaluate:()V",
                "LLib;",
                "LLib;.run:()V",
            ],
        )
        self.assertEqual(
            _names(graph, result.alone["a"]),
            ["LA;", "LA;.evaluate:()V", "LAOnly;", "LAOnly;.run:()V"],
        )
        self.assertEqual(_names(graph, result.alone["b"]), ["LB;", "LB;.evaluate:()V"])
        self.assertEqual(_names(graph, result.shared), ["LLib;", "LLib;.run:()V"])

    def test_overlapping_groups_each_free_the_overlap_alone(self):
        graph = self.graph
        result = graph.cut(
            {"a": self._registration("LA;"), "again": self._registration("LA;")}
        )
        expected = ["LA;", "LA;.evaluate:()V", "LAOnly;", "LAOnly;.run:()V"]
        self.assertEqual(_names(graph, result.alone["a"]), expected)
        self.assertEqual(_names(graph, result.alone["again"]), expected)
        self.assertEqual(result.shared, [])

    def test_no_class_node_is_invented(self):
        # A method whose class has no node, and an array method, which belongs
        # to no class definition.
        graph = _load(
            [
                ((SEED, "<SEED>"), (METHOD, "LSdk;.call:()V")),
                ((SEED, "<SEED>"), (METHOD, "[LFoo;.clone:()Ljava/lang/Object;")),
            ]
        )
        self.assertIsNone(graph.node(CLASS, "LSdk;"))
        array_method = graph.node(METHOD, "[LFoo;.clone:()Ljava/lang/Object;")
        self.assertIsNone(graph.declaring_class(array_method))
        self.assertEqual(len(graph.names), 3)

    def test_a_cut_names_only_graph_edges(self):
        graph = self.graph
        a = graph.node(METHOD, "LA;.evaluate:()V")
        b = graph.node(METHOD, "LB;.evaluate:()V")
        with self.assertRaisesRegex(ValueError, "no edge"):
            graph.cut({"x": Cut(edges=frozenset({(a, b)}))})

    def test_a_kept_class_and_its_members_hang_off_the_seed(self):
        # A kept class and its method retain each other; the seed is the only
        # root, and cutting it frees both.
        seed = (SEED, "KEEP: class Kept")
        cls = (CLASS, "LKept;")
        method = (METHOD, "LKept;.run:()V")
        graph = _load([(seed, cls), (cls, method), (method, cls)])
        self.assertEqual([graph.names[i] for i in graph.roots], ["KEEP: class Kept"])
        self.assertTrue(all(graph.reachable_before))
        seed_id = graph.roots[0]
        result = graph.cut(
            {"k": Cut(edges=frozenset({(seed_id, graph.node(CLASS, "LKept;"))}))}
        )
        self.assertEqual(_names(graph, result.dead), ["LKept;", "LKept;.run:()V"])

    def test_annotation_instances_stay_separate(self):
        # Two classes carry an annotation of the same type, and each instance
        # names a different class. The dump keeps one node per instance; the
        # instance on the live class must not keep what the other one names.
        graph = ReachabilityGraph()

        def add(kind, name):
            node = ReachableObject(kind, name)
            graph.add_node(node)
            return node

        seed = add(SEED, "<SEED>")
        live = add(CLASS, "LLive;")
        register = add(METHOD, "LReg;.register:()V")
        dead = add(CLASS, "LDead;")
        anno_live = add(ANNO, "LMarker;")
        anno_dead = add(ANNO, "LMarker;")
        named_by_live = add(CLASS, "LNamedByLive;")
        named_by_dead = add(CLASS, "LNamedByDead;")
        for retainer, retained in [
            (seed, live),
            (seed, register),
            (register, dead),
            (live, anno_live),
            (dead, anno_dead),
            (anno_live, named_by_live),
            (anno_dead, named_by_dead),
        ]:
            ReachabilityGraph.add_edge(retained, retainer)
        with tempfile.TemporaryDirectory() as temp_dir:
            filename = os.path.join(temp_dir, "graph")
            graph.dump(filename)
            cut_graph = SetCutGraph.load(filename)
        reg = cut_graph.node(METHOD, "LReg;.register:()V")
        dead_id = cut_graph.node(CLASS, "LDead;")
        result = cut_graph.cut({"r": Cut(edges=frozenset({(reg, dead_id)}))})
        self.assertEqual(
            _names(cut_graph, result.dead), ["LDead;", "LMarker;", "LNamedByDead;"]
        )
