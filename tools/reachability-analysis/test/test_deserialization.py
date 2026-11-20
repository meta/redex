# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import tempfile
import unittest

from lib import analysis, core


class TestGraphDeserialization(unittest.TestCase):
    def test_reachability_graph(self):
        """
        Check that we are able to recover the same graph serialized in
        ReachabilityGraphSerialization.cpp.
        """
        graph_file = os.environ["REACHABILITY_GRAPH_FILE"]
        graph = core.ReachabilityGraph()
        graph.load(graph_file)

        [seed] = graph.get_seed("<SEED>")
        cls = graph.get_node("LFoo;")
        [anno] = graph.get_anno("LAnno;")
        field = graph.get_node("LFoo;.field1:I")
        method = graph.get_node("LFoo;.method1:()I")
        removed_root = graph.get_node("LRemovedRoot;")
        removed_cls = graph.get_node("LRemovedChild;")

        self.assertIs(anno, graph.get_node("LAnno;"))
        self.assertIs(seed, graph.get_node("<SEED>"))

        def assertEdge(pred, succ):
            self.assertIn(succ, pred.succs)
            self.assertIn(pred, succ.preds)

        assertEdge(seed, cls)
        assertEdge(cls, anno)
        assertEdge(cls, method)
        assertEdge(method, field)
        assertEdge(removed_root, removed_cls)

        self.assertDictEqual(removed_root.preds, {})
        roots = {node for node in graph.node_records if len(node.preds) == 0}
        self.assertSetEqual(roots, {seed, removed_root})
        self.assertSetEqual(analysis.get_dominated(graph, set()), set())

    def test_reachability_graph_dump_round_trip(self):
        graph = core.ReachabilityGraph()
        graph.load(os.environ["REACHABILITY_GRAPH_FILE"])

        with tempfile.TemporaryDirectory() as temp_dir:
            first_file = os.path.join(temp_dir, "first-graph")
            second_file = os.path.join(temp_dir, "second-graph")
            graph.dump(first_file)

            round_tripped = core.ReachabilityGraph()
            round_tripped.load(first_file)
            round_tripped.dump(second_file)

            self.assertEqual(set(graph.nodes), set(round_tripped.nodes))
            self.assertEqual(
                {
                    key: [
                        {
                            (predecessor.type, predecessor.name)
                            for predecessor in node.preds
                        }
                        for node in nodes
                    ]
                    for key, nodes in graph.nodes.items()
                },
                {
                    key: [
                        {
                            (predecessor.type, predecessor.name)
                            for predecessor in node.preds
                        }
                        for node in nodes
                    ]
                    for key, nodes in round_tripped.nodes.items()
                },
            )
            with open(first_file, "rb") as first, open(second_file, "rb") as second:
                self.assertEqual(first.read(), second.read())

    def test_refuses_a_graph_of_another_format_version(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "graph")
            with open(os.environ["REACHABILITY_GRAPH_FILE"], "rb") as source:
                data = bytearray(source.read())
            # The version follows the 4-byte magic number.
            data[4:8] = (1).to_bytes(4, "little")
            with open(graph_file, "wb") as output:
                output.write(data)

            with self.assertRaisesRegex(
                core.GraphFormatError,
                "Unsupported graph format version 1; this tool reads version 2",
            ):
                core.ReachabilityGraph().load(graph_file)

    def test_dump_preserves_duplicate_node_records(self):
        graph = core.ReachabilityGraph()
        cls = core.ReachableObject(core.ReachableObjectType.CLASS, "LFoo;")
        first_anno = core.ReachableObject(core.ReachableObjectType.ANNO, "LAnno;")
        second_anno = core.ReachableObject(core.ReachableObjectType.ANNO, "LAnno;")
        graph.add_node(cls)
        graph.add_node(first_anno)
        graph.add_node(second_anno)
        graph.add_edge(first_anno, cls)
        graph.add_edge(second_anno, cls)

        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "graph")
            graph.dump(graph_file)
            round_tripped = core.ReachabilityGraph()
            round_tripped.load(graph_file)

        self.assertEqual(3, len(round_tripped.node_records))
        self.assertEqual(2, len(round_tripped.nodes))
        annotation_records = [
            node
            for node in round_tripped.node_records
            if node.type == core.ReachableObjectType.ANNO
        ]
        self.assertEqual(2, len(annotation_records))
        self.assertTrue(
            all(
                cls.name in {predecessor.name for predecessor in node.preds}
                for node in annotation_records
            )
        )

    def test_load_keeps_every_annotation_instance(self):
        # @JsonAdapter(FooAdapter.class) class Foo {} and
        # @JsonAdapter(BarAdapter.class) class Bar {}, each kept by its own
        # rule: one annotation node per instance, each naming its own adapter.
        graph = core.ReachabilityGraph()
        for owner in ("Foo", "Bar"):
            seed = core.ReachableObject(
                core.ReachableObjectType.SEED, f"KEEP: -keep class {owner}"
            )
            cls = core.ReachableObject(core.ReachableObjectType.CLASS, f"L{owner};")
            anno = core.ReachableObject(core.ReachableObjectType.ANNO, "LJsonAdapter;")
            adapter = core.ReachableObject(
                core.ReachableObjectType.CLASS, f"L{owner}Adapter;"
            )
            for node in (seed, cls, anno, adapter):
                graph.add_node(node)
            graph.add_edge(cls, seed)
            graph.add_edge(anno, cls)
            graph.add_edge(adapter, anno)

        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "graph")
            graph.dump(graph_file)
            loaded = core.ReachabilityGraph()
            loaded.load(graph_file)

        self.assertEqual(
            {
                (core.ReachableObjectType.CLASS, "LFoo;"),
                (core.ReachableObjectType.ANNO, "LJsonAdapter;"),
                (core.ReachableObjectType.CLASS, "LFooAdapter;"),
            },
            {
                (node.type, node.name)
                for node in analysis.get_dominated(loaded, {loaded.get_node("LFoo;")})
            },
        )
        annos = loaded.get_anno("LJsonAdapter;")
        self.assertEqual(
            [(["LBar;"], ["LBarAdapter;"]), (["LFoo;"], ["LFooAdapter;"])],
            sorted(
                (
                    [retainer.name for retainer in anno.preds],
                    [retained.name for retained in anno.succs],
                )
                for anno in annos
            ),
        )
        self.assertEqual(annos, loaded.get_nodes("LJsonAdapter;"))
        with self.assertRaises(ValueError):
            loaded.get_node("LJsonAdapter;")

    def test_get_node_prefers_class_over_annotation(self):
        graph = core.ReachabilityGraph()
        annotation = core.ReachableObject(core.ReachableObjectType.ANNO, "LSame;")
        cls = core.ReachableObject(core.ReachableObjectType.CLASS, "LSame;")
        graph.add_node(annotation)
        graph.add_node(cls)

        self.assertIs(cls, graph.get_node("LSame;"))

    def test_get_nodes_finds_keep_reasons_by_their_stored_names(self):
        graph = core.ReachabilityGraph()
        seeds = [
            core.ReachableObject(core.ReachableObjectType.SEED, name)
            for name in (
                "KEEP: -keep class Foo",
                "KEEP: -keep class Foo",
                "KEEP: -keepclassmembers class Bar { void run(); }",
            )
        ]
        for seed in seeds:
            graph.add_node(seed)

        self.assertEqual(seeds[:2], graph.get_nodes("KEEP: -keep class Foo"))
        self.assertIs(
            seeds[2],
            graph.get_node("KEEP: -keepclassmembers class Bar { void run(); }"),
        )
        with self.assertRaises(KeyError):
            graph.get_nodes("LFoo;.missing:()V")

    def test_combined_graph_looks_up_the_graph_s_own_method_nodes(self):
        # class Foo { void bar() {} }, kept by -keep class Foo { void bar(); },
        # with the override graph's methods.
        graph = core.ReachabilityGraph()
        rule = "KEEP: -keep class Foo { void bar(); }"
        seed = core.ReachableObject(core.ReachableObjectType.SEED, rule)
        foo = core.ReachableObject(core.ReachableObjectType.CLASS, "LFoo;")
        methods = {
            name: core.ReachableObject(core.ReachableObjectType.METHOD, name)
            for name in (
                "LFoo;.bar:()V",
                "LBar;.bar:()V",
                "LBaz;.bar:()V",
                "LQux;.bar:()V",
            )
        }
        for node in (seed, foo, *methods.values()):
            graph.add_node(node)
        graph.add_edge(methods["LFoo;.bar:()V"], seed)
        graph.add_edge(foo, methods["LFoo;.bar:()V"])
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "reachability-graph")
            graph.dump(graph_file)
            combined = core.CombinedGraph(
                graph_file, os.environ["METHOD_OVERRIDE_GRAPH_FILE"]
            )

        loaded = combined.reachability_graph
        [bar] = combined.node("LFoo;.bar:()V")
        [kept] = loaded.get_seed(rule)
        loaded_foo = loaded.get_node("LFoo;")
        self.assertIn(bar, kept.succs)
        self.assertEqual(
            ["LBar;.bar:()V", "LBaz;.bar:()V"],
            sorted(method.name for method in bar.overridden_by),
        )
        self.assertEqual([kept, bar], analysis.shortest_path(kept, bar))
        self.assertEqual([kept], analysis.get_dominators(loaded, bar))
        self.assertIn(loaded_foo, analysis.get_dominated(loaded, {bar}))

    def test_combined_graph_skips_overrides_the_graph_does_not_hold(self):
        # The override graph is dumped before the sweep, so it names
        # LQux;.bar:()V, which marking did not retain.
        graph = core.ReachabilityGraph()
        main = core.ReachableObject(core.ReachableObjectType.METHOD, "LMain;.main:()V")
        methods = {
            name: core.ReachableObject(core.ReachableObjectType.METHOD, name)
            for name in ("LFoo;.bar:()V", "LBar;.bar:()V", "LBaz;.bar:()V")
        }
        for node in (main, *methods.values()):
            graph.add_node(node)
        graph.add_edge(methods["LFoo;.bar:()V"], main)
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "reachability-graph")
            graph.dump(graph_file)
            combined = core.CombinedGraph(
                graph_file, os.environ["METHOD_OVERRIDE_GRAPH_FILE"]
            )

        loaded = combined.reachability_graph
        [loaded_main] = loaded.get_nodes("LMain;.main:()V")
        self.assertEqual(
            ["LBar;.bar:()V", "LBaz;.bar:()V", "LFoo;.bar:()V"],
            sorted(node.name for node in loaded_main.succs),
        )
        with self.assertRaises(KeyError):
            loaded.get_nodes("LQux;.bar:()V")

    def test_method_override_graph(self):
        """
        Check that we are able to recover the same graph serialized in
        MethodOverrideGraphSerialization.cpp.
        """
        graph_file = os.environ["METHOD_OVERRIDE_GRAPH_FILE"]
        graph = core.MethodOverrideGraph()
        graph.load(graph_file)

        m1 = graph.nodes["LFoo;.bar:()V"]
        m2 = graph.nodes["LBar;.bar:()V"]
        m3 = graph.nodes["LBaz;.bar:()V"]
        m4 = graph.nodes["LQux;.bar:()V"]

        def assertEdge(parent, child):
            self.assertIn(child, parent.children)
            self.assertIn(parent, child.parents)

        assertEdge(m1, m2)
        assertEdge(m1, m3)
        assertEdge(m2, m4)
        assertEdge(m3, m4)
