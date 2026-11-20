# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import tempfile
import unittest

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType
from lib.reachability_diff import build_diff_graph, NEW_NODE_MARKER, newly_retained_keys
from lib.sqlite_export import export_graph
from lib.sqlite_query import dominators, new_nodes, open_database


def add_node(graph, node_type, name):
    node = ReachableObject(node_type, name)
    graph.add_node(node)
    return node


def keys(graph):
    return set(graph.nodes)


class ReachabilityDiffTest(unittest.TestCase):
    def test_keeps_rooted_ancestors_and_descendants_of_new_nodes(self):
        old_graph = ReachabilityGraph()
        old_root = add_node(old_graph, ReachableObjectType.SEED, "old root")
        old_ancestor = add_node(old_graph, ReachableObjectType.CLASS, "LAncestor;")
        old_descendant = add_node(old_graph, ReachableObjectType.CLASS, "LDescendant;")
        add_node(old_graph, ReachableObjectType.CLASS, "LUnrelated;")
        old_graph.add_edge(old_ancestor, old_root)
        old_graph.add_edge(old_descendant, old_ancestor)

        new_graph = ReachabilityGraph()
        root = add_node(new_graph, ReachableObjectType.SEED, "old root")
        ancestor = add_node(new_graph, ReachableObjectType.CLASS, "LAncestor;")
        new_node = add_node(new_graph, ReachableObjectType.CLASS, "LNew;")
        descendant = add_node(new_graph, ReachableObjectType.CLASS, "LDescendant;")
        unrelated = add_node(new_graph, ReachableObjectType.CLASS, "LUnrelated;")
        new_graph.add_edge(ancestor, root)
        new_graph.add_edge(new_node, ancestor)
        new_graph.add_edge(descendant, new_node)
        new_graph.add_edge(unrelated, root)

        result = build_diff_graph(old_graph, new_graph)

        self.assertEqual(
            {
                (ReachableObjectType.ANNO, NEW_NODE_MARKER),
                (ReachableObjectType.CLASS, "LAncestor;"),
                (ReachableObjectType.CLASS, "LDescendant;"),
                (ReachableObjectType.CLASS, "LNew;"),
                (ReachableObjectType.SEED, "old root"),
            },
            keys(result),
        )
        self.assertNotIn((ReachableObjectType.CLASS, "LUnrelated;"), result.nodes)

        copied_new = result.get_node("LNew;")
        marker = result.get_anno(NEW_NODE_MARKER)
        self.assertEqual({copied_new}, set(marker.preds))
        self.assertIn(marker, copied_new.succs)
        self.assertIn(result.get_node("LAncestor;"), copied_new.preds)
        self.assertIn(result.get_node("LDescendant;"), copied_new.succs)

    def test_excludes_predecessors_without_a_path_from_a_root(self):
        old_graph = ReachabilityGraph()
        old_root = add_node(old_graph, ReachableObjectType.SEED, "root")
        old_ancestor = add_node(old_graph, ReachableObjectType.CLASS, "LAncestor;")
        old_cycle_a = add_node(old_graph, ReachableObjectType.CLASS, "LCycleA;")
        old_cycle_b = add_node(old_graph, ReachableObjectType.CLASS, "LCycleB;")
        old_graph.add_edge(old_ancestor, old_root)
        old_graph.add_edge(old_cycle_b, old_cycle_a)
        old_graph.add_edge(old_cycle_a, old_cycle_b)

        new_graph = ReachabilityGraph()
        root = add_node(new_graph, ReachableObjectType.SEED, "root")
        ancestor = add_node(new_graph, ReachableObjectType.CLASS, "LAncestor;")
        new_node = add_node(new_graph, ReachableObjectType.CLASS, "LNew;")
        cycle_a = add_node(new_graph, ReachableObjectType.CLASS, "LCycleA;")
        cycle_b = add_node(new_graph, ReachableObjectType.CLASS, "LCycleB;")
        new_graph.add_edge(ancestor, root)
        new_graph.add_edge(new_node, ancestor)
        new_graph.add_edge(cycle_b, cycle_a)
        new_graph.add_edge(cycle_a, cycle_b)
        new_graph.add_edge(new_node, cycle_a)

        result = build_diff_graph(old_graph, new_graph)

        self.assertNotIn((ReachableObjectType.CLASS, "LCycleA;"), result.nodes)
        self.assertNotIn((ReachableObjectType.CLASS, "LCycleB;"), result.nodes)
        self.assertIn((ReachableObjectType.CLASS, "LNew;"), result.nodes)

    def test_duplicate_labels_contribute_all_edges(self):
        old_graph = ReachabilityGraph()
        add_node(old_graph, ReachableObjectType.SEED, "root")
        add_node(old_graph, ReachableObjectType.ANNO, "LAnno;")

        new_graph = ReachabilityGraph()
        root = add_node(new_graph, ReachableObjectType.SEED, "root")
        first_anno = add_node(new_graph, ReachableObjectType.ANNO, "LAnno;")
        add_node(new_graph, ReachableObjectType.ANNO, "LAnno;")
        new_node = add_node(new_graph, ReachableObjectType.CLASS, "LNew;")
        new_graph.add_edge(first_anno, root)
        new_graph.add_edge(new_node, first_anno)

        result = build_diff_graph(old_graph, new_graph)

        self.assertIn((ReachableObjectType.SEED, "root"), result.nodes)
        self.assertIn((ReachableObjectType.ANNO, "LAnno;"), result.nodes)
        copied_anno = result.get_anno("LAnno;")
        self.assertIn(result.get_seed("root"), copied_anno.preds)
        self.assertIn(result.get_node("LNew;"), copied_anno.succs)

    def test_annotation_instances_stay_apart(self):
        def add_json_adapter_class(graph, owner):
            # @JsonAdapter(<owner>Adapter.class) class <owner> {}, kept by its
            # own rule.
            seed = add_node(
                graph, ReachableObjectType.SEED, f"KEEP: -keep class {owner}"
            )
            cls = add_node(graph, ReachableObjectType.CLASS, f"L{owner};")
            anno = add_node(graph, ReachableObjectType.ANNO, "LJsonAdapter;")
            adapter = add_node(graph, ReachableObjectType.CLASS, f"L{owner}Adapter;")
            graph.add_edge(cls, seed)
            graph.add_edge(anno, cls)
            graph.add_edge(adapter, anno)

        old_graph = ReachabilityGraph()
        add_json_adapter_class(old_graph, "Foo")
        new_graph = ReachabilityGraph()
        add_json_adapter_class(new_graph, "Foo")
        add_json_adapter_class(new_graph, "Bar")

        result = build_diff_graph(old_graph, new_graph)
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "diff.graph")
            db_file = os.path.join(temp_dir, "diff.sqlite")
            result.dump(graph_file)
            export_graph(graph_file, db_file)
            connection = open_database(db_file)
            try:
                adapter_dominators = dominators(connection, ("CLASS", "LBarAdapter;"))
            finally:
                connection.close()

        self.assertEqual(
            [
                {"type": "ANNO", "name": "LJsonAdapter;"},
                {"type": "CLASS", "name": "LBar;"},
                {"type": "SEED", "name": "KEEP: -keep class Bar"},
            ],
            adapter_dominators,
        )
        # Foo's annotation instance is in both graphs, so nothing of Foo is new.
        self.assertNotIn((ReachableObjectType.CLASS, "LFoo;"), result.nodes)

    def test_new_nodes_lists_each_new_annotation_instance(self):
        def add_json_adapter_class(graph, owner):
            # @JsonAdapter(<owner>Adapter.class) class <owner> {}
            cls = add_node(graph, ReachableObjectType.CLASS, f"L{owner};")
            anno = add_node(graph, ReachableObjectType.ANNO, "LJsonAdapter;")
            graph.add_edge(anno, cls)

        old_graph = ReachabilityGraph()
        new_graph = ReachabilityGraph()
        add_json_adapter_class(new_graph, "Bar")
        add_json_adapter_class(new_graph, "Baz")

        result = build_diff_graph(old_graph, new_graph)
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "diff.graph")
            db_file = os.path.join(temp_dir, "diff.sqlite")
            result.dump(graph_file)
            export_graph(graph_file, db_file)
            connection = open_database(db_file)
            try:
                rows = list(new_nodes(connection, None))
            finally:
                connection.close()

        self.assertEqual(len(newly_retained_keys(old_graph, new_graph)), len(rows))
        self.assertEqual(
            [
                {"type": "ANNO", "name": "LJsonAdapter;"},
                {"type": "ANNO", "name": "LJsonAdapter;"},
                {"type": "CLASS", "name": "LBar;"},
                {"type": "CLASS", "name": "LBaz;"},
            ],
            rows,
        )

    def test_each_old_instance_matches_one_new_instance(self):
        # `-keep class Foo` in one configuration file, then in two.
        def add_keep_rules(graph, count):
            cls = add_node(graph, ReachableObjectType.CLASS, "LFoo;")
            for _ in range(count):
                seed = add_node(
                    graph, ReachableObjectType.SEED, "KEEP: -keep class Foo"
                )
                graph.add_edge(cls, seed)

        old_graph = ReachabilityGraph()
        add_keep_rules(old_graph, 1)
        new_graph = ReachabilityGraph()
        add_keep_rules(new_graph, 2)

        self.assertEqual(
            {(ReachableObjectType.SEED, "KEEP: -keep class Foo")},
            {key[:2] for key in newly_retained_keys(old_graph, new_graph)},
        )
        self.assertEqual(1, len(newly_retained_keys(old_graph, new_graph)))
        self.assertNotEqual([], build_diff_graph(old_graph, new_graph).node_records)

    def test_empty_diff_produces_empty_graph(self):
        old_graph = ReachabilityGraph()
        add_node(old_graph, ReachableObjectType.CLASS, "LFoo;")
        new_graph = ReachabilityGraph()
        add_node(new_graph, ReachableObjectType.CLASS, "LFoo;")

        result = build_diff_graph(old_graph, new_graph)

        self.assertEqual({}, result.nodes)
        self.assertEqual([], result.node_records)
