# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import sqlite3
import tempfile
import unittest

from lib import sqlite_export
from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType

from .test_utils import write_diff_graph


class SqliteExportTest(unittest.TestCase):
    def test_exports_faithful_graph_with_named_edge_direction(self):
        graph_file = os.environ["REACHABILITY_GRAPH_FILE"]
        with tempfile.TemporaryDirectory() as temp_dir:
            output_file = os.path.join(temp_dir, "graph.sqlite")
            sqlite_export.export_graph(graph_file, output_file)

            connection = sqlite3.connect(output_file)
            try:
                self.assertEqual(
                    connection.execute("PRAGMA user_version").fetchone()[0], 2
                )
                self.assertEqual(
                    dict(connection.execute("SELECT key, value FROM meta")),
                    {
                        "schema_version": "2",
                        "source_graph": os.path.abspath(graph_file),
                        "source_format": "Redex reachability graph binary v2",
                        "edge_direction": sqlite_export.EDGE_DIRECTION,
                        "dominator_tree_version": "2",
                        "dominator_algorithm": "cooper-harvey-kennedy",
                    },
                )
                self.assertEqual(
                    connection.execute("SELECT count(*) FROM nodes").fetchone()[0], 7
                )
                self.assertEqual(
                    connection.execute("SELECT count(*) FROM edges").fetchone()[0], 5
                )
                self.assertCountEqual(
                    connection.execute(
                        """
                        SELECT retainer.name, retained.name
                        FROM edges
                        JOIN nodes AS retainer ON retainer.id = edges.retainer_id
                        JOIN nodes AS retained ON retained.id = edges.retained_id
                        """
                    ),
                    [
                        ("<SEED>", "LFoo;"),
                        ("LFoo;", "LAnno;"),
                        ("LFoo;", "LFoo;.method1:()I"),
                        ("LFoo;.method1:()I", "LFoo;.field1:I"),
                        ("LRemovedRoot;", "LRemovedChild;"),
                    ],
                )
                self.assertCountEqual(
                    connection.execute(
                        """
                        SELECT name, kind
                        FROM nodes
                        WHERE id NOT IN (SELECT retained_id FROM edges)
                        """
                    ),
                    [("<SEED>", "SEED"), ("LRemovedRoot;", "CLASS")],
                )
                self.assertEqual(
                    connection.execute(
                        """
                        SELECT retainer.name
                        FROM edges
                        JOIN nodes AS retainer
                          ON retainer.id = edges.retainer_id
                        JOIN nodes AS retained
                          ON retained.id = edges.retained_id
                        WHERE retained.name = 'LFoo;' AND retainer.kind = 'SEED'
                        """
                    ).fetchall(),
                    [("<SEED>",)],
                )
                self.assertTrue(
                    {"edges_by_retainer", "edges_by_retained"}.issubset(
                        {
                            row[1]
                            for row in connection.execute("PRAGMA index_list(edges)")
                        }
                    )
                )
                self.assertCountEqual(
                    connection.execute(
                        """
                        SELECT node.name, idom.name, stats.retained_count
                        FROM dom_stats AS stats
                        JOIN nodes AS node ON node.id = stats.node_id
                        LEFT JOIN nodes AS idom ON idom.id = stats.idom_id
                        """
                    ),
                    [
                        ("<SEED>", None, 5),
                        ("LFoo;", "<SEED>", 4),
                        ("LAnno;", "LFoo;", 1),
                        ("LFoo;.method1:()I", "LFoo;", 2),
                        ("LFoo;.field1:I", "LFoo;.method1:()I", 1),
                        ("LRemovedRoot;", None, 2),
                        ("LRemovedChild;", "LRemovedRoot;", 1),
                    ],
                )
                self.assertTrue(
                    {
                        "dom_stats_by_idom",
                        "dom_stats_by_kind_retained_count",
                        "dom_stats_by_retained_count",
                    }.issubset(
                        {
                            row[1]
                            for row in connection.execute(
                                "PRAGMA index_list(dom_stats)"
                            )
                        }
                    )
                )
            finally:
                connection.close()

    def test_materializes_logical_dominator_tree_and_omits_rootless_nodes(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            left = ReachableObject(ReachableObjectType.CLASS, "left")
            right = ReachableObject(ReachableObjectType.CLASS, "right")
            join_from_left = ReachableObject(ReachableObjectType.CLASS, "join")
            join_from_right = ReachableObject(ReachableObjectType.CLASS, "join")
            leaf = ReachableObject(ReachableObjectType.CLASS, "leaf")
            cycle_first = ReachableObject(ReachableObjectType.CLASS, "cycle-first")
            cycle_second = ReachableObject(ReachableObjectType.CLASS, "cycle-second")
            for node in (
                root,
                left,
                right,
                join_from_left,
                join_from_right,
                leaf,
                cycle_first,
                cycle_second,
            ):
                graph.add_node(node)
            graph.add_edge(left, root)
            graph.add_edge(right, root)
            graph.add_edge(join_from_left, left)
            graph.add_edge(join_from_right, right)
            graph.add_edge(leaf, join_from_left)
            graph.add_edge(cycle_first, cycle_second)
            graph.add_edge(cycle_second, cycle_first)

            graph_file = os.path.join(temp_dir, "graph")
            output_file = os.path.join(temp_dir, "graph.sqlite")
            graph.dump(graph_file)
            sqlite_export.export_graph(graph_file, output_file)

            with sqlite3.connect(output_file) as connection:
                rows = connection.execute(
                    """
                    SELECT node.name, idom.name, stats.retained_count
                    FROM dom_stats AS stats
                    JOIN nodes AS node ON node.id = stats.node_id
                    LEFT JOIN nodes AS idom ON idom.id = stats.idom_id
                    ORDER BY node.name
                    """
                ).fetchall()

        self.assertEqual(
            [
                ("<SEED>", None, 5),
                ("join", "<SEED>", 2),
                ("leaf", "join", 1),
                ("left", "<SEED>", 1),
                ("right", "<SEED>", 1),
            ],
            rows,
        )

    def test_refuses_to_overwrite_output(self):
        graph_file = os.environ["REACHABILITY_GRAPH_FILE"]
        with tempfile.NamedTemporaryFile() as output_file:
            with self.assertRaisesRegex(FileExistsError, "already exists"):
                sqlite_export.export_graph(graph_file, output_file.name)

    def test_exports_new_marker_edges_in_retainer_direction(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "diff.graph")
            output_file = os.path.join(temp_dir, "diff.sqlite")
            write_diff_graph(graph_file)
            sqlite_export.export_graph(graph_file, output_file)

            connection = sqlite3.connect(output_file)
            try:
                self.assertCountEqual(
                    connection.execute(
                        """
                        SELECT retainer.name, retainer.kind,
                               retained.name, retained.kind
                        FROM edges
                        JOIN nodes AS retainer ON retainer.id = edges.retainer_id
                        JOIN nodes AS retained ON retained.id = edges.retained_id
                        WHERE retained.name = '<NEW>'
                        """
                    ),
                    [
                        ("LNewAnno;", "ANNO", "<NEW>", "ANNO"),
                        ("LNewClass;", "CLASS", "<NEW>", "ANNO"),
                        ("LNewClass;.field:I", "FIELD", "<NEW>", "ANNO"),
                        ("LNewClass;.method:()V", "METHOD", "<NEW>", "ANNO"),
                    ],
                )
            finally:
                connection.close()
