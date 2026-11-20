# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import csv
import io
import json
import os
import shutil
import sqlite3
import subprocess
import tempfile
import unittest

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType
from lib.sqlite_export import export_graph

from .test_utils import write_diff_graph


class GraphQueryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls._temp_dir = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls._temp_dir.cleanup)
        cls.db_file = os.path.join(cls._temp_dir.name, "reachability.sqlite")
        export_graph(os.environ["REACHABILITY_GRAPH_FILE"], cls.db_file)

    def _invoke(self, db_file, output_format, *query_args):
        return subprocess.run(
            [
                os.environ["GRAPH_QUERY"],
                "--db",
                db_file,
                "--format",
                output_format,
                *query_args,
            ],
            capture_output=True,
            text=True,
        )

    def _run_db(self, db_file, output_format, *query_args):
        result = self._invoke(db_file, output_format, *query_args)
        self.assertEqual(0, result.returncode, result.stderr)
        return result.stdout

    def _run(self, output_format, *query_args):
        return self._run_db(self.db_file, output_format, *query_args)

    def _copy_db(self, directory):
        db_file = os.path.join(directory, "reachability.sqlite")
        shutil.copyfile(self.db_file, db_file)
        return db_file

    def _write_graph_db(self, graph, directory):
        graph_file = os.path.join(directory, "reachability.graph")
        db_file = os.path.join(directory, "reachability.sqlite")
        graph.dump(graph_file)
        export_graph(graph_file, db_file)
        return db_file

    def test_roots_filters_by_kind_and_limit(self):
        output = self._run("json", "roots", "--kind", "class", "--limit", "1")

        self.assertEqual(
            [{"type": "CLASS", "name": "LRemovedRoot;"}], json.loads(output)
        )

    def test_roots_supports_csv_and_table_output(self):
        csv_output = self._run("csv", "roots", "--kind", "class", "--limit", "1")
        self.assertEqual(
            [{"type": "CLASS", "name": "LRemovedRoot;"}],
            list(csv.DictReader(io.StringIO(csv_output))),
        )

        table_output = self._run("table", "roots", "--kind", "class", "--limit", "1")
        self.assertIn("type", table_output)
        self.assertIn("CLASS", table_output)
        self.assertIn("LRemovedRoot;", table_output)

    def test_roots_collapse_duplicate_logical_nodes(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._copy_db(temp_dir)
            with sqlite3.connect(db_file) as connection:
                duplicate_id = connection.execute(
                    "SELECT MAX(id) + 1 FROM nodes"
                ).fetchone()[0]
                seed_id = connection.execute(
                    "SELECT id FROM nodes WHERE kind = 'SEED' AND name = '<SEED>'"
                ).fetchone()[0]
                connection.execute(
                    "INSERT INTO nodes(id, kind, name) VALUES (?, 'CLASS', ?)",
                    (duplicate_id, "LRemovedRoot;"),
                )
                connection.execute(
                    "INSERT INTO edges(retainer_id, retained_id) VALUES (?, ?)",
                    (seed_id, duplicate_id),
                )

            output = self._run_db(db_file, "json", "roots", "--kind", "class")

        self.assertEqual([], json.loads(output))

    def test_rejects_invalid_catalog_metadata(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._copy_db(temp_dir)
            with sqlite3.connect(db_file) as connection:
                connection.execute(
                    "UPDATE meta SET value = 'backwards' WHERE key = 'edge_direction'"
                )

            result = self._invoke(db_file, "json", "roots")

        self.assertEqual(1, result.returncode)
        self.assertEqual("", result.stdout)
        self.assertEqual(
            "Error: Invalid reachability SQLite metadata: edge_direction\n",
            result.stderr,
        )

    def test_reports_catalog_errors_without_a_traceback(self):
        with tempfile.NamedTemporaryFile() as db_file:
            result = subprocess.run(
                [
                    os.environ["GRAPH_QUERY"],
                    "--db",
                    db_file.name,
                    "roots",
                ],
                capture_output=True,
                text=True,
            )

        self.assertEqual(1, result.returncode)
        self.assertEqual("", result.stdout)
        self.assertEqual(
            "Error: Unsupported reachability SQLite schema version 0; expected 2\n",
            result.stderr,
        )

    def test_help_exposes_only_sqlite_input(self):
        result = subprocess.run(
            [os.environ["GRAPH_QUERY"], "--help"],
            capture_output=True,
            text=True,
        )

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("--db", result.stdout)
        self.assertNotIn("--input", result.stdout)

    def test_semantic_roots_resolves_seed_reasons_and_excludes_non_program_nodes(
        self,
    ):
        output = self._run("json", "semantic-roots")

        self.assertEqual(
            [
                {"type": "CLASS", "name": "LFoo;", "reason": "<SEED>"},
                {"type": "CLASS", "name": "LRemovedRoot;", "reason": ""},
            ],
            json.loads(output),
        )

    def test_neighbors_labels_both_edge_directions(self):
        output = self._run("csv", "neighbors", "LFoo;")

        self.assertEqual(
            [
                {"direction": "retainer", "type": "SEED", "name": "<SEED>"},
                {"direction": "retained", "type": "ANNO", "name": "LAnno;"},
                {
                    "direction": "retained",
                    "type": "METHOD",
                    "name": "LFoo;.method1:()I",
                },
            ],
            list(csv.DictReader(io.StringIO(output))),
        )

    def test_neighbors_resolves_annotation_names(self):
        output = self._run("json", "neighbors", "LAnno;", "--direction", "retainers")

        self.assertEqual(
            [{"direction": "retainer", "type": "CLASS", "name": "LFoo;"}],
            json.loads(output),
        )

    def test_table_format_and_missing_node_error(self):
        output = self._run("table", "neighbors", "LFoo;", "--direction", "retainers")
        self.assertIn("direction", output)
        self.assertIn("retainer", output)
        self.assertIn("<SEED>", output)

        result = self._invoke(self.db_file, "table", "neighbors", "LMissing;")
        self.assertEqual(1, result.returncode)
        self.assertEqual("Error: No node named 'LMissing;'\n", result.stderr)

    def test_neighbors_disambiguates_class_and_annotation_names(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            class_node = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            annotation_node = ReachableObject(ReachableObjectType.ANNO, "LCollision;")
            annotation_retainer = ReachableObject(
                ReachableObjectType.CLASS, "LAnnotationRetainer;"
            )
            for node in (class_node, annotation_node, annotation_retainer):
                graph.add_node(node)
            graph.add_edge(annotation_node, annotation_retainer)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(
                db_file,
                "json",
                "neighbors",
                "LCollision;",
                "--kind",
                "anno",
                "--direction",
                "retainers",
            )

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [
                {
                    "direction": "retainer",
                    "type": "CLASS",
                    "name": "LAnnotationRetainer;",
                }
            ],
            json.loads(result.stdout),
        )

    def test_path_follows_retainer_to_retained(self):
        output = self._run("json", "path", "<SEED>", "LFoo;.field1:I")
        rows = json.loads(output)

        self.assertEqual(
            [
                "<SEED>",
                "LFoo;",
                "LFoo;.method1:()I",
                "LFoo;.field1:I",
            ],
            [row["name"] for row in rows],
        )
        self.assertEqual([0, 1, 2, 3], [row["step"] for row in rows])

    def test_path_reports_no_path(self):
        self.assertEqual(
            [{"status": "no path", "step": "", "type": "", "name": ""}],
            json.loads(self._run("json", "path", "LFoo;.field1:I", "<SEED>")),
        )

    def test_path_disambiguates_both_endpoint_names(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            start = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            target = ReachableObject(ReachableObjectType.ANNO, "LTarget;")
            for node in (
                start,
                ReachableObject(ReachableObjectType.ANNO, "LCollision;"),
                ReachableObject(ReachableObjectType.CLASS, "LTarget;"),
                target,
            ):
                graph.add_node(node)
            graph.add_edge(target, start)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(
                db_file,
                "json",
                "path",
                "LCollision;",
                "LTarget;",
                "--from-kind",
                "class",
                "--to-kind",
                "anno",
            )

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [
                {
                    "status": "found",
                    "step": 0,
                    "type": "CLASS",
                    "name": "LCollision;",
                },
                {
                    "status": "found",
                    "step": 1,
                    "type": "ANNO",
                    "name": "LTarget;",
                },
            ],
            json.loads(result.stdout),
        )

    def test_path_to_root_follows_shortest_retainer_chain(self):
        output = self._run("json", "path-to-root", "LFoo;.field1:I")

        self.assertEqual(
            [
                {
                    "status": "found",
                    "step": 0,
                    "type": "FIELD",
                    "name": "LFoo;.field1:I",
                },
                {
                    "status": "found",
                    "step": 1,
                    "type": "METHOD",
                    "name": "LFoo;.method1:()I",
                },
                {
                    "status": "found",
                    "step": 2,
                    "type": "CLASS",
                    "name": "LFoo;",
                },
                {
                    "status": "found",
                    "step": 3,
                    "type": "SEED",
                    "name": "<SEED>",
                },
            ],
            json.loads(output),
        )

    def test_path_to_root_returns_a_root_and_supports_formats(self):
        csv_output = self._run("csv", "path-to-root", "<SEED>")
        self.assertEqual(
            [
                {
                    "status": "found",
                    "step": "0",
                    "type": "SEED",
                    "name": "<SEED>",
                }
            ],
            list(csv.DictReader(io.StringIO(csv_output))),
        )

        table_output = self._run("table", "path-to-root", "<SEED>")
        self.assertIn("status", table_output)
        self.assertIn("<SEED>", table_output)

    def test_path_to_root_chooses_the_nearest_root(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            selected = ReachableObject(ReachableObjectType.CLASS, "selected")
            near_root = ReachableObject(ReachableObjectType.CLASS, "near-root")
            middle = ReachableObject(ReachableObjectType.CLASS, "middle")
            far_root = ReachableObject(ReachableObjectType.CLASS, "far-root")
            for node in (selected, near_root, middle, far_root):
                graph.add_node(node)
            graph.add_edge(selected, near_root)
            graph.add_edge(selected, middle)
            graph.add_edge(middle, far_root)
            db_file = self._write_graph_db(graph, temp_dir)

            output = self._run_db(db_file, "json", "path-to-root", "selected")

        self.assertEqual(
            ["selected", "near-root"],
            [row["name"] for row in json.loads(output)],
        )

    def test_path_to_root_disambiguates_kind(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            selected = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            other = ReachableObject(ReachableObjectType.ANNO, "LCollision;")
            for node in (root, selected, other):
                graph.add_node(node)
            graph.add_edge(selected, root)
            db_file = self._write_graph_db(graph, temp_dir)

            ambiguous = self._invoke(
                db_file,
                "json",
                "path-to-root",
                "LCollision;",
            )
            selected_class = self._invoke(
                db_file,
                "json",
                "path-to-root",
                "LCollision;",
                "--kind",
                "class",
            )

        self.assertEqual(1, ambiguous.returncode)
        self.assertIn("Ambiguous node named 'LCollision;'", ambiguous.stderr)
        self.assertEqual(0, selected_class.returncode, selected_class.stderr)
        self.assertEqual(
            ["LCollision;", "<SEED>"],
            [row["name"] for row in json.loads(selected_class.stdout)],
        )

    def test_path_to_root_reports_missing_and_root_unreachable_nodes(self):
        missing = self._invoke(
            self.db_file,
            "table",
            "path-to-root",
            "LMissing;",
        )
        self.assertEqual(1, missing.returncode)
        self.assertEqual("Error: No node named 'LMissing;'\n", missing.stderr)

        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            first = ReachableObject(ReachableObjectType.CLASS, "first")
            target = ReachableObject(ReachableObjectType.CLASS, "target")
            graph.add_node(first)
            graph.add_node(target)
            graph.add_edge(target, first)
            graph.add_edge(first, target)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(db_file, "json", "path-to-root", "target")

        self.assertEqual(1, result.returncode)
        self.assertEqual(
            "Error: Node 'target' is not reachable from any root\n",
            result.stderr,
        )

    def _write_json_adapter_db(self, directory):
        # @JsonAdapter(FooAdapter.class) class Foo {} and
        # @JsonAdapter(BarAdapter.class) class Bar {}, each kept by its own
        # rule: one annotation node per instance, each naming its own adapter.
        graph = ReachabilityGraph()
        for owner in ("Foo", "Bar"):
            seed = ReachableObject(
                ReachableObjectType.SEED, f"KEEP: -keep class {owner}"
            )
            cls = ReachableObject(ReachableObjectType.CLASS, f"L{owner};")
            anno = ReachableObject(ReachableObjectType.ANNO, "LJsonAdapter;")
            adapter = ReachableObject(ReachableObjectType.CLASS, f"L{owner}Adapter;")
            for node in (seed, cls, anno, adapter):
                graph.add_node(node)
            graph.add_edge(cls, seed)
            graph.add_edge(anno, cls)
            graph.add_edge(adapter, anno)
        return self._write_graph_db(graph, directory)

    def test_paths_keep_annotation_instances_apart(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._write_json_adapter_db(temp_dir)
            to_root = json.loads(
                self._run_db(db_file, "json", "path-to-root", "LFooAdapter;")
            )
            no_path = json.loads(
                self._run_db(db_file, "json", "path", "LBar;", "LFooAdapter;")
            )
            from_type = json.loads(
                self._run_db(
                    db_file,
                    "json",
                    "path",
                    "LJsonAdapter;",
                    "LBarAdapter;",
                    "--from-kind",
                    "anno",
                )
            )

        self.assertEqual(
            [
                ("CLASS", "LFooAdapter;"),
                ("ANNO", "LJsonAdapter;"),
                ("CLASS", "LFoo;"),
                ("SEED", "KEEP: -keep class Foo"),
            ],
            [(row["type"], row["name"]) for row in to_root],
        )
        self.assertEqual(
            [{"status": "no path", "step": "", "type": "", "name": ""}], no_path
        )
        # A path from an annotation type starts at any of its instances.
        self.assertEqual(
            [("ANNO", "LJsonAdapter;"), ("CLASS", "LBarAdapter;")],
            [(row["type"], row["name"]) for row in from_type],
        )

    def test_dominated_disambiguates_class_and_annotation_names(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            selected = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            child = ReachableObject(ReachableObjectType.CLASS, "LClassChild;")
            other = ReachableObject(ReachableObjectType.ANNO, "LCollision;")
            for node in (root, selected, child, other):
                graph.add_node(node)
            graph.add_edge(selected, root)
            graph.add_edge(child, selected)
            graph.add_edge(other, root)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(
                db_file,
                "json",
                "dominated",
                "LCollision;",
                "--kind",
                "class",
            )

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [
                {"type": "CLASS", "name": "LClassChild;"},
                {"type": "CLASS", "name": "LCollision;"},
            ],
            json.loads(result.stdout),
        )

    def test_dominated_returns_selected_node_and_dominated_set(self):
        output = self._run("json", "dominated", "LRemovedRoot;")

        self.assertCountEqual(
            [
                {"type": "CLASS", "name": "LRemovedRoot;"},
                {"type": "CLASS", "name": "LRemovedChild;"},
            ],
            json.loads(output),
        )

    def test_dominated_terminates_on_cycles(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            selected = ReachableObject(ReachableObjectType.CLASS, "selected")
            child = ReachableObject(ReachableObjectType.CLASS, "child")
            for node in (root, selected, child):
                graph.add_node(node)
            graph.add_edge(selected, root)
            graph.add_edge(child, selected)
            graph.add_edge(selected, child)
            db_file = self._write_graph_db(graph, temp_dir)

            output = self._run_db(db_file, "json", "dominated", "selected")

        self.assertEqual(
            [
                {"type": "CLASS", "name": "child"},
                {"type": "CLASS", "name": "selected"},
            ],
            json.loads(output),
        )

    def test_retained_count_matches_dominated_for_leaf_and_root(self):
        scenarios = (
            ("LFoo;.field1:I", "FIELD", 1),
            ("<SEED>", "SEED", 5),
        )
        for name, kind, expected_count in scenarios:
            with self.subTest(name=name):
                dominated = json.loads(self._run("json", "dominated", name))
                count = json.loads(self._run("json", "retained-count", name))

                self.assertEqual(expected_count, len(dominated))
                self.assertEqual(
                    [
                        {
                            "type": kind,
                            "name": name,
                            "retained_count": expected_count,
                        }
                    ],
                    count,
                )

    def test_retained_count_supports_csv_table_and_describes_node_count(self):
        csv_output = self._run("csv", "retained-count", "LFoo;.field1:I")
        self.assertEqual(
            [
                {
                    "type": "FIELD",
                    "name": "LFoo;.field1:I",
                    "retained_count": "1",
                }
            ],
            list(csv.DictReader(io.StringIO(csv_output))),
        )

        table_output = self._run("table", "retained-count", "LFoo;.field1:I")
        self.assertIn("retained_count", table_output)
        self.assertIn("LFoo;.field1:I", table_output)

        help_result = subprocess.run(
            [os.environ["GRAPH_QUERY"], "retained-count", "--help"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(0, help_result.returncode, help_result.stderr)
        self.assertIn("node count", help_result.stdout)
        self.assertIn("graph contains no size data", help_result.stdout)

    def test_top_retained_orders_limits_filters_and_supports_formats(self):
        output = self._run("json", "top-retained", "--top", "3")
        self.assertEqual(
            [
                {"type": "SEED", "name": "<SEED>", "retained_count": 5},
                {"type": "CLASS", "name": "LFoo;", "retained_count": 4},
                {
                    "type": "CLASS",
                    "name": "LRemovedRoot;",
                    "retained_count": 2,
                },
            ],
            json.loads(output),
        )

        csv_output = self._run(
            "csv",
            "top-retained",
            "--kind",
            "class",
            "--top",
            "2",
        )
        self.assertEqual(
            [
                {"type": "CLASS", "name": "LFoo;", "retained_count": "4"},
                {
                    "type": "CLASS",
                    "name": "LRemovedRoot;",
                    "retained_count": "2",
                },
            ],
            list(csv.DictReader(io.StringIO(csv_output))),
        )

        table_output = self._run("table", "top-retained", "--top", "1")
        self.assertIn("retained_count", table_output)
        self.assertIn("<SEED>", table_output)

    def test_retained_count_disambiguates_kind(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            selected = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            child = ReachableObject(ReachableObjectType.CLASS, "LClassChild;")
            other = ReachableObject(ReachableObjectType.ANNO, "LCollision;")
            for node in (root, selected, child, other):
                graph.add_node(node)
            graph.add_edge(selected, root)
            graph.add_edge(child, selected)
            graph.add_edge(other, root)
            db_file = self._write_graph_db(graph, temp_dir)

            ambiguous = self._invoke(
                db_file,
                "json",
                "retained-count",
                "LCollision;",
            )
            selected_class = self._invoke(
                db_file,
                "json",
                "retained-count",
                "LCollision;",
                "--kind",
                "class",
            )

        self.assertEqual(1, ambiguous.returncode)
        self.assertIn("Ambiguous node named 'LCollision;'", ambiguous.stderr)
        self.assertEqual(0, selected_class.returncode, selected_class.stderr)
        self.assertEqual(
            [
                {
                    "type": "CLASS",
                    "name": "LCollision;",
                    "retained_count": 2,
                }
            ],
            json.loads(selected_class.stdout),
        )

    def test_retained_count_preserves_missing_and_root_unreachable_errors(self):
        missing = self._invoke(
            self.db_file,
            "table",
            "retained-count",
            "LMissing;",
        )
        self.assertEqual(1, missing.returncode)
        self.assertEqual("Error: No node named 'LMissing;'\n", missing.stderr)

        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            first = ReachableObject(ReachableObjectType.CLASS, "first")
            target = ReachableObject(ReachableObjectType.CLASS, "target")
            graph.add_node(first)
            graph.add_node(target)
            graph.add_edge(target, first)
            graph.add_edge(first, target)
            db_file = self._write_graph_db(graph, temp_dir)

            unreachable_count = self._invoke(
                db_file,
                "table",
                "retained-count",
                "target",
            )
            unreachable_set = self._invoke(
                db_file,
                "json",
                "dominated",
                "target",
            )
            top_retained = self._invoke(
                db_file,
                "json",
                "top-retained",
            )

        for result in (unreachable_count, unreachable_set):
            self.assertEqual(1, result.returncode)
            self.assertEqual(
                "Error: Node 'target' is not reachable from any root\n",
                result.stderr,
            )
        self.assertEqual(0, top_retained.returncode, top_retained.stderr)
        self.assertEqual([], json.loads(top_retained.stdout))

    def test_dominators_disambiguates_class_and_annotation_names(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
            selected_retainer = ReachableObject(
                ReachableObjectType.CLASS, "LAnnotationRetainer;"
            )
            selected = ReachableObject(ReachableObjectType.ANNO, "LCollision;")
            other_retainer = ReachableObject(
                ReachableObjectType.CLASS, "LClassRetainer;"
            )
            other = ReachableObject(ReachableObjectType.CLASS, "LCollision;")
            for node in (
                root,
                selected_retainer,
                selected,
                other_retainer,
                other,
            ):
                graph.add_node(node)
            graph.add_edge(selected_retainer, root)
            graph.add_edge(selected, selected_retainer)
            graph.add_edge(other_retainer, root)
            graph.add_edge(other, other_retainer)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(
                db_file,
                "json",
                "dominators",
                "LCollision;",
                "--kind",
                "anno",
            )

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [
                {"type": "CLASS", "name": "LAnnotationRetainer;"},
                {"type": "SEED", "name": "<SEED>"},
            ],
            json.loads(result.stdout),
        )

    def test_dominators_returns_proper_chain_nearest_first(self):
        output = self._run("json", "dominators", "LFoo;.field1:I")

        self.assertEqual(
            [
                {"type": "METHOD", "name": "LFoo;.method1:()I"},
                {"type": "CLASS", "name": "LFoo;"},
                {"type": "SEED", "name": "<SEED>"},
            ],
            json.loads(output),
        )

    def test_dominators_reports_a_target_unreachable_from_roots(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph = ReachabilityGraph()
            first = ReachableObject(ReachableObjectType.CLASS, "first")
            target = ReachableObject(ReachableObjectType.CLASS, "target")
            graph.add_node(first)
            graph.add_node(target)
            graph.add_edge(target, first)
            graph.add_edge(first, target)
            db_file = self._write_graph_db(graph, temp_dir)

            result = self._invoke(db_file, "table", "dominators", "target")

        self.assertEqual(1, result.returncode)
        self.assertIn("target", result.stderr)
        self.assertIn("not reachable from any root", result.stderr)

    def _write_annotation_instances_db(self, directory):
        # Two classes each carry an instance of the same annotation type, and
        # each instance names a class nothing else retains. The dump keeps one
        # node per instance.
        graph = ReachabilityGraph()
        root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
        first = ReachableObject(ReachableObjectType.CLASS, "LFirst;")
        second = ReachableObject(ReachableObjectType.CLASS, "LSecond;")
        first_marker = ReachableObject(ReachableObjectType.ANNO, "LMarker;")
        second_marker = ReachableObject(ReachableObjectType.ANNO, "LMarker;")
        named_by_first = ReachableObject(ReachableObjectType.CLASS, "LNamedByFirst;")
        named_by_second = ReachableObject(ReachableObjectType.CLASS, "LNamedBySecond;")
        for node in (
            root,
            first,
            second,
            first_marker,
            second_marker,
            named_by_first,
            named_by_second,
        ):
            graph.add_node(node)
        graph.add_edge(first, root)
        graph.add_edge(second, root)
        graph.add_edge(first_marker, first)
        graph.add_edge(second_marker, second)
        graph.add_edge(named_by_first, first_marker)
        graph.add_edge(named_by_second, second_marker)
        return self._write_graph_db(graph, directory)

    def test_dominators_lists_each_instance_in_a_chain(self):
        # @Adapter class B, retained through A's @Adapter instance, and
        # @Adapter class C, retained through B's.
        graph = ReachabilityGraph()
        seed = ReachableObject(ReachableObjectType.SEED, "<SEED>")
        a = ReachableObject(ReachableObjectType.CLASS, "LA;")
        first = ReachableObject(ReachableObjectType.ANNO, "LAdapter;")
        b = ReachableObject(ReachableObjectType.CLASS, "LB;")
        second = ReachableObject(ReachableObjectType.ANNO, "LAdapter;")
        c = ReachableObject(ReachableObjectType.CLASS, "LC;")
        chain = (seed, a, first, b, second, c)
        for node in chain:
            graph.add_node(node)
        for retainer, retained in zip(chain, chain[1:]):
            graph.add_edge(retained, retainer)
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._write_graph_db(graph, temp_dir)
            output = self._run_db(db_file, "json", "dominators", "LC;")

        self.assertEqual(
            [
                {"type": "ANNO", "name": "LAdapter;"},
                {"type": "CLASS", "name": "LB;"},
                {"type": "ANNO", "name": "LAdapter;"},
                {"type": "CLASS", "name": "LA;"},
                {"type": "SEED", "name": "<SEED>"},
            ],
            json.loads(output),
        )

    def test_annotation_instances_dominate_separately(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._write_annotation_instances_db(temp_dir)
            dominated = json.loads(
                self._run_db(db_file, "json", "dominated", "LFirst;")
            )
            count = json.loads(
                self._run_db(db_file, "json", "retained-count", "LFirst;")
            )
            dominators = json.loads(
                self._run_db(db_file, "json", "dominators", "LNamedByFirst;")
            )
            marker_count = json.loads(
                self._run_db(
                    db_file, "json", "retained-count", "LMarker;", "--kind", "anno"
                )
            )
            marker_dominated = json.loads(
                self._run_db(db_file, "json", "dominated", "LMarker;", "--kind", "anno")
            )
            marker_dominators = json.loads(
                self._run_db(
                    db_file, "json", "dominators", "LMarker;", "--kind", "anno"
                )
            )

        self.assertEqual(
            [
                {"type": "ANNO", "name": "LMarker;"},
                {"type": "CLASS", "name": "LFirst;"},
                {"type": "CLASS", "name": "LNamedByFirst;"},
            ],
            dominated,
        )
        self.assertEqual(3, count[0]["retained_count"])
        self.assertEqual(
            [
                {"type": "ANNO", "name": "LMarker;"},
                {"type": "CLASS", "name": "LFirst;"},
                {"type": "SEED", "name": "<SEED>"},
            ],
            dominators,
        )
        # Both instances together dominate themselves and what each names;
        # each instance is its own row.
        self.assertEqual(4, marker_count[0]["retained_count"])
        self.assertEqual(
            [
                {"type": "ANNO", "name": "LMarker;"},
                {"type": "ANNO", "name": "LMarker;"},
                {"type": "CLASS", "name": "LNamedByFirst;"},
                {"type": "CLASS", "name": "LNamedBySecond;"},
            ],
            marker_dominated,
        )
        # Only what lies above both instances dominates the annotation type.
        self.assertEqual([{"type": "SEED", "name": "<SEED>"}], marker_dominators)

    def test_nothing_dominates_instances_when_one_is_a_root(self):
        graph = ReachabilityGraph()
        root = ReachableObject(ReachableObjectType.SEED, "<SEED>")
        held = ReachableObject(ReachableObjectType.CLASS, "LHeld;")
        held_marker = ReachableObject(ReachableObjectType.ANNO, "LMarker;")
        loose_marker = ReachableObject(ReachableObjectType.ANNO, "LMarker;")
        for node in (root, held, held_marker, loose_marker):
            graph.add_node(node)
        graph.add_edge(held, root)
        graph.add_edge(held_marker, held)
        with tempfile.TemporaryDirectory() as temp_dir:
            db_file = self._write_graph_db(graph, temp_dir)
            dominators = json.loads(
                self._run_db(
                    db_file, "json", "dominators", "LMarker;", "--kind", "anno"
                )
            )
        self.assertEqual([], dominators)

    def test_new_nodes_returns_marker_predecessors_and_filters_kind(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            graph_file = os.path.join(temp_dir, "diff.graph")
            db_file = os.path.join(temp_dir, "diff.sqlite")
            write_diff_graph(graph_file)
            export_graph(graph_file, db_file)

            result = self._invoke(db_file, "json", "new-nodes")
            self.assertEqual(0, result.returncode, result.stderr)
            self.assertEqual(
                [
                    {"type": "ANNO", "name": "LNewAnno;"},
                    {"type": "CLASS", "name": "LNewClass;"},
                    {"type": "FIELD", "name": "LNewClass;.field:I"},
                    {"type": "METHOD", "name": "LNewClass;.method:()V"},
                ],
                json.loads(result.stdout),
            )

            filtered = self._invoke(
                db_file,
                "json",
                "new-nodes",
                "--kind",
                "class",
            )
            self.assertEqual(0, filtered.returncode, filtered.stderr)
            self.assertEqual(
                [{"type": "CLASS", "name": "LNewClass;"}],
                json.loads(filtered.stdout),
            )

    def test_new_nodes_rejects_a_non_diff_graph(self):
        result = self._invoke(self.db_file, "table", "new-nodes")
        self.assertEqual(1, result.returncode)
        self.assertEqual(
            "Error: input is not a reachability-diff graph: no <NEW> marker\n",
            result.stderr,
        )
