# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import json
import os
import struct
import subprocess
import tempfile
import unittest
import zipfile

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType
from root_ranking.dex_pricing import Deletion, DexReferences


class RankRootsTest(unittest.TestCase):
    def setUp(self):
        self._temp = tempfile.TemporaryDirectory()
        self.addCleanup(self._temp.cleanup)
        self.run_dir = self._temp.name
        with open(os.environ["DEX_FILE"], "rb") as f:
            self.dex_bytes = f.read()
        self.bundle = os.path.join(self.run_dir, "out.apk")
        with zipfile.ZipFile(self.bundle, "w") as bundle:
            bundle.writestr("classes.dex", self.dex_bytes)
        self.dex = DexReferences(self.dex_bytes)
        self.handler_index, self.handler = next(
            (i, self.dex.type_name(c.type_index))
            for i, c in enumerate(self.dex.classes)
            if self.dex.type_name(c.type_index).endswith(
                "PageAdminAppointmentDetailFragmentFactory;"
            )
        )
        self.other_handler = next(
            self.dex.type_name(c.type_index)
            for i, c in enumerate(self.dex.classes)
            if i != self.handler_index
        )
        self.seed_name = "MANIFEST"
        self._write_graph()
        self._write_maps()

    def _write_graph(self):
        graph = ReachabilityGraph()
        seed = ReachableObject(ReachableObjectType.SEED, self.seed_name)
        dispatch = ReachableObject(
            ReachableObjectType.METHOD, "LRegistrar;.dispatch:(I)V"
        )
        registrar = ReachableObject(ReachableObjectType.CLASS, "LRegistrar;")
        handler = ReachableObject(ReachableObjectType.CLASS, self.handler)
        other = ReachableObject(ReachableObjectType.CLASS, self.other_handler)
        for node in (seed, dispatch, registrar, handler, other):
            graph.add_node(node)
        graph.add_edge(dispatch, seed)
        # Redex records that a used method retains its class.
        graph.add_edge(registrar, dispatch)
        graph.add_edge(handler, dispatch)
        graph.add_edge(other, dispatch)
        graph.dump(os.path.join(self.run_dir, "reachability-graph"))

    def _write_maps(self):
        open(os.path.join(self.run_dir, "redex-full-rename-map.txt"), "w").close()
        with open(os.path.join(self.run_dir, "redex-line-number-map-v2"), "wb") as f:
            f.write(struct.pack("<LLLL", 0xFACEB000, 2, 0, 0))
        with open(os.path.join(self.run_dir, "redex-debug-line-map-v2"), "wb") as f:
            f.write(struct.pack("<LLL", 0xFACEB000, 1, 0))
        with open(os.path.join(self.run_dir, "redex.py-invocation.txt"), "w") as f:
            f.write(
                # Both forms of -J that redex.py accepts
                "redex.py -J FBRemoveUnreachablePass.emit_graph_on_run=1 "
                "-Jrecord_keep_reasons=true in.apk"
            )

    def _rank(self, anchors, sets=None):
        anchors_file = os.path.join(self.run_dir, "anchors.jsonl")
        with open(anchors_file, "w") as f:
            f.writelines(json.dumps(a) + "\n" for a in anchors)
        out = os.path.join(self.run_dir, "report.json")
        extra = []
        if sets is not None:
            sets_file = os.path.join(self.run_dir, "sets.json")
            with open(sets_file, "w") as f:
                json.dump(sets, f)
            extra = ["--sets", sets_file]
        result = subprocess.run(
            [
                os.environ["RANK_ROOTS"],
                *extra,
                "--run-dir",
                self.run_dir,
                "--bundle",
                self.bundle,
                "--anchors",
                anchors_file,
                "--out",
                out,
                "-j",
                "1",
            ],
            capture_output=True,
            text=True,
        )
        return result, out

    def test_ranks_a_registration_and_refuses_a_value_root(self):
        result, out = self._rank(
            [
                {
                    "c": "bk:test/app/handler",
                    "how": "switch-arm",
                    "registrar": "LRegistrar;",
                    "handler": self.handler,
                },
                {"c": "bk:mc/config/param", "how": "read"},
            ]
        )
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("not a byte price", result.stderr)
        with open(out) as f:
            report = json.load(f)
        expected = self.dex.freed(Deletion(classes=frozenset({self.handler_index})))
        ranked = report["sets"]["all"]
        self.assertEqual(sum(expected.values()), ranked["total"])
        self.assertEqual(expected["code"], ranked["code"])
        self.assertEqual(
            ranked["total"], ranked["roots"]["bk:test/app/handler"]["total"]
        )
        self.assertEqual(0, ranked["shared_in_set"])
        self.assertIn("bk:mc/config/param", report["refused"])
        self.assertIn("not a byte price", report["meaning"])
        self.assertEqual(
            {"pass": "FBRemoveUnreachablePass", "run": 1, "keep_reasons": True},
            report["provenance"]["graph"]["kind"],
        )

    def test_a_set_whose_anchors_match_no_edge_is_not_ranked(self):
        result, out = self._rank(
            [
                {
                    "c": "bk:test/app/missing",
                    "how": "switch-arm",
                    "registrar": "LRegistrar;",
                    "handler": "LNoSuchHandler;",
                }
            ]
        )
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        self.assertEqual({}, report["sets"])
        self.assertIn("set all: no edge to cut; not ranked", report["problems"])

    def test_a_root_whose_anchors_match_no_edge_is_not_ranked_in_its_set(self):
        def registration(c, handler):
            return {
                "c": c,
                "how": "switch-arm",
                "registrar": "LRegistrar;",
                "handler": handler,
            }

        result, out = self._rank(
            [
                registration("bk:test/app/handler", self.handler),
                registration("bk:test/app/other", self.other_handler),
                registration("bk:test/app/missing", "LNoSuchHandler;"),
            ]
        )
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        ranked = report["sets"]["all"]
        self.assertEqual(
            {"bk:test/app/handler", "bk:test/app/other"}, set(ranked["roots"])
        )
        self.assertEqual(["bk:test/app/missing"], ranked["not_ranked"])
        self.assertIn(
            "bk:test/app/missing: no edge from LRegistrar; into LNoSuchHandler;",
            report["problems"],
        )

    def test_a_root_whose_edges_a_key_outside_the_set_registers_is_not_ranked(self):
        def registration(c, handler):
            return {
                "c": c,
                "how": "switch-arm",
                "registrar": "LRegistrar;",
                "handler": handler,
            }

        result, out = self._rank(
            [
                registration("bk:test/app/handler", self.handler),
                registration("bk:test/app/other", self.other_handler),
                registration("bk:test/app/outside", self.handler),
            ],
            sets={"pair": ["bk:test/app/handler", "bk:test/app/other"]},
        )
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        pair = report["sets"]["pair"]
        self.assertEqual(["bk:test/app/other"], list(pair["roots"]))
        self.assertEqual(["bk:test/app/handler"], pair["not_ranked"])

    def test_a_refused_key_still_holds_what_it_registers(self):
        registration = {
            "how": "switch-arm",
            "registrar": "LRegistrar;",
            "handler": self.handler,
        }
        result, out = self._rank(
            [
                {"c": "bk:test/app/one", **registration},
                # Refused as a whole for its value row, yet it still registers
                # the handler.
                {"c": "bk:test/app/valued", **registration},
                {"c": "bk:test/app/valued", "how": "read"},
            ],
            sets={"one": ["bk:test/app/one"]},
        )
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        self.assertIn("bk:test/app/valued", report["refused"])
        self.assertEqual({}, report["sets"])
        self.assertIn(
            "set one: bk:test/app/one shares registrations with "
            "['bk:test/app/valued'], which stay",
            report["problems"],
        )

    def test_a_key_of_unknown_handler_holds_every_edge_of_its_registrar(self):
        result, out = self._rank(
            [
                {
                    "c": "bk:test/app/one",
                    "how": "switch-arm",
                    "registrar": "LRegistrar;",
                    "handler": self.handler,
                },
                {
                    "c": "bk:test/app/8#minified",
                    "how": "any-handler",
                    "registrar": "LRegistrar;",
                },
            ],
            sets={"one": ["bk:test/app/one"]},
        )
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        self.assertIn("bk:test/app/8#minified", report["refused"])
        self.assertEqual({}, report["sets"])
        self.assertIn(
            "set one: bk:test/app/one shares registrations with "
            "['bk:test/app/8#minified'], which stay",
            report["problems"],
        )

    def test_refuses_when_only_value_roots_remain(self):
        result, _ = self._rank([{"c": "bk:mc/config/param", "how": "literal-arg"}])
        self.assertNotEqual(0, result.returncode)
        self.assertIn("value root", result.stderr)

    def test_refuses_a_graph_without_keep_reasons(self):
        self.seed_name = "<SEED>"
        self._write_graph()
        result, _ = self._rank(
            [
                {
                    "c": "bk:test/app/handler",
                    "how": "switch-arm",
                    "registrar": "LRegistrar;",
                    "handler": self.handler,
                }
            ]
        )
        self.assertEqual(1, result.returncode)
        self.assertIn("records no keep reasons", result.stderr)

    def test_names_a_missing_map(self):
        os.remove(os.path.join(self.run_dir, "redex-debug-line-map-v2"))
        result, _ = self._rank(
            [
                {
                    "c": "bk:test/app/handler",
                    "how": "switch-arm",
                    "registrar": "LRegistrar;",
                    "handler": self.handler,
                }
            ]
        )
        self.assertEqual(1, result.returncode)
        self.assertIn("missing", result.stderr)
        self.assertIn("redex-debug-line-map-v2", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_rejects_a_malformed_coordinate(self):
        result, _ = self._rank(
            [{"c": "handler", "how": "switch-arm", "registrar": "L;", "handler": "L;"}]
        )
        self.assertNotEqual(0, result.returncode)
        self.assertIn("not a bk: coordinate", result.stderr)

    def test_a_handler_two_keys_register_goes_only_with_both(self):
        registration = {
            "how": "switch-arm",
            "registrar": "LRegistrar;",
            "handler": self.handler,
        }
        anchors = [
            {"c": "bk:test/app/one", **registration},
            {"c": "bk:test/app/same", **registration},
        ]
        result, out = self._rank(anchors)
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            ranked = json.load(f)["sets"]["all"]
        self.assertGreater(ranked["total"], 0)
        for root in ranked["roots"].values():
            self.assertEqual(0, root["total"])
        self.assertEqual(ranked["total"], ranked["shared_in_set"])
        result, out = self._rank(anchors, sets={"one": ["bk:test/app/one"]})
        self.assertEqual(0, result.returncode, result.stderr)
        with open(out) as f:
            report = json.load(f)
        self.assertEqual({}, report["sets"])
        self.assertIn(
            "set one: bk:test/app/one shares registrations with "
            "['bk:test/app/same'], which stay",
            report["problems"],
        )
