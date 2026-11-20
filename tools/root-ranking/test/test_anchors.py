# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import json
import os
import tempfile
import unittest

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType
from lib.set_cut import SetCutGraph
from root_ranking.anchors import Anchor, cut_for, read_anchors, refusal

CLASS = ReachableObjectType.CLASS
METHOD = ReachableObjectType.METHOD
SEED = ReachableObjectType.SEED
ANNO = ReachableObjectType.ANNO

# The examples dexvt's coordinate parser accepts and refuses, the same way.
VALID_COORDINATES = (
    "bk:bloks/fb4a/bk.action.core.If",
    "bk:qpl/-/9306113",
    "bk:bloks/fb4a/7#minified",
    "bk:route/fb4a/settings page",
    "bk:x/a%2Fb/c%25d#e%23f",
    "bk:x/a%2fb/c",
    "bk:" + "a" * 32 + "/-/k",
    "bk:a-1/-/k",
)
INVALID_COORDINATES = (
    "handler",
    "bk:1qpl/-/1",
    "bk:Qpl/-/1",
    "bk:-qpl/-/1",
    "bk:" + "a" * 33 + "/-/k",
    "bk:x/a%41/b",
    "bk:x/a%/b",
    "bk:x/a%2/b",
    "bk:x//b",
    "bk:x/a",
    "bk:x/a/b/c",
    "bk:x/a/b#",
    "bk:x/a/b#c#d",
)


def _graph(edges):
    graph = ReachabilityGraph()
    nodes = {}
    for retainer, retained in edges:
        for key in (retainer, retained):
            if key not in nodes:
                nodes[key] = ReachableObject(*key)
                graph.add_node(nodes[key])
        ReachabilityGraph.add_edge(nodes[retained], nodes[retainer])
    with tempfile.TemporaryDirectory() as temp_dir:
        filename = os.path.join(temp_dir, "graph")
        graph.dump(filename)
        return SetCutGraph.load(filename)


def _read(*rows):
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl") as f:
        f.writelines(json.dumps(row) + "\n" for row in rows)
        f.flush()
        return read_anchors(f.name)


class AnchorsTest(unittest.TestCase):
    def test_a_registration_needs_registrar_and_handler(self):
        with self.assertRaisesRegex(ValueError, "needs registrar and handler"):
            _read({"c": "bk:test/app/key", "how": "switch-arm"})

    def test_malformed_rows_raise_value_error(self):
        for row in (
            [1, 2],
            "text",
            {"c": 5},
            {"c": "bk:test//key", "how": "read"},
        ):
            with self.assertRaises(ValueError):
                _read(row)

    def test_coordinates_follow_the_dexvt_grammar(self):
        row = {"how": "switch-arm", "registrar": "LR;", "handler": "LH;"}
        for coordinate in VALID_COORDINATES:
            self.assertIn(coordinate, _read({"c": coordinate, **row}))
        for coordinate in INVALID_COORDINATES:
            with self.assertRaises(ValueError, msg=coordinate):
                _read({"c": coordinate, **row})

    def test_an_entry_point_cuts_the_seeds_of_its_members(self):
        seed = (SEED, "<SEED>")
        on_create = (METHOD, "LAct;.onCreate:()V")
        graph = _graph(
            [
                (seed, (CLASS, "LAct;")),
                (seed, on_create),
                (on_create, (METHOD, "LHelper;.only:()V")),
                # Redex records that a used method retains its class.
                (on_create, (CLASS, "LAct;")),
                ((METHOD, "LHelper;.only:()V"), (CLASS, "LHelper;")),
            ]
        )
        anchor = Anchor("bk:route/app/act", "entry-point", entry_class="LAct;")
        cut, problems = cut_for(graph, [anchor])
        self.assertEqual([], problems)
        dead = graph.cut({"act": cut}).dead
        self.assertEqual(
            ["LAct;", "LAct;.onCreate:()V", "LHelper;", "LHelper;.only:()V"],
            sorted(graph.names[i] for i in dead),
        )

    def test_an_entry_point_held_by_several_keep_reasons_names_one(self):
        manifest = (SEED, "MANIFEST")
        keep = (SEED, "KEEP: -keep class LAct;")
        graph = _graph([(manifest, (CLASS, "LAct;")), (keep, (CLASS, "LAct;"))])
        anchor = Anchor("bk:route/app/act", "entry-point", entry_class="LAct;")
        cut, problems = cut_for(graph, [anchor])
        self.assertEqual(frozenset(), cut.edges)
        self.assertRegex(problems[0], "2 keep reasons hold LAct;")
        named = Anchor(
            "bk:route/app/act", "entry-point", entry_class="LAct;", seed="MANIFEST"
        )
        cut, problems = cut_for(graph, [named])
        self.assertEqual([], problems)
        self.assertEqual(
            [("MANIFEST", "LAct;")],
            [(graph.names[u], graph.names[v]) for u, v in cut.edges],
        )
        self.assertEqual([], list(graph.cut({"act": cut}).dead))

    def test_a_rule_repeated_in_two_files_is_not_cut(self):
        graph = ReachabilityGraph()
        cls = ReachableObject(CLASS, "LAct;")
        graph.add_node(cls)
        for _ in range(2):
            seed = ReachableObject(SEED, "KEEP: -keep class LAct;")
            graph.add_node(seed)
            ReachabilityGraph.add_edge(cls, seed)
        with tempfile.TemporaryDirectory() as temp_dir:
            filename = os.path.join(temp_dir, "graph")
            graph.dump(filename)
            loaded = SetCutGraph.load(filename)
        anchor = Anchor(
            "bk:route/app/act",
            "entry-point",
            entry_class="LAct;",
            seed="KEEP: -keep class LAct;",
        )
        cut, problems = cut_for(loaded, [anchor])
        self.assertEqual(frozenset(), cut.edges)
        self.assertEqual(
            "bk:route/app/act: 2 keep reasons hold LAct; "
            "(several read `KEEP: -keep class LAct;`)",
            problems[0],
        )

    def test_an_annotation_named_like_the_registrar_is_not_cut(self):
        seed = (SEED, "<SEED>")
        registrar = (CLASS, "LRegistrar;")
        graph = _graph(
            [
                (seed, registrar),
                (seed, (CLASS, "LOther;")),
                ((CLASS, "LOther;"), (ANNO, "LRegistrar;")),
                (registrar, (CLASS, "LHandler;")),
                ((ANNO, "LRegistrar;"), (CLASS, "LHandler;")),
            ]
        )
        anchor = Anchor(
            "bk:test/app/h", "switch-arm", registrar="LRegistrar;", handler="LHandler;"
        )
        cut, _ = cut_for(graph, [anchor])
        self.assertEqual([], graph.cut({"h": cut}).dead)

    def test_a_registration_of_unknown_handler_holds_the_whole_registrar(self):
        seed = (SEED, "<SEED>")
        dispatch = (METHOD, "LRegistrar;.dispatch:(I)V")
        graph = _graph(
            [
                (seed, dispatch),
                (dispatch, (CLASS, "LShared;")),
                (dispatch, (CLASS, "LOther;")),
                (seed, (CLASS, "LUnrelated;")),
            ]
        )
        anchor = Anchor("bk:test/app/8#minified", "any-handler", registrar=dispatch[1])
        cut, problems = cut_for(graph, [anchor])
        self.assertEqual([], problems)
        self.assertEqual(
            [
                ("LRegistrar;.dispatch:(I)V", "LOther;"),
                ("LRegistrar;.dispatch:(I)V", "LShared;"),
            ],
            sorted((graph.names[u], graph.names[v]) for u, v in cut.edges),
        )
        # What removing it frees is unknown, so it is never ranked.
        self.assertRegex(refusal([anchor]), "handler unknown")
        with self.assertRaisesRegex(ValueError, "any-handler needs registrar"):
            _read({"c": "bk:test/app/k", "how": "any-handler"})

    def test_a_value_root_cannot_be_cut(self):
        graph = _graph([((SEED, "<SEED>"), (CLASS, "LA;"))])
        anchor = Anchor("bk:mc/app/flag", "read", entry_class="LA;")
        with self.assertRaisesRegex(ValueError, "value root"):
            cut_for(graph, [anchor])
