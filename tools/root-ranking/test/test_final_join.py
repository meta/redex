# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import collections
import os
import tempfile
import unittest

from debug_line_map import method_key
from root_ranking.dex_pricing import DexReferences
from root_ranking.final_join import (
    _dead_ranges,
    DeadCode,
    FinalJoin,
    Overloads,
    read_rename_map,
)


class FinalJoinTest(unittest.TestCase):
    def test_a_cut_claims_a_name_only_with_every_overload(self):
        overloads = Overloads(["Lcom/A;.f:(I)V", "Lcom/A;.f:(J)V", "Lcom/A;.g:()V"])
        self.assertEqual(
            frozenset({"com.A.g"}),
            overloads.removed(["Lcom/A;.f:(I)V", "Lcom/A;.g:()V"]),
        )
        self.assertEqual(
            frozenset({"com.A.f"}),
            overloads.removed(["Lcom/A;.f:(I)V", "Lcom/A;.f:(J)V"]),
        )

    def test_rename_map_keeps_every_original_and_names_none_for_synthetic(self):
        with tempfile.NamedTemporaryFile("w") as f:
            f.write("type Lorig/A; -> La;\n")
            f.write("type Lorig/B; -> La;\n")
            f.write("dmethod  -> La;.synth:()V\n")
            f.write("store classes2 -> base\n")
            f.flush()
            self.assertEqual(
                {
                    "La;": frozenset({"Lorig/A;", "Lorig/B;"}),
                    "La;.synth:()V": frozenset(),
                },
                read_rename_map(f.name),
            )


class FinalJoinDeletionTest(unittest.TestCase):
    def setUp(self):
        with open(os.environ["DEX_FILE"], "rb") as f:
            self.dex = DexReferences(f.read())
        self.index, cls = next(
            (i, c)
            for i, c in enumerate(self.dex.classes)
            if self.dex.type_name(c.type_index).endswith(
                "PageAdminAppointmentDetailFragmentFactory;"
            )
        )
        self.final = self.dex.type_name(cls.type_index)
        self.method = self.dex.method_name(cls.methods[0].index)
        # The final class merges two original classes.
        self.renames = {self.final: frozenset({"LA;", "LB;"})}

    def _deletion(self, classes, known=frozenset(), methods=frozenset()):
        join = FinalJoin(self.dex, self.renames, known, {})
        dead = DeadCode(
            frozenset(classes), frozenset(methods), frozenset(), frozenset()
        )
        return join.deletion(dead)[0]

    def test_a_merged_class_goes_only_with_all_of_its_originals(self):
        self.assertNotIn(self.index, self._deletion({"LA;"}).classes)
        self.assertIn(self.index, self._deletion({"LA;", "LB;"}).classes)

    def test_a_reachable_member_keeps_its_class(self):
        member = self.method.replace(self.final, "LA;", 1)
        deletion = self._deletion({"LA;", "LB;"}, known=frozenset({member}))
        self.assertNotIn(self.index, deletion.classes)

    def test_a_method_made_only_of_cut_code_stays(self):
        cls = self.dex.classes[self.index]
        method = cls.methods[0]
        # A synthetic method: no original names, every instruction from a cut row.
        renames = {**self.renames, self.method: frozenset()}
        lines = {method_key(method.index, self.dex.signature4): [(0, 1)]}
        join = FinalJoin(self.dex, renames, frozenset(), lines)
        dead = DeadCode(frozenset(), frozenset(), frozenset(), frozenset({1}))
        deletion, _ = join.deletion(dead)
        self.assertEqual(frozenset(), deletion.methods)
        self.assertEqual({(self.index, 0): [(0, method.insn_units)]}, deletion.ranges)

    def test_dead_ranges_merge_adjacent_entries(self):
        lines = [(0, 1), (2, 2), (4, 1), (6, 3)]
        self.assertEqual([(0, 2), (4, 6)], _dead_ranges(lines, 8, frozenset({1})))
        self.assertEqual([(0, 6)], _dead_ranges(lines, 8, frozenset({1, 2})))
        self.assertEqual([(6, 8)], _dead_ranges(lines, 8, frozenset({3})))

    def test_dead_ranges_refuse_entries_out_of_pc_order(self):
        with self.assertRaisesRegex(ValueError, "out of pc order"):
            _dead_ranges([(4, 1), (2, 2)], 8, frozenset({1}))
