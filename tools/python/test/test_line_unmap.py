# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import struct
import tempfile
import unittest

from line_unmap import MapEntry, PositionMap


def _line_map(positions, provenance=None):
    """A v2 line map with one pool string, and an optional provenance
    section of (record index, alternate, candidates) entries."""
    data = struct.pack("<LLL", 0xFACEB000, 2, 1) + struct.pack("<L", 1) + b"A"
    data += struct.pack("<L", positions)
    data += struct.pack("<LLLLL", 0, 0, 0, 1, 0) * positions
    if provenance is not None:
        section = len(data)
        data += b"".join(struct.pack("<LLL", *entry) for entry in provenance)
        directory = len(data)
        data += struct.pack("<LLQQ", 0x564F5250, 0, section, directory - section)
        data += struct.pack("<QLL", directory, 1, 0xFACEB002)
    return data


def _read(data):
    with tempfile.NamedTemporaryFile() as f:
        f.write(data)
        f.flush()
        return PositionMap.read_from(f.name, with_unreliable=True)


class LineUnmapTest(unittest.TestCase):
    def test_a_map_without_extension_has_no_unreliable_positions(self):
        pmap = _read(_line_map(3))
        self.assertEqual(3, len(pmap.positions))
        self.assertEqual(frozenset(), pmap.unreliable)

    def test_symbolication_reads_no_extension(self):
        # A malformed extension does not affect reading positions without it.
        data = _line_map(3, [(5, 0, 0)])
        with tempfile.NamedTemporaryFile() as f:
            f.write(data)
            f.flush()
            pmap = PositionMap.read_from(f.name)
        self.assertEqual(3, len(pmap.positions))
        self.assertIsNone(pmap.unreliable)
        with self.assertRaisesRegex(ValueError, "with_unreliable"):
            pmap.rows_naming(frozenset())

    def test_reads_unreliable_positions(self):
        pmap = _read(_line_map(3, [(0, 0, 0), (2, 0, 0)]))
        self.assertEqual(3, len(pmap.positions))
        self.assertEqual(frozenset({0, 2}), pmap.unreliable)

    def test_rows_naming_follows_stacks_and_skips_unreliable_ones(self):
        pmap = PositionMap()
        pmap.string_pool = ["com.A", "run", "com.B", "inlined", "com.C", "other"]
        pmap.positions = [
            MapEntry(0, 1, 0, 1, 0),  # 1: com.A.run
            MapEntry(2, 3, 0, 1, 1),  # 2: com.B.inlined, inlined into row 1
            MapEntry(4, 5, 0, 1, 0),  # 3: com.C.other, unreliable
            MapEntry(2, 3, 0, 1, 3),  # 4: com.B.inlined, inlined into row 3
        ]
        pmap.unreliable = frozenset({2})
        self.assertEqual(
            {"com.A.run": frozenset({1, 2}), "com.B.inlined": frozenset({2})},
            pmap.rows_naming(frozenset({"com.A.run", "com.B.inlined"})),
        )

    def test_rows_naming_refuses_a_parent_cycle(self):
        pmap = PositionMap()
        pmap.string_pool = ["com.A", "run"]
        pmap.positions = [MapEntry(0, 1, 0, 1, 2), MapEntry(0, 1, 0, 1, 1)]
        pmap.unreliable = frozenset()
        with self.assertRaisesRegex(ValueError, "parent cycle"):
            pmap.rows_naming(frozenset({"com.A.run"}))

    def test_rows_naming_ends_a_stack_like_get_stack(self):
        # A parent past the map ends the stack, and a v1 row names no method.
        pmap = PositionMap()
        pmap.string_pool = ["com.A", "run", "File.java"]
        pmap.positions = [
            MapEntry(0, 1, 2, 1, 9),  # 1: com.A.run, parent outside the map
            MapEntry(None, None, 2, 2, 1),  # 2: v1 row inlined into row 1
        ]
        pmap.unreliable = frozenset()
        self.assertEqual(
            {"com.A.run": frozenset({1, 2})},
            pmap.rows_naming(frozenset({"com.A.run"})),
        )
        self.assertEqual(["com.A.run"], [p.method for p in pmap.get_stack(0)])

    def test_refuses_a_record_index_past_the_positions(self):
        with self.assertRaisesRegex(ValueError, "bad provenance record index"):
            _read(_line_map(3, [(3, 0, 0)]))
