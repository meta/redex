# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import struct
import unittest

from dex import TypeCode
from root_ranking.dex_pricing import (
    _iter_instructions,
    ANNO_REF_LIST,
    ANNO_SET,
    Deletion,
    DexReferences,
    METHOD_ID,
    STRING,
)

# map_list type code -> section name, for the sections pricing covers
_SECTIONS = {
    TypeCode.STRING_ID_ITEM.value: "string_id",
    TypeCode.TYPE_ID_ITEM.value: "type_id",
    TypeCode.PROTO_ID_ITEM.value: "proto_id",
    TypeCode.FIELD_ID_ITEM.value: "field_id",
    TypeCode.METHOD_ID_ITEM.value: "method_id",
    TypeCode.CLASS_DEF_ITEM.value: "class_def",
    TypeCode.TYPE_LIST.value: "type_list",
    TypeCode.ANNOTATION_SET_REF_LIST.value: "anno_set_ref_list",
    TypeCode.ANNOTATION_SET_ITEM.value: "anno_set",
    TypeCode.CLASS_DATA_ITEM.value: "class_data",
    TypeCode.CODE_ITEM.value: "code",
    TypeCode.STRING_DATA_ITEM.value: "string_data",
    TypeCode.ANNOTATION_ITEM.value: "annotation",
    TypeCode.ENCODED_ARRAY_ITEM.value: "encoded_array",
    TypeCode.ANNOTATIONS_DIRECTORY_ITEM.value: "anno_dir",
}


def _section_bytes(data):
    """Bytes per map_list section, each running to the next section."""
    map_off = struct.unpack_from("<I", data, 0x34)[0]
    count = struct.unpack_from("<I", data, map_off)[0]
    items = []
    for i in range(count):
        type_code, _, _, offset = struct.unpack_from(
            "<HHII", data, map_off + 4 + 12 * i
        )
        items.append((offset, type_code))
    items.sort()
    file_size = struct.unpack_from("<I", data, 0x20)[0]
    out = {}
    for i, (offset, type_code) in enumerate(items):
        end = items[i + 1][0] if i + 1 < len(items) else file_size
        if type_code in _SECTIONS:
            out[_SECTIONS[type_code]] = end - offset
    return out


def _read(env):
    with open(os.environ[env], "rb") as f:
        return f.read()


class DexPricingTest(unittest.TestCase):
    def test_deleting_every_class_frees_every_section(self):
        data = _read("DEX_FILE")
        dex = DexReferences(data)
        freed = dex.freed(Deletion(classes=frozenset(range(len(dex.classes)))))
        for section, size in _section_bytes(data).items():
            # Alignment padding at a section's end is the only difference.
            self.assertLessEqual(abs(size - freed[section]), 3, section)

    def test_deleting_nothing_frees_nothing(self):
        dex = DexReferences(_read("DEX_FILE"))
        self.assertEqual(sum(dex.freed(Deletion()).values()), 0)

    def test_one_class_frees_its_own_items_only(self):
        dex = DexReferences(_read("DEX_FILE"))
        index = next(
            i
            for i, c in enumerate(dex.classes)
            if dex.type_name(c.type_index).endswith(
                "PageAdminAppointmentDetailFragmentFactory;"
            )
        )
        cls = dex.classes[index]
        freed = dex.freed(Deletion(classes=frozenset({index})))
        self.assertEqual(freed["class_def"], 32)
        self.assertEqual(freed["class_data"], cls.data_bytes)
        self.assertEqual(freed["code"], sum(m.code_bytes for m in cls.methods))
        # Its own descriptor string and type id go with it.
        self.assertGreaterEqual(freed["string_id"], 4)
        self.assertGreaterEqual(freed["type_id"], 4)

    def test_dead_range_frees_its_code_units(self):
        dex = DexReferences(_read("DEX_FILE"))
        c, m = next(
            (c, m)
            for c, cls in enumerate(dex.classes)
            for m, method in enumerate(cls.methods)
            if method.insn_units >= 8
        )
        freed = dex.freed(Deletion(ranges={(c, m): [(0, 4)]}))
        self.assertEqual(freed["code"], 8)

    def test_an_emptied_surviving_method_keeps_a_return(self):
        dex = DexReferences(_read("DEX_FILE"))
        c, m = next(
            (c, m)
            for c, cls in enumerate(dex.classes)
            for m, method in enumerate(cls.methods)
            if method.insn_units >= 4 and not method.has_tries
        )
        method = dex.classes[c].methods[m]
        freed = dex.freed(Deletion(ranges={(c, m): [(0, method.insn_units)]}))
        # What stays: a 16-byte header and one return unit, aligned to 20.
        self.assertEqual(method.code_bytes - 20, freed["code"])

    def test_alignment_can_absorb_a_shrunk_method(self):
        dex = DexReferences(_read("DEX_FILE"))
        c, m = next(
            (c, m)
            for c, cls in enumerate(dex.classes)
            for m, method in enumerate(cls.methods)
            if method.insn_units >= 4
            and method.code_size == method.code_bytes
            and not method.has_tries
        )
        # One unit less leaves 2 bytes of padding: nothing is freed.
        self.assertEqual(0, dex.freed(Deletion(ranges={(c, m): [(0, 1)]}))["code"])
        self.assertEqual(4, dex.freed(Deletion(ranges={(c, m): [(0, 2)]}))["code"])

    def test_a_method_of_a_surviving_class_frees_each_annotation_row(self):
        dex = DexReferences(_read("ANNOTATED_DEX_FILE"))
        # A method with an annotation of its own and of a parameter has a row
        # in each of the two lists of its class's annotation directory.
        c, m = next(
            (c, m)
            for c, cls in enumerate(dex.classes)
            for m, method in enumerate(cls.methods)
            if {ANNO_SET, ANNO_REF_LIST} <= {kind for kind, _ in method.refs}
        )
        freed = dex.freed(Deletion(methods=frozenset({(c, m)})))
        self.assertEqual(16, freed["anno_dir"])

    def test_a_surviving_method_s_debug_program_keeps_its_strings(self):
        dex = DexReferences(_read("DEBUG_LOCALS_DEX_FILE"))
        drops, keeps = (
            next(
                c
                for c, cls in enumerate(dex.classes)
                if dex.type_name(cls.type_index).endswith(f"DebugLocals${name};")
            )
            for name in ("DropsLocal", "KeepsLocal")
        )

        def freed_strings(classes):
            release = dex.release(Deletion(classes=frozenset(classes)))
            return {dex.string(i) for kind, i in release.items if kind == STRING}

        # `drop` loads "local"; `keep`'s debug program names its local `local`.
        self.assertIn("local", freed_strings({drops, keeps}))
        self.assertNotIn("local", freed_strings({drops}))

    def test_reads_dex_039_opcodes(self):
        dex = DexReferences(_read("DEX_039_FILE"))
        self.assertTrue(dex.classes)

    def test_method_handles_keep_what_they_name(self):
        dex = DexReferences(_read("DEX_039_FILE"))
        everything = dex.release(Deletion(classes=frozenset(range(len(dex.classes)))))
        freed_methods = {
            dex.method_name(index)
            for kind, index in everything.items
            if kind == METHOD_ID
        }
        # A method handle names getClass; the handle and what it names stay.
        self.assertTrue(freed_methods)
        self.assertNotIn(
            "Ljava/lang/Object;.getClass:()Ljava/lang/Class;", freed_methods
        )

    def test_union_of_releases_frees_what_any_of_them_frees(self):
        dex = DexReferences(_read("DEX_FILE"))
        first = dex.release(Deletion(classes=frozenset({0})))
        second = dex.release(Deletion(classes=frozenset({1})))
        both = dex.release(Deletion(classes=frozenset({0, 1})))
        union = first.union(second)
        self.assertLessEqual(union.items, both.items)
        self.assertEqual(dex.size(union), dex.size(first) + dex.size(second))

    def test_unused_opcode_is_refused(self):
        with self.assertRaisesRegex(ValueError, "unused opcode 0x3e"):
            list(_iter_instructions([0x003E]))
