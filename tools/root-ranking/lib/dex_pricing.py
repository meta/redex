#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""Bytes a DEX file loses when some of its code goes.

`DexReferences` parses one dex into holders -- class definitions, encoded
methods with their code items, encoded fields -- and the items they reference:
strings, type/proto/field/method ids, type lists, annotation directories, sets
and items, static-value arrays. Every item is sized exactly as the file lays it
out. `release()` deletes holders (and pc ranges of surviving methods) and
returns what goes: the deleted holders themselves plus every item no surviving
holder still references, directly or through other items. `size()` prices a
release per section; releases of several deletions can be merged first.

Some bytes are left out, so a release underestimates: call sites and method
handles stay with everything they name; deleting a member from a surviving
class frees its class_data entry and annotation directory rows, but neither
re-encodes its neighbors' index deltas nor drops a static field's initial
value; debug info is not priced, as builds with instruction-offset debug info
carry almost none, but the strings and types a debug program names count as
references of its method, so they stay while the method does.

This is a separate decoder from `tools/python/dex.py`, whose dump-oriented
parser builds an object per item and instruction, has no annotation item, set
or directory parsing, and no DEX 038+ opcodes after invoke-polymorphic
(invoke-custom, const-method-handle/-type), all of which a reference count over
every dex of an app needs; for the same reason the instruction width table is
its own rather than derived from dex.py's per-opcode classes. The format's
type, value and handle codes come from dex.py.
"""

from __future__ import annotations

import array
import functools
import struct
from collections import Counter
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, field

from dex import MethodHandleTypeCode, TypeCode, ValueFormat

# Item kinds. Strings are reported as their two sections.
STRING, TYPE, PROTO, FIELD_ID, METHOD_ID, TYPE_LIST = 0, 1, 2, 3, 4, 5
ANNO_DIR, ANNO_SET, ANNO_REF_LIST, ANNO_ITEM, STATIC_VALUES = 6, 7, 8, 9, 10
CALL_SITE, METHOD_HANDLE = 11, 12
SECTION = {
    TYPE: "type_id",
    PROTO: "proto_id",
    FIELD_ID: "field_id",
    METHOD_ID: "method_id",
    TYPE_LIST: "type_list",
    ANNO_DIR: "anno_dir",
    ANNO_SET: "anno_set",
    ANNO_REF_LIST: "anno_set_ref_list",
    ANNO_ITEM: "annotation",
    STATIC_VALUES: "encoded_array",
}
_ID_KINDS = (STRING, TYPE, PROTO, FIELD_ID, METHOD_ID)

Ref = tuple[int, int]  # (kind, index or file offset)


def _uleb(data: bytes, offset: int) -> tuple[int, int]:
    result = shift = 0
    while True:
        byte = data[offset]
        offset += 1
        result |= (byte & 0x7F) << shift
        shift += 7
        if byte < 0x80:
            return result, offset


def _sleb(data: bytes, offset: int) -> tuple[int, int]:
    result = shift = 0
    while True:
        byte = data[offset]
        offset += 1
        result |= (byte & 0x7F) << shift
        shift += 7
        if byte < 0x80:
            if byte & 0x40:
                result -= 1 << shift
            return result, offset


@functools.cache
def _instruction_widths() -> list[int]:
    """Code units per opcode; 0 for the opcodes DEX leaves unused."""
    width = [1] * 256
    for op in (*range(0x3E, 0x44), 0x73, 0x79, 0x7A, *range(0xE3, 0xFA)):
        width[op] = 0
    two = [0x02, 0x05, 0x08, 0x13, 0x15, 0x16, 0x19, 0x1A, 0x1C, 0x1F, 0x20, 0x22]
    two += [0x23, 0x29, 0xFE, 0xFF]
    two += [*range(0x2D, 0x3E), *range(0x44, 0x6E), *range(0x90, 0xB0)]
    two += range(0xD0, 0xE3)
    three = [0x03, 0x06, 0x09, 0x14, 0x17, 0x1B, 0x24, 0x25, 0x26, 0x2A, 0x2B]
    three += [0x2C, 0xFC, 0xFD, *range(0x6E, 0x73), *range(0x74, 0x79)]
    for op in two:
        width[op] = 2
    for op in three:
        width[op] = 3
    width[0xFA] = width[0xFB] = 4
    width[0x18] = 5
    return width


@functools.cache
def _instruction_refs() -> dict[int, tuple[int, bool]]:
    """opcode -> (referenced kind, 32-bit index)."""
    refs = {
        0x1A: (STRING, False),
        0x1B: (STRING, True),
        0xFA: (METHOD_ID, False),
        0xFB: (METHOD_ID, False),
        0xFC: (CALL_SITE, False),
        0xFD: (CALL_SITE, False),
        0xFE: (METHOD_HANDLE, False),
        0xFF: (PROTO, False),
    }
    for op in (0x1C, 0x1F, 0x20, 0x22, 0x23, 0x24, 0x25):
        refs[op] = (TYPE, False)
    for op in range(0x52, 0x6E):
        refs[op] = (FIELD_ID, False)
    for op in (*range(0x6E, 0x73), *range(0x74, 0x79)):
        refs[op] = (METHOD_ID, False)
    return refs


# encoded_value type -> the item kind its value indexes
_VALUE_REF = {
    ValueFormat.METHOD_TYPE.value: PROTO,
    ValueFormat.METHOD_HANDLE.value: METHOD_HANDLE,
    ValueFormat.STRING.value: STRING,
    ValueFormat.TYPE.value: TYPE,
    ValueFormat.FIELD.value: FIELD_ID,
    ValueFormat.METHOD.value: METHOD_ID,
    ValueFormat.ENUM.value: FIELD_ID,
}


def _aligned(size: int) -> int:
    """Code items are 4-byte aligned."""
    return size + (-size) % 4


def _shrunk_bytes(method: Method, dead: int) -> int:
    """What a code item frees when `dead` of its code units go. It stays
    aligned, and with try blocks the padding before them follows the parity of
    the unit count."""

    def padding(units: int) -> int:
        return 2 if method.has_tries and units & 1 else 0

    units = method.insn_units
    after = method.code_size - 2 * dead + padding(units - dead) - padding(units)
    return method.code_bytes - _aligned(after)


def _payload_width(units: Sequence[int], pc: int) -> int:
    kind = units[pc] >> 8
    if kind == 1:  # packed-switch
        return 4 + 2 * units[pc + 1]
    if kind == 2:  # sparse-switch
        return 2 + 4 * units[pc + 1]
    if kind == 3:  # fill-array-data
        element = units[pc + 1]
        count = units[pc + 2] | (units[pc + 3] << 16)
        return 4 + (element * count + 1) // 2
    return 1


def _iter_instructions(units: Sequence[int]) -> Iterator[tuple[int, int, Ref | None]]:
    """(pc, width in code units, reference or None) per instruction or payload."""
    widths, refs = _instruction_widths(), _instruction_refs()
    pc = 0
    while pc < len(units):
        unit = units[pc]
        op = unit & 0xFF
        if op == 0 and unit:
            width = _payload_width(units, pc)
            yield pc, width, None
            pc += width
            continue
        width = widths[op]
        if not width:
            raise ValueError(f"unused opcode {op:#04x} at code unit {pc}")
        ref = refs.get(op)
        if ref is None:
            yield pc, width, None
        else:
            kind, wide = ref
            index = units[pc + 1] | (units[pc + 2] << 16) if wide else units[pc + 1]
            yield pc, width, (kind, index)
            if op in (0xFA, 0xFB):  # invoke-polymorphic also names a proto
                yield pc, 0, (PROTO, units[pc + 3])
        pc += width


@dataclass
class Method:
    index: int  # method_id index
    entry_bytes: int  # its encoded_method in class_data
    refs: list[Ref]
    anno_rows: int = 0  # its rows in the annotation directory, 8 bytes each
    code_bytes: int = 0  # code item, aligned
    code_size: int = 0  # code item, unaligned
    insn_units: int = 0
    has_tries: bool = False
    # (pc, kind, index) of every referencing instruction
    insn_pcs: array.array = field(default_factory=lambda: array.array("I"))
    insn_kinds: array.array = field(default_factory=lambda: array.array("B"))
    insn_idxs: array.array = field(default_factory=lambda: array.array("I"))


@dataclass
class Field:
    index: int
    entry_bytes: int
    refs: list[Ref]
    anno_rows: int = 0


@dataclass
class ClassDef:
    type_index: int
    refs: list[Ref]
    data_bytes: int = 0  # class_data item
    methods: list[Method] = field(default_factory=list)
    fields: list[Field] = field(default_factory=list)


@dataclass(frozen=True)
class Deletion:
    """What goes from one dex: class_def indices, (class, position) of methods
    and fields, and dead pc ranges [start, end) of surviving methods."""

    classes: frozenset[int] = frozenset()
    methods: frozenset[tuple[int, int]] = frozenset()
    fields: frozenset[tuple[int, int]] = frozenset()
    ranges: Mapping[tuple[int, int], Sequence[tuple[int, int]]] = field(
        default_factory=dict
    )


@dataclass(frozen=True)
class Release:
    """What deletions remove from one dex: whole classes, members of other
    classes as (class, position), dead code units of other methods as
    (class, position, pc), and the items no survivor references. The union
    of several releases is what goes with any of them."""

    classes: frozenset[int] = frozenset()
    fields: frozenset[tuple[int, int]] = frozenset()
    methods: frozenset[tuple[int, int]] = frozenset()
    units: frozenset[tuple[int, int, int]] = frozenset()
    items: frozenset[Ref] = frozenset()

    def union(self, *others: Release) -> Release:
        return Release(
            self.classes.union(*(o.classes for o in others)),
            self.fields.union(*(o.fields for o in others)),
            self.methods.union(*(o.methods for o in others)),
            self.units.union(*(o.units for o in others)),
            self.items.union(*(o.items for o in others)),
        )


class DexReferences:
    def __init__(self, data: bytes) -> None:
        self._data = data
        u32 = struct.Struct("<I").unpack_from
        self.signature4: int = u32(data, 12)[0]
        sizes = struct.unpack_from("<12I", data, 0x38)
        n_str, o_str, n_typ, o_typ, n_pro, o_pro = sizes[:6]
        n_fld, o_fld, n_mth, o_mth, n_cls, o_cls = sizes[6:]
        self._string_offsets = struct.unpack_from("<%dI" % n_str, data, o_str)
        self._type_strings = struct.unpack_from("<%dI" % n_typ, data, o_typ)
        self._protos = [
            struct.unpack_from("<III", data, o_pro + 12 * i) for i in range(n_pro)
        ]
        self._field_ids = [
            struct.unpack_from("<HHI", data, o_fld + 8 * i) for i in range(n_fld)
        ]
        self._method_ids = [
            struct.unpack_from("<HHI", data, o_mth + 8 * i) for i in range(n_mth)
        ]
        self._call_sites: tuple[int, ...] = ()
        self._method_handles: list[tuple[int, int, int, int]] = []
        self._read_map_list(u32(data, 0x34)[0])
        # offset-keyed items: offset -> (kind, bytes, references)
        self._shared: dict[int, tuple[int, int, list[Ref]]] = {}
        # debug_info_item offset -> what it names, shared by the methods it serves
        self._debug: dict[int, list[Ref]] = {}
        self.classes: list[ClassDef] = [
            self._class_def(o_cls + 32 * k) for k in range(n_cls)
        ]
        self._counts_before: Counter[Ref] | None = None

    # -- names
    def string(self, index: int) -> str:
        _, start = _uleb(self._data, self._string_offsets[index])
        end = self._data.index(0, start)
        return self._data[start:end].decode("utf-8", "replace")

    def type_name(self, index: int) -> str:
        return self.string(self._type_strings[index])

    def method_name(self, index: int) -> str:
        cls, proto, name = self._method_ids[index]
        _, ret, params = self._protos[proto]
        args = "".join(self.type_name(t) for t in self._type_list_types(params))
        return "%s.%s:(%s)%s" % (
            self.type_name(cls),
            self.string(name),
            args,
            self.type_name(ret),
        )

    def field_name(self, index: int) -> str:
        cls, typ, name = self._field_ids[index]
        return "%s.%s:%s" % (
            self.type_name(cls),
            self.string(name),
            self.type_name(typ),
        )

    # -- parsing
    def _read_map_list(self, offset: int) -> None:
        count = struct.unpack_from("<I", self._data, offset)[0]
        for i in range(count):
            kind, _, size, start = struct.unpack_from(
                "<HHII", self._data, offset + 4 + 12 * i
            )
            if kind == TypeCode.CALL_SITE_ID_ITEM.value:
                self._call_sites = struct.unpack_from("<%dI" % size, self._data, start)
            elif kind == TypeCode.METHOD_HANDLE_ITEM.value:
                self._method_handles = [
                    struct.unpack_from("<HHHH", self._data, start + 8 * k)
                    for k in range(size)
                ]

    def _type_list_types(self, offset: int) -> tuple[int, ...]:
        if not offset:
            return ()
        count = struct.unpack_from("<I", self._data, offset)[0]
        return struct.unpack_from("<%dH" % count, self._data, offset + 4)

    def _type_list(self, offset: int) -> Ref:
        if offset not in self._shared:
            types = self._type_list_types(offset)
            size = 4 + 2 * len(types) + (2 if len(types) % 2 else 0)
            self._shared[offset] = (TYPE_LIST, size, [(TYPE, t) for t in types])
        return (TYPE_LIST, offset)

    def _value(self, offset: int, refs: list[Ref]) -> int:
        header = self._data[offset]
        offset += 1
        value_type, arg = header & 0x1F, header >> 5
        kind = _VALUE_REF.get(value_type)
        if kind is not None:
            size = arg + 1
            refs.append(
                (kind, int.from_bytes(self._data[offset : offset + size], "little"))
            )
            return offset + size
        if value_type == ValueFormat.ARRAY.value:
            count, offset = _uleb(self._data, offset)
            for _ in range(count):
                offset = self._value(offset, refs)
            return offset
        if value_type == ValueFormat.ANNOTATION.value:
            return self._annotation(offset, refs)
        if value_type in (ValueFormat.NULL.value, ValueFormat.BOOLEAN.value):
            return offset
        return offset + arg + 1  # numbers

    def _annotation(self, offset: int, refs: list[Ref]) -> int:
        type_index, offset = _uleb(self._data, offset)
        refs.append((TYPE, type_index))
        count, offset = _uleb(self._data, offset)
        for _ in range(count):
            name, offset = _uleb(self._data, offset)
            refs.append((STRING, name))
            offset = self._value(offset, refs)
        return offset

    def _anno_item(self, offset: int) -> Ref:
        if offset not in self._shared:
            refs: list[Ref] = []
            end = self._annotation(offset + 1, refs)  # skip visibility
            self._shared[offset] = (ANNO_ITEM, end - offset, refs)
        return (ANNO_ITEM, offset)

    def _anno_set(self, offset: int) -> Ref:
        if offset not in self._shared:
            count = struct.unpack_from("<I", self._data, offset)[0]
            items = struct.unpack_from("<%dI" % count, self._data, offset + 4)
            refs = [self._anno_item(i) for i in items]
            self._shared[offset] = (ANNO_SET, 4 + 4 * count, refs)
        return (ANNO_SET, offset)

    def _anno_ref_list(self, offset: int) -> Ref:
        if offset not in self._shared:
            count = struct.unpack_from("<I", self._data, offset)[0]
            sets = struct.unpack_from("<%dI" % count, self._data, offset + 4)
            refs = [self._anno_set(s) for s in sets if s]
            self._shared[offset] = (ANNO_REF_LIST, 4 + 4 * count, refs)
        return (ANNO_REF_LIST, offset)

    def _anno_dir(self, offset: int) -> tuple[Ref, dict[tuple[str, int], Ref]]:
        data = self._data
        class_set, n_fields, n_methods, n_params = struct.unpack_from(
            "<4I", data, offset
        )
        refs = [self._anno_set(class_set)] if class_set else []
        members: dict[tuple[str, int], Ref] = {}
        cursor = offset + 16
        for tag, count, reader in (
            ("f", n_fields, self._anno_set),
            ("m", n_methods, self._anno_set),
            ("p", n_params, self._anno_ref_list),
        ):
            for _ in range(count):
                index, target = struct.unpack_from("<II", data, cursor)
                members[(tag, index)] = reader(target)
                cursor += 8
        self._shared.setdefault(offset, (ANNO_DIR, cursor - offset, refs))
        return (ANNO_DIR, offset), members

    def _static_values(self, offset: int) -> Ref:
        if offset not in self._shared:
            refs: list[Ref] = []
            count, cursor = _uleb(self._data, offset)
            for _ in range(count):
                cursor = self._value(cursor, refs)
            self._shared[offset] = (STATIC_VALUES, cursor - offset, refs)
        return (STATIC_VALUES, offset)

    def _class_def(self, offset: int) -> ClassDef:
        cls, _, sup, ifaces, src, annos, data_off, static = struct.unpack_from(
            "<8I", self._data, offset
        )
        refs: list[Ref] = [(TYPE, cls)]
        if sup != 0xFFFFFFFF:
            refs.append((TYPE, sup))
        if src != 0xFFFFFFFF:
            refs.append((STRING, src))
        if ifaces:
            refs.append(self._type_list(ifaces))
        members: dict[tuple[str, int], Ref] = {}
        if annos:
            directory, members = self._anno_dir(annos)
            refs.append(directory)
        if static:
            refs.append(self._static_values(static))
        result = ClassDef(cls, refs)
        if data_off:
            self._class_data(result, data_off, members)
        return result

    def _class_data(
        self, result: ClassDef, offset: int, members: dict[tuple[str, int], Ref]
    ) -> None:
        data = self._data
        static_fields, cursor = _uleb(data, offset)
        instance_fields, cursor = _uleb(data, cursor)
        direct, cursor = _uleb(data, cursor)
        virtual, cursor = _uleb(data, cursor)
        index = 0
        for position in range(static_fields + instance_fields):
            if position == static_fields:
                index = 0
            start = cursor
            delta, cursor = _uleb(data, cursor)
            _, cursor = _uleb(data, cursor)
            index += delta
            fld = Field(index, cursor - start, [(FIELD_ID, index)])
            if ("f", index) in members:
                fld.refs.append(members[("f", index)])
                fld.anno_rows = 1
            result.fields.append(fld)
        index = 0
        for position in range(direct + virtual):
            if position == direct:
                index = 0
            start = cursor
            delta, cursor = _uleb(data, cursor)
            _, cursor = _uleb(data, cursor)
            code, cursor = _uleb(data, cursor)
            index += delta
            method = Method(index, cursor - start, [(METHOD_ID, index)])
            for tag in ("m", "p"):
                if (tag, index) in members:
                    method.refs.append(members[(tag, index)])
                    method.anno_rows += 1
            if code:
                self._code(method, code)
            result.methods.append(method)
        result.data_bytes = cursor - offset

    def _code(self, method: Method, offset: int) -> None:
        data = self._data
        tries, debug_info = struct.unpack_from("<HI", data, offset + 6)
        n_units = struct.unpack_from("<I", data, offset + 12)[0]
        if debug_info:
            method.refs += self._debug_refs(debug_info)
        units = array.array("H")
        units.frombytes(data[offset + 16 : offset + 16 + 2 * n_units])
        end = offset + 16 + 2 * n_units
        if tries:
            end += (2 if n_units & 1 else 0) + 8 * tries
            handlers, end = _uleb(data, end)
            for _ in range(handlers):
                size, end = _sleb(data, end)
                for _ in range(abs(size)):
                    type_index, end = _uleb(data, end)
                    method.refs.append((TYPE, type_index))
                    _, end = _uleb(data, end)
                if size <= 0:
                    _, end = _uleb(data, end)
        method.code_size = end - offset
        method.code_bytes = _aligned(method.code_size)
        method.insn_units = n_units
        method.has_tries = tries > 0
        for pc, _, ref in _iter_instructions(units):
            if ref is not None:
                method.insn_pcs.append(pc)
                method.insn_kinds.append(ref[0])
                method.insn_idxs.append(ref[1])

    def _debug_refs(self, offset: int) -> list[Ref]:
        """The strings and types a debug_info_item names: parameter names,
        local variable names, types and signatures, and source file names."""
        if offset in self._debug:
            return self._debug[offset]
        data = self._data
        refs: list[Ref] = []

        def name(cursor: int, kind: int) -> int:
            # uleb128p1: the index plus one, 0 for none
            index, cursor = _uleb(data, cursor)
            if index:
                refs.append((kind, index - 1))
            return cursor

        _, cursor = _uleb(data, offset)  # line_start
        parameters, cursor = _uleb(data, cursor)
        for _ in range(parameters):
            cursor = name(cursor, STRING)
        while (opcode := data[cursor]) != 0x00:  # DBG_END_SEQUENCE
            cursor += 1
            if opcode in (0x01, 0x02, 0x05, 0x06):  # one uleb128 or sleb128
                _, cursor = _uleb(data, cursor)
            elif opcode in (0x03, 0x04):  # DBG_START_LOCAL(_EXTENDED)
                _, cursor = _uleb(data, cursor)  # register
                cursor = name(cursor, STRING)
                cursor = name(cursor, TYPE)
                if opcode == 0x04:
                    cursor = name(cursor, STRING)  # signature
            elif opcode == 0x09:  # DBG_SET_FILE
                cursor = name(cursor, STRING)
        self._debug[offset] = refs
        return refs

    # -- reference closure
    def _item_refs(self, ref: Ref) -> Sequence[Ref]:
        kind, index = ref
        if kind == TYPE:
            return ((STRING, self._type_strings[index]),)
        if kind == PROTO:
            shorty, ret, params = self._protos[index]
            if params:
                return ((STRING, shorty), (TYPE, ret), self._type_list(params))
            return ((STRING, shorty), (TYPE, ret))
        if kind == FIELD_ID:
            cls, typ, name = self._field_ids[index]
            return ((TYPE, cls), (TYPE, typ), (STRING, name))
        if kind == METHOD_ID:
            cls, proto, name = self._method_ids[index]
            return ((TYPE, cls), (PROTO, proto), (STRING, name))
        if kind == CALL_SITE:
            # call_site_item: an encoded array of the bootstrap method handle,
            # method name, method type and extra arguments
            refs: list[Ref] = []
            count, cursor = _uleb(self._data, self._call_sites[index])
            for _ in range(count):
                cursor = self._value(cursor, refs)
            return refs
        if kind == METHOD_HANDLE:
            handle_type, _, member, _ = self._method_handles[index]
            # Handles up to instance-get access a field; the others invoke a method.
            accessor = handle_type <= MethodHandleTypeCode.INSTANCE_GET.value
            return ((FIELD_ID if accessor else METHOD_ID, member),)
        if kind == STRING:
            return ()
        return self._shared[index][2]

    def _holder_refs(self, deletion: Deletion) -> Iterator[Ref]:
        """Every reference the deletion removes, one per occurrence."""
        for c, cls in enumerate(self.classes):
            whole = c in deletion.classes
            if whole:
                yield from cls.refs
            for f, fld in enumerate(cls.fields):
                if whole or (c, f) in deletion.fields:
                    yield from fld.refs
            for m, method in enumerate(cls.methods):
                if whole or (c, m) in deletion.methods:
                    yield from method.refs
                    ranges: Sequence[tuple[int, int]] = ((0, method.insn_units),)
                else:
                    ranges = deletion.ranges.get((c, m), ())
                    if not ranges:
                        continue
                for pc, kind, index in zip(
                    method.insn_pcs, method.insn_kinds, method.insn_idxs
                ):
                    if any(start <= pc < end for start, end in ranges):
                        yield (kind, index)

    def _reference_counts(self) -> Counter[Ref]:
        """References to each item from holders and from other items. Items
        form no cycles, so an item dies exactly when its count reaches 0.
        Call sites and method handles count one reference more than they
        have, so that they and what they name never die."""
        counts: Counter[Ref] = Counter(self._holder_refs(self._everything()))
        counts.update((CALL_SITE, i) for i in range(len(self._call_sites)))
        counts.update((METHOD_HANDLE, i) for i in range(len(self._method_handles)))
        stack = list(counts)
        while stack:
            for ref in self._item_refs(stack.pop()):
                if ref not in counts:
                    stack.append(ref)
                counts[ref] += 1
        return counts

    def _everything(self) -> Deletion:
        return Deletion(classes=frozenset(range(len(self.classes))))

    def release(self, deletion: Deletion) -> Release:
        """What `deletion` removes from this dex."""
        if self._counts_before is None:
            self._counts_before = self._reference_counts()
        counts = self._counts_before
        items: set[Ref] = set()
        dropped: Counter[Ref] = Counter()
        stack = list(self._holder_refs(deletion))
        while stack:
            ref = stack.pop()
            dropped[ref] += 1
            if dropped[ref] == counts[ref]:
                items.add(ref)
                stack.extend(self._item_refs(ref))
        return Release(
            classes=deletion.classes,
            fields=frozenset(deletion.fields),
            methods=frozenset(deletion.methods),
            units=frozenset(
                (c, m, pc)
                for (c, m), ranges in deletion.ranges.items()
                for start, end in ranges
                for pc in range(start, end)
            ),
            items=frozenset(items),
        )

    def size(self, release: Release) -> Counter[str]:
        """Bytes per section that `release` frees in this dex."""
        out: Counter[str] = Counter()
        for c in release.classes:
            cls = self.classes[c]
            out["class_def"] += 32
            out["class_data"] += cls.data_bytes
            out["code"] += sum(method.code_bytes for method in cls.methods)
        # Members of a surviving class: their class_data entries and
        # annotation directory rows.
        for c, f in release.fields:
            if c not in release.classes:
                fld = self.classes[c].fields[f]
                out["class_data"] += fld.entry_bytes
                out["anno_dir"] += 8 * fld.anno_rows
        for c, m in release.methods:
            if c not in release.classes:
                method = self.classes[c].methods[m]
                out["class_data"] += method.entry_bytes
                out["anno_dir"] += 8 * method.anno_rows
                out["code"] += method.code_bytes
        for (c, m), dead in self._emptied_units(release).items():
            out["code"] += _shrunk_bytes(self.classes[c].methods[m], dead)
        for ref in release.items:
            self._add_item_bytes(ref, out)
        return out

    def _emptied_units(self, release: Release) -> Counter[tuple[int, int]]:
        """Dead code units per surviving method. A surviving method keeps at
        least one unit, a return, even when all of its code is dead."""
        units: Counter[tuple[int, int]] = Counter(
            (c, m)
            for c, m, _ in release.units
            if c not in release.classes and (c, m) not in release.methods
        )
        for (c, m), count in units.items():
            if count == self.classes[c].methods[m].insn_units:
                units[(c, m)] = count - 1
        return units

    def freed(self, deletion: Deletion) -> Counter[str]:
        """Bytes per section that `deletion` frees in this dex."""
        return self.size(self.release(deletion))

    def _add_item_bytes(self, ref: Ref, out: Counter[str]) -> None:
        kind, index = ref
        if kind == STRING:
            offset = self._string_offsets[index]
            _, start = _uleb(self._data, offset)
            out["string_id"] += 4
            out["string_data"] += self._data.index(0, start) + 1 - offset
        elif kind in (CALL_SITE, METHOD_HANDLE):
            return
        elif kind in _ID_KINDS:
            out[SECTION[kind]] += {TYPE: 4, PROTO: 12}.get(kind, 8)
        else:
            out[SECTION[kind]] += self._shared[index][1]
