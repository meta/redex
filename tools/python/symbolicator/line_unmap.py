# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import absolute_import, division, print_function

import logging
import mmap
import struct
from collections import namedtuple


Position = namedtuple("Position", "method file line")
MapEntry = namedtuple("MapEntry", "class_id method_id file_id line parent")

# The v2 map's optional extension (libredex/DexPosition.h): section payloads,
# a directory of (tag, reserved, offset, length), and a trailer of
# (directory offset, section count, magic) at the end of the file.
TRAILER = struct.Struct("<QLL")
SECTION = struct.Struct("<LLQQ")
PROVENANCE_ENTRY = struct.Struct("<LLL")
TRAILER_MAGIC = 0xFACEB002
PROVENANCE_TAG = 0x564F5250  # 'PROV'


def read_unreliable(
    mapping: mmap.mmap, positions_end: int, pos_count: int
) -> frozenset[int]:
    """Indices of the positions the map marks unreliable: their stack may not
    be the code's only source, e.g. one position kept for blocks merged from
    several places. Empty when the map has no extension. `mapping` is the
    whole map, memory-mapped as `PositionMap.read_from` opens it."""
    size = len(mapping)
    if size < positions_end + TRAILER.size:
        return frozenset()
    directory, count, magic = TRAILER.unpack_from(mapping, size - TRAILER.size)
    if magic != TRAILER_MAGIC:
        return frozenset()
    if directory + count * SECTION.size + TRAILER.size != size:
        raise ValueError("line map trailer: directory does not end at the trailer")
    unreliable = []
    for i in range(count):
        tag, _, offset, length = SECTION.unpack_from(
            mapping, directory + i * SECTION.size
        )
        if offset < positions_end or offset + length > directory:
            raise ValueError("line map trailer: section out of bounds")
        if tag != PROVENANCE_TAG:
            continue
        if length % PROVENANCE_ENTRY.size:
            raise ValueError("line map trailer: partial provenance entry")
        for j in range(length // PROVENANCE_ENTRY.size):
            index = PROVENANCE_ENTRY.unpack_from(
                mapping, offset + j * PROVENANCE_ENTRY.size
            )[0]
            if index >= pos_count or (unreliable and index <= unreliable[-1]):
                raise ValueError("line map trailer: bad provenance record index")
            unreliable.append(index)
    return frozenset(unreliable)


class PositionMap(object):
    def __init__(self):
        self.string_pool = []
        self.positions = []
        # None until read_from is asked for them; see rows_naming.
        self.unreliable = None

    @staticmethod
    def read_from(filename, with_unreliable=False):
        """Reads the map. With `with_unreliable`, also reads and validates the
        v2 extension that marks unreliable positions, which `rows_naming`
        needs; symbolication does not use it."""
        with open(filename) as f:
            mapping = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
            magic = struct.unpack("<L", mapping.read(4))[0]
            if magic != 0xFACEB000:
                raise Exception("Magic number mismatch")
            version = struct.unpack("<L", mapping.read(4))[0]
            if version not in [1, 2]:
                raise Exception("Version mismatch")
            spool_count = struct.unpack("<L", mapping.read(4))[0]
            pmap = PositionMap()
            for _ in range(0, spool_count):
                ssize = struct.unpack("<L", mapping.read(4))[0]
                pmap.string_pool.append(mapping.read(ssize).decode("utf-8"))
            logging.info("Unpacked %d strings from line map", spool_count)
            pos_count = struct.unpack("<L", mapping.read(4))[0]
            # this is pretty slow; it would be much faster in C++ with memcpy
            # and arrays of structs, but I don't know how to call C/C++ from
            # Python under our build system
            for _ in range(0, pos_count):
                if version == 1:
                    pmap.positions.append(
                        MapEntry._make(
                            (None, None) + struct.unpack("<LLL", mapping.read(12))
                        )
                    )
                else:
                    pmap.positions.append(
                        MapEntry._make(struct.unpack("<LLLLL", mapping.read(20)))
                    )
            logging.info("Unpacked %d map entries from line map", pos_count)
            if with_unreliable:
                pmap.unreliable = (
                    read_unreliable(mapping, mapping.tell(), pos_count)
                    if version == 2
                    else frozenset()
                )
            return pmap

    def rows_naming(self, names):
        """Method name -> the rows (1-based, as the debug line map refers to
        them) whose stack contains it, for each method name (`com.a.B.m`) in
        `names`. A row with an unreliable position on its stack is left out:
        its code may also come from elsewhere. As in `get_stack`, a parent
        outside the map ends a stack, and a v1 row names no method. Needs the
        map read with `with_unreliable`."""
        if self.unreliable is None:
            raise ValueError("rows_naming needs read_from(..., with_unreliable=True)")
        positions = self.positions
        found = [None] * len(positions)
        tainted = bytearray(len(positions))
        empty = frozenset()
        for start in range(len(positions)):
            # Walk up to the first row already resolved, then resolve the walk.
            chain = []
            index = start
            while 0 <= index < len(positions) and found[index] is None:
                if len(chain) > len(positions):
                    raise ValueError("line map row %d has a parent cycle" % (start + 1))
                chain.append(index)
                index = positions[index].parent - 1
            inside = 0 <= index < len(positions)
            inherited = found[index] if inside else empty
            taint = tainted[index] if inside else 0
            for row in reversed(chain):
                p = positions[row]
                if p.class_id is not None:
                    own = (
                        self.string_pool[p.class_id]
                        + "."
                        + self.string_pool[p.method_id]
                    )
                    if own in names:
                        inherited = inherited | {own}
                taint = taint or row in self.unreliable
                found[row] = inherited
                tainted[row] = taint
        rows = {}
        for row, hit in enumerate(found):
            if not tainted[row]:
                for name in hit:
                    rows.setdefault(name, set()).add(row + 1)
        return {name: frozenset(r) for name, r in rows.items()}

    def get_stack(self, idx):
        stack = []
        while idx >= 0 and idx < len(self.positions):
            pi = self.positions[idx]
            if pi.class_id is not None:
                method = (
                    self.string_pool[pi.class_id] + "." + self.string_pool[pi.method_id]
                )
            else:
                method = None
            stack.append(Position(method, self.string_pool[pi.file_id], pi.line))
            idx = pi.parent - 1
        return stack
