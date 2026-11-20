# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import absolute_import, division, print_function

import logging
import mmap
import struct
from collections import namedtuple


OffsetLine = namedtuple("OffsetLine", "offset line")


def method_key(method_index, dex_signature4):
    """A method's key in the debug line map: its method_id index in the high
    32 bits and the first four bytes of its dex's signature, read
    little-endian, in the low ones."""
    return (method_index << 32) | dex_signature4


class DebugLineMap(object):
    def __init__(self, method_id_map):
        self.method_id_map = method_id_map

    @staticmethod
    def read_from(filename):
        with open(filename) as f:
            mapping = mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ)
            magic = struct.unpack("<L", mapping.read(4))[0]
            if magic != 0xFACEB000:
                raise Exception("Magic number mismatch")
            version = struct.unpack("<L", mapping.read(4))[0]
            if version != 1:
                raise Exception("Version mismatch")
            method_count = struct.unpack("<L", mapping.read(4))[0]
            method_data_struct = struct.Struct("<QLL")
            offset_line_struct = struct.Struct("<LL")
            method_datas = []
            for _ in range(method_count):
                method_datas.append(method_data_struct.unpack(mapping.read(16)))
            method_id_map = {}
            for i in range(method_count):
                method_id = struct.unpack("<Q", mapping.read(8))[0]
                if method_id != method_datas[i][0]:
                    raise Exception("Method id mismatch")
                if method_id in method_id_map:
                    raise Exception(
                        "Found duplicate method id entry: " + str(method_id)
                    )
                line_mapping_size = method_datas[i][2] - 8
                line_mapping_count = line_mapping_size // 8
                if line_mapping_count > 0:
                    line_mappings = []
                    for _ in range(line_mapping_count):
                        line_mappings.append(
                            OffsetLine(*offset_line_struct.unpack(mapping.read(8)))
                        )
                    method_id_map[method_id] = line_mappings
            logging.info(
                "Unpacked " + str(len(method_id_map)) + " methods from debug line map"
            )
            return DebugLineMap(method_id_map)

    def find_line_number(self, method_id, line):
        method_id = int(method_id)
        line = int(line)
        if method_id in self.method_id_map:
            mappings = self.method_id_map[method_id]
            result = None
            for pc, mapped_line in mappings:
                if pc <= line:
                    result = mapped_line
                else:
                    if result is None:
                        # Better to give a rough line number than fail epicly
                        result = mapped_line
                    break
            return result
        return None

    def get_mappings(self, method_id):
        method_id = int(method_id)
        if method_id in self.method_id_map:
            return self.method_id_map[method_id]
        return None
