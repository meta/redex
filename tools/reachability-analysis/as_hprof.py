#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# pyre-strict

import argparse
import io
import logging
from contextlib import contextmanager
from typing import (
    Any,
    Callable,
    Generator,
    List,
    Mapping,
    NewType,
    Optional,
    Set,
    Tuple,
)

from lib.core import ReachabilityGraph, ReachableObject, ReachableObjectType


class Buffer:
    def __init__(self) -> None:
        self._buffer = io.BytesIO()
        self._mark: int = -1

    def write_to(self, out: io.BytesIO) -> int:
        self._buffer.seek(0, io.SEEK_SET)
        buf = bytearray(4096)
        num_bytes = 0
        while True:
            buf_len = self._buffer.readinto(buf)
            if buf_len <= 0:
                break
            num_bytes += buf_len
            if buf_len == len(buf):
                out.write(buf)
            else:
                out.write(buf[:buf_len])

        return num_bytes

    def write(self, data: bytes) -> None:
        self._buffer.write(data)

    def writeU1(self, value: int) -> None:
        self._buffer.write(value.to_bytes(1, "big", signed=False))

    def writeU2(self, value: int) -> None:
        self._buffer.write(value.to_bytes(2, "big", signed=False))

    def writeU4(self, value: int) -> None:
        self._buffer.write(value.to_bytes(4, "big", signed=False))

    def tell(self) -> int:
        return self._buffer.tell()

    def update_u4(self, offset: int, value: int) -> None:
        self._buffer.seek(offset, io.SEEK_SET)
        self.writeU4(value)
        self._buffer.seek(0, io.SEEK_END)

    def start_record_with_mark(self, record_type: int) -> int:
        self.writeU1(record_type)
        self.writeU4(0x87654321)  # No time difference
        mark = self._buffer.tell()
        self.writeU4(0)  # Length, to be fixed up later
        return mark

    def start_record(self, record_type: int) -> None:
        self._mark = self.start_record_with_mark(record_type)

    def end_record_with_mark(self, mark: int) -> None:
        cur = self._buffer.tell()
        self._buffer.seek(mark, io.SEEK_SET)
        self.writeU4(cur - mark - 4)
        self._buffer.seek(cur, io.SEEK_SET)

    def end_record(self) -> None:
        assert self._mark > 0
        self.end_record_with_mark(self._mark)
        self._mark = -1

    @contextmanager
    def new_record(self, record_type: int) -> Generator[None, None, None]:
        mark = self.start_record_with_mark(record_type)
        yield
        self.end_record_with_mark(mark)


StringId = NewType("StringId", int)
ClassId = NewType("ClassId", int)
ObjectId = NewType("ObjectId", int)


class Hprof:
    TYPE_OBJECT: int = 2
    TYPE_BYTE: int = 8

    HPROF_GC_CLASS_DUMP: int = 0x20
    HPROF_GC_INSTANCE_DUMP: int = 0x21
    HPROF_GC_OBJ_ARRAY_DUMP: int = 0x22
    HPROF_GC_PRIM_ARRAY_DUMP: int = 0x23

    HPROF_GC_ROOT_UNKNOWN: int = 0xFF

    def __init__(self) -> None:
        self._buffer = Buffer()
        self._buffer.write(b"JAVA PROFILE 1.0.2\0")
        # IDs are 4 bytes long.
        self._buffer.writeU4(4)
        # Timestamp, leave at era.
        self._buffer.writeU4(0)
        self._buffer.writeU4(0)

        self._write_empty_stack_trace()

        self._strings: dict[str, StringId] = {}
        self._strings_buffer = Buffer()

        self._classes: dict[str, ClassId] = {}
        self._classes_buffer = Buffer()

        # pyre-ignore[4]
        self._objects: dict[Any, ObjectId] = {}
        self._objects_buffer = Buffer()
        self._objects_buffer_check: bool = False

        self._string_class: Optional[ClassId] = None
        self._object_array_class: Optional[ClassId] = None

    def finish(self) -> None:
        self._strings_buffer.write_to(self._buffer._buffer)
        self._classes_buffer.write_to(self._buffer._buffer)
        with self._buffer.new_record(0x0C):
            self._objects_buffer.write_to(self._buffer._buffer)

    def to_bytes(self) -> bytes:
        return self._buffer._buffer.getvalue()

    def _write_empty_stack_trace(self) -> None:
        with self._buffer.new_record(0x05):
            self._buffer.writeU4(0)  # stack trace serial number
            self._buffer.writeU4(0)  # null thread
            self._buffer.writeU4(0)  # no frames

    def lookup_str(self, val: str) -> StringId:
        id = self._strings.get(val)
        if id:
            return id

        # Similar to Android.
        next_id = StringId(0x400000 + len(self._strings))
        self._strings[val] = next_id

        # A string record
        with self._strings_buffer.new_record(0x01):
            self._strings_buffer.writeU4(next_id)
            self._strings_buffer.write(val.encode())  # UTF-8

        return next_id

    def lookup_class(self, val: str) -> ClassId:
        id = self._classes.get(val)
        if id:
            return id

        next_id = ClassId(0x200000 + len(self._classes))
        self._classes[val] = next_id

        with self._classes_buffer.new_record(0x02):
            self._classes_buffer.writeU4(next_id)  # class serial
            self._classes_buffer.writeU4(next_id)  # object id
            self._classes_buffer.writeU4(0)  # stack trace serial
            self._classes_buffer.writeU4(self.lookup_str(val))  # class name string id

        return next_id

    @contextmanager
    def new_object(self, tag: int) -> Generator[Buffer, None, None]:
        assert not self._objects_buffer_check
        self._objects_buffer_check = True

        self._objects_buffer.writeU1(tag)
        yield self._objects_buffer

        self._objects_buffer_check = False

    @contextmanager
    def write_class(
        self, klass: str, superklass: Optional[str], instance_size: int
    ) -> Generator[Tuple[Buffer, ClassId], None, None]:
        with self.new_object(Hprof.HPROF_GC_CLASS_DUMP) as buf:
            class_id = self.lookup_class(klass)
            buf.writeU4(class_id)
            buf.writeU4(0)
            buf.writeU4(self.lookup_class(superklass) if superklass else 0)
            buf.writeU4(0)  # classloader
            buf.writeU4(0)  # signer
            buf.writeU4(0)  # protection domain
            buf.writeU4(0)  # reserved
            buf.writeU4(0)  # reserved
            buf.writeU4(instance_size)
            buf.writeU2(0)  # constant pool
            buf.writeU2(0)  # static fields
            yield buf, class_id

    def write_string_class(self) -> ClassId:
        id = self._string_class
        if id:
            return id

        with self.write_class("Ljava/lang/String;", None, 0) as (buf, class_id):
            # Just a "value" field pointing to data array
            buf.writeU2(1)
            buf.writeU4(self.lookup_str("value"))
            buf.writeU1(Hprof.TYPE_OBJECT)

            self._string_class = class_id
            return class_id

    # pyre-ignore[2]
    def next_object_id(self, key: Optional[Any] = None) -> ObjectId:
        id = ObjectId(0x600000 + len(self._objects))
        self._objects[key or id] = id
        return id

    @contextmanager
    def write_heap_instance(
        self, object_id: ObjectId, class_id: ClassId
    ) -> Generator[Buffer, None, None]:
        with self.new_object(Hprof.HPROF_GC_INSTANCE_DUMP) as buf:
            buf.writeU4(object_id)
            buf.writeU4(0)  # stacktrace serial
            buf.writeU4(class_id)
            # Length, needs to be patched
            len_pos = buf.tell()
            buf.writeU4(0)
            yield buf
            now_pos = buf.tell()
            buf.update_u4(len_pos, now_pos - len_pos - 4)

    def write_string(self, val: str) -> ObjectId:
        id = self._objects.get(val)
        if id:
            return id

        string_class_id = self.write_string_class()  # Ensure the class exists.

        # Dump the string content.
        primitive_id = self.write_byte_array(None, val.encode("utf-8"))

        next_id = self.next_object_id(val)
        # Now write the string object.
        with self.write_heap_instance(next_id, string_class_id) as buf:
            buf.writeU4(primitive_id)

        return next_id

    def write_byte_array(self, object_id: Optional[ObjectId], data: bytes) -> ObjectId:
        if not object_id:
            object_id = self.next_object_id()

        with self.new_object(Hprof.HPROF_GC_PRIM_ARRAY_DUMP) as buf:
            buf.writeU4(object_id)
            buf.writeU4(0)  # stacktrace serial
            buf.writeU4(len(data))
            buf.writeU1(Hprof.TYPE_BYTE)
            buf.write(data)

        return object_id

    def write_object_array_class(self) -> ClassId:
        id = self._object_array_class
        if id:
            return id

        with self.write_class("[Ljava/lang/Object;", None, 0) as (buf, class_id):
            # TODO: Is it OK to elide the length field?
            buf.writeU2(0)

            self._object_array_class = class_id
            return class_id

    def write_object_array(
        self, object_id: Optional[ObjectId], data: List[ObjectId]
    ) -> ObjectId:
        # Ensure the array class exists.
        self.write_object_array_class()

        if not object_id:
            object_id = self.next_object_id()

        with self.new_object(Hprof.HPROF_GC_OBJ_ARRAY_DUMP) as buf:
            buf.writeU4(object_id)
            buf.writeU4(0)  # stacktrace serial
            buf.writeU4(len(data))
            buf.writeU4(self.lookup_class("[Ljava/lang/Object;"))
            for id in data:
                buf.writeU4(id)

        return object_id

    def make_root(self, object_id: ObjectId) -> None:
        with self.new_object(Hprof.HPROF_GC_ROOT_UNKNOWN) as buf:
            buf.writeU4(object_id)


class ReachabilityHprof:
    def __init__(self, hprof: Hprof) -> None:
        self.hprof = hprof
        self._strings: set[ObjectId] = set()

    def alloc_string(self, val: str) -> ObjectId:
        val_id = self.hprof.write_string(val)
        self._strings.add(val_id)
        return val_id

    def finish(self) -> None:
        # Write a synthetic holder for the strings that is a root. We do this
        # so the names are not contained as retained size.
        data = list(self._strings)
        if data:
            object_id = self.hprof.write_object_array(None, data)
            self.hprof.make_root(object_id)
            # Write it again so that unreferenced strings are not dominated.
            object_id = self.hprof.write_object_array(None, data)
            self.hprof.make_root(object_id)

    def reserve_reachable_type_object_ids(
        self, graph: ReachabilityGraph, node_type: int
    ) -> Mapping[ReachableObject, ObjectId]:
        ret = {}
        for node in graph.node_records:
            if node.type != node_type:
                continue

            object_id = self.hprof.next_object_id()
            ret[node] = object_id

        return ret

    def run(self, graph: ReachabilityGraph) -> None:
        class_ids = self.reserve_reachable_type_object_ids(
            graph, ReachableObjectType.CLASS
        )
        logging.info("Found %d classes", len(class_ids))

        method_ids = self.reserve_reachable_type_object_ids(
            graph, ReachableObjectType.METHOD
        )
        logging.info("Found %d methods", len(method_ids))

        field_ids = self.reserve_reachable_type_object_ids(
            graph, ReachableObjectType.FIELD
        )
        logging.info("Found %d fields", len(field_ids))

        anno_ids = self.reserve_reachable_type_object_ids(
            graph, ReachableObjectType.ANNO
        )
        logging.info("Found %d annotations", len(anno_ids))

        seeds_ids = self.reserve_reachable_type_object_ids(
            graph, ReachableObjectType.SEED
        )
        logging.info("Found %d seeds", len(seeds_ids))

        global_ids = {**seeds_ids, **method_ids, **class_ids, **field_ids, **anno_ids}
        assert len(global_ids) == sum(
            len(e) for e in [class_ids, method_ids, field_ids, seeds_ids, anno_ids]
        )

        self.write_reachable_type_objects(class_ids, global_ids, self.write_class)
        self.write_reachable_type_objects(method_ids, global_ids, self.write_method)
        self.write_reachable_type_objects(field_ids, global_ids, self.write_field)
        self.write_reachable_type_objects(anno_ids, global_ids, self.write_anno)
        self.write_reachable_type_objects(seeds_ids, global_ids, self.write_seed)
        for node, object_id in global_ids.items():
            if node.type == ReachableObjectType.SEED or not node.preds:
                self.hprof.make_root(object_id)
        self.finish()

    def write_reachable_type_objects(
        self,
        nodes: Mapping[ReachableObject, ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        write_fn: Callable[
            [
                ReachableObject,
                List[ObjectId],
                Mapping[ReachableObject, ObjectId],
                Optional[ObjectId],
            ],
            ObjectId,
        ],
    ) -> None:
        for node, object_id in nodes.items():
            succs_ids = [
                all_nodes[succ_node]
                for succ_node in node.succs.keys()
                if succ_node in all_nodes
            ]
            write_fn(node, succs_ids, all_nodes, object_id)

    def write_class(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        raise RuntimeError("Unimplemented")

    def write_method(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        raise RuntimeError("Unimplemented")

    def write_field(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        raise RuntimeError("Unimplemented")

    def write_anno(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        raise RuntimeError("Unimplemented")

    def write_seed(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        raise RuntimeError("Unimplemented")


class ReachabilityHprofOneClassEach(ReachabilityHprof):
    def __init__(self, hprof: Hprof, split_fields: bool) -> None:
        super().__init__(hprof)
        self._classes_created: dict[str, ClassId] = {}
        self.split_fields = split_fields

        self.field_names: list[str] = (
            ["methods", "fields", "types", "other"] if split_fields else ["succs"]
        )
        self.field_types: list[set[int]] = (
            [
                {ReachableObjectType.METHOD},
                {ReachableObjectType.FIELD},
                {ReachableObjectType.CLASS},
                {ReachableObjectType.ANNO, ReachableObjectType.SEED},
            ]
            if split_fields
            else [set()]
        )
        assert len(self.field_names) == len(self.field_types)

    def write_reachability_object_class(self, class_name: str) -> ClassId:
        class_id = self._classes_created.get(class_name)
        if class_id:
            return class_id

        with self.hprof.write_class(class_name, None, 0) as (buf, class_id):
            # A field for the name, and a field for the array holding successors.
            buf.writeU2(1 + len(self.field_names))

            buf.writeU4(self.hprof.lookup_str("name"))
            buf.writeU1(Hprof.TYPE_OBJECT)

            for field in self.field_names:
                buf.writeU4(self.hprof.lookup_str(field))
                buf.writeU1(Hprof.TYPE_OBJECT)

            self._classes_created[class_name] = class_id
            return class_id

    def write_reachability_instance(
        self,
        class_id: ClassId,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        name_id = self.alloc_string(obj.name)

        if not obj_id:
            obj_id = self.hprof.next_object_id()

        if not self.split_fields:
            succs_id = self.hprof.write_object_array(None, succs)

            with self.hprof.write_heap_instance(obj_id, class_id) as buf:
                buf.writeU4(name_id)
                buf.writeU4(succs_id)

            return obj_id

        def get_succs_array(node_types: Set[int]) -> ObjectId:
            data = [
                all_nodes[succ_node]
                for succ_node in obj.succs.keys()
                if succ_node.type in node_types and succ_node in all_nodes
            ]
            return self.hprof.write_object_array(None, data) if data else ObjectId(0)

        field_ids = [get_succs_array(node_types) for node_types in self.field_types]

        with self.hprof.write_heap_instance(obj_id, class_id) as buf:
            buf.writeU4(name_id)
            for field_id in field_ids:
                buf.writeU4(field_id)

        return obj_id

    def write_seed(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        keep_class_id = self.write_reachability_object_class("LKeep;")
        return self.write_reachability_instance(
            keep_class_id, obj, succs, all_nodes, obj_id
        )

    def write_method(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        method_class_id = self.write_reachability_object_class("LMethod;")
        return self.write_reachability_instance(
            method_class_id, obj, succs, all_nodes, obj_id
        )

    def write_class(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        class_class_id = self.write_reachability_object_class("LClass;")
        return self.write_reachability_instance(
            class_class_id, obj, succs, all_nodes, obj_id
        )

    def write_field(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        field_class_id = self.write_reachability_object_class("LField;")
        return self.write_reachability_instance(
            field_class_id, obj, succs, all_nodes, obj_id
        )

    def write_anno(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        anno_class_id = self.write_reachability_object_class("LAnno;")
        return self.write_reachability_instance(
            anno_class_id, obj, succs, all_nodes, obj_id
        )


class ReachabilityHprofOneClassPerEntity(ReachabilityHprof):
    def __init__(self, hprof: Hprof, split_fields: bool) -> None:
        super().__init__(hprof)
        self._classes_created: dict[str, ClassId] = {}
        self.split_fields = split_fields

        self.field_names: list[str] = (
            ["methods", "fields", "types", "other"] if split_fields else ["succs"]
        )
        self.field_types: list[set[int]] = (
            [
                {ReachableObjectType.METHOD},
                {ReachableObjectType.FIELD},
                {ReachableObjectType.CLASS},
                {ReachableObjectType.ANNO, ReachableObjectType.SEED},
            ]
            if split_fields
            else [set()]
        )
        assert len(self.field_names) == len(self.field_types)

    def write_reachability_object_class(self, class_name: str) -> ClassId:
        # Note: we should create a Java-legal name here, but at least MAT does
        # not care.
        class_name = f"L{class_name};"

        class_id = self._classes_created.get(class_name)
        if class_id:
            return class_id

        with self.hprof.write_class(class_name, None, 0) as (buf, class_id):
            # A field for the array holding successors.
            buf.writeU2(len(self.field_names))

            for field in self.field_names:
                buf.writeU4(self.hprof.lookup_str(field))
                buf.writeU1(Hprof.TYPE_OBJECT)

            self._classes_created[class_name] = class_id
            return class_id

    def write_reachability_instance(
        self,
        class_id: ClassId,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        if not obj_id:
            obj_id = self.hprof.next_object_id()

        if not self.split_fields:
            succs_id = self.hprof.write_object_array(None, succs)

            with self.hprof.write_heap_instance(obj_id, class_id) as buf:
                buf.writeU4(succs_id)

            return obj_id

        def get_succs_array(node_types: Set[int]) -> ObjectId:
            data = [
                all_nodes[succ_node]
                for succ_node in obj.succs.keys()
                if succ_node.type in node_types and succ_node in all_nodes
            ]
            return self.hprof.write_object_array(None, data) if data else ObjectId(0)

        field_ids = [get_succs_array(node_types) for node_types in self.field_types]

        with self.hprof.write_heap_instance(obj_id, class_id) as buf:
            for field_id in field_ids:
                buf.writeU4(field_id)

        return obj_id

    def write_seed(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        keep_class_id = self.write_reachability_object_class(f"keep/{obj.name}")
        return self.write_reachability_instance(
            keep_class_id, obj, succs, all_nodes, obj_id
        )

    def write_method(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId],
    ) -> ObjectId:
        method_class_id = self.write_reachability_object_class(f"method/{obj.name}")
        return self.write_reachability_instance(
            method_class_id, obj, succs, all_nodes, obj_id
        )

    def write_class(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        class_class_id = self.write_reachability_object_class(f"class/{obj.name}")
        return self.write_reachability_instance(
            class_class_id, obj, succs, all_nodes, obj_id
        )

    def write_field(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        field_class_id = self.write_reachability_object_class(f"field/{obj.name}")
        return self.write_reachability_instance(
            field_class_id, obj, succs, all_nodes, obj_id
        )

    def write_anno(
        self,
        obj: ReachableObject,
        succs: List[ObjectId],
        all_nodes: Mapping[ReachableObject, ObjectId],
        obj_id: Optional[ObjectId] = None,
    ) -> ObjectId:
        anno_class_id = self.write_reachability_object_class(f"anno/{obj.name}")
        return self.write_reachability_instance(
            anno_class_id, obj, succs, all_nodes, obj_id
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="""A tool to translate a grpah generated by Redex's Reachability service to an HPROF file.
It only supports ReachabilityGraph for now.""",
        formatter_class=argparse.RawTextHelpFormatter,
    )
    parser.add_argument(
        "input", help="Input file generated by Reachability.dump_graph()."
    )
    parser.add_argument("output", help="The hprof file that should be generated.")

    parser.add_argument("--split-fields", action="store_true")
    parser.add_argument("--class-each", action="store_true")

    return parser.parse_args()


def main() -> None:
    args = parse_args()
    graph = ReachabilityGraph()

    logging.info(
        "Loading graph from %s. This might take a couple of minutes...", args.input
    )
    graph.load(args.input)

    logging.info("Creating HPROF representation...")

    hprof = Hprof()

    rhprof_type = (
        ReachabilityHprofOneClassPerEntity
        if args.class_each
        else ReachabilityHprofOneClassEach
    )
    rhprof = rhprof_type(hprof, args.split_fields)
    rhprof.run(graph)

    hprof.finish()

    logging.info("Writing to %s...", args.output)

    with open(args.output, "wb") as f:
        f.write(hprof.to_bytes())


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    main()
