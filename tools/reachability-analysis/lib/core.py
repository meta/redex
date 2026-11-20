#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import array
import mmap
import os
import shutil
import struct
import subprocess
import tempfile


class GraphFormatError(ValueError):
    pass


def _read_exact(mapping, size, description):
    data = mapping.read(size)
    if len(data) != size:
        raise GraphFormatError(
            "Truncated graph while reading %s: expected %d bytes, found %d"
            % (description, size, len(data))
        )
    return data


def _read_uint32(mapping, description):
    return struct.unpack("<L", _read_exact(mapping, 4, description))[0]


class ReachableObjectType(object):
    ANNO = 0
    CLASS = 1
    FIELD = 2
    METHOD = 3
    SEED = 4

    @staticmethod
    def to_string(v):
        if v == ReachableObjectType.ANNO:
            return "ANNO"
        if v == ReachableObjectType.CLASS:
            return "CLASS"
        if v == ReachableObjectType.FIELD:
            return "FIELD"
        if v == ReachableObjectType.METHOD:
            return "METHOD"
        if v == ReachableObjectType.SEED:
            return "SEED"


# Kinds whose name is shared by many objects: an annotation node is one
# annotation instance, named by its type, and a seed node is one keep reason.
# Each instance retains only what it names, so instances stay separate nodes.
INSTANCE_TYPES = frozenset((ReachableObjectType.ANNO, ReachableObjectType.SEED))


def instance_kind_names() -> frozenset[str]:
    """INSTANCE_TYPES as the SQL export names kinds."""
    return frozenset(ReachableObjectType.to_string(t) for t in INSTANCE_TYPES)


# A method name contains `(` and a field name contains `:`; a keep reason can
# contain either.


def is_method(node_name):
    return "(" in node_name


def is_field(node_name):
    return ":" in node_name and not is_method(node_name)


def is_seed(node_name):
    return node_name == "<SEED>"


def show_list_with_idx(list):
    ret = ""
    i = 0
    while i < len(list):
        ret += "%d: %s\n" % (i, list[i])
        i += 1

    return ret


def download_from_everstore(handle, filename):
    subprocess.check_call(["clowder", "get", handle, filename])


class ReachableObject(object):
    def __init__(self, type, name):
        self.type = type
        self.name = name
        self.preds = {}
        self.succs = {}

    def __str__(self):
        return "%s: %s\n" % (ReachableObjectType.to_string(self.type), self.name)

    def __repr__(self):
        ret = "%s: %s\n" % (ReachableObjectType.to_string(self.type), self.name)
        ret += "Reachable from %d predecessor(s):\n" % len(self.preds)
        ret += show_list_with_idx(list(self.preds.keys()))
        ret += "Reaching %d successor(s):\n" % len(self.succs)
        ret += show_list_with_idx(list(self.succs.keys()))
        return ret


class ReachableMethod(ReachableObject):
    # we need override info for a method
    def __init__(self, ro, mog):
        self.type = ro.type
        self.name = ro.name
        self.preds = ro.preds
        self.succs = ro.succs
        self.overriding = []
        self.overridden_by = []

        if self.name in list(mog.nodes.keys()):
            n = mog.nodes[self.name]
            self.overriding = n.parents
            self.overridden_by = n.children

    def __repr__(self):
        ret = super(ReachableMethod, self).__repr__()
        if len(self.overriding) != 0:
            ret += "Overriding %s methods:\n" % len(self.overriding)
            ret += show_list_with_idx(list([n.name for n in self.overriding]))

        if len(self.overridden_by) != 0:
            ret += "Overridden by %s methods:\n" % len(self.overridden_by)
            ret += show_list_with_idx(list([n.name for n in self.overridden_by]))
        return ret


class AbstractGraph(object):
    """
    This contains the deserialization counterpart to the graph serialization
    code in BinarySerialization.h.
    """

    def __init__(self):
        self.nodes = {}
        self.node_records = []

    def expected_version(self):
        raise NotImplementedError()

    def read_node(self, mapping):
        raise NotImplementedError()

    def add_node(self, node):
        raise NotImplementedError()

    def add_edge(self, n1, n2):
        raise NotImplementedError()

    def list_nodes(self, search_str=None):
        raise NotImplementedError()

    def read_header(self, mapping):
        magic = _read_uint32(mapping, "magic number")
        if magic != 0xFACEB000:
            raise GraphFormatError("Magic number mismatch")
        version = _read_uint32(mapping, "version")
        if version != self.expected_version():
            raise GraphFormatError(
                f"Unsupported graph format version {version}; this tool reads "
                f"version {self.expected_version()}. Regenerate the graph with "
                "a matching Redex."
            )

    def iter_serialized_records(self, fn):
        """Yield node IDs, nodes, and adjacency IDs without building the graph."""
        with open(fn, "rb") as f:
            if os.fstat(f.fileno()).st_size == 0:
                raise GraphFormatError(
                    "Truncated graph while reading magic number: "
                    "expected 4 bytes, found 0"
                )
            with mmap.mmap(f.fileno(), 0, prot=mmap.PROT_READ) as mapping:
                self.read_header(mapping)
                nodes_count = _read_uint32(mapping, "node count")
                for i in range(nodes_count):
                    node = self.read_node(mapping)
                    edges_size = _read_uint32(
                        mapping, "adjacency count for node %d" % i
                    )
                    adjacent_node_ids = array.array("I")
                    adjacent_node_ids.frombytes(
                        _read_exact(
                            mapping,
                            4 * edges_size,
                            "adjacency for node %d" % i,
                        )
                    )
                    for adjacent_node_id in adjacent_node_ids:
                        if adjacent_node_id >= nodes_count:
                            raise GraphFormatError(
                                "Invalid adjacent node ID %d for node %d"
                                % (adjacent_node_id, i)
                            )
                    yield i, node, adjacent_node_ids

    def load(self, fn):
        nodes = []
        out_edges = []
        for _, node, adjacent_node_ids in self.iter_serialized_records(fn):
            nodes.append(node)
            out_edges.append(adjacent_node_ids)
            self.add_node(node)

        for i, node in enumerate(nodes):
            for target in out_edges[i]:
                target_node = nodes[target]
                self.add_edge(node, target_node)

    def __repr__(self):
        sorted_keys = sorted(self.nodes.keys())
        return "[" + ",\n".join([self.nodes[k].__repr__() for k in sorted_keys]) + "]"


class ReachabilityGraph(AbstractGraph):
    @staticmethod
    def expected_version():
        # GRAPH_FORMAT_VERSION in libredex/Reachability.h.
        return 2

    def read_node(self, mapping):
        node_type = struct.unpack("<B", _read_exact(mapping, 1, "node type"))[0]
        if ReachableObjectType.to_string(node_type) is None:
            raise GraphFormatError("Unsupported reachability node type %d" % node_type)
        node_name_size = _read_uint32(mapping, "node name length")
        node_name = _read_exact(mapping, node_name_size, "node name").decode("ascii")
        return ReachableObject(node_type, node_name)

    def add_node(self, node):
        # `nodes` maps each (type, name) to all its nodes: one for a class,
        # field or method, one per instance of an annotation type or keep rule.
        self.node_records.append(node)
        self.nodes.setdefault((node.type, node.name), []).append(node)

    def __repr__(self):
        return (
            "["
            + ",\n".join(
                node.__repr__()
                for key in sorted(self.nodes.keys())
                for node in self.nodes[key]
            )
            + "]"
        )

    def dump(self, fn):
        nodes = sorted(self.node_records, key=lambda node: (node.type, node.name))
        if len(nodes) > 0xFFFFFFFF:
            raise ValueError("Too many nodes to serialize")

        node_ids = {node: node_id for node_id, node in enumerate(nodes)}
        if len(node_ids) != len(nodes):
            raise ValueError("A node was added to the graph more than once")

        with open(fn, "wb") as output:
            output.write(
                struct.pack("<LLL", 0xFACEB000, self.expected_version(), len(nodes))
            )
            for node in nodes:
                if not 0 <= node.type <= 0xFF:
                    raise ValueError(
                        f"Node type is outside the uint8 range: {node.type}"
                    )
                name = node.name.encode("ascii")
                if len(name) > 0xFFFFFFFF:
                    raise ValueError("Node name is too long to serialize")

                try:
                    predecessor_ids = sorted(node_ids[pred] for pred in node.preds)
                except KeyError as error:
                    raise ValueError(
                        f"Predecessor of {(node.type, node.name)} is not in the graph"
                    ) from error
                if len(predecessor_ids) > 0xFFFFFFFF:
                    raise ValueError("Too many predecessors to serialize")

                output.write(struct.pack("<BL", node.type, len(name)))
                output.write(name)
                output.write(struct.pack("<L", len(predecessor_ids)))
                if predecessor_ids:
                    output.write(
                        struct.pack(f"<{len(predecessor_ids)}L", *predecessor_ids)
                    )

    def list_nodes(self, search_str=None):
        for key in list(self.nodes.keys()):
            type = ReachableObjectType.to_string(key[0])
            name = key[1]
            if search_str is None or search_str in name:
                print(('(ReachableObjectType.%s, "%s")' % (type, name)))

    @staticmethod
    def add_edge(n1, n2):
        if n1 not in n2.succs:
            # We store the edges as a dictionary because lookup times are much
            # faster with dictionaries than with lists.
            # The value isn't important - a None would do
            n2.succs[n1] = None

        if n2 not in n1.preds:
            n1.preds[n2] = None

    def get_nodes(self, node_name):
        """Every node of the named method, field, class, annotation type or
        keep rule: several for an annotation type or keep rule with several
        instances. A name stored under several kinds, such as a class and an
        annotation type, resolves to the first of method, field, class,
        annotation type and keep rule."""
        for node_type in (
            ReachableObjectType.METHOD,
            ReachableObjectType.FIELD,
            ReachableObjectType.CLASS,
            ReachableObjectType.ANNO,
            ReachableObjectType.SEED,
        ):
            nodes = self.nodes.get((node_type, node_name))
            if nodes is not None:
                return nodes
        raise KeyError(node_name)

    def get_node(self, node_name):
        """The node of a name that has exactly one."""
        nodes = self.get_nodes(node_name)
        if len(nodes) != 1:
            raise ValueError(
                f"{len(nodes)} nodes are named {node_name!r}; use get_nodes"
            )
        return nodes[0]

    def get_anno(self, node_name):
        """Every instance of an annotation type. Raises KeyError for a name
        no annotation instance has, like `get_node`."""
        return self.nodes[(ReachableObjectType.ANNO, node_name)]

    def get_seed(self, node_name):
        """Every seed of a keep rule. Raises KeyError for a name no seed has,
        like `get_node`."""
        return self.nodes[(ReachableObjectType.SEED, node_name)]


class MethodOverrideGraph(AbstractGraph):
    class Node(object):
        def __init__(self, name):
            self.name = name
            self.parents = []
            self.children = []

    def __init__(self):
        super().__init__()

    @staticmethod
    def expected_version():
        return 1

    def read_node(self, mapping):
        node_name_size = _read_uint32(mapping, "node name length")
        node_name = _read_exact(mapping, node_name_size, "node name").decode("ascii")
        return self.Node(node_name)

    def add_node(self, node):
        self.node_records.append(node)
        self.nodes[node.name] = node

    def list_nodes(self, search_str=None):
        for key in list(self.nodes.keys()):
            if search_str is None or search_str in key:
                print(('"%s"' % key))

    @staticmethod
    # pyrefly: ignore [bad-override]
    def add_edge(method, child):
        method.children.append(child)
        child.parents.append(method)


class CombinedGraph(object):
    def __init__(self, reachability, method_override):
        self.reachability_graph = ReachabilityGraph()
        self.reachability_graph.load(reachability)
        self.method_override_graph = MethodOverrideGraph()
        self.method_override_graph.load(method_override)

        # extract information from the override graph
        for type, name in self.reachability_graph.nodes:
            if type == ReachableObjectType.METHOD:
                self.reachability_graph.nodes[(type, name)] = [
                    ReachableMethod(node, self.method_override_graph)
                    for node in self.reachability_graph.nodes[(type, name)]
                ]

        for method in list(self.method_override_graph.nodes.keys()):
            method_node = self.reachability_graph.get_node(method)
            for child in method_node.overridden_by:
                # find child in reachability graph, then build edge
                method_child = self.reachability_graph.get_node(child.name)
                for pred in method_node.preds:
                    if pred.type == ReachableObjectType.METHOD:
                        self.reachability_graph.add_edge(method_child, pred)

        self.nodes = self.reachability_graph.nodes

    @staticmethod
    def from_everstore(reachability, method_override):
        temp_dir = tempfile.mkdtemp()
        r_tmp = os.path.join(temp_dir, "redex-reachability.graph")
        download_from_everstore(reachability, r_tmp)
        mog_tmp = os.path.join(temp_dir, "redex-method-override.graph")
        download_from_everstore(method_override, mog_tmp)
        ret = CombinedGraph(r_tmp, mog_tmp)
        shutil.rmtree(temp_dir)
        return ret

    def node(self, search_str=None, search_type=None):
        """The nodes of the one matching (type, name), several for an
        annotation type or keep rule; or, when several names match, a function
        from a printed option's index to its nodes."""
        nodes = None
        known_names = []
        for type, name in list(self.nodes.keys()):
            if search_type is not None and type != search_type:
                # Classes and Annotations may have naming collisions
                # if that happens, use the search_type argument to filter
                continue
            if search_str is None or search_str in name:
                known_names += [(type, name)]

        if search_str is not None and len(known_names) == 1:
            # know exactly one
            nodes = self.nodes[known_names[0]]
        elif search_str is not None:
            # there could be names containing name of another node
            # in this case we prefer the only exact match
            exact_match = list(filter((lambda n: n[1] == search_str), known_names))
            if len(exact_match) == 1:
                nodes = self.nodes[exact_match[0]]

        # if after all we still can't get which one does the user want,
        # print all options
        if nodes is None:
            print(("Found %s matching names:" % len(known_names)))
            idx = 0
            for type, name in known_names:
                print(
                    (
                        '%d: (ReachableObjectType.%s, "%s")'
                        % (idx, ReachableObjectType.to_string(type), name)
                    )
                )
                idx += 1

            return lambda i: self.nodes[known_names[i]]

        return nodes
