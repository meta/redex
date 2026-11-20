#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import os
import sqlite3

from .core import ReachabilityGraph, ReachableObjectType
from .dominator_tree import compute_dominator_stats, iter_dominator_rows


SCHEMA_VERSION = 2
DOMINATOR_TREE_VERSION = "1"
SOURCE_FORMAT = (
    f"Redex reachability graph binary v{ReachabilityGraph.expected_version()}"
)
DOMINATOR_ALGORITHM = "cooper-harvey-kennedy"
_BATCH_SIZE = 10000
EDGE_DIRECTION = (
    "Each edges row means retainer_id retains retained_id. "
    "The binary graph stores each retained target followed by its predecessor "
    "retainer IDs."
)

_SCHEMA_SQL = """
CREATE TABLE nodes(
  id INTEGER PRIMARY KEY,
  kind TEXT NOT NULL CHECK(kind IN ('ANNO', 'CLASS', 'FIELD', 'METHOD', 'SEED')),
  name TEXT NOT NULL
);
CREATE TABLE edges(
  retainer_id INTEGER NOT NULL,
  retained_id INTEGER NOT NULL,
  FOREIGN KEY(retainer_id) REFERENCES nodes(id),
  FOREIGN KEY(retained_id) REFERENCES nodes(id)
);
CREATE TABLE meta(
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
);
CREATE TABLE dom_stats(
  node_id INTEGER PRIMARY KEY,
  idom_id INTEGER,
  kind TEXT NOT NULL CHECK(kind IN ('ANNO', 'CLASS', 'FIELD', 'METHOD', 'SEED')),
  retained_count INTEGER NOT NULL CHECK(retained_count > 0),
  FOREIGN KEY(node_id) REFERENCES nodes(id),
  FOREIGN KEY(idom_id) REFERENCES nodes(id)
);
"""


def _remove_partial_output(output_filename):
    try:
        os.unlink(output_filename)
    except FileNotFoundError:
        pass


def _flush_batches(connection, node_rows, edge_rows):
    if node_rows:
        connection.executemany(
            "INSERT INTO nodes(id, kind, name) VALUES (?, ?, ?)", node_rows
        )
        node_rows.clear()
    if edge_rows:
        connection.executemany(
            "INSERT INTO edges(retainer_id, retained_id) VALUES (?, ?)", edge_rows
        )
        edge_rows.clear()


def export_graph(input_filename, output_filename):
    if os.path.exists(output_filename):
        raise FileExistsError("Output file already exists: %s" % output_filename)

    connection = None
    try:
        connection = sqlite3.connect(output_filename)
        connection.execute("PRAGMA foreign_keys = ON")
        connection.executescript(_SCHEMA_SQL)
        graph = ReachabilityGraph()
        with connection:
            connection.executemany(
                "INSERT INTO meta(key, value) VALUES (?, ?)",
                (
                    ("schema_version", str(SCHEMA_VERSION)),
                    ("source_graph", os.path.abspath(input_filename)),
                    ("source_format", SOURCE_FORMAT),
                    ("edge_direction", EDGE_DIRECTION),
                    ("dominator_tree_version", DOMINATOR_TREE_VERSION),
                    ("dominator_algorithm", DOMINATOR_ALGORITHM),
                ),
            )
            node_rows = []
            for node_id, node, _predecessor_ids in graph.iter_serialized_records(
                input_filename
            ):
                node_rows.append(
                    (
                        node_id,
                        ReachableObjectType.to_string(node.type),
                        node.name,
                    )
                )
                if len(node_rows) >= _BATCH_SIZE:
                    _flush_batches(connection, node_rows, [])
            _flush_batches(connection, node_rows, [])
            connection.execute("CREATE INDEX nodes_by_kind_name ON nodes(kind, name)")

            edge_rows = []
            for node_id, _, predecessor_ids in graph.iter_serialized_records(
                input_filename
            ):
                edge_rows.extend(
                    (predecessor_id, node_id) for predecessor_id in predecessor_ids
                )
                if len(edge_rows) >= _BATCH_SIZE:
                    _flush_batches(connection, [], edge_rows)
            _flush_batches(connection, [], edge_rows)

            connection.execute("CREATE INDEX edges_by_retainer ON edges(retainer_id)")
            connection.execute("CREATE INDEX edges_by_retained ON edges(retained_id)")
            connection.executemany(
                "INSERT INTO dom_stats(node_id, idom_id, kind, retained_count) "
                "VALUES (?, ?, ?, ?)",
                iter_dominator_rows(
                    *compute_dominator_stats(connection, graph, input_filename)
                ),
            )
            connection.execute("CREATE INDEX dom_stats_by_idom ON dom_stats(idom_id)")
            connection.execute(
                "CREATE INDEX dom_stats_by_retained_count "
                "ON dom_stats(retained_count DESC, node_id)"
            )
            connection.execute(
                "CREATE INDEX dom_stats_by_kind_retained_count "
                "ON dom_stats(kind, retained_count DESC, node_id)"
            )
            connection.execute("PRAGMA user_version = %d" % SCHEMA_VERSION)
    except (OSError, ValueError, sqlite3.Error):
        if connection is not None:
            connection.close()
        _remove_partial_output(output_filename)
        raise
    else:
        connection.close()
