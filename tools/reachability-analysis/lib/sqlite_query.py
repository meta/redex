#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

import sqlite3
from collections.abc import Iterator
from pathlib import Path

from .sqlite_export import (
    DOMINATOR_ALGORITHM,
    DOMINATOR_TREE_VERSION,
    EDGE_DIRECTION,
    SCHEMA_VERSION,
    SOURCE_FORMAT,
)


KINDS = ("ANNO", "CLASS", "FIELD", "METHOD", "SEED")


def _validate_database(connection: sqlite3.Connection) -> None:
    version = connection.execute("PRAGMA user_version").fetchone()[0]
    if version != SCHEMA_VERSION:
        raise ValueError(
            "Unsupported reachability SQLite schema version "
            f"{version}; expected {SCHEMA_VERSION}"
        )

    metadata = dict(
        connection.execute(
            "SELECT key, value FROM meta "
            "WHERE key IN ('dominator_algorithm', 'dominator_tree_version', "
            "'edge_direction', 'source_format')"
        )
    )
    expected = {
        "dominator_algorithm": DOMINATOR_ALGORITHM,
        "dominator_tree_version": DOMINATOR_TREE_VERSION,
        "edge_direction": EDGE_DIRECTION,
        "source_format": SOURCE_FORMAT,
    }
    for key, value in expected.items():
        if metadata.get(key) != value:
            raise ValueError(f"Invalid reachability SQLite metadata: {key}")


def open_database(filename: str) -> sqlite3.Connection:
    uri = f"{Path(filename).resolve().as_uri()}?mode=ro"
    connection = sqlite3.connect(uri, uri=True)
    connection.row_factory = sqlite3.Row
    try:
        _validate_database(connection)
    except (sqlite3.Error, ValueError):
        connection.close()
        raise
    return connection


def _rows(cursor: sqlite3.Cursor) -> Iterator[dict[str, object]]:
    for row in cursor:
        yield dict(row)


def roots(
    connection: sqlite3.Connection,
    kind: str | None,
    limit: int | None,
) -> Iterator[dict[str, object]]:
    cursor = connection.execute(
        """
        WITH logical_nodes(kind, name) AS (
          SELECT DISTINCT kind, name FROM nodes
        )
        SELECT node.kind AS type, node.name AS name
        FROM logical_nodes AS node
        WHERE (:kind IS NULL OR node.kind = :kind)
          AND NOT EXISTS (
            SELECT 1
            FROM nodes AS raw
            JOIN edges AS edge INDEXED BY edges_by_retained
              ON edge.retained_id = raw.id
            WHERE raw.kind = node.kind AND raw.name = node.name
          )
        ORDER BY node.kind, node.name
        LIMIT :limit
        """,
        {
            "kind": kind,
            "limit": -1 if limit is None else limit,
        },
    )
    return _rows(cursor)


def semantic_roots(
    connection: sqlite3.Connection,
) -> Iterator[dict[str, object]]:
    cursor = connection.execute(
        """
        WITH logical_nodes(kind, name) AS (
          SELECT DISTINCT kind, name FROM nodes
        ),
        seed_roots(type, name, reason) AS (
          SELECT DISTINCT target.kind, target.name, seed.name
          FROM nodes AS target
          JOIN edges AS edge INDEXED BY edges_by_retained
            ON edge.retained_id = target.id
          JOIN nodes AS seed ON seed.id = edge.retainer_id
          WHERE target.kind IN ('CLASS', 'FIELD', 'METHOD')
            AND seed.kind = 'SEED'
        ),
        literal_roots(type, name, reason) AS (
          SELECT node.kind, node.name, ''
          FROM logical_nodes AS node
          WHERE node.kind IN ('CLASS', 'FIELD', 'METHOD')
            AND NOT EXISTS (
              SELECT 1
              FROM nodes AS raw
              JOIN edges AS edge INDEXED BY edges_by_retained
                ON edge.retained_id = raw.id
              WHERE raw.kind = node.kind AND raw.name = node.name
            )
        )
        SELECT type, name, reason FROM seed_roots
        UNION
        SELECT type, name, reason FROM literal_roots
        ORDER BY type, name, reason
        """
    )
    return _rows(cursor)


def resolve_node(
    connection: sqlite3.Connection,
    name: str,
    kind: str | None = None,
    kind_option: str = "--kind",
) -> tuple[str, str]:
    if kind is None:
        matches = connection.execute(
            """
            SELECT DISTINCT kind, name
            FROM nodes INDEXED BY nodes_by_kind_name
            WHERE kind IN ('ANNO', 'CLASS', 'FIELD', 'METHOD', 'SEED')
              AND name = ?
            ORDER BY kind
            """,
            (name,),
        ).fetchall()
    else:
        matches = connection.execute(
            "SELECT DISTINCT kind, name FROM nodes "
            "WHERE kind = ? AND name = ? ORDER BY kind",
            (kind, name),
        ).fetchall()
    if not matches:
        qualifier = f"{kind} " if kind is not None else ""
        raise ValueError(f"No {qualifier}node named {name!r}")
    if len(matches) > 1:
        kinds = ", ".join(row["kind"] for row in matches)
        raise ValueError(
            f"Ambiguous node named {name!r} ({kinds}); "
            f"use {kind_option} to select one"
        )
    return matches[0]["kind"], matches[0]["name"]


def _neighbors_in_direction(
    connection: sqlite3.Connection,
    node: tuple[str, str],
    direction: str,
) -> Iterator[dict[str, object]]:
    if direction == "retainer":
        join = "edge.retained_id = selected.id"
        neighbor_id = "edge.retainer_id"
        index = "edges_by_retained"
    else:
        join = "edge.retainer_id = selected.id"
        neighbor_id = "edge.retained_id"
        index = "edges_by_retainer"
    cursor = connection.execute(
        f"""
        SELECT DISTINCT :direction AS direction,
               neighbor.kind AS type,
               neighbor.name AS name
        FROM nodes AS selected
        JOIN edges AS edge INDEXED BY {index} ON {join}
        JOIN nodes AS neighbor ON neighbor.id = {neighbor_id}
        WHERE selected.kind = :kind AND selected.name = :name
        ORDER BY neighbor.kind, neighbor.name
        """,
        {
            "direction": direction,
            "kind": node[0],
            "name": node[1],
        },
    )
    return _rows(cursor)


def neighbors(
    connection: sqlite3.Connection,
    node: tuple[str, str],
    direction: str,
) -> Iterator[dict[str, object]]:
    if direction in ("retainers", "both"):
        yield from _neighbors_in_direction(connection, node, "retainer")
    if direction in ("retained", "both"):
        yield from _neighbors_in_direction(connection, node, "retained")


def _create_path_tables(connection: sqlite3.Connection) -> None:
    connection.executescript(
        """
        DROP TABLE IF EXISTS temp.path_seen;
        DROP TABLE IF EXISTS temp.path_frontier;
        DROP TABLE IF EXISTS temp.path_next;
        CREATE TEMP TABLE path_seen(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          parent_kind TEXT,
          parent_name TEXT,
          PRIMARY KEY(kind, name)
        ) WITHOUT ROWID;
        CREATE TEMP TABLE path_frontier(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          PRIMARY KEY(kind, name)
        ) WITHOUT ROWID;
        CREATE TEMP TABLE path_next(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          parent_kind TEXT NOT NULL,
          parent_name TEXT NOT NULL,
          PRIMARY KEY(kind, name)
        ) WITHOUT ROWID;
        """
    )


def _advance_path_frontier(
    connection: sqlite3.Connection,
    *,
    toward_retainers: bool,
) -> bool:
    if toward_retainers:
        edge_join = "edge.retained_id = current.id"
        neighbor_id = "edge.retainer_id"
        index = "edges_by_retained"
    else:
        edge_join = "edge.retainer_id = current.id"
        neighbor_id = "edge.retained_id"
        index = "edges_by_retainer"
    connection.execute("DELETE FROM path_next")
    connection.execute(
        f"""
        INSERT OR IGNORE INTO path_next(kind, name, parent_kind, parent_name)
        SELECT neighbor.kind, neighbor.name, current.kind, current.name
        FROM path_frontier AS frontier
        JOIN nodes AS current
          ON current.kind = frontier.kind AND current.name = frontier.name
        JOIN edges AS edge INDEXED BY {index} ON {edge_join}
        JOIN nodes AS neighbor ON neighbor.id = {neighbor_id}
        LEFT JOIN path_seen AS seen
          ON seen.kind = neighbor.kind AND seen.name = neighbor.name
        WHERE seen.kind IS NULL
        ORDER BY neighbor.kind, neighbor.name, current.kind, current.name
        """
    )
    has_next = connection.execute("SELECT EXISTS(SELECT 1 FROM path_next)").fetchone()[
        0
    ]
    connection.execute(
        """
        INSERT INTO path_seen(kind, name, parent_kind, parent_name)
        SELECT kind, name, parent_kind, parent_name FROM path_next
        """
    )
    connection.execute("DELETE FROM path_frontier")
    connection.execute(
        "INSERT INTO path_frontier(kind, name) SELECT kind, name FROM path_next"
    )
    return bool(has_next)


def _start_path_search(
    connection: sqlite3.Connection,
    start: tuple[str, str],
) -> None:
    _create_path_tables(connection)
    connection.execute(
        "INSERT INTO path_seen(kind, name) VALUES (?, ?)",
        start,
    )
    connection.execute(
        "INSERT INTO path_frontier(kind, name) VALUES (?, ?)",
        start,
    )


def _path_from_seen(
    connection: sqlite3.Connection,
    end: tuple[str, str],
) -> list[dict[str, object]]:
    path = []
    node: tuple[str, str] | None = end
    while node is not None:
        path.append(node)
        parent = connection.execute(
            "SELECT parent_kind, parent_name FROM path_seen "
            "WHERE kind = ? AND name = ?",
            node,
        ).fetchone()
        node = (
            None
            if parent["parent_kind"] is None
            else (parent["parent_kind"], parent["parent_name"])
        )
    path.reverse()
    return [
        {"status": "found", "step": step, "type": node[0], "name": node[1]}
        for step, node in enumerate(path)
    ]


def _path_frontier_root(
    connection: sqlite3.Connection,
) -> tuple[str, str] | None:
    row = connection.execute(
        """
        SELECT frontier.kind, frontier.name
        FROM path_frontier AS frontier
        WHERE NOT EXISTS (
          SELECT 1
          FROM nodes AS raw
          JOIN edges AS edge INDEXED BY edges_by_retained
            ON edge.retained_id = raw.id
          WHERE raw.kind = frontier.kind AND raw.name = frontier.name
        )
        ORDER BY frontier.kind, frontier.name
        LIMIT 1
        """
    ).fetchone()
    if row is None:
        return None
    return row["kind"], row["name"]


def shortest_path(
    connection: sqlite3.Connection,
    start: tuple[str, str],
    end: tuple[str, str],
) -> list[dict[str, object]] | None:
    _start_path_search(connection, start)
    while start != end:
        if not _advance_path_frontier(connection, toward_retainers=False):
            return None
        if connection.execute(
            "SELECT 1 FROM path_seen WHERE kind = ? AND name = ?",
            end,
        ).fetchone():
            break
    return _path_from_seen(connection, end)


def path_to_root(
    connection: sqlite3.Connection,
    start: tuple[str, str],
) -> list[dict[str, object]]:
    _start_path_search(connection, start)
    while True:
        root = _path_frontier_root(connection)
        if root is not None:
            return _path_from_seen(connection, root)
        if not _advance_path_frontier(connection, toward_retainers=True):
            raise ValueError(f"Node {start[1]!r} is not reachable from any root")


def _dom_stats(
    connection: sqlite3.Connection,
    node: tuple[str, str],
) -> sqlite3.Row:
    row = connection.execute(
        """
        SELECT stats.node_id, stats.retained_count
        FROM nodes AS selected INDEXED BY nodes_by_kind_name
        JOIN dom_stats AS stats ON stats.node_id = selected.id
        WHERE selected.kind = :kind AND selected.name = :name
        LIMIT 1
        """,
        {"kind": node[0], "name": node[1]},
    ).fetchone()
    if row is None:
        raise ValueError(f"Node {node[1]!r} is not reachable from any root")
    return row


def dominated(
    connection: sqlite3.Connection,
    blocked: tuple[str, str],
) -> Iterator[dict[str, object]]:
    node_id = _dom_stats(connection, blocked)["node_id"]
    cursor = connection.execute(
        """
        WITH RECURSIVE subtree(node_id) AS (
          VALUES(:node_id)
          UNION ALL
          SELECT child.node_id
          FROM subtree
          JOIN dom_stats AS child INDEXED BY dom_stats_by_idom
            ON child.idom_id = subtree.node_id
        )
        SELECT node.kind AS type, node.name AS name
        FROM subtree
        JOIN nodes AS node ON node.id = subtree.node_id
        ORDER BY node.kind, node.name
        """,
        {"node_id": node_id},
    )
    return _rows(cursor)


def retained_count(
    connection: sqlite3.Connection,
    blocked: tuple[str, str],
) -> dict[str, object]:
    stats = _dom_stats(connection, blocked)
    return {
        "type": blocked[0],
        "name": blocked[1],
        "retained_count": stats["retained_count"],
    }


def top_retained(
    connection: sqlite3.Connection,
    kind: str | None,
    limit: int,
) -> Iterator[dict[str, object]]:
    if kind is None:
        cursor = connection.execute(
            """
            SELECT node.kind AS type, node.name AS name, stats.retained_count
            FROM dom_stats AS stats INDEXED BY dom_stats_by_retained_count
            JOIN nodes AS node ON node.id = stats.node_id
            ORDER BY stats.retained_count DESC, node.kind, node.name
            LIMIT :limit
            """,
            {"limit": limit},
        )
    else:
        cursor = connection.execute(
            """
            SELECT node.kind AS type, node.name AS name, stats.retained_count
            FROM dom_stats AS stats INDEXED BY dom_stats_by_kind_retained_count
            JOIN nodes AS node ON node.id = stats.node_id
            WHERE stats.kind = :kind
            ORDER BY stats.retained_count DESC, node.name
            LIMIT :limit
            """,
            {"kind": kind, "limit": limit},
        )
    return _rows(cursor)


def dominators(
    connection: sqlite3.Connection,
    target: tuple[str, str],
) -> list[dict[str, object]]:
    """The target's chain in the materialized dominator tree, so `dominators`,
    `dominated`, `retained-count` and `top-retained` answer from one tree."""
    node_id = _dom_stats(connection, target)["node_id"]
    cursor = connection.execute(
        """
        WITH RECURSIVE chain(node_id, depth) AS (
          SELECT idom_id, 1 FROM dom_stats WHERE node_id = :node_id
          UNION ALL
          SELECT stats.idom_id, chain.depth + 1
          FROM chain
          JOIN dom_stats AS stats ON stats.node_id = chain.node_id
        )
        SELECT node.kind AS type, node.name AS name
        FROM chain
        JOIN nodes AS node ON node.id = chain.node_id
        ORDER BY chain.depth
        """,
        {"node_id": node_id},
    )
    return list(_rows(cursor))


def new_nodes(
    connection: sqlite3.Connection,
    kind: str | None,
) -> Iterator[dict[str, object]]:
    marker_exists = connection.execute(
        "SELECT 1 FROM nodes WHERE kind = 'ANNO' AND name = '<NEW>' LIMIT 1"
    ).fetchone()
    if marker_exists is None:
        raise ValueError("input is not a reachability-diff graph: no <NEW> marker")

    cursor = connection.execute(
        """
        SELECT DISTINCT node.kind AS type, node.name AS name
        FROM nodes AS marker
        JOIN edges AS edge INDEXED BY edges_by_retained
          ON edge.retained_id = marker.id
        JOIN nodes AS node ON node.id = edge.retainer_id
        WHERE marker.kind = 'ANNO' AND marker.name = '<NEW>'
          AND (:kind IS NULL OR node.kind = :kind)
        ORDER BY node.kind, node.name
        """,
        {"kind": kind},
    )
    return _rows(cursor)
