#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

import sqlite3
from collections.abc import Iterator
from pathlib import Path

from .core import instance_kind_names
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


def _instance_kinds_sql() -> str:
    return ", ".join(f"'{kind}'" for kind in sorted(instance_kind_names()))


def _create_path_tables(connection: sqlite3.Connection) -> None:
    # Each path step stands for one node: an annotation or seed instance is
    # keyed by its node ID, a class, field or method by its name, with
    # instance_id -1.
    connection.executescript(
        """
        DROP TABLE IF EXISTS temp.path_seen;
        DROP TABLE IF EXISTS temp.path_frontier;
        DROP TABLE IF EXISTS temp.path_next;
        CREATE TEMP TABLE path_seen(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          instance_id INTEGER NOT NULL,
          parent_kind TEXT,
          parent_name TEXT,
          parent_instance_id INTEGER,
          PRIMARY KEY(kind, name, instance_id)
        ) WITHOUT ROWID;
        CREATE TEMP TABLE path_frontier(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          instance_id INTEGER NOT NULL,
          PRIMARY KEY(kind, name, instance_id)
        ) WITHOUT ROWID;
        CREATE TEMP TABLE path_next(
          kind TEXT NOT NULL,
          name TEXT NOT NULL,
          instance_id INTEGER NOT NULL,
          parent_kind TEXT NOT NULL,
          parent_name TEXT NOT NULL,
          parent_instance_id INTEGER NOT NULL,
          PRIMARY KEY(kind, name, instance_id)
        ) WITHOUT ROWID;
        """
    )


def _path_instance_id(node: str) -> str:
    """The path step's instance_id of the nodes row aliased `node`."""
    return (
        f"CASE WHEN {node}.kind IN ({_instance_kinds_sql()}) "
        f"THEN {node}.id ELSE -1 END"
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
    neighbor_instance_id = _path_instance_id("neighbor")
    connection.execute("DELETE FROM path_next")
    connection.execute(
        f"""
        WITH current(id, kind, name, instance_id) AS (
          SELECT node.id, node.kind, node.name, -1
          FROM path_frontier AS frontier
          JOIN nodes AS node INDEXED BY nodes_by_kind_name
            ON node.kind = frontier.kind AND node.name = frontier.name
          WHERE frontier.instance_id = -1
          UNION ALL
          SELECT node.id, node.kind, node.name, node.id
          FROM path_frontier AS frontier
          JOIN nodes AS node ON node.id = frontier.instance_id
          WHERE frontier.instance_id != -1
        )
        INSERT OR IGNORE INTO path_next(
          kind, name, instance_id, parent_kind, parent_name, parent_instance_id
        )
        SELECT neighbor.kind, neighbor.name, {neighbor_instance_id},
               current.kind, current.name, current.instance_id
        FROM current
        JOIN edges AS edge INDEXED BY {index} ON {edge_join}
        JOIN nodes AS neighbor ON neighbor.id = {neighbor_id}
        LEFT JOIN path_seen AS seen
          ON seen.kind = neighbor.kind AND seen.name = neighbor.name
          AND seen.instance_id = {neighbor_instance_id}
        WHERE seen.kind IS NULL
        ORDER BY neighbor.kind, neighbor.name, {neighbor_instance_id},
                 current.kind, current.name, current.instance_id
        """
    )
    has_next = connection.execute("SELECT EXISTS(SELECT 1 FROM path_next)").fetchone()[
        0
    ]
    connection.execute(
        """
        INSERT INTO path_seen(
          kind, name, instance_id, parent_kind, parent_name, parent_instance_id
        )
        SELECT kind, name, instance_id, parent_kind, parent_name,
               parent_instance_id
        FROM path_next
        """
    )
    connection.execute("DELETE FROM path_frontier")
    connection.execute(
        "INSERT INTO path_frontier(kind, name, instance_id) "
        "SELECT kind, name, instance_id FROM path_next"
    )
    return bool(has_next)


def _start_path_search(
    connection: sqlite3.Connection,
    start: tuple[str, str],
) -> None:
    """Start from the named node, or from every instance of an annotation
    type or keep rule."""
    _create_path_tables(connection)
    start_instance_id = _path_instance_id("node")
    for table in ("path_seen", "path_frontier"):
        connection.execute(
            f"""
            INSERT OR IGNORE INTO {table}(kind, name, instance_id)
            SELECT node.kind, node.name, {start_instance_id}
            FROM nodes AS node INDEXED BY nodes_by_kind_name
            WHERE node.kind = ? AND node.name = ?
            """,
            start,
        )


def _path_from_seen(
    connection: sqlite3.Connection,
    end: tuple[str, str, int],
) -> list[dict[str, object]]:
    path = []
    node: tuple[str, str, int] | None = end
    while node is not None:
        path.append(node)
        parent = connection.execute(
            "SELECT parent_kind, parent_name, parent_instance_id FROM path_seen "
            "WHERE kind = ? AND name = ? AND instance_id = ?",
            node,
        ).fetchone()
        node = (
            None
            if parent["parent_kind"] is None
            else (
                parent["parent_kind"],
                parent["parent_name"],
                parent["parent_instance_id"],
            )
        )
    path.reverse()
    return [
        {"status": "found", "step": step, "type": node[0], "name": node[1]}
        for step, node in enumerate(path)
    ]


def _path_frontier_root(
    connection: sqlite3.Connection,
) -> tuple[str, str, int] | None:
    row = connection.execute(
        """
        SELECT frontier.kind, frontier.name, frontier.instance_id
        FROM path_frontier AS frontier
        WHERE CASE
          WHEN frontier.instance_id = -1 THEN NOT EXISTS (
            SELECT 1
            FROM nodes AS raw
            JOIN edges AS edge INDEXED BY edges_by_retained
              ON edge.retained_id = raw.id
            WHERE raw.kind = frontier.kind AND raw.name = frontier.name
          )
          ELSE NOT EXISTS (
            SELECT 1
            FROM edges AS edge INDEXED BY edges_by_retained
            WHERE edge.retained_id = frontier.instance_id
          )
        END
        ORDER BY frontier.kind, frontier.name, frontier.instance_id
        LIMIT 1
        """
    ).fetchone()
    if row is None:
        return None
    return row["kind"], row["name"], row["instance_id"]


def shortest_path(
    connection: sqlite3.Connection,
    start: tuple[str, str],
    end: tuple[str, str],
) -> list[dict[str, object]] | None:
    _start_path_search(connection, start)
    while True:
        # Of several reached instances of the end, follow the first.
        reached = connection.execute(
            "SELECT kind, name, instance_id FROM path_seen "
            "WHERE kind = ? AND name = ? ORDER BY instance_id LIMIT 1",
            end,
        ).fetchone()
        if reached is not None:
            return _path_from_seen(
                connection,
                (reached["kind"], reached["name"], reached["instance_id"]),
            )
        if not _advance_path_frontier(connection, toward_retainers=False):
            return None


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
    limit: int,
) -> list[sqlite3.Row]:
    """Up to `limit` dom_stats rows of a node: one for a class, field or
    method, one per instance for an annotation type or keep rule."""
    rows = connection.execute(
        """
        SELECT stats.node_id, stats.retained_count
        FROM nodes AS selected INDEXED BY nodes_by_kind_name
        JOIN dom_stats AS stats ON stats.node_id = selected.id
        WHERE selected.kind = :kind AND selected.name = :name
        LIMIT :limit
        """,
        {"kind": node[0], "name": node[1], "limit": limit},
    ).fetchall()
    if not rows:
        raise ValueError(f"Node {node[1]!r} is not reachable from any root")
    return rows


def _dominated_subtree(instances: int) -> str:
    """The dominator subtrees of every dom_stats row of (:kind, :name). With
    several instances they are deduplicated: an instance can lie in another
    instance's subtree."""
    union = "UNION" if instances > 1 else "UNION ALL"
    return f"""
        WITH RECURSIVE subtree(node_id) AS (
          SELECT stats.node_id
          FROM nodes AS selected INDEXED BY nodes_by_kind_name
          JOIN dom_stats AS stats ON stats.node_id = selected.id
          WHERE selected.kind = :kind AND selected.name = :name
          {union}
          SELECT child.node_id
          FROM subtree
          JOIN dom_stats AS child INDEXED BY dom_stats_by_idom
            ON child.idom_id = subtree.node_id
        )
        """


def dominated(
    connection: sqlite3.Connection,
    blocked: tuple[str, str],
) -> Iterator[dict[str, object]]:
    instances = len(_dom_stats(connection, blocked, 2))
    cursor = connection.execute(
        _dominated_subtree(instances)
        + """
        SELECT node.kind AS type, node.name AS name
        FROM subtree
        JOIN nodes AS node ON node.id = subtree.node_id
        ORDER BY node.kind, node.name
        """,
        {"kind": blocked[0], "name": blocked[1]},
    )
    return _rows(cursor)


def retained_count(
    connection: sqlite3.Connection,
    blocked: tuple[str, str],
) -> dict[str, object]:
    rows = _dom_stats(connection, blocked, 2)
    if len(rows) == 1:
        count = rows[0]["retained_count"]
    else:
        count = connection.execute(
            _dominated_subtree(len(rows)) + "SELECT COUNT(*) FROM subtree",
            {"kind": blocked[0], "name": blocked[1]},
        ).fetchone()[0]
    return {
        "type": blocked[0],
        "name": blocked[1],
        "retained_count": count,
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


def _dominator_chain(connection: sqlite3.Connection, node_id: int) -> list[sqlite3.Row]:
    """A node's proper dominators in the materialized dominator tree, nearest
    first."""
    return connection.execute(
        """
        WITH RECURSIVE chain(node_id, depth) AS (
          SELECT idom_id, 1 FROM dom_stats WHERE node_id = :node_id
          UNION ALL
          SELECT stats.idom_id, chain.depth + 1
          FROM chain
          JOIN dom_stats AS stats ON stats.node_id = chain.node_id
        )
        SELECT node.id AS id, node.kind AS type, node.name AS name
        FROM chain
        JOIN nodes AS node ON node.id = chain.node_id
        ORDER BY chain.depth
        """,
        {"node_id": node_id},
    ).fetchall()


def dominators(
    connection: sqlite3.Connection,
    target: tuple[str, str],
) -> list[dict[str, object]]:
    """The target's chain in the materialized dominator tree, so `dominators`,
    `dominated`, `retained-count` and `top-retained` answer from one tree. For an annotation
    type or keep rule with several instances, the nodes that dominate every
    instance."""
    # SQLite reads a negative LIMIT as no limit.
    instances = [row["node_id"] for row in _dom_stats(connection, target, -1)]
    first = _dominator_chain(connection, instances[0])
    common = {row["id"] for row in first}
    for node_id in instances[1:]:
        # An instance that is itself a root has an empty chain, and once the
        # intersection is empty no node dominates every instance.
        if not common:
            return []
        common &= {row["id"] for row in _dominator_chain(connection, node_id)}
    common.difference_update(instances)
    # One row per node of the chain: each annotation or seed instance is its own.
    return [
        {"type": row["type"], "name": row["name"]}
        for row in first
        if row["id"] in common
    ]


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
