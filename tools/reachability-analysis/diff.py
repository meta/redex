#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

import argparse
import logging
import sys
from collections.abc import Sequence

from lib.core import ReachabilityGraph
from lib.reachability_diff import build_diff_graph, newly_retained_keys

logger: logging.Logger = logging.getLogger(__name__)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Create a reachability graph containing newly retained nodes, "
            "their descendants, and rooted paths to them."
        )
    )
    parser.add_argument("--old", required=True, help="Baseline reachability graph")
    parser.add_argument("--new", required=True, help="New reachability graph")
    parser.add_argument(
        "-o", "--output", required=True, help="Output reachability graph"
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> None:
    args = parse_args(argv)
    old_graph = ReachabilityGraph()
    old_graph.load(args.old)
    new_graph = ReachabilityGraph()
    new_graph.load(args.new)

    new_node_count = len(newly_retained_keys(old_graph, new_graph))
    output_graph = build_diff_graph(old_graph, new_graph)
    output_graph.dump(args.output)
    logger.info(
        "Wrote %d newly retained nodes and %d total output nodes to %s",
        new_node_count,
        len(output_graph.node_records),
        args.output,
    )


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    main(sys.argv[1:])
