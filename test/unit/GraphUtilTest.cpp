/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "GraphUtil.h"

#include <gtest/gtest.h>

#include "SimpleGraph.h"

using namespace graph;

/*
 *  +-> 1 -+
 *  |      v
 *  0      3
 *  |      ^
 *  +-> 2 -+
 */
TEST(GraphUtilTest, postorder_diamond) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(2, 3);
  const auto& sorted = postorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({3, 2, 1, 0}));
}

/*
 *  +-> 1 -+
 *  |      v
 *  0 <--- 3
 *  |      ^
 *  +-> 2 -+
 */
TEST(GraphUtilTest, postorder_diamond_backedge) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(2, 3);
  graph.add_edge(3, 0);
  const auto& sorted = postorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({3, 2, 1, 0}));
}

/*
 *         +-> 3
 *  +-> 1 -|
 *  |      +-> 4
 *  0
 *  |
 *  +-> 2
 */
TEST(GraphUtilTest, postorder_tree) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(1, 4);
  const auto& sorted = postorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({2, 4, 3, 1, 0}));
}

/*
 *         +-> 3
 *  +-> 1 -|
 *  |      +-> 4
 *  0          |
 *  |          |
 *  +-> 2 <----+
 */
TEST(GraphUtilTest, postorder_tree_crossedge) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(1, 4);
  graph.add_edge(4, 2);
  const auto& sorted = postorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({2, 4, 3, 1, 0}));
}

/*
 *  +-> 1 -+
 *  |      v
 *  0      3
 *  |      ^
 *  +-> 2 -+
 */
TEST(GraphUtilTest, preorder_diamond) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(2, 3);
  const auto& sorted = preorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({0, 1, 3, 2}));
}

/*
 *  +-> 1 --+
 *  |       v
 *  0 ----> 3
 *  |
 *  +-> 2
 *
 * 3 is visited through 1, before 2, although 0 also leads to 3 directly.
 */
TEST(GraphUtilTest, preorder_descends_before_later_successors) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(0, 3);
  graph.add_edge(1, 3);
  const auto& sorted = preorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({0, 1, 3, 2}));
}

/*
 *  +-> 2
 *  |   ^
 *  0   |
 *  |   |
 *  +-> 1
 *
 * Successors are visited in the order they are listed: 2 before 1, even though
 * 1 also leads to 2.
 */
TEST(GraphUtilTest, preorder_follows_successor_order) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 2);
  graph.add_edge(0, 1);
  graph.add_edge(1, 2);
  const auto& sorted = preorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({0, 2, 1}));
}

/*
 *  +-> 1 -+
 *  |      v
 *  0 <--- 3
 *  |      ^
 *  +-> 2 -+
 */
TEST(GraphUtilTest, preorder_diamond_backedge) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(1, 3);
  graph.add_edge(2, 3);
  graph.add_edge(3, 0);
  const auto& sorted = preorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({0, 1, 3, 2}));
}

/*
 *  0 -> 1 -> 2
 *       ^    |
 *       +----+
 *
 * A node reached again later is not visited twice.
 */
TEST(GraphUtilTest, preorder_loop) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(1, 2);
  graph.add_edge(2, 1);
  const auto& sorted = preorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({0, 1, 2}));
}

/*
 *  +-> 1 <-+
 *  |       |
 *  0       |
 *  |       |
 *  +-> 2 --+
 *
 * The search reaches 1 through 2 as well, so 1 must be finished before 2;
 * otherwise the edge 2 -> 1 would point backwards in the reverse postorder
 * although the graph has no cycle.
 */
TEST(GraphUtilTest, postorder_reverse_is_topological) {
  GraphInterface::Graph graph;
  graph.add_edge(0, 1);
  graph.add_edge(0, 2);
  graph.add_edge(2, 1);
  const auto& sorted = postorder_sort<GraphInterface>(graph);
  EXPECT_EQ(sorted, std::vector<uint32_t>({1, 2, 0}));
}
