/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <iterator>
#include <vector>

#include "Debug.h"
#include "DeterministicContainers.h"

namespace graph {

/*
 * Iterative implementation of a postorder sort.
 */
template <class GraphInterface>
std::vector<typename GraphInterface::NodeId> postorder_sort(
    const typename GraphInterface::Graph& graph) {
  using NodeId = typename GraphInterface::NodeId;
  enum State { UNVISITED, VISITING, VISITED };
  NodeId entry = GraphInterface::entry(graph);
  std::vector<NodeId> stack{entry};
  UnorderedMap<NodeId, State> states{{entry, UNVISITED}};
  std::vector<NodeId> postorder;

  while (!stack.empty()) {
    const auto& curr = stack.back();
    auto state_it = states.find(curr);
    always_assert(state_it != states.end());
    switch (state_it->second) {
    case UNVISITED: {
      state_it->second = VISITING;
      for (auto const& s : GraphInterface::successors(graph, curr)) {
        const auto& target = GraphInterface::target(graph, s);
        if (!states.count(target)) {
          states[target] = UNVISITED;
          stack.push_back(target);
        }
      }
      break;
    }
    case VISITING: {
      state_it->second = VISITED;
      postorder.push_back(curr);
      stack.pop_back();
      break;
    }
    case VISITED: {
      not_reached();
    }
    }
  }

  return postorder;
}

/*
 * Iterative depth-first preorder from the entry: each node comes before
 * everything first reached through it, and successors are visited in the order
 * GraphInterface::successors returns them.
 */
template <class GraphInterface>
std::vector<typename GraphInterface::NodeId> preorder_sort(
    const typename GraphInterface::Graph& graph) {
  using NodeId = typename GraphInterface::NodeId;
  std::vector<NodeId> stack{GraphInterface::entry(graph)};
  UnorderedSet<NodeId> visited;
  std::vector<NodeId> preorder;

  while (!stack.empty()) {
    NodeId curr = stack.back();
    stack.pop_back();
    if (!visited.insert(curr).second) {
      continue;
    }
    preorder.push_back(curr);
    // Push in reverse, so that the first successor is popped first.
    const auto& succs = GraphInterface::successors(graph, curr);
    for (auto it = std::make_reverse_iterator(succs.end());
         it != std::make_reverse_iterator(succs.begin());
         ++it) {
      const auto& target = GraphInterface::target(graph, *it);
      if (!visited.contains(target)) {
        stack.push_back(target);
      }
    }
  }

  return preorder;
}

} // namespace graph
