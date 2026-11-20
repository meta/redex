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
 * Iterative depth-first postorder. In its reverse, every edge that is not a
 * back edge goes from an earlier node to a later one.
 */
template <class GraphInterface>
std::vector<typename GraphInterface::NodeId> postorder_sort(
    const typename GraphInterface::Graph& graph) {
  using NodeId = typename GraphInterface::NodeId;
  enum State { VISITING, VISITED };
  std::vector<NodeId> stack{GraphInterface::entry(graph)};
  UnorderedMap<NodeId, State> states;
  std::vector<NodeId> postorder;

  while (!stack.empty()) {
    auto curr = stack.back();
    auto [state_it, first_visit] = states.emplace(curr, VISITING);
    if (first_visit) {
      // Mark a node when the search enters it, not when it is pushed: a node
      // pushed by its parent may be entered first from a sibling explored
      // earlier, and must then finish before that sibling.
      for (auto const& s : GraphInterface::successors(graph, curr)) {
        const auto& target = GraphInterface::target(graph, s);
        if (!states.count(target)) {
          stack.push_back(target);
        }
      }
      continue;
    }
    stack.pop_back();
    if (state_it->second == VISITING) {
      state_it->second = VISITED;
      postorder.push_back(curr);
    }
    // Otherwise this is a further stack entry of a node already finished.
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
