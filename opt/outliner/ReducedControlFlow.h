/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "ControlFlow.h"
#include "DeterministicContainers.h"

namespace method_splitting_impl {

// Helper function that checks if a block is hit in any interaction.
bool is_hot(const cfg::Block* b);

enum class HotSplitKind {
  Hot,
  HotCold,
  Cold,
};

std::string_view describe(std::optional<HotSplitKind> kind);

struct ReducedBlock;

struct ReducedEdge {
  const ReducedBlock* src{nullptr};
  const ReducedBlock* target{nullptr};
  UnorderedSet<const cfg::Edge*> edges;
};

struct ReducedBlock {
  size_t id;
  UnorderedSet<const cfg::Block*> blocks;
  UnorderedSet<const ReducedEdge*> preds;
  UnorderedSet<const ReducedEdge*> succs;
  size_t code_size{0};
  bool is_hot{false};

  UnorderedBag<const cfg::Edge*> expand_preds(cfg::Block* src = nullptr) const;
};

// A control-flow-graph where all strongly-connected components have been
// collapsed. Thus, this "graph" is really a DAG.
class ReducedControlFlowGraph {
 public:
  explicit ReducedControlFlowGraph(cfg::ControlFlowGraph& cfg);

  std::vector<const ReducedBlock*> blocks() const;

  const ReducedBlock* entry_block() const;

  UnorderedSet<const ReducedBlock*> reachable(
      const ReducedBlock* head,
      const UnorderedSet<const ReducedEdge*>& except_edges = {}) const;

  ReducedBlock* get_reduced_block(const cfg::Block* block) const;

  size_t code_size() const { return m_code_size; }

 private:
  ReducedEdge* get_edge(ReducedBlock* src, ReducedBlock* target) {
    auto [it, _] =
        m_reduced_edges[src].emplace(target, ReducedEdge{src, target, {}});
    return &it->second;
  }
  cfg::ControlFlowGraph& m_cfg;
  std::vector<std::unique_ptr<ReducedBlock>> m_reduced_blocks;
  UnorderedMap<ReducedBlock*, UnorderedMap<ReducedBlock*, ReducedEdge>>
      m_reduced_edges;
  UnorderedMap<const cfg::Block*, ReducedBlock*> m_blocks;
  size_t m_code_size;
};

template <class ReducedBlockCollection>
size_t code_size(const ReducedBlockCollection& blocks) {
  return unordered_accumulate(blocks, size_t{0},
                              [](size_t acc, const ReducedBlock* block) {
                                return acc + block->code_size;
                              });
}

} // namespace method_splitting_impl
