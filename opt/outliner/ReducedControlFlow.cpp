/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReducedControlFlow.h"

#include <queue>

#include <sparta/WeakTopologicalOrdering.h>

#include "CppUtil.h"
#include "Debug.h"
#include "SourceBlocks.h"

namespace method_splitting_impl {

// Helper function that checks if a block is hit in any interaction.
bool is_hot(const cfg::Block* b) {
  const auto* sb = source_blocks::get_first_source_block(b);
  if (sb == nullptr) {
    return false;
  }

  bool is_hot = false;
  sb->foreach_val_early([&is_hot](const auto& val) {
    is_hot = (val && val->val > 0.0f);
    return is_hot;
  });

  return is_hot;
}

std::string_view describe(std::optional<HotSplitKind> kind) {
  if (kind == std::nullopt) {
    return "uninitialized";
  }
  switch (kind.value()) {
  case HotSplitKind::Hot:
    return "hot";
  case HotSplitKind::HotCold:
    return "hot_cold";
  case HotSplitKind::Cold:
    return "cold";
  default:
    not_reached();
  }
}

// The bag type is the point: no consumer of these edges depends on their order
// -- one takes an order-independent min, the other folds them into flags and a
// set -- and a `std::vector` here would only invite someone to assume the hash
// order it happens to arrive in is meaningful.
UnorderedBag<const cfg::Edge*> ReducedBlock::expand_preds(
    cfg::Block* src) const {
  UnorderedBag<const cfg::Edge*> res;
  for (const auto* reduced_edge : UnorderedIterable(preds)) {
    if (src == nullptr) {
      insert_unordered_iterable(res, reduced_edge->edges);
      continue;
    }
    unordered_for_each(reduced_edge->edges, [src, &res](const cfg::Edge* e) {
      if (e->src() == src) {
        res.insert(e);
      }
    });
  }
  return res;
}

ReducedControlFlowGraph::ReducedControlFlowGraph(cfg::ControlFlowGraph& cfg)
    : m_cfg(cfg) {
  cfg.calculate_exit_block();
  sparta::WeakTopologicalOrdering<cfg::Block*> wto(
      cfg.entry_block(), [](cfg::Block* block) {
        std::vector<cfg::Block*> blocks;
        UnorderedSet<cfg::Block*> set;
        for (auto* edge : block->succs()) {
          if (edge->target() != block && set.insert(edge->target()).second) {
            blocks.emplace_back(edge->target());
          }
        }
        return blocks;
      });
  for (const auto& v : wto) {
    auto reduced_block = std::make_unique<ReducedBlock>();
    self_recursive_fn(
        [&blocks = reduced_block->blocks](const auto& self, const auto& w) {
          blocks.insert(w.head_node());
          if (!w.is_scc()) {
            return;
          }
          for (const auto& inner : w) {
            self(self, inner);
          }
        },
        v);
    reduced_block->id = m_reduced_blocks.size();
    for (const auto* b : UnorderedIterable(reduced_block->blocks)) {
      auto [it, emplaced] = m_blocks.emplace(b, reduced_block.get());
      always_assert(emplaced);
    }
    m_reduced_blocks.push_back(std::move(reduced_block));
  }

  for (auto& reduced_block : m_reduced_blocks) {
    auto& blocks = reduced_block->blocks;
    for (const auto* b : UnorderedIterable(blocks)) {
      for (auto* e : b->succs()) {
        if ((e->target() != nullptr) && !blocks.contains(e->target())) {
          auto* reduced_edge =
              get_edge(reduced_block.get(), get_reduced_block(e->target()));
          reduced_block->succs.insert(reduced_edge);
          reduced_edge->edges.insert(e);
        }
      }
      for (auto* e : b->preds()) {
        if ((e->src() != nullptr) && !blocks.contains(e->src())) {
          auto* reduced_edge =
              get_edge(get_reduced_block(e->src()), reduced_block.get());
          reduced_block->preds.insert(reduced_edge);
          reduced_edge->edges.insert(e);
        }
      }
      reduced_block->code_size += b->estimate_code_units();
      if (is_hot(b)) {
        reduced_block->is_hot = true;
      }
    }
  }

  m_code_size = method_splitting_impl::code_size(blocks());
}

std::vector<const ReducedBlock*> ReducedControlFlowGraph::blocks() const {
  std::vector<const ReducedBlock*> res;
  res.reserve(m_reduced_blocks.size());
  for (const auto& reduced_block : m_reduced_blocks) {
    res.push_back(reduced_block.get());
  }
  return res;
}

const ReducedBlock* ReducedControlFlowGraph::entry_block() const {
  always_assert(m_blocks.count(m_cfg.entry_block()));
  return m_blocks.at(m_cfg.entry_block());
}

UnorderedSet<const ReducedBlock*> ReducedControlFlowGraph::reachable(
    const ReducedBlock* head,
    const UnorderedSet<const ReducedEdge*>& except_edges) const {
  UnorderedSet<const ReducedBlock*> set;
  std::queue<const ReducedBlock*> work_queue;
  work_queue.push(head);
  while (!work_queue.empty()) {
    const auto* reduced_block = work_queue.front();
    work_queue.pop();
    if (set.insert(reduced_block).second) {
      for (const auto* e : UnorderedIterable(reduced_block->succs)) {
        if (except_edges.count(e) == 0u) {
          work_queue.push(e->target);
        }
      }
    }
  }
  return set;
}

ReducedBlock* ReducedControlFlowGraph::get_reduced_block(
    const cfg::Block* block) const {
  return m_blocks.at(block);
}

} // namespace method_splitting_impl
