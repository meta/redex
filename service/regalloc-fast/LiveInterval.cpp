/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LiveInterval.h"

#include "Debug.h"
namespace fastregalloc {

LiveIntervals init_live_intervals(
    cfg::ControlFlowGraph& cfg,
    std::vector<LiveIntervalPoint>* live_interval_points) {
  LiveIntervals live_intervals;
  VRegAliveInsns vreg_alive_insns;
  auto add_live_range = [&vreg_alive_insns](const auto& vreg_block_range) {
    for (auto& [vreg, range] : UnorderedIterable(vreg_block_range)) {
      vreg_alive_insns[vreg].push_back(range);
    }
  };

  LivenessFixpointIterator liveness_fixpoint_iter(cfg);
  liveness_fixpoint_iter.run({});
  UnorderedMap<cfg::Block*, UnorderedSet<vreg_t>>
      check_cast_throw_targets_vregs;
  for (cfg::Block* block : cfg.blocks()) {
    add_live_range(get_live_range_in_block(
        liveness_fixpoint_iter, block, &check_cast_throw_targets_vregs));
  }
  for (auto& [block, vregs] :
       UnorderedIterable(check_cast_throw_targets_vregs)) {
    add_live_range(get_check_cast_throw_targets_live_range(
        liveness_fixpoint_iter, block, vregs));
  }

  // number the instructions to get sortable live intervals
  LiveIntervalPointIndices indices;
  auto add_lip = [&indices, live_interval_points](const auto& lip) {
    auto success = indices.emplace(lip, indices.size()).second;
    always_assert(success);
    live_interval_points->push_back(lip);
  };
  auto ordered_blocks = get_ordered_blocks(cfg, liveness_fixpoint_iter);
  for (auto* block : ordered_blocks) {
    for (auto& mie : InstructionIterable(block)) {
      add_lip(LiveIntervalPoint::get(mie.insn));
    }
    if (cfg.get_succ_edge_if(block, [](cfg::Edge* e) {
          return e->type() != cfg::EDGE_GHOST;
        }) != nullptr) {
      // Any block with continuing control-flow could have a live-out registers,
      // and thus we allocate a block-end point for it.
      add_lip(LiveIntervalPoint::get_block_end(block));
    }
  }

  for (const auto& [vreg, ranges] : UnorderedIterable(vreg_alive_insns)) {
    auto [start_point, end_point] = calculate_live_interval(ranges, indices);
    live_intervals.push_back(VRegLiveInterval{start_point, end_point, vreg});
  }
  std::sort(live_intervals.begin(), live_intervals.end());

  return live_intervals;
}

IntervalEndPoints calculate_live_interval(
    const std::vector<RangeInBlock>& ranges,
    const LiveIntervalPointIndices& indices) {
  always_assert(!indices.empty());
  uint32_t max_index = static_cast<uint32_t>(indices.size() - 1);
  uint32_t interval_start = max_index;
  uint32_t interval_end = 0;
  for (const auto& range : ranges) {
    always_assert(!range.first.is_missing());
    auto range_start = indices.at(range.first);
    interval_start = std::min(interval_start, range_start);
    // if there is deadcode (def no use), we assume the live interval lasts
    // until end of code
    if (range.second.is_missing()) {
      interval_end = max_index;
    } else {
      auto range_end = indices.at(range.second);
      interval_end = std::max(interval_end, range_end);
    }
  }
  redex_assert(interval_start <= interval_end);
  return std::make_pair(interval_start, interval_end);
}

VRegAliveRangeInBlock get_live_range_in_block(
    const LivenessFixpointIterator& fixpoint_iter,
    cfg::Block* block,
    UnorderedMap<cfg::Block*, UnorderedSet<vreg_t>>*
        check_cast_throw_targets_vregs) {
  VRegAliveRangeInBlock vreg_block_range;
  const LivenessDomain& live_in = fixpoint_iter.get_live_in_vars_at(block);
  const LivenessDomain& live_out = fixpoint_iter.get_live_out_vars_at(block);

  LiveIntervalPoint first = LiveIntervalPoint::get_block_begin(block);
  for (auto vreg : live_in.elements()) {
    auto range = std::make_pair(first, LiveIntervalPoint::get());
    bool emplaced = vreg_block_range.emplace(vreg, range).second;
    always_assert(emplaced);
  }
  auto ii = InstructionIterable(block);
  for (auto it = ii.begin(); it != ii.end(); it++) {
    auto* insn = it->insn;
    if (!insn->has_dest()) {
      continue;
    }
    vreg_t vreg = insn->dest();
    auto next = std::next(it) == ii.end()
                    ? LiveIntervalPoint::get_block_end(block)
                    : LiveIntervalPoint::get(std::next(it)->insn);
    auto range = std::make_pair(next, LiveIntervalPoint::get());
    vreg_block_range.emplace(vreg, range);
    // emplace might silently fail if we already had an entry

    if (insn->opcode() != IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
      continue;
    }
    auto& cfg = block->cfg();
    auto primary_insn_it = cfg.primary_instruction_of_move_result(
        block->to_cfg_instruction_iterator(it.unwrap()));
    if (primary_insn_it->insn->opcode() != OPCODE_CHECK_CAST) {
      continue;
    }
    // We need to remember for all catch handlers which check-cast
    // move-result-pseudo-object dest registers should be kept alive to
    // deal with a special quirk of our check-cast instruction lowering.
    auto* src_block = primary_insn_it.block();
    for (auto* e : cfg.get_succ_edges_of_type(src_block, cfg::EDGE_THROW)) {
      (*check_cast_throw_targets_vregs)[e->target()].insert(vreg);
    }
  }

  LiveIntervalPoint last = LiveIntervalPoint::get_block_end(block);
  for (auto vreg : live_out.elements()) {
    vreg_block_range.at(vreg).second = last;
  }
  for (auto& mie : InstructionIterable(block).reversed()) {
    auto* insn = mie.insn;
    for (vreg_t vreg : insn->srcs()) {
      auto it2 = vreg_block_range.find(vreg);
      if (it2 != vreg_block_range.end() && it2->second.second.is_missing()) {
        it2->second.second = LiveIntervalPoint::get(insn);
      }
    }
  }

  return vreg_block_range;
}

VRegAliveRangeInBlock get_check_cast_throw_targets_live_range(
    const LivenessFixpointIterator& fixpoint_iter,
    cfg::Block* block,
    const UnorderedSet<vreg_t>& vregs) {
  VRegAliveRangeInBlock vreg_block_range;
  const LivenessDomain& live_in = fixpoint_iter.get_live_in_vars_at(block);
  const auto& elements = live_in.elements();
  for (auto vreg : UnorderedIterable(vregs)) {
    if (!elements.contains(vreg)) {
      LiveIntervalPoint first = LiveIntervalPoint::get_block_begin(block);
      auto range = std::make_pair(first, first);
      bool emplaced = vreg_block_range.emplace(vreg, range).second;
      always_assert(emplaced);
    }
  }
  return vreg_block_range;
}

std::vector<cfg::Block*> get_ordered_blocks(
    cfg::ControlFlowGraph& cfg,
    const LivenessFixpointIterator& liveness_fixpoint_iter) {
  // For each block, compute distance (in number of blocks) from exit-block.
  UnorderedMap<cfg::Block*, size_t> block_depths;
  std::queue<std::pair<cfg::Block*, size_t>> work_queue;
  work_queue.emplace(cfg.exit_block(), 1);
  while (!work_queue.empty()) {
    auto [block, depth] = work_queue.front();
    work_queue.pop();
    if (!block_depths.emplace(block, depth).second) {
      continue;
    }
    for (auto* e : block->preds()) {
      work_queue.emplace(e->src(), depth + 1);
    }
  }

  // Compute (maximum) depth (in number of blocks, from exit-block) of each
  // assigned register
  UnorderedMap<vreg_t, size_t> vreg_defs_depths;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      if (mie.insn->has_dest()) {
        auto& depth = vreg_defs_depths[mie.insn->dest()];
        depth = std::max(depth, block_depths.at(block));
      }
    }
  }

  // For each block, compute the maximum distance (in number of blocks, from
  // exit-block) over all live-in registers
  UnorderedMap<cfg::Block*, size_t> live_in_def_depths;
  for (cfg::Block* block : cfg.blocks()) {
    const auto& live_in = liveness_fixpoint_iter.get_live_in_vars_at(block);
    size_t depth = 0;
    for (auto vreg : live_in.elements()) {
      auto vreg_defs_depth = vreg_defs_depths.at(vreg);
      depth = std::max(depth, vreg_defs_depth);
    }
    live_in_def_depths.emplace(block, depth);
  }

  // Collect blocks by doing a post-order traversal, processing predecessors in
  // their live-in-def-depths order, smallest depths goes last
  // The traversal keeps its own stack, as its depth is bounded only by the
  // number of blocks.
  auto sorted_preds = [&live_in_def_depths](cfg::Block* block) {
    std::vector<cfg::Block*> pred_blocks;
    for (auto* e : block->preds()) {
      pred_blocks.push_back(e->src());
    }
    // We might have duplicates, but that's okay.
    std::sort(pred_blocks.begin(),
              pred_blocks.end(),
              [&live_in_def_depths](cfg::Block* a, cfg::Block* b) {
                auto a_depth = live_in_def_depths.at(a);
                auto b_depth = live_in_def_depths.at(b);
                if (a_depth != b_depth) {
                  return a_depth > b_depth;
                }
                return a->id() < b->id();
              });
    return pred_blocks;
  };

  struct Frame {
    cfg::Block* block;
    std::vector<cfg::Block*> preds;
    size_t next_pred{0};
  };
  UnorderedSet<cfg::Block*> visited;
  std::vector<cfg::Block*> ordered_blocks;
  std::vector<Frame> stack;
  auto start_visit = [&](cfg::Block* block) {
    if (visited.insert(block).second) {
      stack.push_back(Frame{block, sorted_preds(block)});
    }
  };
  start_visit(cfg.exit_block());
  while (!stack.empty()) {
    auto& frame = stack.back();
    if (frame.next_pred < frame.preds.size()) {
      // Copied out, since `start_visit` may reallocate `stack`.
      auto* pred = frame.preds[frame.next_pred++];
      start_visit(pred);
    } else {
      ordered_blocks.push_back(frame.block);
      stack.pop_back();
    }
  }
  always_assert(ordered_blocks.size() == cfg.num_blocks());
  return ordered_blocks;
}

} // namespace fastregalloc
