/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * MethodClosures discovers the splittable closures of a method: suffix
 * closures (the reachable set running to a return) and cold regions (SESE
 * hammocks embedded in hot methods). It builds the reduced CFG and runs the
 * dominator / post-dominator analysis that region detection relies on.
 */
#include "MethodClosures.h"

#include <algorithm>

#include "Debug.h"
#include "Lazy.h"
#include "Liveness.h"
#include "MethodSplittingStats.h"
#include "MethodUtil.h"
#include "MonitorCount.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"

namespace {

using namespace method_splitting_impl;

UnorderedSet<const ReducedBlock*> get_blocks_with_final_field_puts(
    DexMethod* method, const ReducedControlFlowGraph* rcfg) {
  if (!method::is_any_init(method)) {
    return {};
  }
  bool is_clinit = method::is_clinit(method);
  auto* type = method->get_class();
  auto has_unsplittable_insn = [&](const cfg::Block* block) {
    for (const auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (is_clinit && opcode::is_an_sput(insn->opcode())) {
        auto* f = resolve_field(insn->get_field(), FieldSearch::Static);
        if (f != nullptr && f->get_class() == type && is_final(f)) {
          return true;
        }
      }
      if (!is_clinit && opcode::is_an_iput(insn->opcode())) {
        auto* f = resolve_field(insn->get_field(), FieldSearch::Instance);
        if (f != nullptr && f->get_class() == type && is_final(f)) {
          return true;
        }
      }
    }
    return false;
  };
  UnorderedSet<const ReducedBlock*> res;
  for (const auto* reduced_block : rcfg->blocks()) {
    if (unordered_any_of(reduced_block->blocks, has_unsplittable_insn)) {
      res.insert(reduced_block);
    }
  }
  return res;
}

// Will the split block have a position before the first
// instruction, or do we need to insert one?
bool needs_pos(const IRList::iterator& begin, const IRList::iterator& end) {
  for (auto it = begin; it != end; it++) {
    switch (it->type) {
    case MFLOW_OPCODE: {
      auto op = it->insn->opcode();
      if (opcode::may_throw(op) || opcode::is_throw(op)) {
        return true;
      }
      continue;
    }
    case MFLOW_POSITION:
      return false;
    default:
      continue;
    }
  }
  return true;
}

void split_blocks(DexMethod* method,
                  cfg::ControlFlowGraph& cfg,
                  uint64_t split_block_size) {
  // TODO: Instead of "blindly" going by opcode count, instead nudge the split
  // points towards points with least live registers.
  for (auto* block : cfg.blocks()) {
    if (cfg.get_succ_edge_of_type(block, cfg::EDGE_THROW) != nullptr) {
      // don't bother
      continue;
    }
    auto ii = InstructionIterable(block);
    // We don't want to break up chains of load-param instructions, let's skip
    // over them.
    auto begin = ir_list::InstructionIterator(
        block->get_first_non_param_loading_insn(), block->end());
    if (begin == ii.end()) {
      // don't bother
      continue;
    }
    size_t count = 1;
    for (auto it = std::prev(ii.end()); it != begin; it--, count++) {
      if (count < split_block_size) {
        continue;
      }
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      if (it->insn->has_move_result_any() &&
          !cfg.move_result_of(cfg_it).is_end()) {
        continue;
      }
      auto* pos = cfg.get_dbg_pos(cfg_it);
      auto* split_block = cfg.split_block(cfg_it);
      if ((pos != nullptr) &&
          needs_pos(split_block->begin(), split_block->end())) {
        // Make sure new block gets proper position
        cfg.insert_before(split_block, split_block->begin(),
                          std::make_unique<DexPosition>(*pos));
      }
      auto* template_sb = source_blocks::get_first_source_block(block);
      if ((template_sb != nullptr) &&
          (source_blocks::get_first_source_block(split_block) == nullptr)) {
        auto new_sb = source_blocks::clone_as_synthetic(template_sb, method);
        auto split_it = split_block->get_first_insn();
        split_block->insert_before(split_it, std::move(new_sb));
      }
      count = 1;
    }
  }
}

} // namespace

namespace method_splitting_impl {

RegionMembers::RegionMembers(std::vector<cfg::Block*> blocks)
    : m_blocks(std::move(blocks)) {
  std::sort(m_blocks.begin(), m_blocks.end(), block_id_less);
  for (auto* b : m_blocks) {
    always_assert_log(m_ids.insert(b->id()).second, "block B%zu repeats",
                      (size_t)b->id());
  }
}

void normalize_cfg_for_splitting(DexMethod* method,
                                 std::optional<uint64_t> split_block_size) {
  auto* code = method->get_code();
  auto& cfg = code->cfg();
  // The loop below merges any return-only successor block into its sole
  // predecessor and deletes the successor's incoming edge. A rejoin block whose
  // only instruction is a `return` therefore does not survive: the return is
  // appended to the cold predecessor, whose branchingness becomes
  // BRANCH_RETURN, and cold-region discovery's non-return-entry filter then
  // rejects it without surfacing a useful error. A rejoin needs at least one
  // non-return instruction to survive this.
  bool changed;
  do {
    changed = false;
    for (auto* block : cfg.blocks()) {
      auto* goes_to_block = block->goes_to_only_edge();
      if (goes_to_block == nullptr) {
        continue;
      }
      auto first_insn_it = goes_to_block->get_first_insn();
      if (first_insn_it == goes_to_block->end()) {
        continue;
      }
      if (opcode::is_a_return(first_insn_it->insn->opcode())) {
        auto* last_existing_sb = source_blocks::get_last_source_block(block);
        auto it = goes_to_block->begin();
        while (true) {
          switch (it->type) {
          case MFLOW_OPCODE:
            block->push_back(new IRInstruction(*it->insn));
            break;
          case MFLOW_SOURCE_BLOCK: {
            auto sb_copy = std::make_unique<SourceBlock>(*it->src_block);
            if (last_existing_sb != nullptr) {
              source_blocks::normalize::normalize(
                  last_existing_sb, sb_copy.get(), sb_copy->vals_size);
            }
            block->insert_before(block->end(), std::move(sb_copy));
            break;
          }
          default:
            break;
          }
          if (it == first_insn_it) {
            break;
          }
          it++;
        }
        // TODO(T225634378) - When we improve our profiling data to include
        // proper hit counts, we need to gather the source blocks of
        // `goes_to_block` here and scale them down as well.
        cfg.delete_succ_edges(block);
        changed = true;
      }
    }
    cfg.remove_unreachable_blocks();
  } while (changed);
  if (split_block_size) {
    split_blocks(method, cfg, *split_block_size);
  }
}

std::shared_ptr<const ReducedControlFlowGraph> reduce_cfg(DexMethod* method) {
  auto& cfg = method->get_code()->cfg();
  // Precondition: the CFG has been normalized. An unnormalized CFG still has
  // return-only successors, and reducing over one yields a graph whose block
  // shapes disagree with what the splitter later sees -- wrong quietly, rather
  // than broken loudly. Cheap to check, so check it.
  for (auto* block : cfg.blocks()) {
    auto* goes_to = block->goes_to_only_edge();
    if (goes_to == nullptr) {
      continue;
    }
    auto first = goes_to->get_first_insn();
    always_assert_log(first == goes_to->end() ||
                          !opcode::is_a_return(first->insn->opcode()),
                      "reduce_cfg: CFG not normalized -- call "
                      "normalize_cfg_for_splitting first (%s)",
                      SHOW(method));
  }
  return std::make_shared<const ReducedControlFlowGraph>(cfg);
}

std::vector<Closure> SuffixStrategy::discover(
    DexMethod* method, const ReducedControlFlowGraph& rcfg) const {
  std::vector<Closure> closures;
  Lazy<monitor_count::Analyzer> mca([method] {
    return std::make_unique<monitor_count::Analyzer>(method->get_code()->cfg());
  });
  auto excluded_blocks = get_blocks_with_final_field_puts(method, &rcfg);
  for (const auto* reduced_block : rcfg.blocks()) {
    if (reduced_block == rcfg.entry_block()) {
      continue;
    }
    bool any_throw{false};
    bool any_non_zero_monitor_count{false};
    bool too_many_targets{false};
    UnorderedSet<cfg::Block*> srcs;
    cfg::Block* target{nullptr};
    auto expanded_preds = reduced_block->expand_preds();
    for (const auto* e : UnorderedIterable(expanded_preds)) {
      if (e->type() == cfg::EDGE_THROW) {
        any_throw = true;
        break;
      }
      const auto& count = mca->get_exit_state_at(e->src());
      if (count != sparta::ConstantAbstractDomain<uint32_t>(0)) {
        any_non_zero_monitor_count = true;
        break;
      }
      srcs.insert(e->src());
      if (target != nullptr && target != e->target()) {
        too_many_targets = true;
        break;
      }
      target = e->target();
    }
    if (any_throw || any_non_zero_monitor_count || too_many_targets) {
      continue;
    }
    if (target->starts_with_move_result() ||
        target->starts_with_move_exception()) {
      // TODO: Consider splitting the block?
      continue;
    }
    auto reachable = rcfg.reachable(reduced_block);
    if (unordered_any_of(excluded_blocks,
                         [&](auto* e) { return reachable.contains(e); })) {
      continue;
    }
    closures.push_back(Closure{
        .reduced_block = reduced_block,
        .reduced_components = std::move(reachable),
        .srcs = std::move(srcs),
        .target = target,
        .region = std::nullopt,
    });
  }
  return closures;
}

std::vector<Closure> RegionStrategy::discover(
    DexMethod* method, const ReducedControlFlowGraph& rcfg) const {
  std::vector<Closure> closures;
  auto& cfg = method->get_code()->cfg();
  // Liveness costs O(N) or more over the whole CFG. Most methods have no
  // eligible region, so it is built only once a candidate survives the cheap
  // filters below.
  Lazy<LivenessFixpointIterator> liveness([&cfg] {
    auto l = std::make_unique<LivenessFixpointIterator>(cfg);
    l->run({});
    return l;
  });
  Lazy<monitor_count::Analyzer> mca([method] {
    return std::make_unique<monitor_count::Analyzer>(method->get_code()->cfg());
  });
  auto excluded_blocks = get_blocks_with_final_field_puts(method, &rcfg);

  // Region heads: every cold node with a hot predecessor. Only these are
  // candidates: the call block that replaces the head and calls the split is
  // entered from a hot predecessor.
  for (const auto* reduced_block : rcfg.blocks()) {
    if (reduced_block == rcfg.entry_block() || reduced_block->is_hot) {
      continue;
    }
    const bool has_hot_pred =
        unordered_any_of(reduced_block->preds, [](const auto* pe) {
          return pe->src != nullptr && pe->src->is_hot;
        });
    if (!has_hot_pred) {
      continue;
    }
    // A node of several blocks is named by its lowest block id.
    auto* entry_block = const_cast<cfg::Block*>(
        *unordered_min_element(reduced_block->blocks, block_id_less));
    // The ghost exit holds no code; it is not a region head.
    if (reduced_block->blocks.size() == 1 &&
        is_ghost_exit_block(cfg, entry_block)) {
      continue;
    }
    m_stats.region_fates.candidates++;
    auto refuse = [&](CandidateFate fate) {
      m_stats.record(
          SplitKind::Region,
          [&] { return std::vector<cfg::BlockId>{entry_block->id()}; },
          std::nullopt, fate, reduced_block->code_size);
    };
    // Single-block regions only: a node of several blocks is a loop.
    if (reduced_block->blocks.size() != 1) {
      refuse(CandidateFate::Discovery_Cycle);
      continue;
    }
    // A block that ends in a return is a suffix, not a region.
    auto branch = entry_block->branchingness();
    if (branch == opcode::BRANCH_RETURN) {
      refuse(CandidateFate::Discovery_Return);
      continue;
    }
    // A block that ends in an `if` or a `switch` leaves by more than one edge,
    // and a region here leaves by one, to its continuation.
    if (branch == opcode::BRANCH_SWITCH || branch == opcode::BRANCH_IF) {
      refuse(CandidateFate::Discovery_Branch);
      continue;
    }
    // A block that starts with move-result-* / move-exception cannot
    // have its incoming edges redirected (the move-result pairs with
    // an invoke / throw on the predecessor side).
    if (entry_block->starts_with_move_result() ||
        entry_block->starts_with_move_exception()) {
      refuse(CandidateFate::Discovery_ResultReadingHead);
      continue;
    }
    // Not handled: a region on a try/catch boundary. A throw out of the region
    // leaves the host's handler reading pre-region values, since the region's
    // register writes happened in the split's frame. Regions that write nothing
    // a reachable handler reads would be fine; we don't compute that.
    auto is_throw = [](const cfg::Edge* e) {
      return e->type() == cfg::EDGE_THROW;
    };
    if (std::any_of(entry_block->preds().begin(), entry_block->preds().end(),
                    is_throw) ||
        std::any_of(entry_block->succs().begin(), entry_block->succs().end(),
                    is_throw)) {
      refuse(CandidateFate::Discovery_ThrowEdge);
      continue;
    }
    // Monitors. Extracting code from inside a monitor would split the monitor
    // across the invoke, so a block entered with a monitor held is refused. A
    // block that itself holds a `monitor-enter` or `monitor-exit` is refused
    // too: when the matching op stays outside the block, the split and the host
    // each hold an unbalanced monitor, which the verifier rejects. This is
    // conservative: it also refuses a self-contained synchronized block.
    auto expanded_preds = reduced_block->expand_preds();
    bool bad_monitor =
        unordered_any_of(expanded_preds, [&mca](const cfg::Edge* e) {
          return mca->get_exit_state_at(e->src()) !=
                 sparta::ConstantAbstractDomain<uint32_t>(0);
        });
    if (!bad_monitor) {
      for (const auto& mie : InstructionIterable(entry_block)) {
        auto op = mie.insn->opcode();
        if (op == OPCODE_MONITOR_ENTER || op == OPCODE_MONITOR_EXIT) {
          bad_monitor = true;
          break;
        }
      }
    }
    if (bad_monitor) {
      refuse(CandidateFate::Discovery_Monitor);
      continue;
    }
    if (excluded_blocks.contains(reduced_block)) {
      refuse(CandidateFate::Discovery_FinalFieldPut);
      continue;
    }
    // The continuation, where the host resumes, is where the block's goto
    // leads. The checks above leave the block no other way out: it ends in no
    // return, `if` or `switch`, and has no throw edge. A block that ends in an
    // uncaught `throw` has no goto, and one that jumps to itself has no
    // continuation either.
    cfg::Block* rejoin = entry_block->goes_to();
    if (rejoin == nullptr || rejoin == entry_block ||
        !can_be_region_boundary(rejoin)) {
      refuse(CandidateFate::Discovery_NoRejoin);
      continue;
    }
    redex_assert(entry_block->succs().size() == 1);
    // The region returns no value: no register the block defines may be live at
    // the continuation.
    auto live_at_rejoin = liveness->get_live_in_vars_at(rejoin);
    const auto& live_set = live_at_rejoin.elements();
    bool has_live_out = false;
    for (auto& mie : InstructionIterable(entry_block)) {
      auto* insn = mie.insn;
      // Liveness names a wide value by its LOW register only, so testing
      // `dest()` catches wide and narrow definitions alike.
      if (insn->has_dest() && live_set.contains(insn->dest())) {
        has_live_out = true;
        break;
      }
    }
    if (has_live_out) {
      refuse(CandidateFate::Discovery_TooManyLiveOuts);
      continue;
    }
    // Build the Closure with RegionInfo. `RegionMembers` keeps the blocks in
    // id order, so consumers iterate deterministically without re-sorting.
    UnorderedSet<cfg::Block*> srcs;
    for (const auto* pe : UnorderedIterable(reduced_block->preds)) {
      for (const auto* e : UnorderedIterable(pe->edges)) {
        if (e->src() != nullptr) {
          srcs.insert(e->src());
        }
      }
    }
    UnorderedSet<const ReducedBlock*> components;
    components.insert(reduced_block);
    closures.push_back(Closure{
        .reduced_block = reduced_block,
        .reduced_components = std::move(components),
        .srcs = std::move(srcs),
        .target = entry_block,
        .region =
            RegionInfo{
                .exits = SingleExit{.rejoin = rejoin},
                .members = RegionMembers({entry_block}),
            },
    });
  }
  return closures;
}

std::shared_ptr<MethodClosures> discover_closures(
    DexMethod* method, std::shared_ptr<const ReducedControlFlowGraph> rcfg) {
  SuffixStrategy strategy;
  auto closures = strategy.discover(method, *rcfg);
  if (closures.empty()) {
    return nullptr;
  }
  return std::make_shared<MethodClosures>((MethodClosures){
      method, rcfg->code_size(), std::move(rcfg), std::move(closures)});
}

} // namespace method_splitting_impl
