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

#include "Lazy.h"
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
    closures.push_back((Closure){reduced_block, std::move(reachable),
                                 std::move(srcs), target});
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
