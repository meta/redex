/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BranchPrefixHoisting.h"
#include "PositionJoin.h"

#include <algorithm>
#include <optional>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "GraphUtil.h"
#include "RedexContext.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace {
// Record critical registers that will be clobbered by the hoisted insns.
void setup_side_effect_on_vregs(const IRInstruction* insn,
                                UnorderedMap<reg_t, bool>& vregs) {
  if (!insn->has_dest()) {
    // insn has no destination, can not have a side effect
    return; // we need to return here, otherwise dest() will throw
  }

  auto dest_reg = insn->dest();
  auto it = vregs.find(dest_reg);
  if (it != vregs.end()) {
    it->second = true;
  }
  if (insn->dest_is_wide()) {
    auto it2 = vregs.find(dest_reg + 1);
    if (it2 != vregs.end()) {
      it2->second = true;
    }
  }
}

// takes a list of iterators of the corresponding blocks, find if the
// instruction is common across different blocks at it + iterator_offset
IRInstruction* get_next_common_insn(
    const std::vector<IRList::iterator>& block_iters,
    const std::vector<cfg::Block*>& blocks,
    Lazy<const constant_uses::ConstantUses>& constant_uses) {
  always_assert(block_iters.size() == blocks.size());
  if (block_iters.empty()) {
    // the common of nothing is not defined
    return nullptr;
  }

  IRInstruction* representative_insn_opt = nullptr;

  for (size_t i = 0; i < block_iters.size(); i++) {
    const auto& it = block_iters[i];
    if (it == blocks[i]->end()) {
      return nullptr;
    }
    if (it->type != MFLOW_OPCODE) {
      return nullptr;
    }

    auto* insn = it->insn;
    if (representative_insn_opt == nullptr) {
      representative_insn_opt = insn;
    } else if (*representative_insn_opt != *insn) {
      return nullptr;
    }
  }
  always_assert(representative_insn_opt);

  auto op = representative_insn_opt->opcode();
  if (opcode::is_a_literal_const(op)) {
    // record the (const val) uses and make sure they are the same
    std::optional<constant_uses::TypeDemand> type_demand_opt;
    for (const auto& it : block_iters) {
      auto* insn = it->insn;
      // Make sure all the constant uses are of same type before hoisting.
      auto type_demand = constant_uses->get_constant_type_demand(insn);
      if (type_demand == constant_uses::TypeDemand::Error ||
          (type_demand_opt && *type_demand_opt != type_demand)) {
        return nullptr;
      }
      if (!type_demand_opt) {
        type_demand_opt = type_demand;
      }
    }
  }

  return representative_insn_opt;
}

bool is_block_eligible(IRInstruction* last_insn) {
  // only do the optimization in this pass for if and switches
  auto op = last_insn->opcode();
  return opcode::is_branch(op);
}

bool is_insn_eligible(const IRInstruction* insn) {
  auto op = insn->opcode();
  // In the case of instrumented builds, we cannot hoist
  // any instruction that may throw.
  // For example consider the following
  //                  SB1
  //                   |
  //                -------
  //               |       |
  //               SB2     SB3
  //               T1      T1
  //               SB4     SB5
  //               NT1     NT1
  //               ...     ...
  // If we were to hoist up to NT1, there is no way to arrange the sourceblocks
  // such that we could distinguish the difference one branch being hot and the
  // other cold
  //
  // For example, pulling/copying any source blocks up as in
  //                  SB1
  //                  SB2
  //                  SB3
  //                  T1
  //                  SB4
  //                  SB5
  //                  NT1
  //                   |
  //                -------
  //               |       |
  //               ...     ...
  // or
  //                  SB1
  //                  SB2
  //                  SB3
  //                   |
  //                -------
  //               |       |
  //               T1      T1
  //               SB4     SB5
  //               NT1     NT1
  //               ...     ...
  // Would completely eliminate being able to have profiling information
  // per-branch if the instruction throws.
  //
  // The other alternative of not copying source blocks at all
  //                  SB1
  //                  T1
  //                  NT1
  //                   |
  //                -------
  //               |       |
  //               SB2     SB3
  //               SB4     SB5
  //               ...     ...
  // Would lose the ability to tell if T1 throws or not.
  if (g_redex->instrument_mode && opcode::may_throw(op)) {
    return false;
  }
  return !opcode::is_branch(op) && !opcode::is_throw(op);
}

// Skip over MethodItemEntries that we "handle" in some way:
//  * POSITION, DEBUG: Remain in the block.
//  * SOURCE_BLOCK: Will get hoisted.
// Other types will block hoisting further instructions.
void skip_handled_method_item_entries(IRList::iterator& it,
                                      const IRList::iterator& end) {
  while (it != end &&
         (it->type == MFLOW_POSITION || it->type == MFLOW_DEBUG ||
          it->type == MFLOW_SOURCE_BLOCK || it->type == MFLOW_REMARK)) {
    it++;
  }
}

std::vector<IRInstruction> get_insns_to_hoist(
    const std::vector<cfg::Block*>& succ_blocks,
    Lazy<UnorderedMap<reg_t, bool>>& crit_regs,
    Lazy<const constant_uses::ConstantUses>& constant_uses) {
  // get iterators that points to the beginning of each block
  std::vector<IRList::iterator> block_iters;
  block_iters.reserve(succ_blocks.size());
  for (auto* succ_block : succ_blocks) {
    block_iters.push_back(succ_block->begin());
  }

  // The main while loop here looks for common prefix instructions in
  // succ_blocks. The instruction can be hoist if it doesn't have a side effect
  // on the registers that relate to the branch taking decisions
  bool proceed = true;
  std::vector<IRInstruction> insns_to_hoist;
  while (proceed) {
    // skip pos and debug info and check if at least one block reaches the end
    enum ItersState { kInconsistent, kAllAtEnd, kAllOngoing };
    auto skip_and_check_end = [&succ_blocks](auto& iters, size_t advance) {
      auto check_one = [advance](auto& it, const auto& end) {
        if (it == end) {
          return false;
        }
        for (size_t j = 0; j != advance; ++j) {
          ++it;
          if (it == end) {
            return false;
          }
        }
        skip_handled_method_item_entries(it, end);
        return static_cast<bool>(it != end);
      };

      size_t at_end = 0;
      for (size_t i = 0; i < iters.size(); i++) {
        if (!check_one(iters[i], succ_blocks[i]->end())) {
          ++at_end;
        }
      }
      return at_end == 0              ? kAllOngoing
             : at_end == iters.size() ? kAllAtEnd
                                      : kInconsistent;
    };

    if (skip_and_check_end(block_iters, /*advance=*/0) != kAllOngoing) {
      TRACE(BPH, 5, "At least one successor is at end");
      return insns_to_hoist;
    }

    auto* common_insn =
        get_next_common_insn(block_iters, succ_blocks, constant_uses);
    if (common_insn != nullptr) {
      TRACE(BPH, 5, "Next common instruction: %s", SHOW(common_insn));
    }

    if ((common_insn != nullptr) && is_insn_eligible(common_insn)) {
      if (common_insn->has_move_result_any()) {
        // need to check, for all succ blocks, the associated move-result must:
        // 1. be in the same block
        // 2. be identical
        // 3. have no side effect on crit_regs
        // otherwise, stop here and do not proceed
        auto copy = block_iters;
        auto iters_state = skip_and_check_end(copy, /*advance=*/1);
        switch (iters_state) {
        case kInconsistent:
          // TODO: If the existing continuitions are not move-results, and the
          // blocks at end do not have the move-result in their successors, we
          // can hoist, still (as there is no move-result, then).
          TRACE(BPH, 5, "Successors in inconsistent end state.");
          proceed = false;
          break;
        case kAllAtEnd:
          // TODO: If the successors of the successors do not contain
          // move-results, then we can still hoist (as there is no move-result,
          // then).
          TRACE(BPH, 5, "All successors at end.");
          proceed = false;
          break;
        case kAllOngoing: {
          IRInstruction* next_common_insn =
              get_next_common_insn(copy, succ_blocks, constant_uses);
          if (next_common_insn == nullptr) {
            TRACE(BPH, 5, "No common successor for move-result-any opcode.");
            proceed = false;
            break;
          }
          // This is OK, but should really only be done for a move-result.
          setup_side_effect_on_vregs(next_common_insn, *crit_regs);
        } break;
        }
      }

      setup_side_effect_on_vregs(common_insn, *crit_regs);
      if (proceed) {
        // all conditions satisfied
        insns_to_hoist.push_back(*common_insn);
        for (size_t i = 0; i != block_iters.size(); ++i) {
          redex_assert(block_iters[i] != CONSTP(succ_blocks[i])->end());
          redex_assert(block_iters[i]->type == MFLOW_OPCODE);
          redex_assert(*block_iters[i]->insn == *common_insn);
          ++block_iters[i];
        }
      }
    } else {
      // instructions at this position diverges among the successor blocks
      proceed = false;
    }
  }

  return insns_to_hoist;
}

// If critical registers are clobbered by hosited insns, make copy instructions
// and insert them into heap_insn_objs (which will be before hosisted insns). We
// also modify the critical insn to use the copied reg. RegAlloc will fix this
// and will try to remove the copy.
//
bool create_move_and_fix_clobbered(
    const IRList::iterator& pos,
    std::vector<IRInstruction*>& heap_insn_objs,
    cfg::Block* block,
    cfg::ControlFlowGraph& cfg,
    const UnorderedMap<reg_t, bool>& crit_regs,
    Lazy<const constant_uses::ConstantUses>& constant_uses,
    bool can_allocate_regs) {
  UnorderedMap<reg_t, reg_t> reg_map;
  auto it = block->to_cfg_instruction_iterator(pos);
  auto* cond_insn = it->insn;

  // Go over the critical regs and make a copy before hoisted insns.
  for (size_t i = 0; i < cond_insn->srcs_size(); i++) {
    auto reg = cond_insn->src(i);
    always_assert(!cond_insn->src_is_wide(i));
    auto it_reg = crit_regs.find(reg);
    if (it_reg != crit_regs.end() && it_reg->second) {
      if (!can_allocate_regs) {
        return false;
      }
      const auto& type_envs =
          constant_uses->get_type_inference()->get_type_environments();
      const auto& env = type_envs.at(cond_insn);
      auto type = env.get_type(reg);

      // If type_inference cannot infer type, give-up.
      if (type.is_top() || type.is_bottom()) {
        for (auto* insn_ptr : heap_insn_objs) {
          delete insn_ptr;
        }
        return false;
      }
      reg_t tmp_reg = cfg.allocate_temp();

      // Make a copy.
      IRInstruction* copy_insn;
      if (type.equals(type_inference::TypeDomain(IRType::REFERENCE))) {
        copy_insn = new IRInstruction(OPCODE_MOVE_OBJECT);
      } else {
        copy_insn = new IRInstruction(OPCODE_MOVE);
      }
      reg_map.emplace(reg, tmp_reg);
      copy_insn->set_dest(tmp_reg)->set_src(0, reg);
      heap_insn_objs.push_back(copy_insn);
    }
  }
  // if we have made copy_insns, insert them before hosited insns and change the
  // conditional insn to use the copied (un-clobbered) reg.
  for (size_t i = 0; i < it->insn->srcs_size(); i++) {
    auto reg = it->insn->src(i);
    auto reg_it = reg_map.find(reg);
    if (reg_it != reg_map.end()) {
      it->insn->set_src(i, reg_it->second);
    }
  }
  return true;
}

// This function is where the pass mutates the IR
size_t hoist_insns_for_block(
    cfg::Block* block,
    const IRList::iterator& pos,
    const std::vector<cfg::Block*>& succ_blocks,
    cfg::ControlFlowGraph& cfg,
    const std::vector<IRInstruction>& insns_to_hoist,
    const UnorderedMap<reg_t, bool>& crit_regs,
    Lazy<const constant_uses::ConstantUses>& constant_uses,
    bool can_allocate_regs,
    positions::JoinStats* join_stats) {
  auto insert_it = block->to_cfg_instruction_iterator(pos);

  {
    std::vector<IRInstruction*> heap_insn_objs;
    if (!create_move_and_fix_clobbered(pos, heap_insn_objs, block, cfg,
                                       crit_regs, constant_uses,
                                       can_allocate_regs)) {
      return 0;
    }

    // Make a copy of hoisted insns.
    cfg.insert_before(insert_it, heap_insn_objs);
  }

  // Hoist and delete instructions.

  auto succs = [&]() {
    UnorderedSet<cfg::Block*> succ_blocks_set{succ_blocks.begin(),
                                              succ_blocks.end()};
    std::vector<std::pair<cfg::Block*, IRList::iterator>> ret;
    ret.reserve(succ_blocks_set.size());
    unordered_transform(succ_blocks_set, std::back_inserter(ret),
                        [](auto* b) { return std::make_pair(b, b->begin()); });

    // Need to order in some way for stable insertion of source blocks.
    std::sort(ret.begin(), ret.end(), [](const auto& lhs, const auto& rhs) {
      return lhs.first->id() < rhs.first->id();
    });

    return ret;
  }();

  const bool any_throw = std::any_of(
      insns_to_hoist.begin(), insns_to_hoist.end(),
      [](const auto& insn) { return opcode::can_throw(insn.opcode()); });

  // The last position any successor carries locally; the hoisted copy clones
  // it. When no successor carries one, nothing is cloned and the hoisted code
  // stays under the branch's own position, which every successor inherited.
  const DexPosition* last_position = nullptr;
  // The position each successor is under, tracked separately from
  // `last_position`, which belongs to an arbitrary branch. Comparing them is
  // what says whether the branches actually disagreed about where this code
  // came from. A successor with no local position inherits the position
  // governing the branch itself.
  std::vector<const DexPosition*> succ_positions(succs.size(),
                                                 cfg.get_dbg_pos(insert_it));
  auto account = [join_stats](positions::FidelityChange change) {
    if (join_stats != nullptr) {
      join_stats->account(change);
    }
  };
  // The hoisted prefix needs at most one SourceBlock, not one per successor.
  bool hoisted_source_block_inserted = false;
  for (const auto& insn : insns_to_hoist) {
    // Check if any source blocks or positions precede instructions.
    if (!opcode::is_move_result_any(insn.opcode())) {
      for (size_t succ_idx = 0; succ_idx < succs.size(); ++succ_idx) {
        auto& p = succs[succ_idx];
        auto* b = p.first;
        auto& it = p.second;
        redex_assert(it != CONSTP(b)->end()); // Should have instructions.
        IRList::iterator next;
        for (; it != b->end(); it = next) {
          next = std::next(it);
          if (it->type == MFLOW_OPCODE) {
            break;
          }
          // Leave debug in the block.
          if (it->type == MFLOW_DEBUG) {
            continue;
          }
          // Hoist source blocks and clone positions.
          // TODO: Collapse equivalent source blocks?
          // TODO: Deal with duplication.
          switch (it->type) {
          case MFLOW_SOURCE_BLOCK:
            // The situation is complicated (besides not tracking control flow
            // correctly, being approximative), as inlining may have produced
            // straight code where avoiding that duplication is not obvious. For
            // example:
            //
            // SB1 - NT1 - T1 - SB2 - NT2 | T2 - SB3
            //
            // In this case, it would be best to leave SB2 in the block, as it
            // gives better information than SB3 (or may be necessary to have
            // any SB in the remaining block!).
            //
            // For simplicity, if any instruction to hoist throws, we *copy*
            // *all* source blocks we encounter. This will duplicate every SB,
            // but avoids complicated tracking of what to hoist, clone, or leave
            // alone. Duplication is not an issue for coverage profiling, but
            // for counting.
            // TODO: Revisit.
            //
            // If all hoisted instructions do not throw, just move the
            // instructions. It is safe to do so, as no "additional" control
            // flow is being introduced, such that the SBs in the old block will
            // give the precise information.
            //
            // In the case of instrumented builds, we do not hoist any
            // instructions that may throw. Thus, we shouldn't copy any source
            // blocks because they wouldn't correctly track the branching
            // behavior that ultimately happens. As long as none of the hoisted
            // instructions throw, we can be sure that one of the successor
            // blocks will be hit and the profiling will work correctly.
            if (any_throw && !g_redex->instrument_mode) {
              if (!g_redex->preserve_count_integrity) {
                cfg.insert_before(
                    insert_it, std::make_unique<SourceBlock>(*it->src_block));
              } else if (!hoisted_source_block_inserted) {
                // The hoisted instructions now live in this block, so they run
                // exactly as often as it does -- whatever the successors they
                // came from ran. Emit one SourceBlock carrying this block's own
                // count, rather than a verbatim copy of every successor's,
                // which left the prefix annotated N times over, each claiming
                // the whole of it.
                //
                // Same trigger as before: only when a successor actually had a
                // leading SourceBlock to hoist.
                auto* block_sb = source_blocks::get_last_source_block(block);
                if (block_sb != nullptr) {
                  cfg.insert_before(
                      insert_it, source_blocks::clone_as_synthetic(block_sb));
                } else {
                  // No count of our own to attribute the prefix to. Fall back
                  // to the verbatim copy rather than leaving the hoisted code
                  // with no SourceBlock at all: keeping the new control flow
                  // covered is the reason this copy exists, and a count that
                  // over-attributes beats no annotation.
                  cfg.insert_before(
                      insert_it, std::make_unique<SourceBlock>(*it->src_block));
                }
                // Set on BOTH paths: the fallback also annotates the prefix, so
                // leaving it unset would let the next successor's SourceBlock
                // re-enter and annotate a second time.
                hoisted_source_block_inserted = true;
              }
            }
            break;
          case MFLOW_POSITION:
            last_position = it->pos.get();
            // Fileless positions name no source site, so the successor keeps
            // the inherited branch position for comparison.
            if (it->pos->file != nullptr) {
              // `.at()`: sized from `succs` above and indexed by the loop over
              // `succs`, so this is in range by construction -- but the two are
              // separate containers, which no bounds checker can correlate.
              succ_positions.at(succ_idx) = it->pos.get();
            }
            break;
          case MFLOW_REMARK:
            // Block-anchored metadata; leave remarks in the block (not
            // hoisted).
            break;
          default:
            not_reached();
          }
        }
        redex_assert(it != CONSTP(b)->end());
      }
    }

    if (opcode::may_throw(insn.opcode()) && (last_position != nullptr)) {
      // We clone positions instead of moving, so that we don't move away
      // any initial positions from the sacrificial block. In case of
      // adjacent positions, the cfg will clean up obvious redundancy.
      auto hoisted_position = std::make_unique<DexPosition>(*last_position);
      // One copy of this instruction now runs for every branch it was hoisted
      // out of, but it can carry only one line. The clone records that its
      // retained line is no longer unique; original branch positions remain on
      // the code they still govern.
      //
      // Stats are optional; marking is not.
      const bool disagrees =
          std::any_of(succ_positions.begin(), succ_positions.end(),
                      [&hoisted_position](const DexPosition* succ_position) {
                        return !positions::same_source_claim(
                            hoisted_position.get(), succ_position);
                      });
      if (disagrees) {
        account(
            g_redex->get_position_pattern_switch_manager()->record_candidates(
                hoisted_position.get(), succ_positions));
      }
      cfg.insert_before(insert_it, std::move(hoisted_position));
    }

    // Insert instruction.
    cfg.insert_before(insert_it, new IRInstruction(insn));

    // Delete instruction from successors.
    if (opcode::is_move_result_any(insn.opcode())) {
      // move result pseudo gets removed along with its associating insn
      continue;
    }

    for (auto& p : succs) {
      auto* b = p.first;
      auto& it = p.second;
      redex_assert(it != CONSTP(b)->end());
      redex_assert(it->type == MFLOW_OPCODE);
      redex_assert(*it->insn == insn);

      // Deleting does not have a good API. Gymnastics here.
      std::optional<IRList::iterator> prev =
          it != b->begin() ? std::make_optional(std::prev(it)) : std::nullopt;
      b->remove_insn(it);
      if (prev) {
        it = std::next(*prev);
      } else {
        it = b->begin();
      }
    }
  }

  // Just a sanity check.
  for (const auto& p : succs) {
    const auto& end = p.second;
    for (auto it = p.first->begin(); it != end; ++it) {
      redex_assert(it->type == MFLOW_DEBUG || it->type == MFLOW_POSITION ||
                   it->type == MFLOW_SOURCE_BLOCK || it->type == MFLOW_REMARK);
    }
  }

  // For each succ block, we need to omit extraneous Source Blocks
  // For example, consider the following
  // SB1 - T1 | SB2 - NT1
  // It will be transformed into
  // SB1 - SB2 - NT1
  // If T1 throws, we will have created an impossible state because
  // we have a hot source block flowing into a cold source block
  // In order to fix this, we should change adjacent source blocks
  // and hoisted source blocks only separated from another source blocks by a
  // non-throwing instruction to have the values of the other source block.
  // In the case above, SB1 would have the value of SB2
  for (const auto& p : succs) {
    const auto& end = p.second;
    std::unique_ptr<SourceBlock> last_sb_before_throw = nullptr;
    bool after_hoist = true;
    for (auto it = std::prev(p.first->end()); it != p.first->begin(); --it) {
      if (it->type == MFLOW_SOURCE_BLOCK) {
        always_assert(it->src_block != nullptr);
        if (last_sb_before_throw == nullptr) {
          last_sb_before_throw = std::make_unique<SourceBlock>(*it->src_block);
        } else if (!after_hoist) {
          for (uint32_t i = 0; i < last_sb_before_throw->vals_size; i++) {
            const auto& val = last_sb_before_throw->get_at(i);
            it->src_block->set_at(i, val);
          }
        }
      } else if (it->type == MFLOW_OPCODE) {
        always_assert(it->insn != nullptr);
        if (opcode::may_throw(it->insn->opcode())) {
          last_sb_before_throw = nullptr;
        }
      }
      if (it == end) {
        after_hoist = false;
      }
    }
  }

  return insns_to_hoist.size();
}

// returns number of hoisted instructions
size_t process_hoisting_for_block(
    cfg::Block* block,
    cfg::ControlFlowGraph& cfg,
    Lazy<const constant_uses::ConstantUses>& constant_uses,
    bool can_allocate_regs,
    positions::JoinStats* join_stats) {
  IRList::iterator last_insn_it = block->get_last_insn();
  if (last_insn_it == block->end()) {
    // block is empty
    return 0;
  }
  IRInstruction* last_insn = last_insn_it->insn;
  if (!is_block_eligible(last_insn)) {
    return 0;
  }

  auto all_preds_are_same = [](const auto& edges) {
    auto it = edges.begin();
    always_assert(it != edges.end());
    auto first_src = (*it++)->src();
    for (; it != edges.end(); it++) {
      if ((*it)->src() != first_src) {
        return false;
      }
    }
    return true;
  };

  // make sure every successor has same predecessor and none will have to
  // throw.
  auto get_succ_blocks_if_same_preds_and_no_throw =
      [&cfg, &all_preds_are_same](
          cfg::Block* block) -> std::optional<std::vector<cfg::Block*>> {
    const auto& succ_edges = block->succs();
    std::vector<cfg::Block*> succ_blocks;
    succ_blocks.reserve(succ_edges.size());
    for (auto* edge : succ_edges) {
      auto* succ_block = edge->target();
      const auto& preds_of_succ_block = succ_block->preds();
      if (!all_preds_are_same(preds_of_succ_block)) {
        // we can only hoist the prefix if the block has only one incoming
        // edge
        return std::nullopt;
      }

      if (cfg.get_succ_edge_of_type(succ_block, cfg::EDGE_THROW) != nullptr) {
        return std::nullopt;
      }

      succ_blocks.push_back(succ_block);
    }
    return std::make_optional(std::move(succ_blocks));
  };

  auto succ_blocks = get_succ_blocks_if_same_preds_and_no_throw(block);
  if (!succ_blocks) {
    return 0;
  }

  // find critical registers that relates to branch taking decisions
  // critical registers for hoisting and if they are clobbered.
  // they all start as non-clobbered but if any hoisted insn clobbers it, it
  // will be changed to true.
  Lazy<UnorderedMap<reg_t, bool>> crit_regs([last_insn]() {
    auto res = std::make_unique<UnorderedMap<reg_t, bool>>();
    for (size_t i = 0; i < last_insn->srcs_size(); i++) {
      res->emplace(last_insn->src(i), false);
      if (last_insn->src_is_wide(i)) {
        res->emplace(last_insn->src(i) + 1, false);
      }
    }
    return res;
  });

  auto insns_to_hoist =
      get_insns_to_hoist(*succ_blocks, crit_regs, constant_uses);
  if (insns_to_hoist.empty()) {
    return 0;
  }
  // do the mutation
  auto hoisted = hoist_insns_for_block(
      block, last_insn_it, *succ_blocks, cfg, insns_to_hoist, *crit_regs,
      constant_uses, can_allocate_regs, join_stats);
  TRACE(
      BPH, 5, "Hoisted %zu/%zu instruction from %s into B%zu", hoisted,
      insns_to_hoist.size(),
      [&]() {
        std::ostringstream oss;
        for (auto& insn : insns_to_hoist) {
          oss << show(insn) << " | ";
        }
        return oss.str();
      }()
          .c_str(),
      block->id());
  return hoisted;
}

} // namespace

namespace branch_prefix_hoisting_impl {

size_t process_code(IRCode* code,
                    DexMethod* method,
                    bool can_allocate_regs,
                    positions::JoinStats* join_stats) {
  auto& cfg = code->cfg();
  TRACE(BPH, 5, "%s", SHOW(cfg));
  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method,
        /* force_type_inference */ true);
  });
  size_t ret = process_cfg(cfg, constant_uses, can_allocate_regs, join_stats);
  return ret;
}

size_t process_cfg(cfg::ControlFlowGraph& cfg,
                   Lazy<const constant_uses::ConstantUses>& constant_uses,
                   bool can_allocate_regs,
                   positions::JoinStats* join_stats) {
  size_t ret_insns_hoisted = 0;
  bool performed_transformation = false;
  do {
    performed_transformation = false;
    std::vector<cfg::Block*> blocks =
        graph::postorder_sort<cfg::GraphInterface>(cfg);
    // iterate from the back, may get to the optimal state quicker
    for (auto* block : blocks) {
      // when we are processing hoist for one block, other blocks may be changed
      size_t n_insn_hoisted = process_hoisting_for_block(
          block, cfg, constant_uses, can_allocate_regs, join_stats);
      if (n_insn_hoisted != 0u) {
        performed_transformation = true;
        ret_insns_hoisted += n_insn_hoisted;
        break;
      }
    }
  } while (performed_transformation);
  return ret_insns_hoisted;
}

} // namespace branch_prefix_hoisting_impl
