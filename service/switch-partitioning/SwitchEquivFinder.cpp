/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SwitchEquivFinder.h"

#include <algorithm>
#include <map>
#include <vector>

#include "CFGMutation.h"
#include "ConstantPropagationAnalysis.h"
#include "Debug.h"
#include "IRList.h"
#include "LiveRange.h"
#include "ReachingDefinitions.h"
#include "RedexContext.h"
#include "ScopedCFG.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace {
// Return true if any of the sources of `insn` are `reg`.
bool has_src(IRInstruction* insn, reg_t reg) {
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    if (insn->src(i) == reg) {
      return true;
    }
  }
  return false;
}

bool equals(const SwitchEquivFinder::InstructionSet& a,
            const SwitchEquivFinder::InstructionSet& b) {
  if (a.size() != b.size()) {
    return false;
  }
  const auto& has_equivalent =
      [&b](const std::pair<reg_t, IRInstruction*>& it) {
        const auto& search = b.find(it.first);
        if (search != b.end()) {
          bool just_one_null =
              (search->second == nullptr) != (it.second == nullptr);
          if (just_one_null) {
            return false;
          }
          bool both_null = search->second == nullptr && it.second == nullptr;
          if (both_null || *search->second == *it.second) {
            return true;
          }
        }
        return false;
      };

  for (auto it = a.begin(); it != a.end(); ++it) {
    if (!has_equivalent(*it)) {
      return false;
    }
  }
  return true;
}

// NOTE: instructions here may need to be relocated to leaf blocks. See
// copy_extra_loads_to_leaf_block below and keep that functionality up to date
// with this check.
bool is_valid_load_for_nonleaf(IROpcode op) {
  return opcode::is_a_literal_const(op) || op == OPCODE_CONST_CLASS ||
         opcode::is_move_result_pseudo_object(op);
}

// Return true if this block is a leaf.
// Any block that is not part of the if/switch tree is considered a leaf.
// TODO(T219644020): This function does not identify all blocks that must be
// leafs.
bool is_leaf(cfg::ControlFlowGraph* cfg, cfg::Block* b, reg_t reg) {
  // non-leaf nodes only have GOTO and BRANCH outgoing edges
  if (cfg->get_succ_edge_if(b, [](const cfg::Edge* e) {
        return e->type() == cfg::EDGE_GHOST || e->type() == cfg::EDGE_THROW;
      }) != nullptr) {
    return true;
  }

  if (b->preds().size() > 1) {
    // If there exists multiple ways to get to a block, this can be problematic
    // for tracking extra loads, which only is implemented for leafs.
    return true;
  }

  const auto& last = b->get_last_insn();
  if (last == b->end()) {
    // No instructions in this block => can't be part of the switching logic =>
    // must be a leaf
    return true;
  }
  for (const auto& mie : InstructionIterable(b)) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (!(is_valid_load_for_nonleaf(op) || opcode::is_branch(op))) {
      // non-leaf nodes only have const and branch instructions
      return true;
    }
    if (insn->has_dest() &&
        (insn->dest() == reg ||
         (insn->dest_is_wide() && insn->dest() + 1 == reg))) {
      // Overwriting the switching reg marks the end of the switch construct
      return true;
    }
  }

  auto* last_insn = last->insn;
  auto last_op = last_insn->opcode();
  // The only non-leaf block is one that branches on the switching reg
  // Any other block must be a leaf
  return !(opcode::is_branch(last_op) && has_src(last_insn, reg));
}

// For the leaf, check if the non-leaf predecessor block contributes to any
// extra loads. This is a check so that if this leaf is one of multiple that has
// the same case, we can determine if dropping the later (in execution order)
// would erroneously lose track of some surviving/relevant load.
bool pred_creates_extra_loads(const SwitchEquivFinder::ExtraLoads& extra_loads,
                              cfg::Block* leaf) {
  // There is probably a more convenient way to do this, but this condition
  // being hit should be quite rare (probably doesn't matter this is loopy).
  UnorderedSet<IRInstruction*> insns;
  for (const auto& [b, map] : UnorderedIterable(extra_loads)) {
    for (const auto& [reg, insn] : map) {
      insns.emplace(insn);
    }
  }
  for (auto* e : leaf->preds()) {
    auto* block = e->src();
    for (auto it = block->begin(); it != block->end(); it++) {
      if (it->type == MFLOW_OPCODE && insns.count(it->insn) > 0) {
        return true;
      }
    }
  }
  return false;
}

bool is_sled(cfg::Block* b) {
  auto* only = b->goes_to_only_edge();
  if (only == nullptr || only == b) {
    return false;
  }
  for (auto it = b->begin(); it != b->end(); it++) {
    if (it->type != MFLOW_SOURCE_BLOCK && it->type != MFLOW_REMARK) {
      return false;
    }
  }
  return true;
}

/*
 * Checks possible ConstantValue domains for if they are known/supported for
 * switching over, and returns the key.
 */
class key_creating_visitor
    : public boost::static_visitor<SwitchEquivFinder::SwitchingKey> {
 public:
  key_creating_visitor() {}

  SwitchEquivFinder::SwitchingKey operator()(
      const SignedConstantDomain& dom) const {
    if (dom.is_top() || dom.get_constant() == std::nullopt) {
      return SwitchEquivFinder::DefaultCase{};
    }
    // It's safe to cast down to 32 bits because long values can't be used in
    // switch statements.
    return static_cast<int32_t>(*dom.get_constant());
  }

  SwitchEquivFinder::SwitchingKey operator()(
      const ConstantClassObjectDomain& dom) const {
    if (dom.is_top() || !dom.get_constant()) {
      return SwitchEquivFinder::DefaultCase{};
    }
    return *dom.get_constant();
  }

  template <typename Domain>
  SwitchEquivFinder::SwitchingKey operator()(const Domain&) const {
    return SwitchEquivFinder::DefaultCase{};
  }
};

bool is_precise_branch(
    constant_propagation::intraprocedural::FixpointIterator& fixpoint,
    cfg::Block* block,
    reg_t switching_reg) {
  auto last = block->get_last_insn();
  always_assert_log(last != block->end(), "Expected branch in B%zu",
                    block->id());
  auto* insn = last->insn;
  always_assert_log(opcode::is_branch(insn->opcode()) &&
                        has_src(insn, switching_reg),
                    "Expected branch on v%u in B%zu, got %s", switching_reg,
                    block->id(), SHOW(insn));
  if (insn->srcs_size() == 1) {
    return insn->src(0) == switching_reg;
  }
  if (insn->srcs_size() != 2 || insn->src(0) == insn->src(1)) {
    return false;
  }
  const auto other =
      insn->src(0) == switching_reg ? insn->src(1) : insn->src(0);
  const auto& env = fixpoint.get_exit_state_at(block);
  const auto key =
      ConstantValue::apply_visitor(key_creating_visitor(), env.get(other));
  return !SwitchEquivFinder::is_default_case(key);
}
} // namespace

std::ostream& operator<<(std::ostream& os,
                         const SwitchEquivFinder::DefaultCase&) {
  return os << "DEFAULT";
}

// All DefaultCase structs should be considered equal.
bool operator<(const SwitchEquivFinder::DefaultCase&,
               const SwitchEquivFinder::DefaultCase&) {
  return false;
}

namespace cp = constant_propagation;

SwitchEquivFinder::SwitchEquivFinder(
    cfg::ControlFlowGraph* cfg,
    const cfg::InstructionIterator& root_branch,
    reg_t switching_reg,
    uint32_t leaf_duplication_threshold,
    std::shared_ptr<constant_propagation::intraprocedural::FixpointIterator>
        fixpoint_iterator,
    DuplicateCaseStrategy duplicates_strategy,
    std::shared_ptr<DefUseBlocks> def_use_blocks)
    : m_cfg(cfg),
      m_root_branch(root_branch),
      m_switching_reg(switching_reg),
      m_leaf_duplication_threshold(leaf_duplication_threshold),
      m_fixpoint_iterator(std::move(fixpoint_iterator)),
      m_duplicates_strategy(duplicates_strategy),
      m_def_use_blocks(std::move(def_use_blocks)) {
  {
    // make sure the input is well-formed
    auto* insn = m_root_branch->insn;
    auto op = insn->opcode();
    always_assert_log(opcode::is_branch(op), "Expected branch, got %s",
                      SHOW(insn));
    always_assert_log(has_src(insn, m_switching_reg),
                      "Branch %s does not test switching register v%u",
                      SHOW(insn), m_switching_reg);
  }

  const auto& leaves = find_leaves();
  if (leaves.empty()) {
    m_extra_loads.clear();
    m_success = false;
    return;
  }
  find_case_keys(leaves);
}

// Starting from the branch instruction, find all reachable branch
// instructions (with no intervening leaf blocks) that also have `reg` as a
// source (and without `reg` being overwritten)
//
// While we're searching for the leaf blocks, keep track of any constant loads
// that occur between the root branch and the leaf block. Put those in
// `m_extra_loads`.
std::vector<cfg::Edge*> SwitchEquivFinder::find_leaves() {
  std::vector<cfg::Edge*> leaves;

  // Traverse the tree in an depth first order so that the extra loads are
  // tracked in the same order that they will be executed at runtime
  UnorderedMap<cfg::Block*, bool> block_to_is_leaf;
  auto block_is_leaf = [&](cfg::Block* b) {
    auto search = block_to_is_leaf.find(b);
    if (search != block_to_is_leaf.end()) {
      return search->second;
    }
    auto ret = is_leaf(m_cfg, b, m_switching_reg);
    block_to_is_leaf[b] = ret;
    return ret;
  };

  // Validate every incorporated branch before duplicating or retargeting
  // leaves.
  UnorderedSet<cfg::Block*> checked_blocks;
  std::vector<cfg::Block*> pending_blocks{m_root_branch.block()};
  auto& fixpoint = get_analyzed_cfg();
  while (!pending_blocks.empty()) {
    auto* block = pending_blocks.back();
    pending_blocks.pop_back();
    if (!checked_blocks.insert(block).second) {
      continue;
    }
    if (!is_precise_branch(fixpoint, block, m_switching_reg)) {
      TRACE(SWITCH_EQUIV, 2, "Failure Reason: Imprecise comparison in B%zu",
            block->id());
      return leaves;
    }
    for (auto* edge : block->succs()) {
      if (!block_is_leaf(edge->target())) {
        pending_blocks.push_back(edge->target());
      }
    }
  }

  std::function<bool(cfg::Block*, InstructionSet,
                     const std::vector<SourceBlock*>&)>
      recurse;
  std::vector<std::pair<cfg::Edge*, cfg::Block*>> edges_to_move;
  UnorderedMap<cfg::Block*, std::vector<SourceBlock*>> source_blocks_to_move;

  recurse = [&](cfg::Block* b, const InstructionSet& loads,
                const std::vector<SourceBlock*>& source_blocks_in) {
    // `loads` represents the state of the registers after evaluating `b`.
    std::vector<cfg::Edge*> ordered_edges(b->succs().to_vector());
    // NOTE: To maintain proper order of duplicated cases, non leafs successors
    // will be encountered first.
    std::stable_sort(ordered_edges.begin(), ordered_edges.end(),
                     [&](const cfg::Edge* a, const cfg::Edge* b) {
                       return !block_is_leaf(a->target()) &&
                              block_is_leaf(b->target());
                     });
    for (cfg::Edge* succ : ordered_edges) {
      cfg::Block* next = succ->target();

      uint16_t count = ++m_visit_count[next];
      if (count > next->preds().size()) {
        // Infinite loop. Bail
        TRACE(SWITCH_EQUIV, 2, "Failure Reason: Detected loop");
        TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
        return false;
      }

      auto source_blocks_out = std::ref(source_blocks_in);

      if (block_is_leaf(next)) {
        leaves.push_back(succ);
        auto& source_blocks_vec = source_blocks_to_move[succ->target()];
        source_blocks_vec.insert(source_blocks_vec.end(),
                                 source_blocks_in.begin(),
                                 source_blocks_in.end());
        const auto& pair = m_extra_loads.emplace(next, loads);
        bool already_there = !pair.second;
        if (already_there) {
          // There are multiple ways to reach this leaf. Make sure the extra
          // loads are consistent.
          const auto& it = pair.first;
          const InstructionSet& existing_loads = it->second;
          if (!::equals(existing_loads, loads)) {
            if (next->num_opcodes() < m_leaf_duplication_threshold) {
              // A switch cannot represent this control flow graph unless we
              // duplicate this leaf. See the comment on
              // m_leaf_duplication_threshold for more details.
              cfg::Block* copy = m_cfg->duplicate_block(next);
              edges_to_move.emplace_back(succ, copy);
              m_extra_loads.emplace(copy, loads);
            } else {
              TRACE(SWITCH_EQUIV, 2, "Failure Reason: divergent entry states");
              TRACE(SWITCH_EQUIV, 3, "B%zu in %s", next->id(), SHOW(*m_cfg));
              return false;
            }
          }
        }
      } else {
        std::optional<InstructionSet> next_loads;
        std::vector<SourceBlock*> next_source_blocks;
        for (const auto& mie : *next) {
          if (mie.type == MFLOW_SOURCE_BLOCK) {
            if (&source_blocks_out.get() == &source_blocks_in) {
              next_source_blocks = source_blocks_in;
              source_blocks_out = next_source_blocks;
            }
            next_source_blocks.push_back(mie.src_block.get());
            continue;
          }

          if (mie.type != MFLOW_OPCODE) {
            continue;
          }

          // A chain of if-else blocks loads constants into register to do the
          // comparisons, however, the leaf blocks may also use those registers,
          // so this function finds any loads that occur in non-leaf blocks that
          // lead to `leaf`.
          auto* insn = mie.insn;
          auto op = insn->opcode();
          if (is_valid_load_for_nonleaf(op)) {
            if (next_loads == std::nullopt) {
              // Copy loads here because we only want these loads to propagate
              // to successors of `next`, not any other successors of `b`
              next_loads = loads;
            }

            if (insn->has_dest()) {
              // Overwrite any previous mapping for this dest register.
              (*next_loads)[insn->dest()] = insn;
              if (insn->dest_is_wide()) {
                // And don't forget to clear out the upper register of wide
                // loads.
                (*next_loads)[insn->dest() + 1] = nullptr;
              }
            }
          }
        }

        bool success = false;
        if (next_loads != std::nullopt) {
          success = recurse(next, *next_loads, source_blocks_out.get());
        } else {
          success = recurse(next, loads, source_blocks_out.get());
        }
        if (!success) {
          return false;
        }
      }
    }
    return true;
  };

  const auto& bail = [&leaves, this, &edges_to_move]() {
    // While traversing the CFG, we may have duplicated case blocks (see the
    // comment on m_leaf_duplication_threshold for more details). If we did not
    // successfully find a switch equivalent here, we need to remove those
    // blocks.
    std::vector<cfg::Block*> blocks_to_remove;
    for (const auto& pair : edges_to_move) {
      cfg::Block* copy = pair.second;
      blocks_to_remove.push_back(copy);
    }
    m_cfg->remove_blocks(blocks_to_remove);
    leaves.clear();
    return leaves;
  };

  bool success = recurse(m_root_branch.block(), {}, {});
  if (!success) {
    return bail();
  }

  normalize_extra_loads(block_to_is_leaf);

  if (!m_extra_loads.empty()) {
    // Make sure there are no other ways to reach the leaf nodes. If there were
    // other ways to reach them, m_extra_loads would be incorrect.
    for (const auto& block_and_count : UnorderedIterable(m_visit_count)) {
      cfg::Block* b = block_and_count.first;
      uint16_t count = block_and_count.second;
      if (b->preds().size() > count) {
        TRACE(SWITCH_EQUIV, 2,
              "Failure Reason: Additional ways to reach blocks");
        TRACE(SWITCH_EQUIV, 3,
              "  B%zu has %zu preds but was hit %d times in \n%s", b->id(),
              b->preds().size(), count, SHOW(*m_cfg));
        return bail();
      }
    }
  }

  success = move_edges(edges_to_move);
  if (!success) {
    return bail();
  }

  // This code would transform the source blocks as so
  //
  // <source-block 1>
  // x = ...
  // if (x == 2) {
  //   <source-block 2>
  //   goto A;
  // } else {
  //   <source-block 3>
  //   if (x = 4) {
  //     <source-block 4>
  //     goto B;
  //   } else {
  //     <source-block 5>
  //     if (x == 6) {
  //       <source-block 6>
  //       goto C;
  //     }
  //   }
  // }
  //
  // to
  //
  // <source-block 1>
  // x = ...
  // switch (x) {
  //   case 2:
  //   A:
  //     <source-block 2>
  //     break;
  //   case 4:
  //   B:
  //     <source-block 3>
  //     <source-block 4>
  //     break;
  //   case 6:
  //   C:
  //     <source-block 3>
  //     <source-block 5>
  //     <source-block 6>
  //     break;
  // }
  //
  // In instrumented builds, this behavior ensures we log hits correctly in a
  // way that is faithful to the original code structure.
  //
  // However, for non-instrumented builds, if B is always hit, we would have
  // non-sensical data in C where @3 (hot) goes directly to @5 (cold). Thus, we
  // want to disable this behavior for everything except for instrumented
  // builds.
  if (g_redex->instrument_mode) {
    for (auto& [blk, source_blocks] :
         UnorderedIterable(source_blocks_to_move)) {
      auto it_insert = source_blocks::find_first_block_insert_point(blk);

      for (auto* source_block : source_blocks) {
        blk->insert_before(it_insert,
                           std::make_unique<SourceBlock>(*source_block));
      }
    }
  }

  if (leaves.empty()) {
    TRACE(SWITCH_EQUIV, 2, "Failure Reason: No leaves found");
    TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
  }
  return leaves;
}

namespace {

// Split a duplicated block's execution count between the original and the copy
// when one predecessor edge moves to the copy. `duplicate_block` copies
// SourceBlocks verbatim, so without this both blocks claim the whole count.
//
// The two sides need different factors when several edges move in turn. The
// original shrinks step by step, so its share is taken against its current
// predecessor set. Each copy, though, still holds the pre-split count -- it
// does not shrink as earlier edges depart -- so scaling it by a fraction of the
// original's already-reduced total would leave it inflated. Take the copy's
// factor against its own value instead, which makes each copy land on exactly
// the count its moved predecessor contributes, whatever order the edges move
// in.
void split_counts_for_moved_edge(cfg::Block* orig,
                                 cfg::Block* copy,
                                 const cfg::Block* moved_from) {
  auto* orig_sb = source_blocks::get_first_source_block(orig);
  const size_t n_slots = orig_sb != nullptr ? orig_sb->vals_size : 0;
  if (n_slots == 0) {
    return;
  }
  const auto pred_total =
      source_blocks::apportion::predecessor_totals(orig, n_slots);
  auto* copy_sb = source_blocks::get_first_source_block(copy);
  const auto* moved_sb = source_blocks::get_last_source_block(moved_from);
  std::vector<double> leaving(n_slots, 0.0);
  for (size_t i = 0; i < n_slots; ++i) {
    const double share =
        source_blocks::apportion::share_of(pred_total, moved_from, i);
    if (share < 0.0) {
      continue; // no count evidence for this slot -- leave both alone
    }
    leaving[i] = share;
    if (copy_sb == nullptr || moved_sb == nullptr) {
      continue;
    }
    const double copy_val = copy_sb->get_val(i).value_or(0.0f);
    if (copy_val <= 0.0) {
      continue;
    }
    const double moved_val = moved_sb->get_val(i).value_or(0.0f);
    const double copy_factor = moved_val / copy_val;
    source_blocks::foreach_source_block(copy, [&](auto* sb) {
      source_blocks::apportion::scale_val(sb, i, copy_factor);
    });
  }
  source_blocks::apportion::shrink_by_departed(orig, leaving);
}

} // namespace

bool SwitchEquivFinder::move_edges(
    const std::vector<std::pair<cfg::Edge*, cfg::Block*>>& edges_to_move) {
  for (const auto& pair : edges_to_move) {
    cfg::Edge* edge = pair.first;
    cfg::Block* orig = edge->target();
    for (cfg::Edge* orig_succ : orig->succs()) {
      always_assert_log(orig_succ != nullptr, "B%zu in %s", orig->id(),
                        SHOW(*m_cfg));
      if (orig_succ->type() == cfg::EDGE_GOTO &&
          orig_succ->target()->starts_with_move_result()) {
        // Two blocks can't share a single move-result-psuedo
        TRACE(SWITCH_EQUIV, 2,
              "Failure Reason: Can't share move-result-pseudo");
        TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
        return false;
      }
    }
  }
  std::vector<cfg::Block*> blocks_to_remove;
  for (const auto& pair : edges_to_move) {
    cfg::Edge* edge = pair.first;
    cfg::Block* orig = edge->target();
    cfg::Block* copy = pair.second;
    const auto& copy_loads = m_extra_loads.find(copy);
    const auto& orig_loads = m_extra_loads.find(orig);
    const auto& have_copy_loads = copy_loads != m_extra_loads.end();
    const auto& have_orig_loads = orig_loads != m_extra_loads.end();
    bool just_one_null = have_copy_loads != have_orig_loads;
    bool both_null = !have_copy_loads && !have_orig_loads;
    if (!just_one_null &&
        (both_null || ::equals(copy_loads->second, orig_loads->second))) {
      // When we normalized the extra loads, the copy and original may have
      // converged to the same state. We don't need the duplicate block anymore
      // in this case.
      blocks_to_remove.push_back(copy);
      continue;
    }
    // copy on purpose so we can alter in the loop
    // NOLINTNEXTLINE(performance-unnecessary-copy-initialization)
    const auto orig_succs = orig->succs();
    for (cfg::Edge* orig_succ : orig_succs) {
      cfg::Edge* copy_succ = new cfg::Edge(*orig_succ);
      m_cfg->add_edge(copy_succ);
      m_cfg->set_edge_source(copy_succ, copy);
    }
    // Before the retarget, while `edge->src()` still counts as a predecessor of
    // `orig`. Done here rather than where the copy was made, because a copy
    // whose loads converged with the original is discarded above and never
    // takes any of its count.
    if (g_redex->preserve_count_integrity) {
      split_counts_for_moved_edge(orig, copy, edge->src());
    }
    m_cfg->set_edge_target(edge, copy);
  }
  m_cfg->remove_blocks(blocks_to_remove);
  return true;
}

SwitchEquivFinder::DefUseBlocks SwitchEquivFinder::GetDefUseBlocks(
    cfg::ControlFlowGraph& cfg) {
  DefUseBlocks res;
  reaching_defs::FixpointIterator fixpoint_iter(cfg);
  fixpoint_iter.run(reaching_defs::Environment());
  for (cfg::Block* block : cfg.blocks()) {
    reaching_defs::Environment defs_in =
        fixpoint_iter.get_entry_state_at(block);
    if (defs_in.is_bottom()) {
      continue;
    }
    for (const auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      for (size_t i = 0; i < insn->srcs_size(); ++i) {
        auto src = insn->src(i);
        const auto& defs = defs_in.get(src);
        always_assert_log(!defs.is_top(), "Undefined register v%u", src);
        for (IRInstruction* def : defs.elements()) {
          res[def].insert(block);
        }
      }
      fixpoint_iter.analyze_instruction(insn, &defs_in);
    }
  }
  return res;
}

// Before this function, m_extra_loads is overly broad
// * Remove loads that are never used outside the if-else chain blocks
// * Remove empty lists of loads from the map (possibly emptying the map)
void SwitchEquivFinder::normalize_extra_loads(
    const UnorderedMap<cfg::Block*, bool>& block_to_is_leaf) {

  // Use ReachingDefinitions to find the loads that are used outside the if-else
  // chain blocks
  auto& def_use_blocks = get_def_use_blocks();
  UnorderedSet<IRInstruction*> used_defs;
  for (const auto& [b, is_leaf] : UnorderedIterable(block_to_is_leaf)) {
    if (is_leaf) {
      continue;
    }
    for (const auto& mie : InstructionIterable(b)) {
      if (!is_valid_load_for_nonleaf(mie.insn->opcode())) {
        continue;
      }
      for (auto* use_block : UnorderedIterable(def_use_blocks[mie.insn])) {
        auto search = block_to_is_leaf.find(use_block);
        if (search != block_to_is_leaf.end() && !search->second) {
          continue;
        }
        used_defs.insert(mie.insn);
      }
    }
  }

  // Remove loads that aren't used outside the if-else chain blocks
  for (auto& block_and_insns : UnorderedIterable(m_extra_loads)) {
    InstructionSet& insns = block_and_insns.second;
    std::erase_if(insns, [&used_defs](auto& p) {
      return used_defs.count(p.second) == 0;
    });
  }

  // Remove empty instruction lists from `m_extra_loads` (possibly emptying it)
  unordered_erase_if(m_extra_loads, [](auto& p) { return p.second.empty(); });
}

cp::intraprocedural::FixpointIterator& SwitchEquivFinder::get_analyzed_cfg() {
  if (!m_fixpoint_iterator) {
    m_fixpoint_iterator =
        std::make_shared<cp::intraprocedural::FixpointIterator>(*m_cfg,
                                                                Analyzer());
    m_fixpoint_iterator->run(ConstantEnvironment());
  }
  return *m_fixpoint_iterator;
}

SwitchEquivFinder::DefUseBlocks& SwitchEquivFinder::get_def_use_blocks() {
  if (!m_def_use_blocks) {
    m_def_use_blocks = std::make_shared<DefUseBlocks>(GetDefUseBlocks(*m_cfg));
  }
  return *m_def_use_blocks;
}

// Use a sparta analysis to find the value of reg at the beginning of each leaf
// block
void SwitchEquivFinder::find_case_keys(const std::vector<cfg::Edge*>& leaves) {
  // We use the fixpoint iterator to infer the values of registers at different
  // points in the program. Especially `m_switching_reg`.
  auto& fixpoint = get_analyzed_cfg();

  // return true on success
  // return false on failure (there was a conflicting entry already in the map)
  const auto& insert = [this](const SwitchingKey& key, cfg::Block* b) {
    const auto& pair = m_key_to_case.emplace(key, b);
    const auto& it = pair.first;
    bool already_there = !pair.second;
    if (already_there && it->second != b) {
      if (m_duplicates_strategy == NOT_ALLOWED) {
        TRACE(SWITCH_EQUIV, 2,
              "Failure Reason: Divergent key to block mapping.");
        TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
        return false;
      } else if (m_duplicates_strategy == EXECUTION_ORDER) {
        // Disallow Multiple default cases, even with EXECUTION_ORDER
        if (is_default_case(key)) {
          TRACE(SWITCH_EQUIV, 2,
                "Failure Reason: Multiple Default cases detected.");
          TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
          return false;
        }
        if (pred_creates_extra_loads(m_extra_loads, it->second)) {
          TRACE(SWITCH_EQUIV, 2,
                "Failure Reason: Divergent key to block mapping with extra "
                "loads.");
          TRACE(SWITCH_EQUIV, 3, "%s", SHOW(*m_cfg));
          return false;
        }
        TRACE(SWITCH_EQUIV, 2,
              "Updating key to block mapping for duplicate case; B%zu will be "
              "supplanted by B%zu.",
              it->second->id(), b->id());
        it->second = b;
        m_duplicate_case_keys = true;
      } else {
        not_reached();
      }
    }
    return true;
  };

  // returns the value of `m_switching_reg` if the leaf is reached via this edge
  const auto& get_case_key =
      [this, &fixpoint](cfg::Edge* edge_to_leaf) -> SwitchingKey {
    // Get the inferred value of m_switching_reg at the end of `edge_to_leaf`
    // but before the beginning of the leaf block because we would lose the
    // information by merging all the incoming edges.
    const auto& exit_env = fixpoint.get_exit_state_at(edge_to_leaf->src());
    auto env = fixpoint.analyze_edge(edge_to_leaf, exit_env);
    const auto& val = env.get(m_switching_reg);
    return ConstantValue::apply_visitor(key_creating_visitor(), val);
  };

  for (cfg::Edge* edge_to_leaf : leaves) {
    const auto& case_key = get_case_key(edge_to_leaf);
    bool success = insert(case_key, edge_to_leaf->target());
    if (!success) {
      // If we didn't insert into result for this leaf node, abort the entire
      // operation because we don't want to present incomplete information about
      // the possible successors
      m_key_to_case.clear();
      m_extra_loads.clear();
      m_success = false;
      return;
    }
  }
  m_success = true;
}

UnorderedBag<cfg::Block*> SwitchEquivFinder::visited_blocks() const {
  UnorderedBag<cfg::Block*> result;
  result.reserve(1 + m_visit_count.size());
  result.insert(m_root_branch.block());
  for (auto entry : UnorderedIterable(m_visit_count)) {
    result.insert(entry.first);
  }
  return result;
}

size_t SwitchEquivEditor::copy_extra_loads_to_leaf_block(
    const SwitchEquivFinder::ExtraLoads& extra_loads,
    cfg::ControlFlowGraph* cfg,
    cfg::Block* leaf) {
  size_t changes = 0;
  auto push_front = [&](IRInstruction* insn) {
    auto* copy = new IRInstruction(*insn);
    TRACE(SWITCH_EQUIV, 4, "adding %s to B%zu", SHOW(copy), leaf->id());
    changes++;
    leaf->push_front(copy);
  };
  const auto& loads_for_this_leaf = extra_loads.find(leaf);
  if (loads_for_this_leaf != extra_loads.end()) {
    for (const auto& register_and_insn : loads_for_this_leaf->second) {
      IRInstruction* insn = register_and_insn.second;
      if (insn != nullptr) {
        // null instruction pointers are used to signify the upper half of
        // a wide load.
        push_front(insn);
        if (opcode::is_move_result_pseudo_object(insn->opcode())) {
          auto primary_it =
              cfg->primary_instruction_of_move_result(cfg->find_insn(insn));
          push_front(primary_it->insn);
        }
      }
    }
  }
  return changes;
}

size_t SwitchEquivEditor::copy_extra_loads_to_leaf_blocks(
    const SwitchEquivFinder& finder, cfg::ControlFlowGraph* cfg) {
  size_t result = 0;
  const auto& extra_loads = finder.extra_loads();
  for (const auto& pair : finder.key_to_case()) {
    result += copy_extra_loads_to_leaf_block(extra_loads, cfg, pair.second);
  }
  return result;
}

size_t SwitchEquivEditor::simplify_moves(IRCode* code) {
  auto scoped_cfg = std::make_unique<cfg::ScopedCFG>(code);
  auto& cfg = **scoped_cfg;

  size_t changes{0};
  cfg::CFGMutation mutation(cfg);
  auto udchains = live_range::MoveAwareChains(cfg).get_use_def_chains();

  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (insn->opcode() == OPCODE_MOVE_OBJECT) {
      auto search = udchains.find((live_range::Use){insn, 0});
      if (search != udchains.end() && search->second.size() == 1) {
        auto* def = *search->second.begin();
        if (def->opcode() == OPCODE_CONST_CLASS) {
          auto* duplicated_const_class = new IRInstruction(*def);
          auto* move_pseudo =
              new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
          move_pseudo->set_dest(insn->dest());
          mutation.replace(it, {duplicated_const_class, move_pseudo});
          changes++;
        }
      }
    }
  }
  mutation.flush();
  return changes;
}

size_t SwitchEquivEditor::normalize_sled_blocks(
    cfg::ControlFlowGraph* cfg, const uint32_t leaf_duplication_threshold) {
  size_t changes{0};
  for (auto* b : cfg->blocks()) {
    if (is_sled(b)) {
      auto* dest = b->goes_to_only_edge();
      if (!is_sled(dest) && dest->num_opcodes() < leaf_duplication_threshold) {
        // Make a replacement for b, which is b's source blocks plus dest.
        TRACE(SWITCH_EQUIV, 2,
              "Removing sled block B%zu; duplicating instructions from B%zu",
              b->id(), dest->id());
        auto* replacement = cfg->duplicate_block(dest);
        // Scale before b's own SourceBlocks are prepended below, so only the
        // ones duplicated from `dest` are touched. `b` is about to be replaced
        // by this copy, so `dest` keeps its other predecessors and sheds the
        // flow that used to arrive through the sled.
        if (g_redex->preserve_count_integrity) {
          split_counts_for_moved_edge(dest, replacement, b);
        }
        for (auto* succ : dest->succs()) {
          cfg->add_edge(replacement, succ->target(), succ->type());
        }
        // Put b's source blocks into b's replacement.
        for (auto it = b->rbegin(); it != b->rend(); ++it) {
          if (it->type == MFLOW_SOURCE_BLOCK) {
            auto& source_block = it->src_block;
            auto it_insert =
                source_blocks::find_first_block_insert_point(replacement);
            replacement->insert_before(
                it_insert, std::make_unique<SourceBlock>(*source_block));
          }
        }
        cfg->replace_block(b, replacement);
        TRACE(SWITCH_EQUIV, 2, " -> Inserted replacement block B%zu",
              replacement->id());
        changes++;
      }
    }
  }
  return changes;
}
