/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TailDuplicationPass.h"

#include <sparta/WeakTopologicalOrdering.h>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DedupBlocks.h"
#include "DexAssessments.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "PassManager.h"
#include "ScopedMetrics.h"
#include "Shrinker.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

bool make_hot_tail_unique(cfg::ControlFlowGraph& cfg,
                          cfg::Edge* succ,
                          size_t max_block_code_units) {
  auto* target = succ->target();
  always_assert(target);
  auto target_preds = target->preds().size();
  always_assert(target_preds > 0);
  if (target_preds == 1) {
    // Don't bother trying to specialize a block that is already unique.
    return false;
  }
  auto ii = InstructionIterable(target);
  if (std::any_of(ii.begin(), ii.end(), [&](auto& mie) {
        return dedup_blocks_impl::is_ineligible_because_of_fill_in_stack_trace(
                   mie.insn) ||
               opcode::is_new_instance(mie.insn->opcode()) ||
               (opcode::is_invoke_direct(mie.insn->opcode()) &&
                method::is_init(mie.insn->get_method()));
      })) {
    // Don't duplicate blocks that we cannote deduplicate because of existing
    // limitations in dedup-blocks.
    return false;
  }
  auto* target_target = target->goes_to();
  if (target_target != nullptr) {
    auto target_target_first_insn = target_target->get_first_insn();
    if (target_target_first_insn != target_target->end() &&
        opcode::is_move_result_any(target_target_first_insn->insn->opcode())) {
      // Implementation limitation: Cannot duplicate blocks that have an
      // associated move-result instruction in yet another block.
      return false;
    }
  }
  if (target->estimate_code_units() > max_block_code_units) {
    // Don't bother trying to specialize very long code
    return false;
  }
  auto* target_copy = cfg.duplicate_block(target);
  auto target_succs_copy = target->succs();
  for (auto* target_succ : target_succs_copy) {
    always_assert(target_succ->src() == target);
    always_assert(target_succ->target() != target);
    switch (target_succ->type()) {
    case cfg::EDGE_BRANCH:
      if (target_succ->case_key()) {
        cfg.add_edge(target_copy, target_succ->target(),
                     *target_succ->case_key());
        break;
      }
      [[fallthrough]];
    case cfg::EDGE_GOTO:
    case cfg::EDGE_GHOST:
      cfg.add_edge(target_copy, target_succ->target(), target_succ->type());
      break;
    case cfg::EDGE_THROW:
      cfg.add_edge(target_copy, target_succ->target(),
                   target_succ->throw_info()->catch_type,
                   target_succ->throw_info()->index);
      break;
    default:
      not_reached();
    }
  }
  cfg.set_edge_target(succ, target_copy);
  always_assert(target_copy->preds().size() == 1);
  always_assert(target_copy->preds().front() == succ);
  always_assert(target->preds().size() + 1 == target_preds);
  return true;
}

// (Weak) topological order of blocks, filtering out blocks with back-edges.
std::vector<cfg::Block*> get_ordered_blocks(const cfg::ControlFlowGraph& cfg) {
  sparta::WeakTopologicalOrdering<cfg::Block*> wto(
      cfg.entry_block(), [&](const cfg::Block* block) {
        std::vector<cfg::Block*> targets;
        UnorderedSet<cfg::Block*> set;
        for (auto* edge : block->succs()) {
          if ((edge->target() != nullptr) &&
              set.emplace(edge->target()).second) {
            targets.emplace_back(edge->target());
          }
        }
        return targets;
      });

  std::vector<cfg::Block*> blocks;
  UnorderedSet<cfg::Block*> set;
  wto.visit_depth_first([&](cfg::Block* block) {
    const auto& preds = block->preds();
    if (std::all_of(preds.begin(), preds.end(),
                    [&](auto* edge) { return set.count(edge->src()); })) {
      blocks.push_back(block);
    }
    set.insert(block);
  });
  return blocks;
}

using baseline_profiles::compute_dex2oat_facts;
using baseline_profiles::dex2oat_compiles;
using baseline_profiles::flags_request_compilation;

} // namespace

namespace tail_duplication_impl {

size_t make_hot_tails_unique(cfg::ControlFlowGraph& cfg,
                             size_t max_block_code_units) {
  auto blocks = get_ordered_blocks(cfg);
  UnorderedMap<cfg::Block*, cfg::Block*> new_blocks;
  UnorderedSet<cfg::Block*> duplicated_blocks;
  for (auto* block : blocks) {
    if (!source_blocks::is_hot(block)) {
      continue;
    }

    auto block_preds_copy = block->preds();
    std::vector<cfg::Block*> new_targets;
    for (auto* pred : block_preds_copy) {
      if (pred->type() != cfg::EDGE_GOTO && pred->type() != cfg::EDGE_BRANCH) {
        continue;
      }

      auto* src = pred->src();
      always_assert(pred->target() == block);
      if ((src == nullptr) || !source_blocks::is_hot(src)) {
        continue;
      }

      auto it = new_blocks.find(src);
      auto* old_src = it != new_blocks.end() ? it->second : src;
      if (duplicated_blocks.count(old_src) != 0u) {
        // To avoid a combinatorial exploration, we'll only create at most one
        // duplicate target from any particular source block  (or one of its
        // duplicates).
        continue;
      }

      if (make_hot_tail_unique(cfg, pred, max_block_code_units)) {
        always_assert(pred->target() != block);
        new_targets.push_back(pred->target());
        duplicated_blocks.insert(old_src);
      }
    }

    if (!new_targets.empty()) {
      source_blocks::scale_source_blocks(block);
      for (auto* new_target : new_targets) {
        source_blocks::scale_source_blocks(new_target);
        new_blocks.emplace(new_target, block);
      }
    }
  }

  return new_blocks.size();
}

} // namespace tail_duplication_impl

void TailDuplicationPass::bind_config() {
  bind("run_const_prop", true, m_config.run_const_prop,
       "Whether to run constant-propagation.");
  bind("run_cse", true, m_config.run_cse,
       "Whether to run common-subexpression-elimination.");
  bind("run_copy_prop", true, m_config.run_copy_prop,
       "Whether to run copy-propagation.");
  bind("run_local_dce", true, m_config.run_local_dce,
       "Whether to run local-dead-code-elimination.");
  bind("run_reg_alloc", false, m_config.run_reg_alloc,
       "Whether to run register allocation.");
  bind("run_fast_reg_alloc", false, m_config.run_fast_reg_alloc,
       "Whether to run fast register allocation.");
  bind("run_dedup_blocks", true, m_config.run_dedup_blocks,
       "Whether to run dedup-blocks.");
  bind("run_branch_prefix_hoisting", false, m_config.run_branch_prefix_hoisting,
       "Whether to run branch-prefix hoisting.");

  bind("compute_pure_methods", true, m_config.compute_pure_methods,
       "Whether to compute pure methods with a relatively expensive analysis "
       "over the scope.");

  bind("reg_alloc_random_forest", "", m_config.reg_alloc_random_forest,
       "Decide which functions to run register allocation on.");

  bind("analyze_constructors", false, m_config.analyze_constructors,
       "Whether to analyze constructors to find immutable attributes (only "
       "relevant when using constant-propagaation)");

  bind("max_block_code_units", 16, m_max_block_code_units,
       "Maximum size of block considered for duplication. Larger blocks offer "
       "more potential for specialization, but may also lead to a significant "
       "code size increase. While specialization is beneficial for "
       "performance, the code size increase may cause more icache misses and "
       "performance degradation.");
}

void TailDuplicationPass::eval_pass(DexStoresVector&,
                                    ConfigFiles&,
                                    PassManager&) {
  constant_propagation::StringAnalyzerState::make_default()
      .set_methods_as_root();
}

void TailDuplicationPass::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
  // Don't run under instrumentation.
  if (mgr.get_redex_options().instrument_pass_enabled) {
    return;
  }

  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  auto baseline_profile =
      baseline_profiles::get_default_baseline_profile(scope, conf);
  const auto huge_method_max = baseline_profiles::get_huge_method_max(conf);

  int min_sdk = mgr.get_redex_options().min_sdk;
  shrinker::Shrinker shrinker(stores, scope, init_classes_with_side_effects,
                              conf, m_config, min_sdk, conf.get_pure_methods(),
                              conf.get_finalish_field_names(), {},
                              mgr.get_redex_options().package_name);

  std::atomic<size_t> new_blocks{0};
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (method->rstate.no_optimizations()) {
      return;
    }
    if (!source_blocks::is_hot(code.cfg().entry_block())) {
      return;
    }
    // The flags first, so that only entries that ask for compilation pay for
    // the size, which the threshold below then reuses.
    auto it = baseline_profile.methods.find(method);
    if (it == baseline_profile.methods.end() ||
        !flags_request_compilation(it->second)) {
      return;
    }
    auto facts = compute_dex2oat_facts(method, huge_method_max);
    if (!dex2oat_compiles(it->second, facts)) {
      return;
    }
    if (facts.code_units > assessments::HUGE_METHOD_THRESHOLD / 4) {
      // This transformation could double the code size. Let's make sure we are
      // getting nowhere near "huge" territory.
      return;
    }

    // Tighten everything up.
    shrinker.shrink_method(method);
    code.clear_cfg();
    code.build_cfg();

    size_t local_new_blocks = tail_duplication_impl::make_hot_tails_unique(
        code.cfg(), m_max_block_code_units);
    if (local_new_blocks == 0) {
      return;
    }

    new_blocks.fetch_add(local_new_blocks);
    shrinker.shrink_method(method);
  });

  TRACE(CSE, 1, "%zu new blocks", new_blocks.load());

  mgr.incr_metric("new_blocks", new_blocks.load());
  mgr.incr_metric("methods_shrunk", shrinker.get_methods_shrunk());
  mgr.incr_metric(
      "instructions_eliminated_const_prop",
      shrinker.get_const_prop_stats().branches_removed +
          shrinker.get_const_prop_stats().unreachable_instructions_removed +
          shrinker.get_const_prop_stats().redundant_puts_removed +
          shrinker.get_const_prop_stats().branches_forwarded +
          shrinker.get_const_prop_stats().materialized_consts +
          shrinker.get_const_prop_stats().added_param_const +
          shrinker.get_const_prop_stats().throws +
          shrinker.get_const_prop_stats().null_checks);
  {
    ScopedMetrics sm(mgr);
    auto sm_scope = sm.scope("shrinker");
    shrinker.log_metrics(sm);
  }
  mgr.incr_metric("instructions_eliminated_cse",
                  shrinker.get_cse_stats().instructions_eliminated);
  mgr.incr_metric("instructions_eliminated_copy_prop",
                  shrinker.get_copy_prop_stats().moves_eliminated);
  mgr.incr_metric("instructions_eliminated_localdce_dead",
                  shrinker.get_local_dce_stats().dead_instruction_count);
  mgr.incr_metric("instructions_eliminated_localdce_unreachable",
                  shrinker.get_local_dce_stats().unreachable_instruction_count);
  mgr.incr_metric("instructions_eliminated_dedup_blocks",
                  shrinker.get_dedup_blocks_stats().insns_removed);
  mgr.incr_metric("blocks_eliminated_by_dedup_blocks",
                  shrinker.get_dedup_blocks_stats().blocks_removed);
  mgr.incr_metric("instructions_eliminated_branch_prefix_hoisting",
                  shrinker.get_branch_prefix_hoisting_stats());
  mgr.incr_metric("methods_reg_alloced", shrinker.get_methods_reg_alloced());
  mgr.incr_metric("localdce_init_class_instructions_added",
                  shrinker.get_local_dce_stats().init_class_instructions_added);
  mgr.incr_metric(
      "localdce_init_class_instructions",
      shrinker.get_local_dce_stats().init_classes.init_class_instructions);
  mgr.incr_metric("localdce_init_class_instructions_removed",
                  shrinker.get_local_dce_stats()
                      .init_classes.init_class_instructions_removed);
  mgr.incr_metric("localdce_init_class_instructions_refined",
                  shrinker.get_local_dce_stats()
                      .init_classes.init_class_instructions_refined);

  // Expose the shrinking timers as Timers.
  Timer::add_timer("Shrinker.Shrinking.ConstantPropagation",
                   shrinker.get_const_prop_seconds());
  Timer::add_timer("Shrinker.Shrinking.CSE", shrinker.get_cse_seconds());
  Timer::add_timer("Shrinker.Shrinking.CopyPropagation",
                   shrinker.get_copy_prop_seconds());
  Timer::add_timer("Shrinker.Shrinking.LocalDCE",
                   shrinker.get_local_dce_seconds());
  Timer::add_timer("Shrinker.Shrinking.DedupBlocks",
                   shrinker.get_dedup_blocks_seconds());
  Timer::add_timer("Shrinker.Shrinking.BranchPrefixHoisting",
                   shrinker.get_branch_prefix_hoisting_seconds());
  Timer::add_timer("Shrinker.Shrinking.RegAlloc",
                   shrinker.get_reg_alloc_seconds());
}

static TailDuplicationPass s_pass;
