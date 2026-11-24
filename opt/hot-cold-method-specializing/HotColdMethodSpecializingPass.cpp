/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "HotColdMethodSpecializingPass.h"

#include "ConfigFiles.h"
#include "Debug.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "Show.h"
#include "Shrinker.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "Walkers.h"

namespace {
// Computes all blocks backwards-reachable from a given set of success blocks,
// excluding those successor blocks (unless they are also backwards reachable
// otherwise).
template <typename Collection>
UnorderedSet<cfg::Block*> get_backwards_reachable_blocks_from(
    const cfg::ControlFlowGraph& /*cfg*/,
    const Collection& succ_blocks,
    const UnorderedSet<cfg::Block*>* filter_blocks = nullptr) {
  UnorderedSet<cfg::Block*> res;
  std::queue<cfg::Block*> work_queue;
  auto push_preds_srcs = [&](auto* block) {
    for (auto* edge : block->preds()) {
      if (filter_blocks == nullptr || filter_blocks->count(edge->src())) {
        work_queue.push(edge->src());
      }
    }
  };
  for (auto* block : UnorderedIterable(succ_blocks)) {
    push_preds_srcs(block);
  }
  while (!work_queue.empty()) {
    auto* block = work_queue.front();
    work_queue.pop();
    if (res.insert(block).second) {
      push_preds_srcs(block);
    }
  }
  return res;
}

template <typename Collection>
UnorderedSet<cfg::Block*> get_forward_reachable_blocks(
    const cfg::ControlFlowGraph& /*cfg*/,
    const Collection& entry_blocks,
    const UnorderedSet<cfg::Block*>& frontier = {}) {
  UnorderedSet<cfg::Block*> res;
  std::queue<cfg::Block*> work_queue;
  for (auto* entry_block : UnorderedIterable(entry_blocks)) {
    always_assert(!frontier.count(entry_block));
    work_queue.push(entry_block);
  }
  while (!work_queue.empty()) {
    auto* block = work_queue.front();
    work_queue.pop();
    if (!res.insert(block).second) {
      continue;
    }
    for (auto* edge : block->succs()) {
      if (!frontier.count(edge->target())) {
        work_queue.push(edge->target());
      }
    }
  }
  return res;
}

bool does_not_read_mutable_heap(cfg::Block* block) {
  for (auto& mie : InstructionIterable(block)) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (opcode::is_an_aget(op) || opcode::is_an_sget(op) ||
        opcode::is_an_iget(op)) {
      // TODO: It's okay to read from newly created objects.
      return false;
    }
  }
  return true;
}

bool is_pure(cfg::Block* block) {
  for (auto& mie : InstructionIterable(block)) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (opcode::is_an_aput(op) || opcode::is_an_sput(op) ||
        opcode::is_an_iput(op) || opcode::is_fill_array_data(op) ||
        opcode::is_an_invoke(op)) {
      // TODO: It's okay to mutate newly created objects, and to invoke
      // pure methods.
      return false;
    }
    if (opcode::is_a_monitor(op) || opcode::is_throw(op)) {
      // No inherent problem with monitor or throw, just simplifying our life
      // here. TODO: Support.
      return false;
    }
    always_assert(!opcode::has_side_effects(op) || opcode::is_a_return(op) ||
                  opcode::is_branch(op) || opcode::is_an_internal(op));
    // Some of the allowed opcodes have indirect side effects, e.g.
    // new-instance and init-class instructions can trigger static
    // initializers to run, and/or throw exceptions. That is okay, as they are
    // idempotent, and/or might get cleaned up by Local-DCE.
  }
  for (auto* edge : block->succs()) {
    if (edge->type() == cfg::EDGE_THROW) {
      // For simplicity, let's not deal with exception handlers in the pure
      // prefix. Give up for now. TODO: Support.
      return false;
    }
  }
  return true;
}

// Find cold blocks that are reachable from a pure hot prefix.
UnorderedSet<cfg::Block*> propose_cold_frontier(
    const cfg::ControlFlowGraph& cfg) {
  auto normal_blocks = cfg.blocks_reaching_return();
  if (normal_blocks.count(cfg.entry_block()) == 0u) {
    // We are not interested in methods that always throw. Those certainly
    // exist.
    return {};
  }

  std::queue<cfg::Block*> work_queue;
  work_queue.push(cfg.entry_block());
  UnorderedSet<cfg::Block*> cold_frontier;
  UnorderedSet<cfg::Block*> visited_blocks;
  while (!work_queue.empty()) {
    auto* block = work_queue.front();
    work_queue.pop();
    if (!visited_blocks.emplace(block).second) {
      continue;
    }
    if ((normal_blocks.count(block) == 0u) ||
        !source_blocks::maybe_hot(block)) {
      // We ignore blocks that are cold or will eventually throw exception.
      cold_frontier.insert(block);
      continue;
    }
    if (!is_pure(block)) {
      // We have not-cold block that we can't deal with. Give up.
      continue;
    }
    for (auto* edge : block->succs()) {
      always_assert(edge->type() != cfg::EDGE_GHOST);
      work_queue.push(edge->target());
    }
  }
  return cold_frontier;
}

// We have collected cold frontier blocks that are reachable from a pure
// prefix. Remove any blocks that are also reachable through an impure path in
// the residual blocks.
void prune_cold_frontier(const cfg::ControlFlowGraph& cfg,
                         UnorderedSet<cfg::Block*>* cold_frontier) {
  while (true) {
    if (cold_frontier->empty()) {
      return;
    }
    auto residual_blocks = get_forward_reachable_blocks(
        cfg, std::initializer_list<cfg::Block*>{cfg.entry_block()},
        *cold_frontier);
    if (residual_blocks.size() == cfg.num_blocks()) {
      cold_frontier->clear();
      return;
    }
    using cold_frontier_iterator = decltype(cold_frontier->end());
    std::optional<std::pair<cold_frontier_iterator, uint32_t>> to_remove;
    for (auto* cold_frontier_block : cfg.blocks()) {
      auto it = cold_frontier->find(cold_frontier_block);
      if (it == cold_frontier->end()) {
        continue;
      }
      auto closure = get_backwards_reachable_blocks_from(
          cfg, std::initializer_list<cfg::Block*>{cold_frontier_block},
          &residual_blocks);
      if (unordered_all_of(closure, is_pure)) {
        continue;
      }
      uint32_t closure_code_units = 0;
      for (auto* block : UnorderedIterable(closure)) {
        closure_code_units += block->estimate_code_units();
      }
      if (!to_remove || closure_code_units > to_remove->second) {
        to_remove = std::make_pair(it, closure_code_units);
      }
    }
    if (!to_remove) {
      return;
    }
    // There is a way to reach this cold-frontier-to-remove via an impure block
    // in the residual blocks, which wouldn't be idempotent. So we remove this
    // cold-frontier block.
    cold_frontier->erase(to_remove->first);
  }
}

bool starts_with_required_insn(cfg::Block* block) {
  auto first_insn = block->get_first_insn();
  if (first_insn == block->end()) {
    return false;
  }
  auto op = first_insn->insn->opcode();
  return opcode::is_a_move_result_pseudo(op) || opcode::is_move_exception(op);
}

void specialize_hot_code(DexMethod* method,
                         IRCode& code,
                         const UnorderedSet<cfg::Block*>& cold_frontier,
                         DexMethodRef* cold_copy_ref) {
  auto& cfg = code.cfg();
  std::vector<IRInstruction*> arg_copy_insns;
  std::vector<reg_t> arg_copies;
  for (const auto& mie : InstructionIterable(cfg.get_param_instructions())) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    switch (op) {
    case IOPCODE_LOAD_PARAM:
      op = OPCODE_MOVE;
      break;
    case IOPCODE_LOAD_PARAM_OBJECT:
      op = OPCODE_MOVE_OBJECT;
      break;
    case IOPCODE_LOAD_PARAM_WIDE:
      op = OPCODE_MOVE_WIDE;
      break;
    default:
      not_reached();
    }
    auto tmp_reg =
        insn->dest_is_wide() ? cfg.allocate_wide_temp() : cfg.allocate_temp();
    arg_copy_insns.push_back(
        (new IRInstruction(op))->set_src(0, insn->dest())->set_dest(tmp_reg));
    arg_copies.push_back(tmp_reg);
  }
  auto* entry_block = cfg.entry_block();
  auto insert_it = entry_block->get_first_non_param_loading_insn();
  cfg.insert_before(entry_block->to_cfg_instruction_iterator(insert_it),
                    arg_copy_insns);
  auto* new_block = cfg.create_block();
  // Insert dummy position (this will make the stack trace look slightly weird
  // because of a duplicated function, but that shouldn't too confusing)
  if (code.get_debug_item() != nullptr) {
    // Create a fake position.
    cfg.insert_before(new_block,
                      new_block->begin(),
                      DexPosition::make_synthetic_entry_position(method));
  }
  // Insert cold source-block
  auto* template_sb = source_blocks::get_first_source_block(cfg.entry_block());
  always_assert(template_sb);
  new_block->insert_before(new_block->begin(),
                           source_blocks::clone_as_synthetic(
                               template_sb, method, SourceBlock::Val(0, 0)));

  auto* invoke_insn =
      (new IRInstruction(is_static(method) ? OPCODE_INVOKE_STATIC
                                           : OPCODE_INVOKE_DIRECT))
          ->set_method(cold_copy_ref)
          ->set_srcs_size(arg_copy_insns.size());
  for (src_index_t i = 0; i < arg_copies.size(); i++) {
    invoke_insn->set_src(i, arg_copies[i]);
  }
  new_block->push_back(invoke_insn);
  auto* proto = method->get_proto();
  if (proto->is_void()) {
    new_block->push_back(new IRInstruction(OPCODE_RETURN_VOID));
  } else {
    auto* rtype = proto->get_rtype();
    auto tmp_reg = type::is_wide_type(rtype) ? cfg.allocate_wide_temp()
                                             : cfg.allocate_temp();
    auto move_result_op = type::is_object(rtype) ? OPCODE_MOVE_RESULT_OBJECT
                          : type::is_wide_type(rtype) ? OPCODE_MOVE_RESULT_WIDE
                                                      : OPCODE_MOVE_RESULT;
    new_block->push_back(
        (new IRInstruction(move_result_op))->set_dest(tmp_reg));
    auto return_op = type::is_object(rtype)      ? OPCODE_RETURN_OBJECT
                     : type::is_wide_type(rtype) ? OPCODE_RETURN_WIDE
                                                 : OPCODE_RETURN;
    new_block->push_back((new IRInstruction(return_op))->set_src(0, tmp_reg));
  }

  for (auto* block : cfg.blocks()) {
    if (cold_frontier.count(block) == 0u) {
      continue;
    }
    always_assert(!starts_with_required_insn(block));
    auto preds_copy = block->preds();
    for (auto* edge : preds_copy) {
      cfg.set_edge_target(edge, new_block);
    }
  }
  cfg.remove_unreachable_blocks();
}

void specialize_cold_code(
    DexMethod* method,
    cfg::ControlFlowGraph& cfg,
    const UnorderedSet<cfg::Block*>& cold_closure_blocks) {
  std::vector<cfg::Edge*> to_redirect;
  for (auto* block : cfg.blocks()) {
    if (cold_closure_blocks.count(block) == 0u) {
      continue;
    }
    for (auto* edge : block->succs()) {
      if (cold_closure_blocks.count(edge->target()) != 0u) {
        continue;
      }
      always_assert(!starts_with_required_insn(edge->target()));
      to_redirect.push_back(edge);
    }
  }
  auto* new_block = cfg.create_block();
  auto tmp = cfg.allocate_temp();
  // Insert cold source-block
  auto* template_sb = source_blocks::get_first_source_block(cfg.entry_block());
  always_assert(template_sb);
  new_block->insert_before(new_block->begin(),
                           source_blocks::clone_as_synthetic(
                               template_sb, method, SourceBlock::Val(0, 0)));
  new_block->push_back((new IRInstruction(IOPCODE_UNREACHABLE))->set_dest(tmp));
  new_block->push_back((new IRInstruction(OPCODE_THROW))->set_src(0, tmp));
  for (auto* edge : to_redirect) {
    cfg.set_edge_target(edge, new_block);
  }
  cfg.remove_unreachable_blocks();
}

UnorderedSet<cfg::Block*> map(cfg::ControlFlowGraph& target,
                              const UnorderedSet<cfg::Block*>& source) {
  UnorderedSet<cfg::Block*> res;
  res.reserve(source.size());
  for (auto* block : UnorderedIterable(source)) {
    res.insert(target.get_block(block->id()));
  }
  return res;
};

} // namespace

HotColdMethodSpecializingPass::Stats
HotColdMethodSpecializingPass::analyze_and_specialize(
    const Config& config,
    size_t iteration,
    DexMethod* method,
    DexMethod** cold_copy,
    shrinker::Shrinker* shrinker) {
  Stats stats;

  if (shrinker != nullptr) {
    shrinker->shrink_method(method);
    method->get_code()->cfg().reset_exit_block();
  }

  auto& code = *method->get_code();
  auto& cfg = code.cfg();
  if (!source_blocks::is_hot(cfg.entry_block())) {
    // Shouldn't happen, but we are not going to fight that here.
    return stats;
  }

  auto cold_frontier = propose_cold_frontier(cfg);
  stats.proposed_cold_frontier_blocks += cold_frontier.size();
  prune_cold_frontier(cfg, &cold_frontier);
  stats.pruned_cold_frontier_blocks += cold_frontier.size();
  if (cold_frontier.empty()) {
    return stats;
  }

  auto cold_copy_name_str =
      method->get_name()->str() + "$hcms$" + std::to_string(iteration);
  auto* cold_copy_ref = DexMethod::make_method(
      method->get_class(), DexString::make_string(cold_copy_name_str),
      method->get_proto());

  auto hot_code =
      std::make_unique<IRCode>(std::make_unique<cfg::ControlFlowGraph>());
  cfg.deep_copy(&hot_code->cfg());
  specialize_hot_code(method, *hot_code, map(hot_code->cfg(), cold_frontier),
                      cold_copy_ref);

  auto residual_blocks = get_forward_reachable_blocks(
      cfg, std::initializer_list<cfg::Block*>{cfg.entry_block()},
      cold_frontier);
  auto hot_prefix_blocks =
      get_backwards_reachable_blocks_from(cfg, cold_frontier, &residual_blocks);
  always_assert(unordered_all_of(hot_prefix_blocks, is_pure));
  auto cold_code =
      std::make_unique<IRCode>(std::make_unique<cfg::ControlFlowGraph>());
  cfg.deep_copy(&cold_code->cfg());
  // When the "pure" hot prefix involves reading mutable heap memory, the exact
  // taken path in the hot method might not reproduce in the cold method when
  // there are concurrent mutations. In such cases, we cannot predict where we
  // end up when executing the prefix for a second time, and thus we won't
  // insert unreachable instructions then.
  // TODO: More closely inspect which paths through the prefix do not in fact
  // read mutable heap memory, and insert unreachable instructions (only) for
  // those paths.
  if (unordered_all_of(hot_prefix_blocks, does_not_read_mutable_heap)) {
    auto cold_closure_blocks = get_forward_reachable_blocks(cfg, cold_frontier);
    insert_unordered_iterable(cold_closure_blocks, hot_prefix_blocks);
    specialize_cold_code(method, cold_code->cfg(),
                         map(cold_code->cfg(), cold_closure_blocks));
  } else {
    stats.unspecializable_cold_code++;
  }
  if (shrinker != nullptr) {
    shrinker->shrink_code(hot_code.get(), is_static(method),
                          method::is_any_init(method), method->get_class(),
                          method->get_proto(), [&]() { return show(method); });
    shrinker->shrink_code(cold_code.get(), is_static(method),
                          method::is_any_init(method), method->get_class(),
                          method->get_proto(), [&]() { return show(method); });
  }

  auto estimate_adjusted_code_size = [&](auto& code) {
    return code.estimate_code_units() + code.cfg().get_size_adjustment();
  };
  uint32_t original_code_units = estimate_adjusted_code_size(code);
  uint32_t hot_code_units = estimate_adjusted_code_size(*hot_code);
  if (static_cast<float>(hot_code_units) * config.threshold_factor +
          config.threshold_offset >
      static_cast<float>(original_code_units)) {
    stats.methods_with_inefficient_cold_frontier++;
    return stats;
  }

  // Apply changes

  stats.methods_with_efficient_cold_frontier++;
  stats.selected_cold_frontier_blocks += cold_frontier.size();
  stats.original_code_units += original_code_units;
  stats.hot_code_units += hot_code_units;
  stats.cold_code_units += estimate_adjusted_code_size(*cold_code);

  method->set_code(std::move(cold_code));
  *cold_copy = DexMethod::make_method_from(method, method->get_class(),
                                           cold_copy_ref->get_name());
  always_assert(*cold_copy == cold_copy_ref);
  if (method->is_virtual()) {
    (*cold_copy)->set_virtual(false);
    set_private(*cold_copy);
  }
  (*cold_copy)->rstate.set_generated();
  (*cold_copy)->rstate.set_dont_inline();
  (*cold_copy)->set_deobfuscated_name(show(*cold_copy));
  source_blocks::fill_source_block_entry_values((*cold_copy)->get_code()->cfg(),
                                                SourceBlock::Val(0, 0));

  method->set_code(std::move(hot_code));

  return stats;
}

void HotColdMethodSpecializingPass::bind_config() {
  bind("threshold_factor", m_config.threshold_factor,
       m_config.threshold_factor);
  bind("threshold_offset", m_config.threshold_offset,
       m_config.threshold_offset);
  bind("blocklist", m_config.blocklist, m_config.blocklist);
}

void HotColdMethodSpecializingPass::run_pass(DexStoresVector& stores,
                                             ConfigFiles& conf,
                                             PassManager& mgr) {
  if (g_redex->instrument_mode) {
    return;
  }

  auto scope = build_class_scope(stores);
  auto min_sdk = mgr.get_redex_options().min_sdk;
  auto mog = method_override_graph::build_graph(scope);
  auto non_true_virtuals =
      method_override_graph::get_non_true_virtuals(*mog, scope);

  shrinker::ShrinkerConfig shrinker_config;
  shrinker_config.run_const_prop = true;
  shrinker_config.run_cse = false;
  shrinker_config.run_copy_prop = true;
  shrinker_config.run_local_dce = true;
  shrinker_config.compute_pure_methods = false;

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  shrinker::Shrinker shrinker(stores, scope, init_classes_with_side_effects,
                              conf, shrinker_config, min_sdk);

  Stats stats;
  std::mutex stats_mutex;
  InsertOnlyConcurrentMap<DexClass*, std::vector<DexMethod*>>
      specialized_methods_by_class;
  walk::parallel::classes(scope, [&](DexClass* cls) {
    for (auto& str : m_config.blocklist) {
      if (cls->get_deobfuscated_name_or_empty().starts_with(str)) {
        return;
      }
    }

    std::vector<DexMethod*> specialized_methods;
    for (auto* method : cls->get_all_methods()) {
      if ((method->get_code() == nullptr) || method::is_any_init(method) ||
          method->rstate.no_optimizations() ||
          method->rstate.should_not_outline()) {
        continue;
      }
      if (method->is_virtual() && (non_true_virtuals.count(method) == 0u)) {
        continue;
      }

      DexMethod* cold_copy{nullptr};
      auto local_stats = analyze_and_specialize(m_config, m_iteration, method,
                                                &cold_copy, &shrinker);
      if (local_stats.empty()) {
        continue;
      }

      {
        std::lock_guard<std::mutex> m_lock(stats_mutex);
        stats += local_stats;
      }

      if (cold_copy == nullptr) {
        continue;
      }

      TRACE(HCMS, 5, "=== %s (%u => %u + %u)\n--- hot:\n%s\n--- cold:\n%s",
            SHOW(method), (unsigned)local_stats.original_code_units,
            (unsigned)local_stats.hot_code_units,
            (unsigned)local_stats.cold_code_units,
            SHOW(method->get_code()->cfg()),
            SHOW(cold_copy->get_code()->cfg()));

      specialized_methods.push_back(cold_copy);
    }

    if (!specialized_methods.empty()) {
      specialized_methods_by_class.emplace(cls, std::move(specialized_methods));
    }
  });

  // Add specialized methods to their owning classes
  UnorderedBag<DexClass*> classes;
  for (auto& p : UnorderedIterable(specialized_methods_by_class)) {
    classes.insert(p.first);
  }
  workqueue_run<DexClass*>(
      [&](DexClass* cls) {
        for (auto* method : specialized_methods_by_class.at_unsafe(cls)) {
          cls->add_method(method);
        }
      },
      classes);

  TRACE(HCMS,
        1,
        "Methods with efficient cold frontiers: %zu",
        (size_t)stats.methods_with_efficient_cold_frontier);
  TRACE(HCMS,
        1,
        "Methods with inefficient cold frontiers: %zu",
        (size_t)stats.methods_with_inefficient_cold_frontier);
  TRACE(HCMS, 1, "Proposed cold frontiers: %zu",
        (size_t)stats.proposed_cold_frontier_blocks);
  TRACE(HCMS, 1, "Pruned cold frontiers: %zu",
        (size_t)stats.pruned_cold_frontier_blocks);
  TRACE(HCMS, 1, "Selected cold frontiers: %zu",
        (size_t)stats.selected_cold_frontier_blocks);
  TRACE(HCMS, 1, "Original code units: %zu", (size_t)stats.original_code_units);
  TRACE(HCMS, 1, "Hot code units: %zu", (size_t)stats.hot_code_units);
  TRACE(HCMS, 1, "Cold code units: %zu", (size_t)stats.cold_code_units);
  TRACE(HCMS, 1, "Unspecializable cold code: %zu",
        (size_t)stats.unspecializable_cold_code);

  mgr.set_metric("methods_with_efficient_cold_frontier",
                 stats.methods_with_efficient_cold_frontier);
  mgr.set_metric("methods_with_inefficient_cold_frontier",
                 stats.methods_with_inefficient_cold_frontier);
  mgr.set_metric("proposed_cold_frontier_blocks",
                 stats.proposed_cold_frontier_blocks);
  mgr.set_metric("pruned_cold_frontier_blocks",
                 stats.pruned_cold_frontier_blocks);
  mgr.set_metric("selected_cold_frontier_blocks",
                 stats.selected_cold_frontier_blocks);
  mgr.set_metric("original_code_units", stats.original_code_units);
  mgr.set_metric("hot_code_units", stats.hot_code_units);
  mgr.set_metric("cold_code_units", stats.cold_code_units);
  mgr.set_metric("unspecializable_cold_code", stats.unspecializable_cold_code);
  m_iteration++;
}

static HotColdMethodSpecializingPass s_pass;
