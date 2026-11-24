/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ObjectSensitiveDce.h"

#include "CFGMutation.h"
#include "ClassHierarchy.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DexUtil.h"
#include "HierarchyUtil.h"
#include "InitClassPruner.h"
#include "InitClassesWithSideEffects.h"
#include "LocalPointersAnalysis.h"
#include "MethodUtil.h"
#include "TypeUtil.h"
#include "UsedVarsAnalysis.h"
#include "Walkers.h"

namespace hier = hierarchy_util;
namespace ptrs = local_pointers;
namespace uv = used_vars;

namespace {

class CallGraphStrategy final : public ptrs::EscapeCallGraphStrategy {
 public:
  explicit CallGraphStrategy(const method_override_graph::Graph& graph,
                             const Scope& scope,
                             const UnorderedSet<DexMethodRef*>& pure_methods,
                             const ptrs::SummaryMap& escape_summaries,
                             const side_effects::SummaryMap& effect_summaries,
                             uint32_t big_override_threshold)
      : ptrs::EscapeCallGraphStrategy(graph, scope, big_override_threshold),
        m_pure_methods(pure_methods),
        m_escape_summaries(escape_summaries),
        m_effect_summaries(effect_summaries) {}

 private:
  // A pure call that returns no object interacts with no object and has no
  // side effects, so it gets the empty summaries.
  bool is_object_free_call(const IRInstruction* insn,
                           const DexMethod* callee) const override {
    return is_pure(insn) && !type::is_object(callee->get_proto()->get_rtype());
  }

  bool has_external_summary(const DexMethod* callee) const override {
    return ptrs::EscapeCallGraphStrategy::has_external_summary(callee) ||
           ((m_escape_summaries.count(callee) != 0u) &&
            (m_effect_summaries.count(callee) != 0u));
  }

  bool is_pure(const IRInstruction* insn) const {
    // This is what LocalDce does.
    auto* ref = insn->get_method();
    auto* const meth = resolve_method_deprecated(ref, opcode_to_search(insn));
    if (meth == nullptr) {
      return false;
    }
    if (::assumenosideeffects(meth)) {
      return true;
    }
    return m_pure_methods.count(ref) != 0u;
  }

  const UnorderedSet<DexMethodRef*>& m_pure_methods;
  const ptrs::SummaryMap& m_escape_summaries;
  const side_effects::SummaryMap& m_effect_summaries;
};

} // namespace

void ObjectSensitiveDce::dce() {
  walk::parallel::code(m_scope, [&](const DexMethod* /*method*/, IRCode& code) {
    always_assert(code.cfg_built());
    // The backwards used_vars::FixpointIterator analysis will need it later.
    code.cfg().calculate_exit_block();
  });
  auto call_graph = call_graph::Graph(CallGraphStrategy(
      m_method_override_graph, m_scope, m_pure_methods, *m_escape_summaries,
      *m_effect_summaries, m_big_override_threshold));
  auto class_hierarchy = build_internal_type_hierarchy(m_scope);

  // R8 does not remove a new instance instruction if the class defines a
  // finalize method So we do the same here.
  auto excluded_classes =
      method_override_graph::get_classes_with_overridden_finalize(
          m_method_override_graph, class_hierarchy);
  auto analyze_scope_result = ptrs::analyze_scope(
      m_scope, call_graph, m_escape_summaries, &excluded_classes);
  auto& ptrs_fp_iter_map = analyze_scope_result.data;
  m_stats.lpa_iterations = analyze_scope_result.iterations;

  side_effects::analyze_scope(*m_init_classes_with_side_effects, m_scope,
                              call_graph, ptrs_fp_iter_map, m_effect_summaries);

  std::atomic<size_t> removed{0};
  std::atomic<size_t> init_class_instructions_added{0};
  std::mutex init_class_stats_mutex;
  init_classes::Stats init_class_stats;
  std::mutex invokes_with_summaries_mutex;
  UnorderedMap<uint16_t, size_t> invokes_with_summaries{0};

  walk::parallel::code(m_scope, [&](DexMethod* method, IRCode& code) {
    if (!method::is_optimizable(method)) {
      return;
    }
    auto& cfg = code.cfg();
    auto summary_map =
        build_summary_map(*m_effect_summaries, call_graph, method);
    UnorderedMap<uint32_t, size_t> local_invokes_with_summaries;
    for (auto&& [insn, summary] : UnorderedIterable(summary_map)) {
      if (summary.effects == 0u) {
        local_invokes_with_summaries[insn->opcode()]++;
      }
    }
    uv::FixpointIterator used_vars_fp_iter(*ptrs_fp_iter_map.at_unsafe(method),
                                           std::move(summary_map), cfg, method);
    used_vars_fp_iter.run(uv::UsedVarsSet());

    cfg::CFGMutation mutator(cfg);

    TRACE(OSDCE, 5, "Transforming %s", SHOW(method));
    TRACE(OSDCE, 5, "Before:\n%s", SHOW(cfg));
    auto dead_instructions =
        used_vars::get_dead_instructions(cfg, used_vars_fp_iter);
    auto local_init_class_instructions_added = 0;
    for (const auto& dead : dead_instructions) {
      // This logging is useful for quantifying what gets removed. E.g. to
      // see all the removed callsites: grep "^DEAD.*INVOKE[^ ]*" log |
      // grep " L.*$" -Po | sort | uniq -c
      TRACE(OSDCE, 3, "DEAD: %s", SHOW(dead->insn));
      auto* init_class_insn =
          m_init_classes_with_side_effects->create_init_class_insn(
              get_init_class_type_demand(dead->insn));
      if (init_class_insn != nullptr) {
        mutator.replace(dead, {init_class_insn});
        local_init_class_instructions_added++;
      } else {
        mutator.remove(dead);
      }
    }

    mutator.flush();

    cfg.remove_unreachable_blocks();
    TRACE(OSDCE, 5, "After:\n%s", SHOW(cfg));
    if (!dead_instructions.empty()) {
      removed += dead_instructions.size();
      if (local_init_class_instructions_added > 0) {
        init_class_instructions_added += local_init_class_instructions_added;
        init_classes::InitClassPruner init_class_pruner(
            *m_init_classes_with_side_effects, method->get_class(), cfg);
        init_class_pruner.apply();
        std::lock_guard lock_guard(init_class_stats_mutex);
        init_class_stats += init_class_pruner.get_stats();
      }
    }

    std::lock_guard<std::mutex> lock(invokes_with_summaries_mutex);
    for (auto&& [opcode, count] :
         UnorderedIterable(local_invokes_with_summaries)) {
      invokes_with_summaries[opcode] += count;
    }
  });

  m_stats.removed_instructions = (size_t)removed;
  m_stats.init_class_instructions_added = init_class_instructions_added;
  m_stats.init_class_stats = init_class_stats;
  for (auto&& [_, summary] : UnorderedIterable(*m_effect_summaries)) {
    if (summary.effects == 0u) {
      m_stats.methods_with_summaries++;
    }
    m_stats.modified_params += summary.modified_params.size();
  }
  m_stats.invokes_with_summaries = invokes_with_summaries;
  TRACE(OSDCE, 1, "%zu methods with summaries, removed %zu instructions",
        m_stats.methods_with_summaries, m_stats.removed_instructions);
}
