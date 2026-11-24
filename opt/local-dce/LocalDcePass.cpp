/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LocalDcePass.h"

#include "ConfigFiles.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "LocalDce.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Purity.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

constexpr const char* METRIC_NPE_INSTRUCTIONS = "num_npe_instructions";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS_ADDED =
    "num_init_class_instructions_added";
constexpr const char* METRIC_DEAD_INSTRUCTIONS = "num_dead_instructions";
constexpr const char* METRIC_UNREACHABLE_INSTRUCTIONS =
    "num_unreachable_instructions";
constexpr const char* METRIC_NORMALIZED_NEW_INSTANCES =
    "num_normalized_new_instances";
constexpr const char* METRIC_ALIASED_NEW_INSTANCES =
    "num_aliased_new_instances";
constexpr const char* METRIC_COMPUTED_NO_SIDE_EFFECTS_METHODS =
    "num_computed_no_side_effects_methods";
constexpr const char* METRIC_COMPUTED_NO_SIDE_EFFECTS_METHODS_ITERATIONS =
    "num_computed_no_side_effects_methods_iterations";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS =
    "num_init_class_instructions";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS_REMOVED =
    "num_init_class_instructions_removed";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS_REFINED =
    "num_init_class_instructions_refined";

} // namespace

void LocalDcePass::run_pass(DexStoresVector& stores,
                            ConfigFiles& conf,
                            PassManager& mgr) {
  auto scope = build_class_scope(stores);

  auto pure_methods = get_pure_methods();
  auto configured_pure_methods = conf.get_pure_methods();
  insert_unordered_iterable(pure_methods, configured_pure_methods);
  auto immutable_getters = get_immutable_getters(scope);
  insert_unordered_iterable(pure_methods, immutable_getters);
  std::unique_ptr<const method_override_graph::Graph> override_graph;
  if (!mgr.unreliable_virtual_scopes()) {
    override_graph = method_override_graph::build_graph(scope);
  }
  std::unique_ptr<init_classes::InitClassesWithSideEffects>
      init_classes_with_side_effects;
  if (!mgr.init_class_lowering_has_run()) {
    init_classes_with_side_effects =
        std::make_unique<init_classes::InitClassesWithSideEffects>(
            scope, conf.create_init_class_insns(), override_graph.get());
  }

  UnorderedSet<const DexMethod*> computed_no_side_effects_methods;
  size_t computed_no_side_effects_methods_iterations = 0;
  if (!mgr.unreliable_virtual_scopes()) {
    method::ClInitHasNoSideEffectsPredicate clinit_has_no_side_effects =
        [&](const DexType* type) {
          return !init_classes_with_side_effects ||
                 (init_classes_with_side_effects->refine(type) == nullptr);
        };
    computed_no_side_effects_methods_iterations =
        compute_no_side_effects_methods(
            scope, override_graph.get(), clinit_has_no_side_effects,
            pure_methods, &computed_no_side_effects_methods);
    for (const auto* m : UnorderedIterable(computed_no_side_effects_methods)) {
      pure_methods.insert(const_cast<DexMethod*>(m));
    }
  }

  if (mgr.materialize_nullchecks_has_run()) {
    // If MaterializeNullchecksPass is run,
    // "Ljava/lang/Object;.getClass:()Ljava/lang/Class;" will be used to keep
    // proper null check and it shouldn't be deleted. Therefore, we remove it
    // from pure method list.
    DexMethodRef* getClassRef = DexMethod::get_method(
        "Ljava/lang/Object;.getClass:()Ljava/lang/Class;");
    if (getClassRef != nullptr) {
      pure_methods.erase(getClassRef);
    }
  }

  bool may_allocate_registers = !mgr.regalloc_has_run();
  if (!may_allocate_registers) {
    // compute_no_side_effects_methods might have found methods that have no
    // implementors. Let's not silently remove invocations to those in LocalDce,
    // as invoking them *will* unconditionally cause an exception.
    unordered_erase_if(pure_methods, [&](auto* m) {
      return m->is_def() && !has_implementor(override_graph.get(), m->as_def());
    });
  }

  bool may_remove_nops = !mgr.nopper_has_run();

  auto stats =
      walk::parallel::methods<LocalDce::Stats>(scope, [&](DexMethod* m) {
        auto* code = m->get_code();
        if (!method::is_optimizable(m)) {
          return LocalDce::Stats();
        }

        LocalDce ldce(init_classes_with_side_effects.get(), pure_methods,
                      override_graph.get(), may_allocate_registers,
                      /* ignore_pure_method_init_classes */ false,
                      may_remove_nops);
        ldce.dce(code, /* normalize_new_instances */ true, m->get_class());
        return ldce.get_stats();
      });
  mgr.incr_metric(METRIC_NPE_INSTRUCTIONS, stats.npe_instruction_count);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS_ADDED,
                  stats.init_class_instructions_added);
  mgr.incr_metric(METRIC_DEAD_INSTRUCTIONS, stats.dead_instruction_count);
  mgr.incr_metric(METRIC_UNREACHABLE_INSTRUCTIONS,
                  stats.unreachable_instruction_count);
  mgr.incr_metric(METRIC_NORMALIZED_NEW_INSTANCES,
                  stats.normalized_new_instances);
  mgr.incr_metric(METRIC_ALIASED_NEW_INSTANCES, stats.aliased_new_instances);
  mgr.incr_metric(METRIC_COMPUTED_NO_SIDE_EFFECTS_METHODS,
                  computed_no_side_effects_methods.size());
  mgr.incr_metric(METRIC_COMPUTED_NO_SIDE_EFFECTS_METHODS_ITERATIONS,
                  computed_no_side_effects_methods_iterations);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS,
                  stats.init_classes.init_class_instructions);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS_REMOVED,
                  stats.init_classes.init_class_instructions_removed);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS_REFINED,
                  stats.init_classes.init_class_instructions_refined);
  TRACE(DCE, 1,
        "instructions removed -- npe: %zu, dead: %zu, init-class added: %zu, "
        "unreachable: %zu; "
        "normalized %zu new-instance instructions, %zu aliased",
        stats.npe_instruction_count, stats.dead_instruction_count,
        stats.init_class_instructions_added,
        stats.unreachable_instruction_count, stats.normalized_new_instances,
        stats.aliased_new_instances);
}

static LocalDcePass s_pass;
