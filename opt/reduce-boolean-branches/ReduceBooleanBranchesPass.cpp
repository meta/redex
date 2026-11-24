/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReduceBooleanBranchesPass.h"

#include "CopyPropagation.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "LocalDce.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Purity.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

constexpr const char* METRIC_BOOLEAN_BRANCHES_REMOVED =
    "num_boolean_branches_removed";
constexpr const char* METRIC_OBJECT_BRANCHES_REMOVED =
    "num_object_branches_removed";
constexpr const char* METRIC_XORS_REDUCED = "num_xors_reduced";

} // namespace

void ReduceBooleanBranchesPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles& /* unused */,
                                         PassManager& mgr) {
  auto scope = build_class_scope(stores);

  copy_propagation_impl::Config copy_prop_config;
  copy_prop_config.eliminate_const_classes = false;
  copy_prop_config.eliminate_const_strings = false;
  copy_prop_config.static_finals = false;
  auto pure_methods = get_pure_methods();
  auto stats = walk::parallel::methods<reduce_boolean_branches_impl::Stats>(
      scope, [&config = m_config, &copy_prop_config,
              &pure_methods](DexMethod* method) {
        auto* const code = method->get_code();
        if (!method::is_optimizable(method)) {
          return reduce_boolean_branches_impl::Stats{};
        }
        always_assert(code->cfg_built());
        reduce_boolean_branches_impl::ReduceBooleanBranches rbb(
            config, is_static(method), method->get_proto()->get_args(), code);
        while (rbb.run()) {
          // clean up
          copy_propagation_impl::CopyPropagation copy_propagation(
              copy_prop_config);
          copy_propagation.run(code, method);
          LocalDce(/* init_classes_with_side_effects */ nullptr, pure_methods)
              .dce(code);
        }

        return rbb.get_stats();
      });

  mgr.incr_metric(METRIC_BOOLEAN_BRANCHES_REMOVED,
                  stats.boolean_branches_removed);
  mgr.incr_metric(METRIC_OBJECT_BRANCHES_REMOVED,
                  stats.object_branches_removed);
  mgr.incr_metric(METRIC_XORS_REDUCED, stats.xors_reduced);
  TRACE(RBB, 1,
        "[reduce boolean branches] Removed %zu boolean branches, %zu object "
        "branches, reduced %zu xors",
        stats.boolean_branches_removed, stats.object_branches_removed,
        stats.xors_reduced);
}

static ReduceBooleanBranchesPass s_pass;
