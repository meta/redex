/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Debug.h"
#include "Model.h"

#include "ClassMerging.h"
#include "ConfigUtils.h"
#include "InterDexGrouping.h"
#include "InterDexPass.h"
#include "IntraDexClassMergingPass.h"
#include "ModelSpecGenerator.h"
#include "PassManager.h"
#include "Trace.h"

namespace class_merging {
void IntraDexClassMergingPass::bind_config() {
  std::vector<std::string> excl_names;
  bind("exclude",
       {},
       excl_names,
       "Do not merge the classes or its implementors");
  utils::load_types_and_prefixes(excl_names, m_merging_spec.exclude_types,
                                 m_merging_spec.exclude_prefixes);
  bind("global_min_count",
       4,
       m_global_min_count,
       "Ignore interface or class hierarchies with less than global_min_count "
       "implementors or subclasses");
  bind("min_count",
       2,
       m_merging_spec.min_count,
       "Minimal number of mergeables to be merged together");
  size_t max_count;
  bind("max_count",
       50,
       max_count,
       "Maximum mergeable class count per merging group");
  if (max_count > 0) {
    m_merging_spec.max_count = std::optional<size_t>(max_count);
  }
  bind("use_stable_shape_names", false, m_merging_spec.use_stable_shape_names);
  bind("preserve_unanimous_field_types", false,
       m_merging_spec.preserve_unanimous_field_types,
       "Keep unanimous reference slot types when they are safe to reference.");
  bind("mergeability_checks_use_of_const_class", false,
       m_merging_spec.mergeability_checks_use_of_const_class);
  std::string interdex_grouping;
  bind("interdex_grouping", "non-ordered-set", interdex_grouping);
  m_merging_spec.interdex_config.init_type(interdex_grouping);
  // Inferring_mode is "class-loads" by default.
  std::string interdex_grouping_inferring_mode;
  bind("interdex_grouping_inferring_mode", "class-loads",
       interdex_grouping_inferring_mode);
  m_merging_spec.interdex_config.init_inferring_mode(
      interdex_grouping_inferring_mode);
  bind("hot_cold_grouping", false, m_merging_spec.hot_cold_grouping,
       "Split each merging group into hot and cold mergeables");
  bind("enable_reshuffle", true, m_enable_reshuffle);
  bind("enable_mergeability_aware_reshuffle", true,
       m_enable_mergeability_aware_reshuffle);
  // Bind reshuffle config.
  bind("reserved_extra_frefs",
       m_reshuffle_config.reserved_extra_frefs,
       m_reshuffle_config.reserved_extra_frefs,
       "How many extra frefs to be reserved for the dexes this pass "
       "processes.");
  bind("reserved_extra_trefs",
       m_reshuffle_config.reserved_extra_trefs,
       m_reshuffle_config.reserved_extra_trefs,
       "How many extra trefs to be reserved for the dexes this pass "
       "processes.");
  bind("reserved_extra_mrefs",
       m_reshuffle_config.reserved_extra_mrefs,
       m_reshuffle_config.reserved_extra_mrefs,
       "How many extra mrefs to be reserved for the dexes this pass "
       "processes.");
  bind("extra_linear_alloc_limit",
       m_reshuffle_config.extra_linear_alloc_limit,
       m_reshuffle_config.extra_linear_alloc_limit,
       "How many extra linear_alloc_limit to be reserved for the dexes "
       "this pass processes.");
  bind("max_batches",
       m_reshuffle_config.max_batches,
       m_reshuffle_config.max_batches,
       "How many batches to execute. More might yield better results, but "
       "might take longer.");
  bind("max_batch_size",
       m_reshuffle_config.max_batch_size,
       m_reshuffle_config.max_batch_size,
       "How many class to move per batch. More might yield better results, "
       "but might take longer.");
  bind("other_weight",
       m_reshuffle_config.other_weight,
       m_reshuffle_config.other_weight,
       "Weight for non-deduped method in mergeability-aware reshuffle cost "
       "function.");
  bind("deduped_weight",
       m_reshuffle_config.deduped_weight,
       m_reshuffle_config.deduped_weight,
       "Weight for deduped method in mergeability-aware reshuffle cost "
       "function.");
  bind("exclude_below20pct_coldstart_classes",
       false,
       m_reshuffle_config.exclude_below20pct_coldstart_classes,
       "Whether to exclude coldstart classes in between 1pctColdStart and "
       "20pctColdStart marker"
       "from the reshuffle.");
}

void IntraDexClassMergingPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  mgr.set_metric("num_merged_volatile_fields", 0);
  mgr.set_metric("num_merged_final_fields", 0);
  // Fill the merging configurations.
  m_merging_spec.name = "Intra Dex";
  m_merging_spec.class_name_prefix = "IDx";
  // The merging strategy can be tuned.
  m_merging_spec.strategy = strategy::BY_CODE_SIZE;
  // TODO: Can merge FULL interdex groups.
  m_merging_spec.per_dex_grouping = true;
  m_merging_spec.dedup_fill_in_stack_trace = false;

  const auto* interdex_pass =
      dynamic_cast<interdex::InterDexPass*>(mgr.find_pass("InterDexPass"));
  always_assert_log(interdex_pass, "InterDexPass missing");
  // If dynamically-dead-classes are reordered in InterDexPass, should not merge
  // those classes.
  bool skip_dynamically_dead =
      interdex_pass->reorder_dynamically_dead_classes();

  auto scope = build_class_scope(stores);
  TypeSystem type_system(scope);
  find_all_mergeables_and_roots(type_system, scope, m_global_min_count, mgr,
                                &m_merging_spec, skip_dynamically_dead);
  if (m_merging_spec.roots.empty()) {
    TRACE(CLMG, 1, "No mergeable classes found by IntraDexClassMergingPass");
    return;
  }

  virtual_scope::VirtualScopes vscopes(scope);

  auto& root_store = stores.at(0);
  auto& root_dexen = root_store.get_dexen();
  if (m_enable_reshuffle && interdex_pass->minimize_cross_dex_refs() &&
      root_dexen.size() > 1) {
    if (m_enable_mergeability_aware_reshuffle) {
      class_merging::Model merging_model =
          class_merging::construct_global_model(
              type_system, vscopes, scope, mgr, conf, stores, m_merging_spec,
              m_global_min_count);
      InterDexReshuffleImpl impl(
          conf, mgr, m_reshuffle_config, scope, root_dexen,
          interdex_pass->get_dynamically_dead_dexes(), &merging_model);
      impl.compute_plan();
      impl.apply_plan();
    } else {
      InterDexReshuffleImpl impl(conf, mgr, m_reshuffle_config, scope,
                                 root_dexen,
                                 interdex_pass->get_dynamically_dead_dexes());
      impl.compute_plan();
      impl.apply_plan();
    }
    // Sanity check
    UnorderedSet<DexClass*> original_scope_set(scope.begin(), scope.end());
    scope = build_class_scope(stores);
    UnorderedSet<DexClass*> new_scope_set(scope.begin(), scope.end());
    always_assert(unordered_equal(original_scope_set, new_scope_set));
  }

  mgr.set_metric("num_spec_merging_targets",
                 m_merging_spec.merging_targets.size());
  mgr.set_metric("num_spec_excluded_types",
                 m_merging_spec.exclude_types.size());

  class_merging::merge_model(type_system, vscopes, scope, conf, mgr, stores,
                             m_merging_spec, true /* is_intra_dex */);

  post_dexen_changes(scope, stores);

  // For interface roots, the num_roots count is not accurate. It counts the
  // total number of unique common base classes among the implementors, not the
  // common interface roots.
  mgr.set_metric("num_roots", m_merging_spec.roots.size());

  m_merging_spec.merging_targets.clear();
  m_merging_spec.roots.clear();
}

static IntraDexClassMergingPass s_intra_dex_merging_pass;
} // namespace class_merging
