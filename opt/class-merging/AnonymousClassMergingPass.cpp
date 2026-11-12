/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Model.h"

#include "AnonymousClassMergingPass.h"

#include "ClassMerging.h"
#include "ConfigFiles.h"
#include "ConfigUtils.h"
#include "DexUtil.h"
#include "InterDexGrouping.h"
#include "MergingStrategies.h"
#include "ModelSpecGenerator.h"
#include "PassManager.h"
#include "Trace.h"

namespace class_merging {

void AnonymousClassMergingPass::bind_config() {
  std::vector<std::string> excl_names;
  bind("exclude",
       {},
       excl_names,
       "Do not merge the classes or its implementors");
  utils::load_types_and_prefixes(excl_names, m_merging_spec.exclude_types,
                                 m_merging_spec.exclude_prefixes);
  bind("include_primary_dex", false, m_merging_spec.include_primary_dex);
  bind("global_min_count",
       500,
       m_global_min_count,
       "Ignore interface or class hierarchies with less than "
       "global_min_count implementors or subclasses");
  bind("min_count",
       2,
       m_min_count,
       "Minimum mergeable class count per merging group");
  bind("max_count",
       50,
       m_max_count,
       "Maximum mergeable class count per merging group");
  bind("use_stable_shape_names", false, m_merging_spec.use_stable_shape_names);
  bind("preserve_unanimous_field_types", false,
       m_merging_spec.preserve_unanimous_field_types,
       "Keep unanimous reference slot types when they are safe to reference.");
  std::string interdex_grouping;
  bind("interdex_grouping", "non-ordered-set", interdex_grouping);
  // Inferring_mode is "class-loads" by default.
  m_merging_spec.interdex_config.init_type(interdex_grouping);
  bind("hot_cold_grouping", false, m_merging_spec.hot_cold_grouping,
       "Split each merging group into hot and cold mergeables");
}

void AnonymousClassMergingPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles& conf,
                                         PassManager& mgr) {
  mgr.set_metric("num_merged_volatile_fields", 0);
  mgr.set_metric("num_merged_final_fields", 0);
  // Fill the merging configurations.
  m_merging_spec.name = "Anonymous Classes";
  m_merging_spec.class_name_prefix = "Anon";
  m_merging_spec.strategy = strategy::BY_REFS;
  if (conf.force_single_dex() ||
      (!stores.empty() && stores[0].num_dexes() == 1)) {
    m_merging_spec.include_primary_dex = true;
  }
  m_merging_spec.dedup_fill_in_stack_trace = false;
  m_merging_spec.min_count = m_min_count;
  if (m_max_count > 0) {
    m_merging_spec.max_count = m_max_count;
  }

  auto scope = build_class_scope(stores);
  TypeSystem type_system(scope);
  find_all_mergeables_and_roots(type_system, scope, m_global_min_count, mgr,
                                &m_merging_spec);
  if (!m_merging_spec.roots.empty()) {
    virtual_scope::VirtualScopes vscopes(scope);
    class_merging::merge_model(type_system, vscopes, scope, conf, mgr, stores,
                               m_merging_spec, false);
    post_dexen_changes(scope, stores);
  } else {
    TRACE(CLMG, 2, "No enough anonymous classes to merge");
  }
}

static AnonymousClassMergingPass s_pass;

} // namespace class_merging
