/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Reachability.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"

class FlowSensitiveReachabilityTest : public RedexIntegrationTest {};

TEST_F(FlowSensitiveReachabilityTest,
       relaxed_keep_class_members_and_cfg_gathering_check_instantiable) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void root();
    }
  )");

  EXPECT_TRUE(pg_config->ok);
  EXPECT_EQ(pg_config->keep_rules.size(), 1);

  int num_ignore_check_strings = 0;
  reachability::IgnoreSets ig_sets;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ false,
      /* cfg_gathering_check_instantiable */ true);

  //// instantiable_types
  EXPECT_EQ(reachable_aspects.instantiable_types.size(), 5);
  auto is_instantiable = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.instantiable_types,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_instantiable("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_instantiable("LData;"));
  EXPECT_FALSE(is_instantiable("LDataHolder;"));
  EXPECT_FALSE(is_instantiable("LLegacyInstantiable;"));
  EXPECT_TRUE(is_instantiable("LStringInstantiable;"));
  EXPECT_TRUE(is_instantiable("LBase;"));
  EXPECT_TRUE(is_instantiable("LIntermediate;"));
  EXPECT_TRUE(is_instantiable("LRegularInstantiable;"));

  //// dynamically_referenced_classes
  EXPECT_EQ(reachable_aspects.dynamically_referenced_classes.size(), 2);
  auto is_dynamically_referenced = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.dynamically_referenced_classes,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_FALSE(is_dynamically_referenced("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_dynamically_referenced("LData;"));
  EXPECT_FALSE(is_dynamically_referenced("LDataHolder;"));
  EXPECT_FALSE(is_dynamically_referenced("LLegacyInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LStringInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LRegularInstantiable;"));

  //// instructions_unvisited
  EXPECT_GT(reachable_aspects.instructions_unvisited, 0);

  //// uninstantiable_dependencies
  EXPECT_EQ(reachable_aspects.uninstantiable_dependencies.size(), 1);
  auto is_uninstantiable_dependency = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.uninstantiable_dependencies,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_uninstantiable_dependency("LDataHolder;"));

  // Code sweeping
  remove_uninstantiables_impl::Stats remove_uninstantiables_stats;
  std::atomic<size_t> throws_inserted{0};
  InsertOnlyConcurrentSet<DexMethod*> affected_methods;
  reachability::sweep_code(
      stores, /* prune_uncallable_instance_method_bodies */ false,
      /* skip_uncallable_virtual_methods */ false, reachable_aspects,
      &remove_uninstantiables_stats, &throws_inserted, &affected_methods);
  EXPECT_EQ(remove_uninstantiables_stats.field_accesses_on_uninstantiable, 3);
  EXPECT_EQ(remove_uninstantiables_stats.invokes, 7);
  EXPECT_EQ(remove_uninstantiables_stats.check_casts, 1);
  EXPECT_EQ(remove_uninstantiables_stats.instance_ofs, 1);

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
}

TEST_F(FlowSensitiveReachabilityTest, cfg_gathering_check_instance_callable) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void root();
    }
  )");

  EXPECT_TRUE(pg_config->ok);
  EXPECT_EQ(pg_config->keep_rules.size(), 1);

  int num_ignore_check_strings = 0;
  reachability::IgnoreSets ig_sets;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ false,
      /* cfg_gathering_check_instantiable */ true,
      /* cfg_gathering_check_instance_callable */ true);

  //// instantiable_types
  EXPECT_EQ(reachable_aspects.instantiable_types.size(), 5);
  auto is_instantiable = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.instantiable_types,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_instantiable("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_instantiable("LData;"));
  EXPECT_FALSE(is_instantiable("LDataHolder;"));
  EXPECT_FALSE(is_instantiable("LLegacyInstantiable;"));
  EXPECT_TRUE(is_instantiable("LStringInstantiable;"));
  EXPECT_TRUE(is_instantiable("LBase;"));
  EXPECT_TRUE(is_instantiable("LIntermediate;"));
  EXPECT_TRUE(is_instantiable("LRegularInstantiable;"));

  //// dynamically_referenced_classes
  EXPECT_EQ(reachable_aspects.dynamically_referenced_classes.size(), 2);
  auto is_dynamically_referenced = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.dynamically_referenced_classes,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_FALSE(is_dynamically_referenced("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_dynamically_referenced("LData;"));
  EXPECT_FALSE(is_dynamically_referenced("LDataHolder;"));
  EXPECT_FALSE(is_dynamically_referenced("LLegacyInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LStringInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LRegularInstantiable;"));

  //// instructions_unvisited
  EXPECT_GT(reachable_aspects.instructions_unvisited, 0);

  //// uninstantiable_dependencies
  EXPECT_EQ(reachable_aspects.uninstantiable_dependencies.size(), 1);
  auto is_uninstantiable_dependency = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.uninstantiable_dependencies,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_uninstantiable_dependency("LDataHolder;"));

  // Code sweeping
  remove_uninstantiables_impl::Stats remove_uninstantiables_stats;
  std::atomic<size_t> throws_inserted{0};
  InsertOnlyConcurrentSet<DexMethod*> affected_methods;
  reachability::sweep_code(
      stores, /* prune_uncallable_instance_method_bodies */ true,
      /* skip_uncallable_virtual_methods */ false, reachable_aspects,
      &remove_uninstantiables_stats, &throws_inserted, &affected_methods);
  EXPECT_EQ(remove_uninstantiables_stats.field_accesses_on_uninstantiable, 1);
  EXPECT_EQ(remove_uninstantiables_stats.invokes, 5);
  EXPECT_EQ(remove_uninstantiables_stats.check_casts, 1);
  EXPECT_EQ(remove_uninstantiables_stats.instance_ofs, 1);
  EXPECT_EQ(remove_uninstantiables_stats.throw_null_methods, 12);

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
}

TEST_F(FlowSensitiveReachabilityTest, sweep_uncallable_virtual_methods) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void root();
    }
  )");

  EXPECT_TRUE(pg_config->ok);
  EXPECT_EQ(pg_config->keep_rules.size(), 1);

  int num_ignore_check_strings = 0;
  reachability::IgnoreSets ig_sets;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ false,
      /* cfg_gathering_check_instantiable */ true,
      /* cfg_gathering_check_instance_callable */ true);

  //// instantiable_types
  EXPECT_EQ(reachable_aspects.instantiable_types.size(), 5);
  auto is_instantiable = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.instantiable_types,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_instantiable("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_instantiable("LData;"));
  EXPECT_FALSE(is_instantiable("LDataHolder;"));
  EXPECT_FALSE(is_instantiable("LLegacyInstantiable;"));
  EXPECT_TRUE(is_instantiable("LStringInstantiable;"));
  EXPECT_TRUE(is_instantiable("LBase;"));
  EXPECT_TRUE(is_instantiable("LIntermediate;"));
  EXPECT_TRUE(is_instantiable("LRegularInstantiable;"));

  //// dynamically_referenced_classes
  EXPECT_EQ(reachable_aspects.dynamically_referenced_classes.size(), 2);
  auto is_dynamically_referenced = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.dynamically_referenced_classes,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_FALSE(is_dynamically_referenced("LFlowSensitiveReachabilityTest;"));
  EXPECT_FALSE(is_dynamically_referenced("LData;"));
  EXPECT_FALSE(is_dynamically_referenced("LDataHolder;"));
  EXPECT_FALSE(is_dynamically_referenced("LLegacyInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LStringInstantiable;"));
  EXPECT_TRUE(is_dynamically_referenced("LRegularInstantiable;"));

  //// instructions_unvisited
  EXPECT_GT(reachable_aspects.instructions_unvisited, 0);

  //// uninstantiable_dependencies
  EXPECT_EQ(reachable_aspects.uninstantiable_dependencies.size(), 1);
  auto is_uninstantiable_dependency = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.uninstantiable_dependencies,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_uninstantiable_dependency("LDataHolder;"));

  // Code sweeping
  remove_uninstantiables_impl::Stats remove_uninstantiables_stats;
  std::atomic<size_t> throws_inserted{0};
  InsertOnlyConcurrentSet<DexMethod*> affected_methods;
  reachability::sweep_code(
      stores, /* prune_uncallable_instance_method_bodies */ true,
      /* skip_uncallable_virtual_methods */ true, reachable_aspects,
      &remove_uninstantiables_stats, &throws_inserted, &affected_methods);
  EXPECT_EQ(remove_uninstantiables_stats.field_accesses_on_uninstantiable, 1);
  EXPECT_EQ(remove_uninstantiables_stats.invokes, 5);
  EXPECT_EQ(remove_uninstantiables_stats.check_casts, 1);
  EXPECT_EQ(remove_uninstantiables_stats.instance_ofs, 1);
  EXPECT_EQ(remove_uninstantiables_stats.throw_null_methods, 7);

  auto abstracted_classes = reachability::mark_classes_abstract(
      stores, *reachable_objects, reachable_aspects);
  EXPECT_EQ(abstracted_classes.size(), 5);
  reachability::sweep(stores, *reachable_objects);
  remove_uninstantiables_stats =
      reachability::sweep_uncallable_virtual_methods(stores, reachable_aspects);
  EXPECT_EQ(remove_uninstantiables_stats.abstracted_vmethods, 1);
  EXPECT_EQ(remove_uninstantiables_stats.abstracted_classes, 0);
  EXPECT_EQ(remove_uninstantiables_stats.removed_vmethods, 1);

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
}

TEST_F(FlowSensitiveReachabilityTest, abstract_overrides_non_abstract) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void abstract_overrides_non_abstract();
    }
  )");

  EXPECT_TRUE(pg_config->ok);
  EXPECT_EQ(pg_config->keep_rules.size(), 1);

  int num_ignore_check_strings = 0;
  reachability::IgnoreSets ig_sets;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ false,
      /* cfg_gathering_check_instantiable */ true);

  //// instantiable_types
  EXPECT_EQ(reachable_aspects.instantiable_types.size(), 4);
  auto is_instantiable = [&](const std::string_view& s) {
    return unordered_any_of(reachable_aspects.instantiable_types,
                            [s](const auto* cls) { return cls->str() == s; });
  };
  EXPECT_TRUE(is_instantiable("LFlowSensitiveReachabilityTest;"));
  EXPECT_TRUE(is_instantiable("LSurpriseBase;"));
  EXPECT_TRUE(is_instantiable("LSurprise;"));
  EXPECT_TRUE(is_instantiable("LSurpriseSub;"));

  EXPECT_TRUE(reachable_objects->marked_unsafe(
      DexMethod::get_method("LSurpriseBase;.foo:()V")));
  EXPECT_FALSE(reachable_objects->marked_unsafe(
      DexMethod::get_method("LSurprise;.foo:()V")));
  EXPECT_TRUE(reachable_objects->marked_unsafe(
      DexMethod::get_method("LSurpriseSub;.foo:()V")));

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
}

TEST_F(FlowSensitiveReachabilityTest, throw_propagation) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void throw_propagation();
    }
  )");

  EXPECT_TRUE(pg_config->ok);
  EXPECT_EQ(pg_config->keep_rules.size(), 1);

  int num_ignore_check_strings = 0;
  reachability::IgnoreSets ig_sets;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ true,
      /* cfg_gathering_check_instantiable */ true,
      /* cfg_gathering_check_instance_callable */ true,
      /* cfg_gathering_check_returning */ true);

  //// returning_methods
  for (const auto* m : UnorderedIterable(reachable_aspects.returning_methods)) {
    EXPECT_TRUE(method::is_init(m)); // only the FlowSensitiveReachabilityTest
                                     // contructor returns
  }
  auto* dead_cls = find_class(*classes, "LDead;");
  ASSERT_TRUE(dead_cls);
  ASSERT_FALSE(reachable_objects->marked_unsafe(dead_cls));

  // Code sweeping
  remove_uninstantiables_impl::Stats remove_uninstantiables_stats;
  std::atomic<size_t> throws_inserted{0};
  InsertOnlyConcurrentSet<DexMethod*> affected_methods;
  reachability::sweep_code(
      stores, /* prune_uncallable_instance_method_bodies */ true,
      /* skip_uncallable_virtual_methods */ true, reachable_aspects,
      &remove_uninstantiables_stats, &throws_inserted, &affected_methods);

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });

  auto* method = find_dmethod(*classes, "LFlowSensitiveReachabilityTest;", "V",
                              "throw_propagation", {});
  ASSERT_TRUE(method);
  auto ii = InstructionIterable(method->get_code());
  ASSERT_TRUE(ii.begin()->insn->opcode() == OPCODE_INVOKE_STATIC);
  ASSERT_TRUE(std::prev(ii.end())->insn->opcode() == OPCODE_THROW);
}

TEST_F(FlowSensitiveReachabilityTest,
       ignore_check_strings_counts_each_method_once) {
  const auto& dexen = stores[0].get_dexen();
  auto pg_config = process_and_get_proguard_config(dexen, R"(
    -keepclasseswithmembers public class FlowSensitiveReachabilityTest {
      public void root();
    }
  )");
  EXPECT_TRUE(pg_config->ok);

  // `root` is gathered in more than one step: the code after `obj.foo()` is
  // only reached once `RegularInstantiable` becomes instantiable.
  reachability::IgnoreSets ig_sets;
  ig_sets.string_literals.insert(
      DexType::get_type("LFlowSensitiveReachabilityTest;"));
  int num_ignore_check_strings = 0;
  reachability::ReachableAspects reachable_aspects;
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto method_override_graph = method_override_graph::build_graph(scope);

  auto reachable_objects = reachability::compute_reachable_objects(
      scope, *method_override_graph, ig_sets, &num_ignore_check_strings,
      &reachable_aspects, false,
      /* relaxed_keep_class_members */ true,
      /* relaxed_keep_interfaces */ false,
      /* cfg_gathering_check_instantiable */ true,
      /* cfg_gathering_check_instance_callable */ true);

  auto* cls = type_class(DexType::get_type("LFlowSensitiveReachabilityTest;"));
  int num_marked_methods = 0;
  for (auto* method : cls->get_all_methods()) {
    if (reachable_objects->marked(method)) {
      ++num_marked_methods;
    }
  }
  EXPECT_GT(num_marked_methods, 1);
  EXPECT_EQ(num_ignore_check_strings, num_marked_methods);

  walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
}
