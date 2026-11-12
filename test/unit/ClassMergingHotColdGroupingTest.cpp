/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <fstream>
#include <gtest/gtest.h>

#include "BaselineProfile.h"
#include "ClassMerging.h"
#include "ClassMergingPass.h"
#include "ConfigFiles.h"
#include "CppUtil.h"
#include "DexStore.h"
#include "HotColdGrouping.h"
#include "IRAssembler.h"
#include "IRTemplate.h"
#include "MethodProfiles.h"
#include "Model.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "ScopeHelper.h"
#include "TypeSystem.h"
#include "TypeUtil.h"
#include "VirtualScopes.h"

using namespace class_merging;

namespace {

constexpr std::string_view kCtor = R"(
  (method (public constructor) "$CLS.<init>:()V"
   (
    (load-param-object v0)
    (invoke-direct (v0) "$SUPER.<init>:()V")
    (return-void)
   )
  )
)";

constexpr std::string_view kVirtual = R"(
  (method (public) "$CLS.$NAME:()V"
   (
    (load-param-object v0)
    (return-void)
   )
  )
)";

DexMethod* add_method(DexClass* cls, const std::string& code) {
  auto* method = assembler::method_from_string(code);
  method->get_code()->build_cfg();
  cls->add_method(method);
  return method;
}

DexMethod* add_ctor(DexClass* cls) {
  const auto cls_name = cls->get_type()->str_copy();
  const auto super_name = cls->get_super_class()->str_copy();
  return add_method(cls,
                    ir(kCtor, {{"$CLS", cls_name}, {"$SUPER", super_name}}));
}

DexMethod* add_virtual(DexClass* cls, const std::string& name) {
  const auto cls_name = cls->get_type()->str_copy();
  return add_method(cls, ir(kVirtual, {{"$CLS", cls_name}, {"$NAME", name}}));
}

class ClassMergingHotColdGroupingTest : public RedexTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("LBase;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
  }

  DexClass* make_class(const char* name, DexType* super) {
    auto* cls = create_internal_class(DexType::make_type(name), super, {});
    m_scope.push_back(cls);
    return cls;
  }

  // A subclass of Base with a ctor and an override of Base.run(), either of
  // which can be marked hot.
  DexClass* make_mergeable(const std::string& name,
                           bool hot_ctor = false,
                           bool hot_run = false) {
    auto* cls = make_class(name.c_str(), m_base->get_type());
    auto* ctor = add_ctor(cls);
    auto* run = add_virtual(cls, "run");
    if (hot_ctor) {
      m_hot_methods.push_back(ctor);
    }
    if (hot_run) {
      m_hot_methods.push_back(run);
    }
    return cls;
  }

  bool is_hot(const DexClass* cls) {
    virtual_scope::VirtualScopes vscopes(m_scope);
    UnorderedSet<const DexMethod*> hot_methods(m_hot_methods.begin(),
                                               m_hot_methods.end());
    return is_hot_mergeable(cls, vscopes, hot_methods);
  }

  // Builds the model for all subclasses of Base, with `m_hot_methods` hot in
  // the method profiles, and returns the sorted mergeables of each merger.
  std::vector<std::vector<std::string>> merger_groups(
      bool hot_cold_grouping, ModelStats* stats = nullptr) {
    DexStore store("classes");
    store.add_classes(m_scope);
    DexStoresVector stores{store};
    // java.lang.Object is external, as in real builds, so RefChecker only
    // accepts hierarchies rooted at it when the SDK API list has it.
    auto tmp_dir = redex::make_tmp_dir("hot_cold_grouping_test_%%%%%%%%");
    const auto api_file = tmp_dir.path + "/api.txt";
    {
      std::ofstream out(api_file);
      out << "Ljava/lang/Object; 1 Ljava/lang/Object; 1 0\n"
          << "  M Ljava/lang/Object;.<init>:()V 1\n";
    }
    Json::Value json;
    json["android_sdk_api_21_file"] = api_file;
    ConfigFiles conf(json);
    method_profiles::Stats hot_stats;
    hot_stats.appear_percent = 100.0;
    hot_stats.call_count = 100.0;
    UnorderedMap<const DexMethodRef*, method_profiles::Stats> manual_hot_stats;
    for (auto* m : m_hot_methods) {
      manual_hot_stats[m] = hot_stats;
    }
    conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
        "manual_hot", manual_hot_stats);
    RedexOptions options;
    options.min_sdk = 21;
    PassManager mgr({}, conf, options);

    ModelSpec spec;
    spec.name = "HotCold";
    spec.class_name_prefix = "HotCold";
    spec.roots.insert(m_base->get_type());
    spec.include_primary_dex = true;
    spec.hot_cold_grouping = hot_cold_grouping;

    TypeSystem type_system(m_scope);
    load_roots_subtypes_as_merging_targets(type_system, &spec);
    virtual_scope::VirtualScopes vscopes(m_scope);
    auto model =
        construct_model(type_system, vscopes, m_scope, conf, mgr, stores, spec);
    if (stats != nullptr) {
      *stats = model.get_model_stats();
    }

    std::vector<std::vector<std::string>> groups;
    model.walk_hierarchy([&](const MergerType& merger) {
      if (merger.mergeables.empty()) {
        return;
      }
      std::vector<std::string> group;
      for (const auto* type : merger.mergeables) {
        group.push_back(type->str_copy());
      }
      std::sort(group.begin(), group.end());
      groups.push_back(std::move(group));
    });
    std::sort(groups.begin(), groups.end());
    return groups;
  }

  Json::Value field_metrics_model(DexClass* root = nullptr) {
    if (root == nullptr) {
      root = m_base;
    }
    Json::Value model;
    model["enabled"] = true;
    model["name"] = root->get_type()->str_copy();
    model["class_name_prefix"] = "FieldMetrics";
    model["roots"].append(root->get_type()->str_copy());
    model["interdex_grouping"] = "disabled";
    model["include_primary_dex"] = true;
    model["merge_types_with_static_fields"] = true;
    return model;
  }

  void add_field(DexClass* cls,
                 const char* name,
                 DexType* field_type,
                 DexAccessFlags access) {
    cls->add_field(DexField::make_field(cls->get_type(),
                                        DexString::make_string(name),
                                        field_type)
                       ->make_concrete(access));
  }

  void add_metric_fields(DexClass* cls, DexAccessFlags mixed_access) {
    add_field(cls, "wide", type::_long(), ACC_PUBLIC | ACC_VOLATILE);
    add_field(cls, "mixed", type::_double(), ACC_PUBLIC | mixed_access);
    add_field(cls, "immutable", type::_float(), ACC_PUBLIC | ACC_FINAL);
    add_field(cls, "mutable", type::_int(), ACC_PUBLIC);
  }

  UnorderedMap<std::string, int64_t> run_merging(
      const std::vector<Json::Value>& models) {
    auto tmp_dir = redex::make_tmp_dir("field_metrics_test_%%%%%%%%");
    const auto api_file = tmp_dir.path + "/api.txt";
    {
      std::ofstream out(api_file);
      out << "Ljava/lang/Object; 1 Ljava/lang/Object; 1 0\n"
          << "  M Ljava/lang/Object;.<init>:()V 1\n";
    }
    Json::Value json;
    json["android_sdk_api_21_file"] = api_file;
    for (const auto& model : models) {
      json["ClassMergingPass"]["models"].append(model);
    }
    ConfigFiles conf(json);
    conf.parse_global_config();
    method_profiles::Stats hot_stats;
    hot_stats.appear_percent = 100.0;
    hot_stats.call_count = 100.0;
    UnorderedMap<const DexMethodRef*, method_profiles::Stats> manual_hot_stats;
    for (auto* method : m_hot_methods) {
      manual_hot_stats[method] = hot_stats;
    }
    conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
        "manual_hot", manual_hot_stats);
    RedexOptions options;
    options.min_sdk = 21;
    ClassMergingPass pass;
    PassManager mgr({&pass}, conf, options);
    DexStore store("classes");
    store.add_classes(m_scope);
    DexStoresVector stores{store};
    mgr.run_passes(stores, conf);
    m_scope = build_class_scope(stores);
    return mgr.get_pass_info().at(0).metrics;
  }

  void expect_field_metrics(const UnorderedMap<std::string, int64_t>& metrics,
                            int64_t volatile_fields,
                            int64_t final_fields) {
    ASSERT_EQ(metrics.count("num_merged_volatile_fields"), 1u);
    ASSERT_EQ(metrics.count("num_merged_final_fields"), 1u);
    EXPECT_EQ(metrics.at("num_merged_volatile_fields"), volatile_fields);
    EXPECT_EQ(metrics.at("num_merged_final_fields"), final_fields);
  }

  Scope m_scope;
  DexClass* m_base{nullptr};
  std::vector<DexMethod*> m_hot_methods;
};

class ClassMergingFieldMetricsTest : public ClassMergingHotColdGroupingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redex/test/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
  }
};

} // namespace

TEST_F(ClassMergingHotColdGroupingTest, DedupTransfersProfilesToSurvivor) {
  m_base = make_class("Lprofile/Base;", type::java_lang_Object());
  add_ctor(m_base);
  add_virtual(m_base, "run");
  auto* a = make_mergeable("Lprofile/A;");
  auto* b = make_mergeable("Lprofile/B;");
  auto add_value = [](DexClass* cls) {
    return add_method(cls,
                      ir(R"(
      (method (public static) "$CLS.value:()I"
        ((const v0 7) (return v0)))
    )",
                         {{"$CLS", cls->get_type()->str_copy()}}));
  };
  auto* a_value = add_value(a);
  auto* b_value = add_value(b);

  DexStore store("classes");
  store.add_classes(m_scope);
  DexStoresVector stores{store};
  auto tmp_dir = redex::make_tmp_dir("dedup_method_profiles_test_%%%%%%%%");
  const auto api_file = tmp_dir.path + "/api.txt";
  {
    std::ofstream out(api_file);
    out << "Ljava/lang/Object; 1 Ljava/lang/Object; 1 0\n"
        << "  M Ljava/lang/Object;.<init>:()V 1\n";
  }
  Json::Value json;
  json["android_sdk_api_21_file"] = api_file;
  json["update_method_profiles_stats"] = true;
  Json::Value model;
  model["name"] = "DedupProfiles";
  model["class_name_prefix"] = "DedupProfiles";
  model["roots"].append("Lprofile/Base;");
  model["include_primary_dex"] = true;
  json["ClassMergingPass"]["models"].append(model);
  ConfigFiles conf(json);
  conf.parse_global_config();
  conf.set_outdir(tmp_dir.path);
  method_profiles::Stats hot_stats{100.0, 10.0, 0.0, 21};
  conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
      "manual_hot", {{b_value, hot_stats}});
  RedexOptions options;
  options.min_sdk = 21;
  ClassMergingPass pass;
  PassManager mgr({&pass}, conf, options);
  mgr.run_passes(stores, conf);
  EXPECT_TRUE(a_value->is_def());
  EXPECT_EQ(DexMethod::get_method("Lprofile/B;.value:()I"), nullptr);
  auto profile =
      conf.get_method_profiles().get_method_stat("manual_hot", a_value);
  ASSERT_TRUE(profile.has_value());
  EXPECT_EQ(*profile, hot_stats);
  auto baseline = baseline_profiles::get_default_baseline_profile(
      build_class_scope(stores), {{"default", {}}}, conf.get_method_profiles(),
      /* coldstart_classes */ {}, baseline_profiles::get_huge_method_max(conf));
  EXPECT_TRUE(baseline_profiles::is_compiled(baseline, a_value));
}

TEST_F(ClassMergingHotColdGroupingTest, NoHotMethodIsCold) {
  auto* a = make_mergeable("LA;");
  EXPECT_FALSE(is_hot(a));
}

TEST_F(ClassMergingHotColdGroupingTest, HotCtorIsHot) {
  auto* a = make_mergeable("LA;", /* hot_ctor */ true);
  EXPECT_TRUE(is_hot(a));
}

TEST_F(ClassMergingHotColdGroupingTest, HotOverrideIsHot) {
  auto* a = make_mergeable("LA;", /* hot_ctor */ false, /* hot_run */ true);
  EXPECT_TRUE(is_hot(a));
}

// A virtual method only A declares is effectively final: merging relocates it
// instead of folding it into a dispatch, so its hotness does not count.
TEST_F(ClassMergingHotColdGroupingTest, HotEffectivelyFinalMethodIsIgnored) {
  auto* a = make_mergeable("LA;");
  m_hot_methods.push_back(add_virtual(a, "helper"));
  EXPECT_FALSE(is_hot(a));
}

TEST_F(ClassMergingHotColdGroupingTest, DisabledKeepsOneGroup) {
  make_mergeable("LA;", false, true);
  make_mergeable("LB;", false, true);
  make_mergeable("LC;");
  make_mergeable("LD;");

  ModelStats stats;
  EXPECT_EQ(
      merger_groups(false, &stats),
      (std::vector<std::vector<std::string>>{{"LA;", "LB;", "LC;", "LD;"}}));
  EXPECT_EQ(stats.m_hot_mergeables + stats.m_cold_mergeables, 0u);
}

TEST_F(ClassMergingHotColdGroupingTest, EnabledSplitsHotAndCold) {
  make_mergeable("LA;", false, true);
  make_mergeable("LB;", true);
  make_mergeable("LC;");
  make_mergeable("LD;");

  ModelStats stats;
  EXPECT_EQ(
      merger_groups(true, &stats),
      (std::vector<std::vector<std::string>>{{"LA;", "LB;"}, {"LC;", "LD;"}}));
  EXPECT_EQ(stats.m_hot_mergeables, 2u);
  EXPECT_EQ(stats.m_cold_mergeables, 2u);
  EXPECT_EQ(stats.m_hot_cold_split_groups, 1u);
  EXPECT_EQ(stats.m_hot_cold_dropped, 0u);
}

TEST_F(ClassMergingHotColdGroupingTest, UndersizedPartStaysUnmerged) {
  make_mergeable("LA;", false, true);
  make_mergeable("LB;");
  make_mergeable("LC;");
  make_mergeable("LD;");

  ModelStats stats;
  EXPECT_EQ(merger_groups(true, &stats),
            (std::vector<std::vector<std::string>>{{"LB;", "LC;", "LD;"}}));
  EXPECT_EQ(stats.m_hot_cold_dropped, 1u);
  EXPECT_EQ(stats.m_dropped, 1u);
}

TEST_F(ClassMergingHotColdGroupingTest, AllHotIsNotSplit) {
  make_mergeable("LA;", false, true);
  make_mergeable("LB;", false, true);
  make_mergeable("LC;", true);

  ModelStats stats;
  EXPECT_EQ(merger_groups(true, &stats),
            (std::vector<std::vector<std::string>>{{"LA;", "LB;", "LC;"}}));
  EXPECT_EQ(stats.m_hot_cold_split_groups, 0u);
}

TEST_F(ClassMergingHotColdGroupingTest, StringFieldOffsetsFollowTheContext) {
  MergerType merger{};
  merger.shape.string_fields = 1;
  merger.shape.reference_fields = 1;
  auto* first_string = type::java_lang_String();
  EXPECT_EQ(merger.start_index_for(first_string), 0);

  // Keep the first context alive so allocator address reuse cannot hide a stale
  // type pointer.
  auto* first_context = g_redex;
  g_redex = new RedexContext();
  ScopeGuard restore_context{[first_context]() {
    delete g_redex;
    g_redex = first_context;
  }};

  auto* second_string = type::java_lang_String();
  ASSERT_NE(first_string, second_string);
  EXPECT_EQ(merger.start_index_for(second_string), 0);
  EXPECT_EQ(merger.start_index_for(type::java_lang_Object()), 1);
}

TEST_F(ClassMergingFieldMetricsTest, FieldMetricsCountSourcesNotSlots) {
  add_metric_fields(make_mergeable("LA;"), ACC_VOLATILE);
  add_metric_fields(make_mergeable("LB;"), ACC_FINAL);

  auto metrics = run_merging({field_metrics_model()});
  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  expect_field_metrics(metrics, 3, 3);
}

TEST_F(ClassMergingFieldMetricsTest,
       FieldMetricsIgnoreUnmergedAndStaticFields) {
  auto* a = make_mergeable("LA;");
  auto* b = make_mergeable("LB;");
  add_metric_fields(a, ACC_VOLATILE);
  add_metric_fields(b, ACC_FINAL);
  add_field(a, "static_volatile", type::_long(),
            ACC_PUBLIC | ACC_STATIC | ACC_VOLATILE);
  add_field(b, "static_final", type::_long(),
            ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  add_metric_fields(make_mergeable("LC;", true), ACC_VOLATILE);
  add_field(m_base, "inherited", type::_long(), ACC_PUBLIC | ACC_VOLATILE);
  auto model = field_metrics_model();
  model["hot_cold_grouping"] = true;

  auto metrics = run_merging({model});
  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  expect_field_metrics(metrics, 3, 3);
}

TEST_F(ClassMergingFieldMetricsTest, FieldMetricsIgnoreRejectedMergers) {
  add_metric_fields(make_mergeable("LA;"), ACC_VOLATILE);
  add_metric_fields(make_mergeable("LB;"), ACC_FINAL);
  auto model = field_metrics_model();
  model["type_tag_config"] = "none";

  auto metrics = run_merging({model});
  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  expect_field_metrics(metrics, 0, 0);
}

TEST_F(ClassMergingFieldMetricsTest, FieldMetricsIgnoreGeneratedTypeTags) {
  make_mergeable("LA;");
  make_mergeable("LB;");

  auto metrics = run_merging({field_metrics_model()});
  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  expect_field_metrics(metrics, 0, 0);
}

TEST_F(ClassMergingFieldMetricsTest, FieldMetricsSumModelsOnce) {
  add_metric_fields(make_mergeable("LA;"), ACC_VOLATILE);
  add_metric_fields(make_mergeable("LB;"), ACC_FINAL);
  auto* second_base =
      make_class("Lcom/redex/test/SecondBase;", type::java_lang_Object());
  add_ctor(second_base);
  add_virtual(second_base, "run");
  for (const auto* name : {"LSecondA;", "LSecondB;"}) {
    auto* cls = make_class(name, second_base->get_type());
    add_ctor(cls);
    add_virtual(cls, "run");
    add_metric_fields(cls, ACC_FINAL);
  }

  auto metrics =
      run_merging({field_metrics_model(), field_metrics_model(second_base)});
  EXPECT_EQ(metrics.at(" total_class_merged"), 4);
  expect_field_metrics(metrics, 5, 7);
}

TEST_F(ClassMergingFieldMetricsTest, FieldMetricsEmitZeroWithoutModels) {
  auto metrics = run_merging({});
  expect_field_metrics(metrics, 0, 0);
}

TEST_F(ClassMergingFieldMetricsTest,
       ShapesWithMultiDigitFieldCountsGetTheirOwnMergers) {
  // `One1` and `One2` have 1 String field and 11 other reference fields;
  // `Eleven1` and `Eleven2` have 11 String fields and 1 other reference field.
  // Each pair merges into a class of its own shape.
  auto* base = make_class("Lcom/s/Base;", type::java_lang_Object());
  add_ctor(base);
  auto add_fields = [this](DexClass* cls, int strings, int refs) {
    for (int i = 0; i < strings; ++i) {
      add_field(cls, ("s" + std::to_string(i)).c_str(),
                type::java_lang_String(), ACC_PUBLIC);
    }
    for (int i = 0; i < refs; ++i) {
      add_field(cls, ("r" + std::to_string(i)).c_str(),
                type::java_lang_Object(), ACC_PUBLIC);
    }
  };
  for (const auto* name : {"Lcom/s/One1;", "Lcom/s/One2;"}) {
    auto* cls = make_class(name, base->get_type());
    add_ctor(cls);
    add_fields(cls, 1, 11);
  }
  for (const auto* name : {"Lcom/s/Eleven1;", "Lcom/s/Eleven2;"}) {
    auto* cls = make_class(name, base->get_type());
    add_ctor(cls);
    add_fields(cls, 11, 1);
  }

  auto metrics = run_merging({field_metrics_model(base)});

  EXPECT_EQ(metrics.at(" total_class_merged"), 4);
  std::vector<std::pair<int, int>> merger_fields;
  for (const auto* cls : m_scope) {
    if (cls->get_super_class() != base->get_type()) {
      continue;
    }
    int strings = 0;
    int objects = 0;
    for (const auto* field : cls->get_ifields()) {
      strings += field->get_type() == type::java_lang_String() ? 1 : 0;
      objects += field->get_type() == type::java_lang_Object() ? 1 : 0;
    }
    merger_fields.emplace_back(strings, objects);
  }
  std::sort(merger_fields.begin(), merger_fields.end());
  EXPECT_EQ(merger_fields,
            (std::vector<std::pair<int, int>>{{1, 11}, {11, 1}}));
}

TEST_F(ClassMergingFieldMetricsTest, ModelsWithTheSameShapeNamesMergeOnce) {
  // Both models use the same class name prefix and have a root named `Base`, so
  // they name the merger of their two field-less subclasses alike. The second
  // model leaves its subclasses alone instead of reusing the class the first
  // model created.
  for (const auto* pkg : {"Lcom/a/", "Lcom/b/"}) {
    auto* base = make_class((std::string(pkg) + "Base;").c_str(),
                            type::java_lang_Object());
    add_ctor(base);
    for (const auto* leaf : {"Leaf1;", "Leaf2;"}) {
      add_ctor(make_class((std::string(pkg) + leaf).c_str(), base->get_type()));
    }
  }
  auto metrics = run_merging(
      {field_metrics_model(type_class(DexType::make_type("Lcom/a/Base;"))),
       field_metrics_model(type_class(DexType::make_type("Lcom/b/Base;")))});

  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  for (const auto* name : {"Lcom/b/Leaf1;", "Lcom/b/Leaf2;"}) {
    const auto* cls = type_class(DexType::make_type(name));
    EXPECT_NE(std::find(m_scope.begin(), m_scope.end(), cls), m_scope.end())
        << name;
  }
}
