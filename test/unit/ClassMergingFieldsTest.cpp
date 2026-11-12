/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <fstream>
#include <gtest/gtest.h>

#include "ClassMergingPass.h"
#include "ClassMergingTestFixture.h"
#include "ConfigFiles.h"
#include "DexStore.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexTestUtils.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"

using namespace class_merging;
using namespace class_merging_test;

namespace {

class ClassMergingFieldMetricsTest : public ClassMergingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redex/test/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
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
};

} // namespace

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
