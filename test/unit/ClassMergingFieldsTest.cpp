/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <fstream>
#include <gtest/gtest.h>

#include "ClassAssemblingUtils.h"
#include "ClassMergingPass.h"
#include "ClassMergingTestFixture.h"
#include "ConfigFiles.h"
#include "DexStore.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexTestUtils.h"
#include "RefChecker.h"
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
      const std::vector<Json::Value>& models,
      bool preserve_unanimous_field_types = false) {
    auto tmp_dir = redex::make_tmp_dir("field_metrics_test_%%%%%%%%");
    const auto api_file = tmp_dir.path + "/api.txt";
    {
      std::ofstream out(api_file);
      out << "Ljava/lang/Object; 1 Ljava/lang/Object; 1 0\n"
          << "  M Ljava/lang/Object;.<init>:()V 1\n";
    }
    Json::Value json;
    json["android_sdk_api_21_file"] = api_file;
    json["ClassMergingPass"]["preserve_unanimous_field_types"] =
        preserve_unanimous_field_types;
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

class ClassMergingFieldTypesTest : public ClassMergingFieldMetricsTest {
 protected:
  DexType* make_payload(const char* name = "Lcom/redex/test/Payload;",
                        DexAccessFlags access = ACC_PUBLIC) {
    auto* cls = make_class(name, type::java_lang_Object());
    cls->set_access(access);
    return cls->get_type();
  }

  void add_capture(DexClass* cls,
                   DexType* type,
                   const char* name = "capture",
                   DexAccessFlags access = ACC_PUBLIC) {
    add_field(cls, name, type, access);
    add_method(cls, ir(R"(
      (method (public) "$CLS.get:()$TYPE"
        ((load-param-object v0)
         (iget-object v0 "$CLS.$FIELD:$TYPE")
         (move-result-pseudo-object v1)
         (return-object v1)))
    )",
                       {{"$CLS", cls->get_type()->str_copy()},
                        {"$TYPE", type->str_copy()},
                        {"$FIELD", name}}));
  }

  void make_pair(DexType* first, DexType* second) {
    add_capture(make_mergeable("Lcom/redex/test/A;"), first);
    add_capture(make_mergeable("Lcom/redex/test/B;"), second);
  }

  FieldsMap source_fields() {
    FieldsMap fields;
    for (auto* cls : m_scope) {
      if (cls->get_super_class() == m_base->get_type()) {
        fields[cls->get_type()] = cls->get_ifields();
      }
    }
    return fields;
  }

  DexField* find_slot() {
    for (auto* cls : m_scope) {
      if (cls->get_super_class() != m_base->get_type() ||
          !cls->rstate.is_generated()) {
        continue;
      }
      for (auto* field : cls->get_ifields()) {
        if (field->get_name()->str() == "l0") {
          return field;
        }
      }
    }
    return nullptr;
  }

  size_t count_casts_to(const DexType* type) {
    size_t count = 0;
    for (auto* cls : m_scope) {
      for (auto* method : cls->get_all_methods()) {
        auto* code = method->get_code();
        if (code == nullptr) {
          continue;
        }
        code->build_cfg();
        for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
          if (mie.insn->opcode() == OPCODE_CHECK_CAST &&
              mie.insn->get_type() == type) {
            ++count;
          }
        }
      }
    }
    return count;
  }
};

struct FieldAccessCase {
  const char* name;
  DexAccessFlags access;
  bool preserve;
};

class ClassMergingFieldAccessTest
    : public ClassMergingFieldTypesTest,
      public testing::WithParamInterface<FieldAccessCase> {};

class ClassMergingPlatformFieldAccessTest
    : public ClassMergingFieldTypesTest,
      public testing::WithParamInterface<FieldAccessCase> {};

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

TEST_F(ClassMergingFieldTypesTest, DefaultKeepsErasedStorage) {
  auto* payload = make_payload();
  make_pair(payload, payload);
  auto metrics = run_merging({field_metrics_model()});
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), type::java_lang_Object());
  EXPECT_GT(count_casts_to(payload), 0u);
  EXPECT_EQ(metrics.at("FieldMetrics_typed_merger_fields"), 0);
}

TEST_F(ClassMergingFieldTypesTest, UnanimousTypeAvoidsRecoveryCasts) {
  auto* payload = make_payload();
  make_pair(payload, payload);
  auto metrics = run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), payload);
  EXPECT_EQ(count_casts_to(payload), 0u);
  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  EXPECT_EQ(metrics.at("FieldMetrics_typed_merger_fields"), 1);
}

TEST_F(ClassMergingFieldTypesTest, MixedTypesStayErased) {
  auto* payload = make_payload();
  auto* other = make_payload("Lcom/redex/test/Other;");
  make_pair(payload, other);
  auto metrics = run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), type::java_lang_Object());
  EXPECT_GT(count_casts_to(payload), 0u);
  EXPECT_GT(count_casts_to(other), 0u);
  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  EXPECT_EQ(metrics.at("FieldMetrics_typed_merger_fields"), 0);
}

TEST_F(ClassMergingFieldTypesTest, ObjectDeclarationStaysErased) {
  auto* payload = make_payload();
  make_pair(payload, type::java_lang_Object());
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, UnanimousArrayPreservesRank) {
  auto* array = type::make_array_type(make_payload(), 2);
  make_pair(array, array);
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), array);
  EXPECT_EQ(count_casts_to(array), 0u);
}

TEST_F(ClassMergingFieldTypesTest, PrimitiveArrayPreservesType) {
  auto* array = type::make_array_type(type::_int(), 1);
  make_pair(array, array);
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), array);
}

TEST_F(ClassMergingFieldTypesTest, MixedArrayRanksStayErased) {
  auto* payload = make_payload();
  make_pair(type::make_array_type(payload, 1),
            type::make_array_type(payload, 2));
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, PreservedArrayTracksLaterTypeRemapping) {
  auto* second_base =
      make_class("Lother/SecondBase;", type::java_lang_Object());
  add_ctor(second_base);
  add_virtual(second_base, "run");
  auto* a = make_class("Lother/A;", second_base->get_type());
  auto* b = make_class("Lother/B;", second_base->get_type());
  for (auto* cls : {a, b}) {
    cls->set_access(ACC_PUBLIC);
    add_ctor(cls);
    add_virtual(cls, "run");
  }
  auto* array = type::make_array_type(a->get_type(), 2);
  make_pair(array, array);
  auto metrics = run_merging(
      {field_metrics_model(), field_metrics_model(second_base)}, true);
  ASSERT_NE(find_slot(), nullptr);
  auto* rewritten = find_slot()->get_type();
  EXPECT_EQ(type::get_array_level(rewritten), 2u);
  EXPECT_NE(rewritten, array);
  auto* element = type_class(type::get_element_type_if_array(rewritten));
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(element->get_super_class(), second_base->get_type());
  EXPECT_EQ(count_casts_to(rewritten), 0u);
  EXPECT_EQ(metrics.at(" total_class_merged"), 4);
}

TEST_F(ClassMergingFieldTypesTest, SelfAndMutualDeclarationsTrackSameModel) {
  auto* a = make_mergeable("Lcom/redex/test/SelfA;");
  auto* b = make_mergeable("Lcom/redex/test/SelfB;");
  for (auto* cls : {a, b}) {
    add_field(cls, "first", a->get_type(), ACC_PUBLIC);
    add_field(cls, "second", b->get_type(), ACC_PUBLIC);
  }
  auto metrics = run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  auto* merger = type_class(find_slot()->get_class());
  ASSERT_NE(merger, nullptr);
  size_t typed_fields = 0;
  for (auto* field : merger->get_ifields()) {
    if (field->get_name()->str().starts_with("l")) {
      EXPECT_EQ(field->get_type(), merger->get_type());
      ++typed_fields;
    }
  }
  EXPECT_EQ(typed_fields, 2u);
  EXPECT_EQ(metrics.at("FieldMetrics_typed_merger_fields"), 2);
}

TEST_F(ClassMergingFieldTypesTest, TypedStorageKeepsFinal) {
  auto* payload = make_payload();
  for (const auto* name : {"Lcom/redex/test/A;", "Lcom/redex/test/B;"}) {
    add_capture(make_mergeable(name), payload, "capture",
                ACC_PUBLIC | ACC_FINAL);
  }
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), payload);
  EXPECT_TRUE(is_final(find_slot()));
  EXPECT_FALSE(is_volatile(find_slot()));
}

TEST_F(ClassMergingFieldTypesTest, TypedStorageKeepsVolatileAndDropsFinal) {
  auto* payload = make_payload();
  add_capture(make_mergeable("Lcom/redex/test/A;"), payload, "capture",
              ACC_PUBLIC | ACC_FINAL);
  add_capture(make_mergeable("Lcom/redex/test/B;"), payload, "capture",
              ACC_PUBLIC | ACC_VOLATILE);
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), payload);
  EXPECT_TRUE(is_volatile(find_slot()));
  EXPECT_FALSE(is_final(find_slot()));
}

TEST_F(ClassMergingFieldTypesTest, PlaceholderHoleCannotNarrowStorage) {
  auto* payload = make_payload();
  auto* a = make_mergeable("Lcom/redex/test/A;");
  auto* b = make_mergeable("Lcom/redex/test/B;");
  add_capture(a, payload);
  auto* placeholder =
      DexField::make_field(b->get_type(),
                           DexString::make_string("placeholder_0"),
                           type::java_lang_Object())
          ->make_concrete(ACC_PUBLIC);
  FieldsMap fields;
  fields[a->get_type()] = {a->get_ifields().at(0)};
  fields[b->get_type()] = {placeholder};
  RefChecker checker(nullptr, 0, nullptr);
  auto slots = create_merger_fields(DexType::make_type("LHoleMerger;"), fields,
                                    m_base->get_type(), checker, true);
  ASSERT_EQ(slots.size(), 1u);
  EXPECT_EQ(slots[0]->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, StickyMismatchKeepsIndependentSlots) {
  auto* ints = type::make_array_type(type::_int(), 1);
  auto* longs = type::make_array_type(type::_long(), 1);
  auto* bytes = type::make_array_type(type::_byte(), 1);
  auto* shorts = type::make_array_type(type::_short(), 1);
  FieldsMap map;
  for (size_t row = 0; row < 3; ++row) {
    auto* cls =
        make_mergeable("Lcom/redex/test/Sticky" + std::to_string(row) + ";");
    std::vector<DexType*> types{row == 1 ? longs : ints, bytes,
                                row == 2 ? type::java_lang_Object() : shorts};
    std::vector<DexField*> fields;
    for (size_t slot = 0; slot < types.size(); ++slot) {
      auto name = row == 2 && slot == 2 ? "placeholder_2"
                                        : "slot" + std::to_string(slot);
      auto* field = DexField::make_field(cls->get_type(),
                                         DexString::make_string(name),
                                         types.at(slot))
                        ->make_concrete(ACC_PUBLIC);
      if (row != 2 || slot != 2) {
        cls->add_field(field);
      }
      fields.push_back(field);
    }
    map[cls->get_type()] = std::move(fields);
  }
  RefChecker checker(nullptr, 0, nullptr);
  auto slots = create_merger_fields(DexType::make_type("LStickyMerger;"), map,
                                    m_base->get_type(), checker, true);
  ASSERT_EQ(slots.size(), 3u);
  EXPECT_EQ(slots.at(0)->get_type(), type::java_lang_Object());
  EXPECT_EQ(slots.at(1)->get_type(), bytes);
  EXPECT_EQ(slots.at(2)->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, RejectedMergersDoNotCountTypedFields) {
  auto* payload = make_payload();
  make_pair(payload, payload);
  auto model = field_metrics_model();
  model["type_tag_config"] = "none";
  auto metrics = run_merging({model}, true);
  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_EQ(metrics.at("FieldMetrics_typed_merger_fields"), 0);
}

TEST_F(ClassMergingFieldTypesTest, MissingTypeKeepsErasedStorage) {
  make_pair(DexType::make_type("LMissingPayload;"),
            DexType::make_type("LMissingPayload;"));
  RefChecker checker(nullptr, 0, nullptr);
  auto slots =
      create_merger_fields(DexType::make_type("LMissingTypeMerger;"),
                           source_fields(), m_base->get_type(), checker, true);
  ASSERT_EQ(slots.size(), 1u);
  EXPECT_EQ(slots[0]->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, SdkGateKeepsErasedStorage) {
  auto* payload = make_payload("Landroid/FutureApi;");
  type_class(payload)->set_external();
  make_pair(payload, payload);
  RefChecker checker(nullptr, 0, nullptr);
  auto slots =
      create_merger_fields(DexType::make_type("LSdkGateMerger;"),
                           source_fields(), m_base->get_type(), checker, true);
  ASSERT_EQ(slots.size(), 1u);
  EXPECT_EQ(slots[0]->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, StoreGateKeepsErasedStorage) {
  auto* payload = make_payload();
  make_pair(payload, payload);
  DexStore root("classes");
  root.add_classes({m_base});
  DexStore feature("feature");
  feature.add_classes({type_class(payload)});
  DexStoresVector stores{root, feature};
  XStoreRefs xstores(stores, true);
  RefChecker checker(&xstores, xstores.largest_root_store_id(), nullptr);
  auto slots =
      create_merger_fields(DexType::make_type("LStoreGateMerger;"),
                           source_fields(), m_base->get_type(), checker, true);
  ASSERT_EQ(slots.size(), 1u);
  EXPECT_EQ(slots[0]->get_type(), type::java_lang_Object());
}

TEST_F(ClassMergingFieldTypesTest, RealMarkerNamedFieldIsNotAHole) {
  auto* payload = make_payload();
  add_capture(make_mergeable("Lcom/redex/test/A;"), payload, "placeholder_0");
  add_capture(make_mergeable("Lcom/redex/test/B;"), payload, "placeholder_0");
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(), payload);
}

TEST_P(ClassMergingFieldAccessTest, UsesActualDestinationPackage) {
  const auto& value = GetParam();
  auto* payload = make_payload(value.name, value.access);
  make_pair(payload, payload);
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(find_slot()->get_type(),
            value.preserve ? payload : type::java_lang_Object());
}

TEST_P(ClassMergingPlatformFieldAccessTest, UsesRelocatedPlatformPackage) {
  const auto& value = GetParam();
  m_base = type_class(type::java_lang_Object());
  ASSERT_NE(m_base, nullptr);
  ASSERT_TRUE(m_base->is_external());
  // ScopeHelper defines Object's other methods, but not its constructor.
  auto* object_ctor = dynamic_cast<DexMethod*>(DexMethod::make_method(
      m_base->get_type(), DexString::make_string("<init>"),
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}))));
  ASSERT_NE(object_ctor, nullptr);
  object_ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
  object_ctor->set_virtual(false);
  object_ctor->set_external();
  m_base->add_method(object_ctor);
  auto* payload = make_payload(value.name, value.access);
  const auto package = std::string(type::get_package_name(payload));
  add_capture(make_mergeable(package + "PlatformA;"), payload);
  add_capture(make_mergeable(package + "PlatformB;"), payload);
  run_merging({field_metrics_model()}, true);
  ASSERT_NE(find_slot(), nullptr);
  EXPECT_EQ(type::get_package_name(find_slot()->get_class()),
            "Lcom/facebook/redex/");
  EXPECT_EQ(find_slot()->get_type(),
            value.preserve ? payload : type::java_lang_Object());
}

INSTANTIATE_TEST_SUITE_P(
    Platform,
    ClassMergingPlatformFieldAccessTest,
    testing::Values(FieldAccessCase{"Lcom/facebook/redex/PlatformPayload;",
                                    static_cast<DexAccessFlags>(0), true},
                    FieldAccessCase{"Ljava/PlatformPayload;",
                                    static_cast<DexAccessFlags>(0), false}));

INSTANTIATE_TEST_SUITE_P(
    Access,
    ClassMergingFieldAccessTest,
    testing::Values(
        FieldAccessCase{"Lother/Public;", ACC_PUBLIC, true},
        FieldAccessCase{"Lcom/redex/test/PackagePrivate;",
                        static_cast<DexAccessFlags>(0), true},
        FieldAccessCase{"Lother/PackagePrivate;",
                        static_cast<DexAccessFlags>(0), false},
        FieldAccessCase{"Lcom/redex/test/Private;", ACC_PRIVATE, false},
        FieldAccessCase{"Lcom/redex/test/Protected;", ACC_PROTECTED, false}));
