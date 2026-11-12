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
#include "ClassMergingTestFixture.h"
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
#include "TypeSystem.h"
#include "TypeUtil.h"
#include "VirtualScopes.h"

using namespace class_merging;
using namespace class_merging_test;

namespace {

class ClassMergingHotColdGroupingTest : public ClassMergingTest {
 protected:
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
  EXPECT_TRUE(baseline_profiles::dex2oat_compiles(
      baseline, a_value, baseline_profiles::get_huge_method_max(conf)));
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
