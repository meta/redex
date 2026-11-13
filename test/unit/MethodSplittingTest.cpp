/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <deque>
#include <limits>
#include <memory>

#include <gtest/gtest.h>

#include "MethodClosures.h"
#include "MethodProfiles.h"
#include "MethodSplitter.h"
#include "MethodSplittingTestUtil.h"
#include "SplittableClosures.h"

#include "Creators.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"

class MethodSplitterTest : public RedexTest {
 public:
  static std::pair<DexClass*, DexMethod*> create(const std::string& sig,
                                                 const std::string& code_str) {
    // Create a totally new class.
    size_t c = s_counter.fetch_add(1);
    std::string name = std::string("LFoo") + std::to_string(c) + ";";
    ClassCreator cc{DexType::make_type(name)};
    cc.set_super(type::java_lang_Object());

    auto* m =
        DexMethod::make_method(name + ".bar:" + sig)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                            assembler::ircode_from_string(code_str), false);
    m->set_deobfuscated_name(show(m));
    cc.add_method(m);
    return std::make_pair(cc.create(), m);
  }

  static std::string replace_count(const std::string& str, DexMethod* m) {
    const std::string replacement = "LFoo;";
    const auto needle = m->get_class()->str();
    std::string res = str;
    for (;;) {
      size_t i = res.find(needle);
      if (i == std::string::npos) {
        break;
      }
      res.replace(i, needle.length(), replacement);
    }
    return res;
  }

  static std::pair<std::string, std::string> pair(std::string l,
                                                  std::string r) {
    return std::make_pair(std::move(l), std::move(r));
  }

  static method_splitting_impl::Config defaultConfig() {
    method_splitting_impl::Config config;
    // set some low limits...
    config.split_block_size = 4;
    config.min_original_size = 1;
    config.min_cold_split_size = 4;
    config.max_overhead_ratio = 0.5;
    config.max_iteration = 1;
    config.cost_split_method = 1;
    config.cost_split_switch = 1;
    config.min_large_switch_size = 0;
    return config;
  }

  static ::testing::AssertionResult test(
      const std::string& sig,
      const std::string& code_str,
      const method_splitting_impl::Config& config,
      std::initializer_list<std::pair<std::string, std::string>> expected,
      // Auxiliary classes the code under test references. They must go into the
      // store, not just the global class registry: a type whose class is
      // internal but held by no store is an illegal cross-store reference, so a
      // split taking one as an argument would be dropped.
      const std::vector<DexClass*>& extra_classes = {},
      bool no_outlining = false,
      // Select the closures first, then split them with
      // `split_selected_closures`.
      bool preselect = false) {
    auto [cls, m] = create(sig, code_str);
    m->get_code()->build_cfg();
    if (no_outlining) {
      m->rstate.set_no_outlining();
    }
    DexStoresVector stores;
    stores.emplace_back("test_store");
    DexClasses dex{cls};
    dex.insert(dex.end(), extra_classes.begin(), extra_classes.end());
    stores.front().get_dexen().push_back(std::move(dex));
    auto env = method_splitting_test::split_environment(
        stores, /* normal_primary_dex */ true);
    method_splitting_impl::Stats stats;
    if (preselect) {
      ConcurrentSet<DexMethod*> methods;
      methods.insert(m);
      auto splittable_closures =
          method_splitting_impl::select_splittable_closures_based_on_costs(
              methods, config, env.store_ref_checkers,
              /* concurrent_hot_methods */ nullptr,
              /* concurrent_splittable_no_optimizations_methods */ nullptr,
              stats);
      method_profiles::MethodProfiles method_profiles;
      method_splitting_impl::split_selected_closures(
          stores, env, splittable_closures, /* name_infix */ "",
          method_profiles, &stats);
    } else {
      method_splitting_impl::split_methods_in_stores(stores, env, config,
                                                     &stats);
    }
    // Every candidate is recorded once, at its final fate.
    const auto fates = stats.snapshot().suffix_fates;
    EXPECT_EQ(fates.recorded(), fates.candidates);
    m->get_code()->cfg().simplify();
    for (const auto& [out, kind] : stats.added_methods) {
      (void)kind;
      out->get_code()->cfg().simplify();
    }
    UnorderedMap<std::string, std::string> expected_map;
    for (const auto& p : expected) {
      expected_map.insert(p);
    }
    expected_map.emplace("", code_str);
    auto compare = [&](DexMethod* mm) {
      const auto name = mm->str();
      size_t index = name.find('$');
      std::string suffix;
      if (index != std::string::npos) {
        suffix = name.substr(index + 1);
      }
      auto it = expected_map.find(suffix);
      if (it == expected_map.end()) {
        return show(mm) + "(" + suffix + ") not expected.";
      }
      if (mm->get_code()->cfg_built()) {
        mm->get_code()->clear_cfg();
      }
      std::string out_str =
          replace_count(assembler::to_string(mm->get_code()), mm);
      auto exp_ir = assembler::ircode_from_string(it->second);
      std::string exp_str = assembler::to_string(exp_ir.get());
      if (out_str != exp_str) {
        return "Actual:\n" + out_str + "\nExpected:\n" + exp_str;
      }
      return std::string();
    };
    auto main_error = compare(m);
    if (!main_error.empty()) {
      return ::testing::AssertionFailure() << show(m) << ": " << main_error;
    }
    std::vector<DexMethod*> ordered;
    ordered.reserve(stats.added_methods.size());
    for (const auto& [out, kind] : stats.added_methods) {
      (void)kind;
      ordered.push_back(out);
    }
    std::sort(ordered.begin(), ordered.end(), compare_dexmethods);
    for (auto* out : ordered) {
      auto out_error = compare(out);
      if (!out_error.empty()) {
        return ::testing::AssertionFailure() << show(out) << ": " << out_error;
      }
    }
    if (stats.added_methods.size() + 1 != expected_map.size()) {
      return ::testing::AssertionFailure() << "Unexpected amount of methods";
    }
    return ::testing::AssertionSuccess();
  }

  // How many split methods splitting `code_str` creates.
  static size_t split_count(const std::string& sig,
                            const std::string& code_str,
                            const method_splitting_impl::Config& config) {
    auto [cls, m] = create(sig, code_str);
    m->get_code()->build_cfg();
    DexStoresVector stores;
    stores.emplace_back("test_store");
    stores.front().get_dexen().push_back({cls});
    auto env = method_splitting_test::split_environment(
        stores, /* normal_primary_dex */ true);
    method_splitting_impl::Stats stats;
    method_splitting_impl::split_methods_in_stores(stores, env, config, &stats);
    const auto fates = stats.snapshot().suffix_fates;
    EXPECT_EQ(fates.recorded(), fates.candidates);
    return stats.added_methods.size();
  }

 private:
  static std::atomic<size_t> s_counter;
};
std::atomic<size_t> MethodSplitterTest::s_counter{0};

namespace {
cfg::Block* profile_block(DexMethod* method, uint32_t id);
DexMethod* make_source_block_copy(DexClass* cls,
                                  DexMethod* method,
                                  const std::vector<cfg::Block*>& heads,
                                  cfg::Block* switch_block = nullptr);
} // namespace

TEST_F(MethodSplitterTest, ColdSuffixCopyDoesNotInheritHotJoinCounts) {
  auto [cls, method] = create("(I)I", R"((
    (load-param v0)
    (.src_block "LFoo;.bar:(I)I" 1 (10.0 100.0))
    (if-eqz v0 :cold)
    (.src_block "LFoo;.bar:(I)I" 2 (10.0 100.0))
    (add-int v0 v0 v0)
    (goto :join)
    (:cold)
    (.src_block "LFoo;.bar:(I)I" 3 (0.0 0.0))
    (add-int v0 v0 v0)
    (goto :join)
    (:join)
    (.src_block "LFoo;.bar:(I)I" 4 (10.0 100.0))
    (add-int v0 v0 v0)
    (return v0)
  ))");
  method->get_code()->build_cfg();
  auto* cold = profile_block(method, 3);
  auto* join = profile_block(method, 4);
  ASSERT_NE(cold, nullptr);
  ASSERT_NE(join, nullptr);
  auto* split = make_source_block_copy(cls, method, {cold});
  ASSERT_NE(split, nullptr);
  method->get_code()->cfg().remove_unreachable_blocks();
  auto& split_cfg = split->get_code()->cfg();
  split_cfg.remove_unreachable_blocks();
  auto* copy = split_cfg.get_block(join->id());
  ASSERT_NE(copy, nullptr);
  EXPECT_TRUE(method_splitting_impl::is_hot(join));
  EXPECT_FALSE(method_splitting_impl::is_hot(copy));
  EXPECT_FLOAT_EQ(*source_blocks::get_first_source_block(join)->get_val(0),
                  10.0f);
  EXPECT_FLOAT_EQ(*source_blocks::get_first_source_block(copy)->get_val(0),
                  0.0f);
}

TEST_F(MethodSplitterTest, NothingToDo) {
  const auto* before = R"(
    (
      (return-void)
    ))";
  const auto* after = before;
  auto res = test("()V",
                  before,
                  defaultConfig(),
                  {std::make_pair<std::string, std::string>("", after)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, NoOutliningPreventsSuffixExtraction) {
  const auto* before = R"((
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  EXPECT_TRUE(test("(I)I", before, defaultConfig(), {{"", before}}, {}, true));
}

TEST_F(MethodSplitterTest, SplitLargeBlock) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitNameSkipsExistingMethods) {
  // A method already has the name the split would get, e.g. a split made by
  // an earlier run. The split takes the next free name instead of replacing
  // that method.
  auto [cls, m] = create("(I)I", R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))");
  auto* existing =
      DexMethod::make_method(cls->get_type()->str() + ".bar$split$cold0:(I)I")
          ->make_concrete(ACC_PRIVATE | ACC_STATIC,
                          assembler::ircode_from_string(R"(
            (
              (load-param v0)
              (const v0 7)
              (return v0)
            ))"),
                          false);
  cls->add_method(existing);
  auto* existing_code = existing->get_code();
  existing_code->build_cfg();
  m->get_code()->build_cfg();
  DexStoresVector stores;
  stores.emplace_back("test_store");
  stores.front().get_dexen().push_back(DexClasses{cls});
  auto env = method_splitting_test::split_environment(
      stores, /* normal_primary_dex */ true);
  method_splitting_impl::Stats stats;
  method_splitting_impl::split_methods_in_stores(stores, env, defaultConfig(),
                                                 &stats);
  ASSERT_EQ(stats.added_methods.size(), 1);
  auto* split = stats.added_methods.begin()->first;
  EXPECT_EQ(split->str(), "bar$split$cold1");
  EXPECT_EQ(existing->get_code(), existing_code);
  size_t named_cold0 = 0;
  for (auto* d : cls->get_dmethods()) {
    named_cold0 += d->str() == "bar$split$cold0" ? 1 : 0;
  }
  EXPECT_EQ(named_cold0, 1);
}

TEST_F(MethodSplitterTest, KeepsConstructorCodeBeforeReceiverInitialization) {
  // The throwing check runs before the superclass constructor call. Splitting
  // it out would leave a launchpad that returns with the receiver
  // uninitialized, which ART's verifier rejects.
  std::string name = "LReceiverInit;";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  auto* init = DexMethod::make_method(name + ".<init>:(Ljava/lang/Object;)V")
                   ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR,
                                   assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (if-nez v1 :ok)
        (new-instance "Ljava/lang/IllegalStateException;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2) "Ljava/lang/IllegalStateException;.<init>:()V")
        (throw v2)
        (:ok)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      ))"),
                                   false);
  init->set_deobfuscated_name(show(init));
  cc.add_method(init);
  auto* cls = cc.create();
  init->get_code()->build_cfg();
  DexStoresVector stores;
  stores.emplace_back("test_store");
  stores.front().get_dexen().push_back(DexClasses{cls});
  auto env = method_splitting_test::split_environment(
      stores, /* normal_primary_dex */ true);
  method_splitting_impl::Stats stats;
  method_splitting_impl::split_methods_in_stores(stores, env, defaultConfig(),
                                                 &stats);
  EXPECT_EQ(stats.added_methods.size(), 0);
}

TEST_F(MethodSplitterTest, SplitPreselectedClosures) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  EXPECT_TRUE(test("(I)I", before, defaultConfig(),
                   {{"", after}, {"split$cold0", split0}}, {},
                   /* no_outlining */ false, /* preselect */ true));
}

TEST_F(MethodSplitterTest, SplitConstants) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (const v1 1)
      (const v2 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v1)
      (add-int v0 v0 v2)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (const v1 1)
      (const v2 2)
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v1)
      (add-int v0 v0 v2)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, CannotSplitUninitializedObject) {
  const auto* before = R"(
    (
      (load-param v0)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (return v0)
    ))";
  const auto* after = before;
  auto res = test("(I)I",
                  before,
                  defaultConfig(),
                  {std::make_pair<std::string, std::string>("", after)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, CanSplitInitializedObject) {
  const auto* before = R"(
    (
      (load-param v0)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-object v1)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (.pos:dbg_0 "LFoo;.bar:(I)Ljava/lang/Object;" RedexGenerated 0)
      (invoke-static (v0 v1) "LFoo;.bar$split$cold0:(ILjava/lang/Object;)Ljava/lang/Object;")
      (move-result-object v0)
      (return-object v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (load-param-object v1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-object v1)
    ))";
  auto res =
      test("(I)Ljava/lang/Object;",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitBranchFallthrough) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (if-eqz v0 :L0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
    (:L0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (if-eqz v0 :L0)
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    (:L0)
      (return v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitSwitch) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:a :b :c :d))
      (return v0)
    (:a 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:b 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:d 3)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:b :a))
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    (:b 1)
      (invoke-static (v0) "LFoo;.bar$split$cold2:(I)I")
      (move-result v0)
      (return v0)
    (:a 0)
      (invoke-static (v0) "LFoo;.bar$split$cold1:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0cd = R"(
    (
      (load-param v0)
      (switch v0 (:d :c))
      (return v0)
    (:d 3)
      (add-int v0 v0 v0)
      (return v0)
    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split1a = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split2b = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0cd),
            std::make_pair<std::string, std::string>("split$cold1", split1a),
            std::make_pair<std::string, std::string>("split$cold2", split2b)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitHotColdSwitch) {
  const auto* before = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:()V" 1 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:a :b :c :d))
    (:fallthrough)
      (.src_block "LFoo;.bar:()V" 2 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:a 0)
      (.src_block "LFoo;.bar:()V" 3 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:b 1)
      (.src_block "LFoo;.bar:()V" 4 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:c 2)
      (.src_block "LFoo;.bar:()V" 5 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:d 3)
      (.src_block "LFoo;.bar:()V" 6 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:()V" 1 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:c :a))

      (.src_block "LFoo;.bar:(I)I" 4294967295 (0.0 0.0))
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$hot_cold0:(I)I")
      (move-result v0)
      (return v0)
    (:c 2)
      (.src_block "LFoo;.bar:()V" 5 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:a 0)
      (.src_block "LFoo;.bar:()V" 3 (0.5 0.5))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar$split$hot_cold0:(I)I" 4294967295 (0.0 0.0))
      (switch v0 (:L0 :L1))

      (.src_block "LFoo;.bar:()V" 2 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:L0 3)
      (.src_block "LFoo;.bar:()V" 6 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:L1 1)
      (.src_block "LFoo;.bar:()V" 4 (0.0 0.0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto config = defaultConfig();
  config.min_hot_split_size = 16;
  config.min_hot_cold_split_size = 8;
  config.min_cold_split_size = 1000;
  config.max_overhead_ratio = 0.8;
  auto res = test(
      "(I)I",
      before,
      config,
      {std::make_pair<std::string, std::string>("", after),
       std::make_pair<std::string, std::string>("split$hot_cold0", split0)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitSwitchPreferCasesWithSharedCode) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:a :b :c :d))
      (return v0)
    (:a 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :shared)
    (:b 11)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:c 22)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:d 33)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :shared)

    (:shared)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:b :c))
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    (:b 11)
      (invoke-static (v0) "LFoo;.bar$split$cold2:(I)I")
      (move-result v0)
      (return v0)
    (:c 22)
      (invoke-static (v0) "LFoo;.bar$split$cold1:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0ad = R"(
    (
      (load-param v0)
      (switch v0 (:d :a))
      (return v0)
    (:d 33)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :shared)
    (:a 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)

    (:shared)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split1b = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split2c = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0ad),
            std::make_pair<std::string, std::string>("split$cold1", split1b),
            std::make_pair<std::string, std::string>("split$cold2", split2c)});
  ASSERT_TRUE(res);
}

TEST_F(MethodSplitterTest, SplitSwitchPreferNotBreakingLargePackedSwitches) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:a :b :c :d))
      (return v0)
    (:a 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :shared)
    (:b 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    (:d 3)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :shared)

    (:shared)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:b :a))
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    (:b 1)
      (invoke-static (v0) "LFoo;.bar$split$cold2:(I)I")
      (move-result v0)
      (return v0)
    (:a 0)
      (invoke-static (v0) "LFoo;.bar$split$cold1:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0cd = R"(
    (
      (load-param v0)
      (switch v0 (:d :c))
      (return v0)
    (:d 3)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)

    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split1a = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split2b = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0cd),
            std::make_pair<std::string, std::string>("split$cold1", split1a),
            std::make_pair<std::string, std::string>("split$cold2", split2b)});
  ASSERT_TRUE(res);
}

// When computing type demand for split proto, only consider type demands from
// instructions that are being split out. Here, the demand for LSpecificType; in
// the iput-object must be ignored, and the argument type must only be
// Ljava/lang/Object; not LSpecificType;.
TEST_F(MethodSplitterTest, SplitTypeDemands) {
  ClassCreator cc{DexType::make_type("LSpecificType;")};
  cc.set_super(type::java_lang_Object());
  auto* specific_type_cls = cc.create();

  const auto* before = R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param-object v2)
      (if-eqz v0 :specific_type_demand)
      (if-eqz v1 :weaken_type)
    (:code_to_split_out)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-object v2)

    (:weaken_type)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
      (goto :code_to_split_out)
    (:specific_type_demand)
      (iput-object v2 v2 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param-object v2)
      (if-eqz v0 :specific_type_demand)
      (if-eqz v1 :weaken_type)
    (:code_to_split_out)
      (.pos:dbg_0 "LFoo;.bar:(IILSpecificType;)Ljava/lang/Object;" RedexGenerated 0)
      (invoke-static (v0 v2) "LFoo;.bar$split$cold0:(ILjava/lang/Object;)Ljava/lang/Object;")
      (move-result-object v0)
      (return-object v0)

    (:weaken_type)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
      (goto :code_to_split_out)
    (:specific_type_demand)
      (iput-object v2 v2 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (load-param-object v2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-object v2)
    ))";
  auto config = defaultConfig();
  config.min_cold_split_size = 8;
  auto res =
      test("(IILSpecificType;)Ljava/lang/Object;",
           before,
           config,
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)},
           {specific_type_cls});
  ASSERT_TRUE(res);
}

// When determining type demands on values flowing into the code to split-out,
// only consider uses of definitions that flow through the register involved in
// the outlined call.
TEST_F(MethodSplitterTest, SplitTypeDemandsRegression) {
  ClassCreator cc{DexType::make_type("LSpecificType;")};
  cc.set_super(type::java_lang_Object());
  auto* specific_type_cls = cc.create();

  const auto* before = R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param-object v2)
      (move-object v3 v2)
      (if-eqz v0 :specific_type_demand)
      (if-eqz v1 :weaken_type)
    (:code_to_split_out)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (iput-object v3 v3 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)

    (:weaken_type)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
      (goto :code_to_split_out)
    (:specific_type_demand)
      (iput-object v2 v2 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param-object v2)
      (move-object v3 v2)
      (if-eqz v0 :specific_type_demand)
      (if-eqz v1 :weaken_type)
    (:code_to_split_out)
      (.pos:dbg_0 "LFoo;.bar:(IILSpecificType;)Ljava/lang/Object;" RedexGenerated 0)
      (invoke-static (v0 v2 v3) "LFoo;.bar$split$cold0:(ILjava/lang/Object;LSpecificType;)Ljava/lang/Object;")
      (move-result-object v0)
      (return-object v0)

    (:weaken_type)
      (new-instance "Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
      (goto :code_to_split_out)
    (:specific_type_demand)
      (iput-object v2 v2 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)
    ))";
  const auto* split0 = R"(
    (
      (load-param v0)
      (load-param-object v2)
      (load-param-object v3)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (iput-object v3 v3 "LSpecificType;.foo:LSpecificType;")
      (return-object v2)
    ))";
  auto config = defaultConfig();
  config.min_cold_split_size = 8;
  auto res =
      test("(IILSpecificType;)Ljava/lang/Object;",
           before,
           config,
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0)},
           {specific_type_cls});
  ASSERT_TRUE(res);
}

// A suffix whose head is a loop is entered at the loop header, so a def inside
// the loop reaches its own entry through the back edge. The launchpad passes
// only the defs from outside the closure. Adding the in-loop def's uses to the
// parameter's type would type it `LLoopB;` here, while the host passes its
// `LLoopA;` parameter.
TEST_F(MethodSplitterTest, LoopHeadedSplitTypesLiveInsByTheDefsItIsPassed) {
  ClassCreator a_creator{DexType::make_type("LLoopA;")};
  a_creator.set_super(type::java_lang_Object());
  auto* a_cls = a_creator.create();
  ClassCreator b_creator{DexType::make_type("LLoopB;")};
  b_creator.set_super(a_cls->get_type());
  auto* b_cls = b_creator.create();
  auto [cls, m] = create("(ILLoopA;)V", R"(
    (
      (load-param v0)
      (load-param-object v1)
      (mul-int v0 v0 v0)
      (mul-int v0 v0 v0)
      (mul-int v0 v0 v0)
      (mul-int v0 v0 v0)
      (mul-int v0 v0 v0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :exit)
    (:loop)
      (sput-object v1 "LLoopA;.a:LLoopA;")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (sget-object "LLoopB;.b:LLoopB;")
      (move-result-pseudo-object v1)
      (sput-object v1 "LLoopB;.b:LLoopB;")
      (if-nez v0 :loop)
      (sput v0 "LLoopA;.i:I")
      (return-void)
    (:exit)
      (return-void)
    ))");
  m->get_code()->build_cfg();
  DexStoresVector stores;
  stores.emplace_back("test_store");
  stores.front().get_dexen().push_back({cls, a_cls, b_cls});
  auto env = method_splitting_test::split_environment(
      stores, /* normal_primary_dex */ true);
  // One entry block, and the loop's exit alone is below the floor, so the
  // split is the loop.
  auto config = defaultConfig();
  config.split_block_size = 100000;
  config.min_cold_split_size = 8;
  method_splitting_impl::Stats stats;
  method_splitting_impl::split_methods_in_stores(stores, env, config, &stats);
  ASSERT_EQ(stats.added_methods.size(), 1u);
  auto* split = stats.added_methods.front().first;
  EXPECT_EQ(show(split->get_proto()), "(ILLoopA;)V");
}

TEST_F(MethodSplitterTest, DontSplitLoadParamChains) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param v2)
      (load-param v3)
      (load-param v4)
      (load-param v5)
      (load-param v6)
      (load-param v7)
      (load-param v8)
      (load-param v9)
      (return v0)
    ))";
  auto [cls, m] = create("(IIIIIIIIII)I", code_str);
  m->get_code()->build_cfg();
  auto config = defaultConfig();
  method_splitting_impl::normalize_cfg_for_splitting(m,
                                                     config.split_block_size);
  const auto reduced = method_splitting_impl::reduce_cfg(m);
  method_splitting_impl::discover_closures(m, reduced);
  ASSERT_EQ(m->get_code()->cfg().blocks().size(), 1);
  m->get_code()->clear_cfg();
}

TEST_F(MethodSplitterTest, NormalizeTransitiveEmptyBlocksBeforeReturn) {
  auto [cls, m] = create("()V", "((return-void))");
  m->get_code()->build_cfg();
  auto& cfg = m->get_code()->cfg();
  auto* return_block = cfg.entry_block();
  auto* entry_block = cfg.create_block();
  auto* empty_block = cfg.create_block();
  cfg.set_entry_block(entry_block);
  cfg.add_edge(entry_block, empty_block, cfg::EDGE_GOTO);
  cfg.add_edge(empty_block, return_block, cfg::EDGE_GOTO);

  method_splitting_impl::normalize_cfg_for_splitting(m);

  ASSERT_EQ(cfg.num_blocks(), 1);
  auto first_insn = cfg.entry_block()->get_first_insn();
  ASSERT_NE(first_insn, cfg.entry_block()->end());
  EXPECT_EQ(first_insn->insn->opcode(), OPCODE_RETURN_VOID);
  method_splitting_impl::reduce_cfg(m);
  m->get_code()->clear_cfg();
}

TEST_F(MethodSplitterTest, DuplicateSourceBlocksWithReturn) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
    (if-eqz v0 :return)
      (const v1 1)
      (goto :return)
    (:return)
      (return v1)
    ))";
  auto [cls, m] = create("(II)I", code_str);
  m->get_code()->build_cfg();
  auto profile = std::vector<source_blocks::ProfileData>{
      std::make_pair("(1:1 g(0:0 g(1:1)) b)", std::nullopt)};
  auto res =
      source_blocks::insert_source_blocks(m, &m->get_code()->cfg(), profile,
                                          /*serialize=*/true);
  auto config = defaultConfig();
  method_splitting_impl::normalize_cfg_for_splitting(m,
                                                     config.split_block_size);
  auto blocks = m->get_code()->cfg().blocks();
  ASSERT_TRUE(blocks.size() >= 3);
  auto source_blocks = source_blocks::gather_source_blocks(blocks[1]);
  ASSERT_EQ(source_blocks.size(), 2);
  m->get_code()->clear_cfg();
}

namespace {

cfg::Block* profile_block(DexMethod* method, uint32_t id) {
  for (auto* block : method->get_code()->cfg().blocks()) {
    auto* sb = source_blocks::get_first_source_block(block);
    if (sb != nullptr && sb->id == id) {
      return block;
    }
  }
  return nullptr;
}

void replace_test_profile(cfg::Block* block,
                          const std::vector<SourceBlock::Val>& vals) {
  for (auto& mie : *block) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      mie.src_block = std::make_unique<SourceBlock>(mie.src_block->src,
                                                    mie.src_block->id, vals);
      return;
    }
  }
  ADD_FAILURE() << "Missing fixture SourceBlock";
}

void remove_test_profile(cfg::Block* block) {
  for (auto it = block->begin(); it != block->end(); ++it) {
    if (it->type == MFLOW_SOURCE_BLOCK) {
      block->remove_mie(it);
      return;
    }
  }
  ADD_FAILURE() << "Missing fixture SourceBlock";
}

std::optional<method_splitting_impl::SplittableClosure> make_test_closure(
    const std::shared_ptr<method_splitting_impl::MethodClosures>& mcs,
    const std::vector<cfg::Block*>& heads,
    cfg::Block* switch_block = nullptr) {
  std::vector<const method_splitting_impl::Closure*> closures;
  closures.reserve(heads.size());
  UnorderedSet<cfg::BlockId> head_ids;
  for (auto* head : heads) {
    head_ids.insert(head->id());
    auto it = std::find_if(
        mcs->closures.begin(), mcs->closures.end(),
        [head](const auto& closure) { return closure.target == head; });
    if (it == mcs->closures.end()) {
      ADD_FAILURE() << "Missing fixture closure";
      return std::nullopt;
    }
    closures.push_back(&*it);
  }
  return method_splitting_impl::SplittableClosure{
      .method_closures = mcs,
      .switch_block = switch_block,
      .closures = std::move(closures),
      .grouped_heads = std::move(head_ids),
      .args = {{0, type::_int(), nullptr}},
      .rank = 0,
      .added_code_size = 0,
      .hot_split_kind = method_splitting_impl::HotSplitKind::HotCold,
      .net_terms = std::nullopt};
}

DexMethod* make_source_block_copy(DexClass* cls,
                                  DexMethod* method,
                                  const std::vector<cfg::Block*>& heads,
                                  cfg::Block* switch_block) {
  method_splitting_impl::normalize_cfg_for_splitting(method);
  auto rcfg = method_splitting_impl::reduce_cfg(method);
  auto mcs = method_splitting_impl::discover_closures(method, rcfg);
  EXPECT_NE(mcs, nullptr);
  if (!mcs) {
    return nullptr;
  }
  auto sc = make_test_closure(mcs, heads, switch_block);
  if (!sc) {
    return nullptr;
  }
  auto split = method_splitting_impl::SplitMethod::create(
      *sc, cls->get_type(), DexString::make_string("profileCopy"),
      sc->get_arg_types());
  split.add_to_target();
  split.apply_code_changes();
  return split.get_new_method();
}

std::string shared_copy_fixture(bool loop = false) {
  std::string code = R"((
    (load-param v0)
    (.src_block "LFoo;.bar:(I)I" 1 (10.0 100.0))
    (if-eqz v0 :cold)
    (.src_block "LFoo;.bar:(I)I" 2 (10.0 100.0))
    (add-int v0 v0 v0)
    (goto :join)
    (:cold)
    (.src_block "LFoo;.bar:(I)I" 3 (0.0 0.0))
    (add-int v0 v0 v0)
    (goto :private)
    (:private)
    (.src_block "LFoo;.bar:(I)I" 5 (0.0 0.0))
    (add-int v0 v0 v0)
    (:join)
    (.src_block "LFoo;.bar:(I)I" 4 (10.0 100.0))
    (add-int v0 v0 v0)
  )";
  code += loop ? R"(
    (if-eqz v0 :tail)
    (.src_block "LFoo;.bar:(I)I" 7 (10.0 100.0))
    (add-int v0 v0 v0)
    (goto :join)
  )"
               : "(goto :tail)\n";
  return code + R"(
    (:tail)
    (.src_block "LFoo;.bar:(I)I" 6 (20.0 100.0))
    (add-int v0 v0 v0)
    (return v0)
  ))";
}

} // namespace

TEST_F(MethodSplitterTest,
       SharedCopyPreservesInteractionsAndSourceBlockChains) {
  auto [cls, method] = create("(I)I", shared_copy_fixture());
  method->get_code()->build_cfg();
  auto* head = profile_block(method, 3);
  auto* private_block = profile_block(method, 5);
  auto* join = profile_block(method, 4);
  auto* tail = profile_block(method, 6);
  ASSERT_NE(head, nullptr);
  ASSERT_NE(private_block, nullptr);
  ASSERT_NE(join, nullptr);
  ASSERT_NE(tail, nullptr);
  replace_test_profile(head, {{0, 0}, {1, 10}, {0, 0}, {0, 0}});
  replace_test_profile(private_block, {{0, 0}, {0, 0}, {0, 0}, {0, 0}});
  replace_test_profile(join, {{std::numeric_limits<float>::infinity(), 80},
                              {10, 81},
                              SourceBlock::Val::none(),
                              {30, 83}});
  replace_test_profile(tail, {{20, 90}, {21, 91}, {22, 92}, {23, 93}});
  auto* head_sb = source_blocks::get_first_source_block(head);
  head_sb->next = std::make_unique<SourceBlock>(
      head_sb->src, 30,
      std::vector<SourceBlock::Val>{
          {0, 0}, {0, 0}, {0, 0}, SourceBlock::Val::none()});
  auto* join_sb = source_blocks::get_first_source_block(join);
  join_sb->next = std::make_unique<SourceBlock>(
      join_sb->src, 40,
      std::vector<SourceBlock::Val>{{11, 70}, {12, 71}, {13, 72}, {14, 73}});
  const SourceBlock join_before(*join_sb);
  const SourceBlock tail_before(*source_blocks::get_first_source_block(tail));
  const SourceBlock head_before(*head_sb);
  auto* split = make_source_block_copy(cls, method, {head});
  ASSERT_NE(split, nullptr);
  auto* copied_join = profile_block(split, 4);
  auto* copied_tail = profile_block(split, 6);
  ASSERT_NE(copied_join, nullptr);
  ASSERT_NE(copied_tail, nullptr);
  auto* copy_sb = source_blocks::get_first_source_block(copied_join);
  ASSERT_NE(copy_sb->next, nullptr);
  for (size_t i = 0; i < 4; ++i) {
    SCOPED_TRACE(i);
    const bool cold = i == 0 || i == 2;
    EXPECT_EQ(copy_sb->get_val(i),
              i == 2 ? std::nullopt
              : cold ? std::optional<float>{0}
                     : join_before.get_val(i));
    EXPECT_EQ(copy_sb->next->get_val(i),
              cold ? std::optional<float>{0} : join_before.next->get_val(i));
    EXPECT_EQ(source_blocks::get_first_source_block(copied_tail)->get_val(i),
              cold ? std::optional<float>{0} : tail_before.get_val(i));
    EXPECT_EQ(copy_sb->get_appear100(i), join_before.get_appear100(i));
    EXPECT_EQ(copy_sb->next->get_appear100(i),
              join_before.next->get_appear100(i));
    EXPECT_EQ(join_sb->get_at(i), join_before.get_at(i));
    EXPECT_EQ(join_sb->next->get_at(i), join_before.next->get_at(i));
    EXPECT_EQ(head_sb->get_at(i), head_before.get_at(i));
    EXPECT_EQ(head_sb->next->get_at(i), head_before.next->get_at(i));
  }
}

TEST_F(MethodSplitterTest,
       PrivateOrHeadUnknownEvidenceProtectsSharedDescendants) {
  for (bool at_head : {false, true}) {
    for (int evidence = 0; evidence < 4; ++evidence) {
      SCOPED_TRACE(at_head);
      SCOPED_TRACE(evidence);
      auto [cls, method] = create("(I)I", shared_copy_fixture());
      method->get_code()->build_cfg();
      auto* head = profile_block(method, 3);
      auto* private_block = profile_block(method, 5);
      auto* join = profile_block(method, 4);
      auto* tail = profile_block(method, 6);
      ASSERT_NE(head, nullptr);
      ASSERT_NE(private_block, nullptr);
      ASSERT_NE(join, nullptr);
      ASSERT_NE(tail, nullptr);
      replace_test_profile(head, {{0, 0}, {0, 0}});
      replace_test_profile(private_block, {{0, 0}, {0, 0}});
      replace_test_profile(join, {{10, 80}, {20, 81}});
      replace_test_profile(tail, {{30, 90}, {40, 91}});
      auto* seed = at_head ? head : private_block;
      const auto seed_id = seed->id();
      if (evidence == 0) {
        replace_test_profile(seed, {{9, 70}, {0, 0}});
      } else if (evidence == 1) {
        auto* sb = source_blocks::get_first_source_block(seed);
        sb->next = std::make_unique<SourceBlock>(
            sb->src, 50,
            std::vector<SourceBlock::Val>{SourceBlock::Val::none(), {0, 0}});
      } else if (evidence == 2) {
        remove_test_profile(seed);
      } else {
        replace_test_profile(seed, {{0, 0}});
      }
      auto before = source_blocks::gather_source_blocks(seed);
      std::vector<SourceBlock> seed_before;
      seed_before.reserve(before.size());
      for (auto* sb : before) {
        seed_before.emplace_back(*sb);
      }
      auto* split = make_source_block_copy(cls, method, {head});
      ASSERT_NE(split, nullptr);
      auto* copy_seed = split->get_code()->cfg().get_block(seed_id);
      ASSERT_NE(copy_seed, nullptr);
      auto copied_seed = source_blocks::gather_source_blocks(copy_seed);
      ASSERT_EQ(copied_seed.size(), seed_before.size());
      for (size_t s = 0; s < copied_seed.size(); ++s) {
        EXPECT_EQ(copied_seed[s]->vals_size, seed_before[s].vals_size);
        for (size_t i = 0; i < copied_seed[s]->vals_size; ++i) {
          EXPECT_EQ(copied_seed[s]->get_at(i), seed_before[s].get_at(i));
        }
      }
      auto* copy_join = profile_block(split, 4);
      auto* copy_tail = profile_block(split, 6);
      ASSERT_NE(copy_join, nullptr);
      ASSERT_NE(copy_tail, nullptr);
      for (size_t i = 0; i < 2; ++i) {
        const bool protected_slot =
            evidence == 2 || (evidence == 3 ? i == 1 : i == 0);
        EXPECT_EQ(source_blocks::get_first_source_block(copy_join)->get_val(i),
                  std::optional<float>{protected_slot ? i == 0 ? 10.0f : 20.0f
                                                      : 0.0f});
        EXPECT_EQ(source_blocks::get_first_source_block(copy_tail)->get_val(i),
                  std::optional<float>{protected_slot ? i == 0 ? 30.0f : 40.0f
                                                      : 0.0f});
        EXPECT_EQ(source_blocks::get_first_source_block(join)->get_val(i),
                  std::optional<float>{i == 0 ? 10.0f : 20.0f});
      }
    }
  }
}

TEST_F(MethodSplitterTest, SharedLoopCopyDoesNotResurrectHotBackedgeCounts) {
  auto [cls, method] = create("(I)I", shared_copy_fixture(true));
  method->get_code()->build_cfg();
  auto* head = profile_block(method, 3);
  auto* join = profile_block(method, 4);
  ASSERT_NE(head, nullptr);
  ASSERT_NE(join, nullptr);
  method_splitting_impl::ReducedControlFlowGraph graph(
      method->get_code()->cfg());
  EXPECT_GT(graph.get_reduced_block(join)->blocks.size(), 1u);
  auto* split = make_source_block_copy(cls, method, {head});
  ASSERT_NE(split, nullptr);
  auto host_reached = method->get_code()->cfg().visit();
  auto split_reached = split->get_code()->cfg().visit();
  for (uint32_t id : {4u, 7u, 6u}) {
    auto* original = profile_block(method, id);
    auto* copy = profile_block(split, id);
    ASSERT_NE(original, nullptr);
    ASSERT_NE(copy, nullptr);
    EXPECT_TRUE(host_reached[original->id()]);
    EXPECT_TRUE(split_reached[copy->id()]);
    auto* original_sb = source_blocks::get_first_source_block(original);
    auto* copy_sb = source_blocks::get_first_source_block(copy);
    EXPECT_EQ(copy_sb->get_val(0), std::optional<float>{0});
    EXPECT_EQ(original_sb->get_val(0),
              std::optional<float>{id == 6 ? 20.0f : 10.0f});
    EXPECT_EQ(copy_sb->get_appear100(0), original_sb->get_appear100(0));
  }
}

TEST_F(MethodSplitterTest, MixedSwitchHeadsProtectOnlyTheirSharedPaths) {
  for (int evidence = 0; evidence < 4; ++evidence) {
    SCOPED_TRACE(evidence);
    auto [cls, method] = create("(I)I", R"((
      (load-param v0)
      (.src_block "LFoo;.bar:(I)I" 1 (10.0 100.0))
      (switch v0 (:hot :retained))
      (.src_block "LFoo;.bar:(I)I" 3 (0.0 0.0))
      (add-int v0 v0 v0)
      (goto :cold_join)
      (:hot 0)
      (.src_block "LFoo;.bar:(I)I" 4 (10.0 100.0))
      (add-int v0 v0 v0)
      (goto :hot_join)
      (:retained 1)
      (.src_block "LFoo;.bar:(I)I" 5 (10.0 100.0))
      (if-eqz v0 :hot_join)
      (:cold_join)
      (.src_block "LFoo;.bar:(I)I" 6 (20.0 100.0))
      (add-int v0 v0 v0)
      (return v0)
      (:hot_join)
      (.src_block "LFoo;.bar:(I)I" 7 (30.0 100.0))
      (add-int v0 v0 v0)
      (return v0)
    ))");
    method->get_code()->build_cfg();
    auto* cold = profile_block(method, 3);
    auto* hot = profile_block(method, 4);
    auto* dispatch = profile_block(method, 1);
    ASSERT_NE(cold, nullptr);
    ASSERT_NE(hot, nullptr);
    ASSERT_NE(dispatch, nullptr);
    replace_test_profile(cold, {{0, 0}, {0, 0}});
    replace_test_profile(hot, {{10, 70}, {0, 0}});
    replace_test_profile(profile_block(method, 6), {{20, 80}, {21, 81}});
    replace_test_profile(profile_block(method, 7), {{30, 90}, {31, 91}});
    if (evidence == 1) {
      replace_test_profile(hot, {{10, 70}, SourceBlock::Val::none()});
    } else if (evidence == 2) {
      replace_test_profile(hot, {{10, 70}});
    } else if (evidence == 3) {
      remove_test_profile(hot);
    }
    auto* split = make_source_block_copy(cls, method, {cold, hot}, dispatch);
    ASSERT_NE(split, nullptr);
    auto* cold_copy = profile_block(split, 6);
    auto* hot_copy = profile_block(split, 7);
    ASSERT_NE(cold_copy, nullptr);
    ASSERT_NE(hot_copy, nullptr);
    for (size_t i = 0; i < 2; ++i) {
      EXPECT_EQ(source_blocks::get_first_source_block(cold_copy)->get_val(i),
                std::optional<float>{0});
      EXPECT_EQ(source_blocks::get_first_source_block(hot_copy)->get_val(i),
                std::optional<float>{i == 0          ? 30.0f
                                     : evidence == 0 ? 0.0f
                                                     : 31.0f});
      EXPECT_EQ(source_blocks::get_first_source_block(profile_block(method, 6))
                    ->get_val(i),
                std::optional<float>{i == 0 ? 20.0f : 21.0f});
      EXPECT_EQ(source_blocks::get_first_source_block(profile_block(method, 7))
                    ->get_val(i),
                std::optional<float>{i == 0 ? 30.0f : 31.0f});
    }
  }
}

TEST_F(MethodSplitterTest, PreCreatedCopiesPreserveSharedAndEvictedProfiles) {
  for (int count : {2, 3}) {
    for (bool keep_host_path : {false, true}) {
      for (bool reverse : {false, true}) {
        SCOPED_TRACE(count);
        SCOPED_TRACE(keep_host_path);
        SCOPED_TRACE(reverse);
        std::string code = R"((
          (load-param v0)
          (.src_block "LFoo;.bar:(I)I" 1 (10.0 100.0))
        )";
        for (int i = 0; i < count; ++i) {
          code += "(if-eqz v0 :cold" + std::to_string(i) + ")\n";
          code += "(.src_block \"LFoo;.bar:(I)I\" " + std::to_string(100 + i) +
                  " (10.0 100.0))\n";
        }
        code += "(add-int v0 v0 v0)\n";
        code += keep_host_path ? "(goto :join)\n" : "(return v0)\n";
        for (int i = 0; i < count; ++i) {
          code += "(:cold" + std::to_string(i) + ")\n";
          code += "(.src_block \"LFoo;.bar:(I)I\" " + std::to_string(10 + i) +
                  " (0.0 0.0))\n";
          code += "(add-int v0 v0 v0)\n(goto :join)\n";
        }
        // Deliberately inconsistent input: cold heads share a hot tail.
        code += R"(
          (:join)
          (.src_block "LFoo;.bar:(I)I" 4 (10.0 80.0))
          (add-int v0 v0 v0)
          (return v0)
        ))";
        auto [cls, method] = create("(I)I", code);
        method->get_code()->build_cfg();
        method_splitting_impl::normalize_cfg_for_splitting(method);
        auto rcfg = method_splitting_impl::reduce_cfg(method);
        auto mcs = method_splitting_impl::discover_closures(method, rcfg);
        ASSERT_NE(mcs, nullptr);
        auto* join = profile_block(method, 4);
        ASSERT_NE(join, nullptr);
        const auto join_id = join->id();
        auto* host_sb = source_blocks::get_first_source_block(join);
        const SourceBlock before(*host_sb);
        std::deque<method_splitting_impl::SplittableClosure> closures;
        std::vector<method_splitting_impl::SplitMethod> splits;
        splits.reserve(count);
        for (int i = 0; i < count; ++i) {
          auto* head = profile_block(method, 10 + i);
          ASSERT_NE(head, nullptr);
          auto closure = make_test_closure(mcs, {head});
          ASSERT_TRUE(closure);
          closures.push_back(std::move(*closure));
          splits.push_back(method_splitting_impl::SplitMethod::create(
              closures.back(), cls->get_type(),
              DexString::make_string("copy" + std::to_string(i)),
              closures.back().get_arg_types()));
          splits.back().add_to_target();
        }
        // All copies exist before any host edges are rewritten.
        for (int i = 0; i < count; ++i) {
          const int index = reverse ? count - 1 - i : i;
          splits[index].apply_code_changes();
          auto& host_cfg = method->get_code()->cfg();
          const bool shared = host_cfg.visit()[join_id];
          auto& split_cfg = splits[index].get_new_method()->get_code()->cfg();
          ASSERT_TRUE(split_cfg.visit()[join_id]);
          auto* copy_sb = source_blocks::get_first_source_block(
              split_cfg.get_block(join_id));
          ASSERT_NE(copy_sb, nullptr);
          EXPECT_EQ(copy_sb->get_val(0),
                    shared ? std::optional<float>{0} : before.get_val(0));
          EXPECT_EQ(copy_sb->get_appear100(0), before.get_appear100(0));
          EXPECT_EQ(host_sb->get_at(0), before.get_at(0));
          EXPECT_EQ(host_sb->src, before.src);
          EXPECT_EQ(host_sb->id, before.id);
          EXPECT_EQ(host_sb->vals_size, before.vals_size);
          EXPECT_EQ(shared, keep_host_path || i + 1 < count);
        }
      }
    }
  }
}

TEST_F(MethodSplitterTest, UndupReturns) {
  const auto* before = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:a :b :c :d))
    (:common)
      (return v0)
    (:a 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :common)
    (:b 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :common)
    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :common)
    (:d 3)
      (add-int v0 v0 v0)
      (goto :common)
    ))";
  const auto* after = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (switch v0 (:b :a))
      (.pos:dbg_0 "LFoo;.bar:(I)I" RedexGenerated 0)
      (invoke-static (v0) "LFoo;.bar$split$cold0:(I)I")
      (move-result v0)
      (return v0)
    (:b 1)
      (invoke-static (v0) "LFoo;.bar$split$cold2:(I)I")
      (move-result v0)
      (return v0)
    (:a 0)
      (invoke-static (v0) "LFoo;.bar$split$cold1:(I)I")
      (move-result v0)
      (return v0)
    ))";
  const auto* split0cd = R"(
    (
      (load-param v0)
      (switch v0 (:d :c))
      (return v0)
    (:d 3)
      (add-int v0 v0 v0)
      (return v0)
    (:c 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split1a = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* split2b = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  auto res =
      test("(I)I",
           before,
           defaultConfig(),
           {std::make_pair<std::string, std::string>("", after),
            std::make_pair<std::string, std::string>("split$cold0", split0cd),
            std::make_pair<std::string, std::string>("split$cold1", split1a),
            std::make_pair<std::string, std::string>("split$cold2", split2b)});
  ASSERT_TRUE(res);
}

// Selects and splits the cases of a top-level switch the way a
// switch-outlining pass would. The switch and its cases carry source blocks,
// as such a pass would see them if it ran after source blocks are inserted.
// Those closures carry no split kind, so a split is not known to be cold, and
// its synthetic source blocks keep the values of the blocks they are modeled
// on.
TEST_F(MethodSplitterTest, TopLevelSwitchCasesWithSourceBlocksKeepTheirValues) {
  auto [cls, method] = create("(I)V", R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (switch v0 (:a :b))
      (return-void)
      (:a 0)
      (.src_block "LFoo;.bar:(I)V" 1 (1.0 1.0))
      (sput v0 "LFoo;.a0:I")
      (sput v0 "LFoo;.a1:I")
      (sput v0 "LFoo;.a2:I")
      (return-void)
      (:b 1)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (sput v0 "LFoo;.b0:I")
      (sput v0 "LFoo;.b1:I")
      (sput v0 "LFoo;.b2:I")
      (return-void)
    )
  )");
  method->get_code()->build_cfg();
  auto selected = method_splitting_impl::
      select_splittable_closures_from_top_level_switch_cases(
          {method}, /*max_live_in=*/32);
  const auto* closures = selected.get(method);
  ASSERT_NE(closures, nullptr);
  ASSERT_FALSE(closures->empty());
  size_t index = 0;
  for (const auto& sc : *closures) {
    auto split = method_splitting_impl::SplitMethod::create(
        sc, cls->get_type(),
        DexString::make_string("outlined$" + std::to_string(index++)),
        sc.get_arg_types());
    split.apply_code_changes();
  }
  size_t source_blocks = 0;
  for (auto* b : method->get_code()->cfg().blocks()) {
    for (auto* sb : source_blocks::gather_source_blocks(b)) {
      source_blocks++;
      ASSERT_TRUE(sb->get_val(0).has_value());
      EXPECT_EQ(*sb->get_val(0), 1.0f);
    }
  }
  EXPECT_GT(source_blocks, 0u);
}

// A candidate that needs more live-in registers than `max_live_in` allows is
// refused; one that needs exactly that many is split.
TEST_F(MethodSplitterTest, RefuseMoreLiveInsThanMaxLiveIn) {
  const auto* code = R"(
    (
      (load-param v0)
      (load-param v1)
      (add-int v0 v0 v1)
      (add-int v0 v0 v1)
      (add-int v0 v0 v1)
      (add-int v0 v0 v1)
      (add-int v0 v0 v1)
      (return v0)
    ))";
  auto config = defaultConfig();
  config.max_live_in = 2;
  EXPECT_EQ(split_count("(II)I", code, config), 1u);
  config.max_live_in = 1;
  EXPECT_EQ(split_count("(II)I", code, config), 0u);
}

// A live-in whose type neither its uses nor its definitions determine cannot
// become a parameter of the split, so the candidate is refused. Here `v1` is an
// int on one path and a string on the other, and every candidate only copies
// it into a register nothing reads.
TEST_F(MethodSplitterTest, RefuseLiveInWithoutType) {
  auto code = [](const std::string& use) {
    return R"(
    (
      (load-param v0)
      (if-eqz v0 :str)
      (add-int v1 v0 v0)
      (goto :join)
    (:str)
      (const-string "s")
      (move-result-pseudo-object v1)
    (:join)
      (move v2 v1)
      (add-int v0 v0 v0)
      (move v2 v1)
      (add-int v0 v0 v0)
      (move v2 v1)
      (add-int v0 v0 v0)
      (move v2 v1)
      (add-int v0 v0 v0)
      (move v2 v1)
      )" + use +
           R"(
      (return v0)
    ))";
  };
  // The same shape with the copy read as an int: typed by its use, and split.
  EXPECT_GT(split_count("(I)I", code("(add-int v0 v0 v2)"), defaultConfig()),
            0u);
  EXPECT_EQ(split_count("(I)I", code(""), defaultConfig()), 0u);
}

namespace {

// `n` writes of `v0` to distinct static fields named `<prefix>_<i>`, 2 code
// units each.
std::string sputs(size_t n, const std::string& prefix) {
  std::string out;
  for (size_t i = 0; i < n; ++i) {
    out += "  (sput v0 \"LFoo;." + prefix + "_" + std::to_string(i) + ":I\")\n";
  }
  return out;
}

// A hot entry (`kEntrySputs` writes) branches to a head block (`kHeadSputs`
// writes) or to a hot block (`kOtherSputs`), and both jump to a hot join
// (`kJoinSputs` writes, then `return-void`). The suffix at the head takes the
// head and the join, and the host keeps the join too: it still reaches it
// through the hot block. The head is cold unless `hot_head`, and every block
// is cold when `all_cold`.
constexpr size_t kEntrySputs = 100;
constexpr size_t kHeadSputs = 150;
constexpr size_t kOtherSputs = 5;
constexpr size_t kJoinSputs = 5;

std::string sharedJoinCode(bool hot_head, bool all_cold = false) {
  const std::string hot = all_cold ? "(0.0 0.0)" : "(1.0 1.0)";
  const std::string head = hot_head ? hot : "(0.0 0.0)";
  return "(\n  (load-param v0)\n  (.src_block \"LFoo;.bar:(I)V\" 0 " + hot +
         ")\n" + sputs(kEntrySputs, "entry") + "  (if-eqz v0 :other)\n" +
         "  (.src_block \"LFoo;.bar:(I)V\" 1 " + head + ")\n" +
         sputs(kHeadSputs, "head") + "  (goto :join)\n  (:other)\n" +
         "  (.src_block \"LFoo;.bar:(I)V\" 2 " + hot + ")\n" +
         sputs(kOtherSputs, "other") + "  (goto :join)\n  (:join)\n" +
         "  (.src_block \"LFoo;.bar:(I)V\" 3 " + hot + ")\n" +
         sputs(kJoinSputs, "join") + "  (return-void)\n)\n";
}

// What the host keeps of `sharedJoinCode` once the head's suffix is split: the
// entry with its `if-eqz`, the hot block, and the join with its
// `return-void`.
constexpr size_t kKeptCodeUnits =
    2 * kEntrySputs + 2 + 2 * kOtherSputs + 2 * kJoinSputs + 1;

// Floors that leave the head's suffix the only candidate to clear them: the
// hot block's and the join's suffixes are far smaller than the head's.
method_splitting_impl::Config floorConfig() {
  method_splitting_impl::Config config;
  config.min_original_size = 1;
  config.split_block_size = 100000;
  config.max_overhead_ratio = 0.5;
  config.max_hot_overhead_ratio = 0.5;
  config.max_iteration = 1;
  config.cost_split_method = 1;
  config.min_hot_cold_split_size = 4;
  config.min_hot_split_size = 4;
  config.min_cold_split_size = 4;
  return config;
}

} // namespace

// The remaining floor reads what the host keeps, including the join that the
// split copies. A floor of exactly that size admits the suffix, and a floor one
// code unit higher refuses it. The method's size less the suffix's blocks falls
// `kJoinSputs * 2 + 1` code units short of what the host keeps.
TEST_F(MethodSplitterTest, RemainingFloorHotColdAtItsBoundary) {
  auto config = floorConfig();
  config.min_hot_split_size = kKeptCodeUnits;
  EXPECT_EQ(split_count("(I)V", sharedJoinCode(/*hot_head=*/false), config),
            1u);
  config.min_hot_split_size = kKeptCodeUnits + 1;
  EXPECT_EQ(split_count("(I)V", sharedJoinCode(/*hot_head=*/false), config),
            0u);
}

// A hot suffix's floors are both `min_hot_split_size`.
TEST_F(MethodSplitterTest, RemainingFloorHotAtItsBoundary) {
  auto config = floorConfig();
  config.min_hot_split_size = kKeptCodeUnits;
  EXPECT_EQ(split_count("(I)V", sharedJoinCode(/*hot_head=*/true), config), 1u);
  config.min_hot_split_size = kKeptCodeUnits + 1;
  EXPECT_EQ(split_count("(I)V", sharedJoinCode(/*hot_head=*/true), config), 0u);
}

// A cold suffix's floors are both `min_cold_split_size`.
TEST_F(MethodSplitterTest, RemainingFloorColdAtItsBoundary) {
  auto config = floorConfig();
  const auto code = sharedJoinCode(/*hot_head=*/false, /*all_cold=*/true);
  config.min_cold_split_size = kKeptCodeUnits;
  EXPECT_EQ(split_count("(I)V", code, config), 1u);
  config.min_cold_split_size = kKeptCodeUnits + 1;
  EXPECT_EQ(split_count("(I)V", code, config), 0u);
}

namespace {

// A hot `switch` whose default (`kCaseSputs` writes) and two cases (as many
// writes each) are cold and return. The only candidate the floors of the test
// below admit is the group of the default and one case: each block alone is
// under the split floor.
constexpr size_t kCaseSputs = 100;

std::string switchGroupCode() {
  return "(\n  (load-param v0)\n  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
         "  (switch v0 (:a :b))\n"
         "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n" +
         sputs(kCaseSputs, "dflt") +
         "  (return-void)\n  (:a 1)\n"
         "  (.src_block \"LFoo;.bar:(I)V\" 2 (0.0 0.0))\n" +
         sputs(kCaseSputs, "casea") +
         "  (return-void)\n  (:b 2)\n"
         "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n" +
         sputs(kCaseSputs, "caseb") + "  (return-void)\n)\n";
}

} // namespace

// A group's remaining size is what the host keeps, less
// `cost_split_switch_case` for each case after the first, and its floor reads
// that size. The host keeps the entry (a 2-key packed `switch`, 11 code units
// with its payload) and the case the group leaves (`2 * kCaseSputs + 1` code
// units).
TEST_F(MethodSplitterTest, RemainingFloorOfASwitchGroupAtItsBoundary) {
  auto config = floorConfig();
  config.cost_split_switch_case = 20;
  config.min_hot_cold_split_size = 3 * kCaseSputs;
  constexpr size_t kGroupRemaining = 11 + 2 * kCaseSputs + 1 - 20;
  config.min_hot_split_size = kGroupRemaining;
  EXPECT_EQ(split_count("(I)V", switchGroupCode(), config), 1u);
  config.min_hot_split_size = kGroupRemaining + 1;
  EXPECT_EQ(split_count("(I)V", switchGroupCode(), config), 0u);
}

// The cases of a top-level switch, selected and split the way a
// switch-outlining pass does it. Those closures carry no split kind. Emission
// reads the kind only to set the values of a synthetic source block, and this
// host has no source blocks.
TEST_F(MethodSplitterTest, TopLevelSwitchCasesSplitWithoutAKind) {
  auto [cls, method] = create("(I)V", R"(
    (
      (load-param v0)
      (switch v0 (:a :b))
      (return-void)
      (:a 0)
      (sput v0 "LFoo;.a0:I")
      (sput v0 "LFoo;.a1:I")
      (sput v0 "LFoo;.a2:I")
      (return-void)
      (:b 1)
      (sput v0 "LFoo;.b0:I")
      (sput v0 "LFoo;.b1:I")
      (sput v0 "LFoo;.b2:I")
      (return-void)
    )
  )");
  method->get_code()->build_cfg();
  auto selected = method_splitting_impl::
      select_splittable_closures_from_top_level_switch_cases(
          {method}, /*max_live_in=*/32);
  const auto* closures = selected.get(method);
  ASSERT_NE(closures, nullptr);
  ASSERT_FALSE(closures->empty());
  size_t index = 0;
  for (const auto& sc : *closures) {
    EXPECT_FALSE(sc.hot_split_kind.has_value());
    auto split = method_splitting_impl::SplitMethod::create(
        sc, cls->get_type(),
        DexString::make_string("outlined$" + std::to_string(index++)),
        sc.get_arg_types());
    split.apply_code_changes();
  }
}
