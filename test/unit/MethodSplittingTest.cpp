/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>

#include <gtest/gtest.h>

#include "MethodClosures.h"
#include "MethodSplitter.h"
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
      bool no_outlining = false) {
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
    method_splitting_impl::StoreRefCheckers store_ref_checkers(
        stores, /* normal_primary_dex */ true, /* min_sdk_api */ nullptr);
    method_splitting_impl::Stats stats;
    method_splitting_impl::split_methods_in_stores(
        stores, /* min_sdk */ 0, config, store_ref_checkers,
        /* create_init_class_insns */ false,
        /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats);
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
    method_splitting_impl::StoreRefCheckers store_ref_checkers(
        stores, /* normal_primary_dex */ true, /* min_sdk_api */ nullptr);
    method_splitting_impl::Stats stats;
    method_splitting_impl::split_methods_in_stores(
        stores, /* min_sdk */ 0, config, store_ref_checkers,
        /* create_init_class_insns */ false,
        /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats);
    const auto fates = stats.snapshot().suffix_fates;
    EXPECT_EQ(fates.recorded(), fates.candidates);
    return stats.added_methods.size();
  }

 private:
  static std::atomic<size_t> s_counter;
};
std::atomic<size_t> MethodSplitterTest::s_counter{0};

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
  method_splitting_impl::StoreRefCheckers store_ref_checkers(
      stores, /* normal_primary_dex */ true, /* min_sdk_api */ nullptr);
  method_splitting_impl::Stats stats;
  method_splitting_impl::split_methods_in_stores(
      stores, /* min_sdk */ 0, defaultConfig(), store_ref_checkers,
      /* create_init_class_insns */ false,
      /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats);
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
  method_splitting_impl::StoreRefCheckers store_ref_checkers(
      stores, /* normal_primary_dex */ true, /* min_sdk_api */ nullptr);
  // One entry block, and the loop's exit alone is below the floor, so the
  // split is the loop.
  auto config = defaultConfig();
  config.split_block_size = 100000;
  config.min_cold_split_size = 8;
  method_splitting_impl::Stats stats;
  method_splitting_impl::split_methods_in_stores(
      stores, /* min_sdk */ 0, config, store_ref_checkers,
      /* create_init_class_insns */ false,
      /* reserved_mrefs */ 0, /* reserved_trefs */ 0, &stats);
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
