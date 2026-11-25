/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>
#include <unordered_map>

#include <gtest/gtest.h>

#include "MethodClosures.h"
#include "MethodSplitter.h"

#include "Creators.h"
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
      const std::vector<DexClass*>& extra_classes = {}) {
    auto [cls, m] = create(sig, code_str);
    m->get_code()->build_cfg();
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
    m->get_code()->cfg().simplify();
    for (auto* out : UnorderedIterable(stats.added_methods)) {
      out->get_code()->cfg().simplify();
    }
    std::unordered_map<std::string, std::string> expected_map;
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
    auto ordered =
        unordered_to_ordered(stats.added_methods, compare_dexmethods);
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
  method_splitting_impl::discover_closures(
      m, method_splitting_impl::reduce_cfg(m, config.split_block_size));
  ASSERT_EQ(m->get_code()->cfg().blocks().size(), 1);
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
  method_splitting_impl::reduce_cfg(m, config.split_block_size);
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
