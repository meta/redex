/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <atomic>
#include <gtest/gtest.h>
#include <memory>
#include <string>

#include "SplitHugeSwitchPass.h"

#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodProfiles.h"
#include "RedexTest.h"
#include "Show.h"

class SplitHugeSwitchTest : public RedexTest {
 public:
  static DexMethod* create(const std::string& sig,
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
    cc.add_method(m);

    cc.create();

    return m;
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

  static ::testing::AssertionResult test(
      const std::string& sig,
      const std::string& code_str,
      size_t code_units_threshold,
      size_t case_threshold,
      const method_profiles::MethodProfiles& method_profiles,
      double hotness_threshold,
      std::initializer_list<std::pair<std::string, std::string>> expected) {
    auto* m = create(sig, code_str);
    auto stats = SplitHugeSwitchPass::run(m, m->get_code(),
                                          code_units_threshold, case_threshold,
                                          method_profiles, hotness_threshold);
    UnorderedMap<std::string, std::string> expected_map;
    for (const auto& p : expected) {
      expected_map.insert(p);
    }
    expected_map.emplace("", code_str);
    auto compare = [&](DexMethod* m) {
      const auto name = m->str();
      size_t index = name.find('$');
      std::string suffix;
      if (index != std::string::npos) {
        suffix = name.substr(index + 1);
      }
      auto it = expected_map.find(suffix);
      if (it == expected_map.end()) {
        return show(m) + "(" + suffix + ") not expected.";
      }
      if (m->get_code()->cfg_built()) {
        m->get_code()->clear_cfg();
      }
      std::string out_str =
          replace_count(assembler::to_string(m->get_code()), m);
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
    for (auto* out : UnorderedIterable(stats.new_methods)) {
      auto out_error = compare(out);
      if (!out_error.empty()) {
        return ::testing::AssertionFailure() << show(out) << ": " << out_error;
      }
    }
    if (stats.orig_methods.size() != stats.new_methods.size()) {
      return ::testing::AssertionFailure()
             << "Unexpected amount of orig methods";
    }
    if (stats.new_methods.size() + 1 != expected_map.size()) {
      return ::testing::AssertionFailure() << "Unexpected amount of methods";
    }
    return ::testing::AssertionSuccess();
  }

 private:
  static std::atomic<size_t> s_counter;
};
std::atomic<size_t> SplitHugeSwitchTest::s_counter{0};

TEST_F(SplitHugeSwitchTest, NoSwitch) {
  const auto* src = R"(
    (
      (load-param v0)
      (return-void)
    ))";
  auto res = test("(I)V",
                  src,
                  0,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {std::make_pair<std::string, std::string>("", src)});
  ASSERT_TRUE(res);
}

namespace {

auto SRC = R"(
    (
      (load-param v0)

      (switch v0 (:a :b :c :d :e :f))
      (:end)
      (return-void)

      (:a 0)
      (const v1 0)
      (goto :end)

      (:b 1)
      (const v1 1)
      (goto :end)

      (:c 2)
      (const v1 2)
      (goto :end)

      (:d 3)
      (const v1 3)
      (goto :end)

      (:e 4)
      (const v1 4)
      (goto :end)

      (:f 5)
      (const v1 5)
      (goto :end)
    ))";

auto SRC_REORDER = R"(
    (
      (load-param v0)

      (switch v0 (:a :b :c :d :e :f))
      (:end)
      (return-void)

      (:f 5)
      (const v1 5)
      (goto :end)

      (:e 4)
      (const v1 4)
      (goto :end)

      (:d 3)
      (const v1 3)
      (goto :end)

      (:c 2)
      (const v1 2)
      (goto :end)

      (:b 1)
      (const v1 1)
      (goto :end)

      (:a 0)
      (const v1 0)
      (goto :end)
    ))";

} // namespace

TEST_F(SplitHugeSwitchTest, NoOp) {
  auto res = test("(I)V",
                  SRC,
                  100,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {std::make_pair<std::string, std::string>("", SRC)});
  EXPECT_TRUE(res);
  auto res2 = test("(I)V",
                   SRC,
                   0,
                   100,
                   method_profiles::MethodProfiles(),
                   0.0,
                   {std::make_pair<std::string, std::string>("", SRC_REORDER)});
  EXPECT_TRUE(res2);
}

TEST_F(SplitHugeSwitchTest, Split1) {
  const auto* main_res = R"(
    (
      (load-param v0)

      (const v2 2)
      (if-gt v0 v2 :L4)

      (switch v0 (:L1 :L2 :L3))
      (:L0)
      (return-void)

      (:L3 2)
      (const v1 2)
      (goto :L0)

      (:L2 1)
      (const v1 1)
      (goto :L0)

      (:L1 0)
      (const v1 0)
      (goto :L0)

      (:L4)
      (invoke-static (v0) "LFoo;.bar$split_switch_clone:(I)V")
      (return-void)
    ))";
  const auto* split_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1 :L2 :L3))
      (:L0)
      (return-void)

      (:L3 5)
      (const v1 5)
      (goto :L0)

      (:L2 4)
      (const v1 4)
      (goto :L0)

      (:L1 3)
      (const v1 3)
      (goto :L0)
    ))";
  auto res = test("(I)V",
                  SRC,
                  30,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {
                      pair("", main_res),
                      pair("split_switch_clone", split_res),
                  });
  EXPECT_TRUE(res);
}

TEST_F(SplitHugeSwitchTest, Split2) {
  const auto* main_res = R"(
    (
      (load-param v0)

      (const v2 1)
      (if-gt v0 v2 :L3)

      (switch v0 (:L1 :L2))
      (:L0)
      (return-void)

      (:L2 1)
      (const v1 1)
      (goto :L0)

      (:L1 0)
      (const v1 0)
      (goto :L0)

      (:L3)
      (const v2 3)
      (if-gt v0 v2 :L4)
      (invoke-static (v0) "LFoo;.bar$split_switch_clone:(I)V")
      (return-void)

      (:L4)
      (invoke-static (v0) "LFoo;.bar$split_switch_cloner$0:(I)V")
      (return-void)
    ))";
  const auto* split1_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1 :L2))
      (:L0)
      (return-void)

      (:L2 3)
      (const v1 3)
      (goto :L0)

      (:L1 2)
      (const v1 2)
      (goto :L0)
    ))";
  const auto* split2_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1 :L2))
      (:L0)
      (return-void)

      (:L2 5)
      (const v1 5)
      (goto :L0)

      (:L1 4)
      (const v1 4)
      (goto :L0)
    ))";
  auto res = test("(I)V",
                  SRC,
                  20,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {
                      pair("", main_res),
                      pair("split_switch_clone", split1_res),
                      pair("split_switch_cloner$0", split2_res),
                  });
  EXPECT_TRUE(res);
}

TEST_F(SplitHugeSwitchTest, Split3) {
  const auto* main_res = R"(
    (
      (load-param v0)

      (const v2 0)
      (if-gt v0 v2 :L2)

      (switch v0 (:L1))
      (:L0)
      (return-void)

      (:L1 0)
      (const v1 0)
      (goto :L0)

      (:L2)
      (const v2 2)
      (if-gt v0 v2 :L3)
      (invoke-static (v0) "LFoo;.bar$split_switch_clone:(I)V")
      (return-void)

      (:L3)
      (const v2 3)
      (if-gt v0 v2 :L4)
      (invoke-static (v0) "LFoo;.bar$split_switch_cloner$0:(I)V")
      (return-void)

      (:L4)
      (invoke-static (v0) "LFoo;.bar$split_switch_cloner$1:(I)V")
      (return-void)
    ))";
  const auto* split1_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1 :L2))
      (:L0)
      (return-void)

      (:L2 2)
      (const v1 2)
      (goto :L0)

      (:L1 1)
      (const v1 1)
      (goto :L0)
    ))";
  const auto* split2_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1))
      (:L0)
      (return-void)

      (:L1 3)
      (const v1 3)
      (goto :L0)
    ))";
  const auto* split3_res = R"(
    (
      (load-param v0)

      (switch v0 (:L1 :L2))
      (:L0)
      (return-void)

      (:L2 5)
      (const v1 5)
      (goto :L0)

      (:L1 4)
      (const v1 4)
      (goto :L0)
    ))";
  auto res = test("(I)V",
                  SRC,
                  11,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {
                      pair("", main_res),
                      pair("split_switch_clone", split1_res),
                      pair("split_switch_cloner$0", split2_res),
                      pair("split_switch_cloner$1", split3_res),
                  });
  EXPECT_TRUE(res);
}

TEST_F(SplitHugeSwitchTest, NoSplitExactThreshold) {
  auto res = test("(I)V",
                  SRC,
                  44,
                  0,
                  method_profiles::MethodProfiles(),
                  0.0,
                  {pair("", SRC)});
  EXPECT_TRUE(res);
}
