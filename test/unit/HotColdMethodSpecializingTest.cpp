/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>

#include <gtest/gtest.h>

#include "HotColdMethodSpecializingPass.h"

#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Show.h"

class HotColdMethodSpecializingTest : public RedexTest {
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

  static HotColdMethodSpecializingPass::Config defaultConfig() {
    HotColdMethodSpecializingPass::Config config;
    // set some low limits...
    config.threshold_factor = 2;
    config.threshold_offset = 4;
    return config;
  }

  static ::testing::AssertionResult test(
      const std::string& sig,
      const std::string& code_str,
      const HotColdMethodSpecializingPass::Config& config,
      const std::string& expected,
      const std::string& expected_cold = "") {
    auto [cls, method] = create(sig, code_str);
    method->get_code()->build_cfg();
    HotColdMethodSpecializingPass::Stats stats;
    DexMethod* cold_copy{nullptr};
    stats = HotColdMethodSpecializingPass::analyze_and_specialize(
        config, /* iteration */ 42, method, &cold_copy);
    if (expected.empty()) {
      if (cold_copy != nullptr) {
        return ::testing::AssertionFailure() << "Unexpected cold copy";
      }
      return ::testing::AssertionSuccess();
    }

    if (cold_copy == nullptr) {
      return ::testing::AssertionFailure() << "Missing cold copy";
    }
    method->get_code()->cfg().simplify();
    method->get_code()->clear_cfg();
    std::string out_str =
        replace_count(assembler::to_string(method->get_code()), method);
    auto exp_ir = assembler::ircode_from_string(expected);
    std::string exp_str = assembler::to_string(exp_ir.get());
    if (out_str != exp_str) {
      return ::testing::AssertionFailure()
             << "Actual:\n" + out_str + "\nExpected:\n" + exp_str;
    }
    auto* cold_code = cold_copy->get_code();
    cold_code->cfg().simplify();
    cold_code->clear_cfg();
    std::string cold_out_str =
        replace_count(assembler::to_string(cold_code), cold_copy);
    auto cold_exp_ir = assembler::ircode_from_string(expected_cold);
    std::string cold_exp_str = assembler::to_string(cold_exp_ir.get());
    if (cold_out_str != cold_exp_str) {
      return ::testing::AssertionFailure()
             << "Actual:\n" + cold_out_str + "\nExpected:\n" + cold_exp_str;
    }

    return ::testing::AssertionSuccess();
  }

 private:
  static std::atomic<size_t> s_counter;
};
std::atomic<size_t> HotColdMethodSpecializingTest::s_counter{0};

TEST_F(HotColdMethodSpecializingTest, NoBasicHotColdSpecialization) {
  // Size of cold code in relation to hot code is not big enough,
  const auto* before = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))
      (if-eqz v0 :cold)

      (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
      (return v0)
    (:cold)
      (.src_block "LFoo;.bar:(I)I" 3 (0 0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = "";
  auto config = defaultConfig();
  auto res = test("(I)I", before, config, after);
  ASSERT_TRUE(res);
}

TEST_F(HotColdMethodSpecializingTest, NoImpurePathHotColdSpecialization) {
  // An impure path to the cold code disqualifies this example from hot-cold
  // specialization.
  const auto* before = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))

    (:L0)
      (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
      (if-eqz v0 :cold)

      (.src_block "LFoo;.bar:(I)I" 3 (0.5 0.5))
      (sput v0 "LClass;.static:I")
      (goto :L0)

    (:cold)
      (.src_block "LFoo;.bar:(I)I" 4 (0 0))
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = "";
  auto config = defaultConfig();
  auto res = test("(I)I", before, config, after);
  ASSERT_TRUE(res);
}

TEST_F(HotColdMethodSpecializingTest, BasicHotColdSpecialization) {
  const auto* before = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))
      (if-eqz v0 :cold)

      (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
      (return v0)
    (:cold)
      (.src_block "LFoo;.bar:(I)I" 3 (0 0))
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
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
      (
        (load-param v0)
        (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))
        (move v1 v0)
        (if-eqz v0 :L0)
        (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
        (return v0)

        (:L0)
        (.src_block "LFoo;.bar:(I)I" 4294967295 (0 0))
        (invoke-static (v1) "LFoo;.bar$hcms$42:(I)I")
        (move-result v2)
        (return v2)
    ))";
  const auto* cold_after = R"(
      (
        (load-param v0)
        (.src_block "LFoo;.bar:(I)I" 1 (0.000000 0.000000))
        (if-eqz v0 :L0)
        (.src_block "LFoo;.bar:(I)I" 4294967295 (0.000000 0.000000))
        (unreachable v1)
        (throw v1)

      (:L0)
        (.src_block "LFoo;.bar:(I)I" 3 (0.000000 0.000000))
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
        (add-int v0 v0 v0)
        (return v0)
    ))";
  auto config = defaultConfig();
  auto res = test("(I)I", before, config, after, cold_after);
  ASSERT_TRUE(res);
}

TEST_F(HotColdMethodSpecializingTest, MutableHeapReadingHotColdSpecialization) {
  // When the "pure" hot prefix involves reading mutable heap memory, we must
  // not insert "unreachable" instructions in the cold method.
  const auto* before = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (if-eqz v0 :cold)

      (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
      (return v0)
    (:cold)
      (.src_block "LFoo;.bar:(I)I" 3 (0 0))
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
      (add-int v0 v0 v0)
      (return v0)
    ))";
  const auto* after = R"(
      (
        (load-param v0)
        (.src_block "LFoo;.bar:(I)I" 1 (0.5 0.5))
        (move v1 v0)
        (sget "LFoo;.a:I")
        (move-result-pseudo v0)
        (if-eqz v0 :L0)
        (.src_block "LFoo;.bar:(I)I" 2 (0.5 0.5))
        (return v0)

        (:L0)
        (.src_block "LFoo;.bar:(I)I" 4294967295 (0 0))
        (invoke-static (v1) "LFoo;.bar$hcms$42:(I)I")
        (move-result v2)
        (return v2)
    ))";
  const auto* cold_after = R"(
      (
        (load-param v0)
        (.src_block "LFoo;.bar:(I)I" 1 (0.000000 0.000000))
        (sget "LFoo;.a:I")
        (move-result-pseudo v0)
        (if-eqz v0 :L0)

        (.src_block "LFoo;.bar:(I)I" 2 (0.000000 0.000000))
        (return v0)

      (:L0)
        (.src_block "LFoo;.bar:(I)I" 3 (0.000000 0.000000))
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
        (add-int v0 v0 v0)
        (return v0)
    ))";
  auto config = defaultConfig();
  auto res = test("(I)I", before, config, after, cold_after);
  ASSERT_TRUE(res);
}

// A method handle call in the hot prefix may do anything, so the prefix is not
// pure and must not be run again by a cold copy.
TEST_F(HotColdMethodSpecializingTest, InvokePolymorphicInHotPrefixIsImpure) {
  const auto* before = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (.src_block "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;I)I" 1 (0.5 0.5))
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (if-eqz v1 :cold)

      (.src_block "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;I)I" 2 (0.5 0.5))
      (return v1)
    (:cold)
      (.src_block "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;I)I" 3 (0 0))
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (add-int v1 v1 v1)
      (return v1)
    ))";
  auto res =
      test("(Ljava/lang/invoke/MethodHandle;I)I", before, defaultConfig(), "");
  ASSERT_TRUE(res);
}
