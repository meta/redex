/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "BranchPrefixHoisting.h"
#include "CppUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PositionJoin.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "ScopeHelper.h"
#include "Show.h"
#include "SourceBlocks.h"

class BranchPrefixHoistingTest : public RedexTest {};

// TODO: "full_validation" should always be true, but some existing (broken?)
// legacy tests don't meet this bar
void test(const std::string& code_str,
          const std::string& expected_str,
          size_t expected_instructions_hoisted,
          bool full_validation = false,
          bool can_allocate_regs = true) {

  DexType* type = DexType::make_type("testClass");
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  DexMethod* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  method->set_code(assembler::ircode_from_string(code_str));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();
  std::cerr << "before:" << "\n" << SHOW(cfg);

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method,
        /* force_type_inference */ true);
  });
  int actual_insns_hoisted = branch_prefix_hoisting_impl::process_cfg(
      cfg, constant_uses, can_allocate_regs);

  std::cerr << "after:" << "\n" << SHOW(code->cfg());
  EXPECT_EQ(expected_instructions_hoisted, actual_insns_hoisted);
  auto expected = assembler::ircode_from_string(expected_str);
  auto* expected_ptr = expected.get();
  expected_ptr->build_cfg();
  auto& expected_cfg = expected_ptr->cfg();
  std::cerr << "expected:" << "\n" << SHOW(expected_cfg);
  if (full_validation) {
    code->clear_cfg();
    expected_ptr->clear_cfg();

    EXPECT_EQ(assembler::to_s_expr(code), assembler::to_s_expr(expected.get()));
  }
}

// When a hoisted instruction may throw, the prefix keeps SourceBlocks so the
// new control flow stays annotated. Those instructions now live in the parent,
// so they run exactly as often as it does -- one SourceBlock carrying the
// parent's count. Copying every successor's verbatim annotated the prefix once
// per arm, each copy claiming the whole of it.
TEST_F(BranchPrefixHoistingTest, hoisted_prefix_carries_this_blocks_count) {
  g_redex->preserve_count_integrity = true;
  ScopeGuard restore_count_integrity{
      []() { g_redex->preserve_count_integrity = false; }};

  DexType* type = DexType::make_type("LHoistSB;");
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.src_block "LHoistSB;.test:(I)V" 0 (10.0 1.0))
      (if-eqz v0 :true)

      (.src_block "LHoistSB;.test:(I)V" 1 (4.0 1.0))
      (sget "LHoistSB;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (.src_block "LHoistSB;.test:(I)V" 2 (6.0 1.0))
      (sget "LHoistSB;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )"));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses);

  auto sbs = source_blocks::gather_source_blocks(cfg.entry_block());
  // The block's own SourceBlock, plus exactly one for the hoisted prefix --
  // not one per arm.
  ASSERT_EQ(sbs.size(), 2u);
  auto v = sbs.back()->get_val(0);
  ASSERT_TRUE(v.has_value());
  EXPECT_FLOAT_EQ(*v, 10.0f);
}

// Same, but the hoisting block has no SourceBlock of its own, so the prefix
// falls back to a verbatim copy of a successor's. The fallback still annotates
// the prefix, so it must count as "annotated": one copy, not one per arm.
TEST_F(BranchPrefixHoistingTest, hoisted_prefix_falls_back_to_a_single_copy) {
  g_redex->preserve_count_integrity = true;
  ScopeGuard restore_count_integrity{
      []() { g_redex->preserve_count_integrity = false; }};

  DexType* type = DexType::make_type("LHoistSBNone;");
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  // No .src_block before the branch: the hoisting block has no count of its
  // own.
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :true)

      (.src_block "LHoistSBNone;.test:(I)V" 1 (4.0 1.0))
      (sget "LHoistSBNone;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (.src_block "LHoistSBNone;.test:(I)V" 2 (6.0 1.0))
      (sget "LHoistSBNone;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )"));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses);

  // Exactly one. Leaving the fallback's guard unset let the next arm's
  // SourceBlock annotate the prefix a second time.
  auto sbs = source_blocks::gather_source_blocks(cfg.entry_block());
  EXPECT_EQ(sbs.size(), 1u);
}

TEST_F(BranchPrefixHoistingTest, simple_insn_hoisting) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 6)
      (goto :end)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 7)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (if-eqz v0 :true)
      (const v6 6)
      (goto :end)
      (:true)
      (const v6 7)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 5);
}

TEST_F(BranchPrefixHoistingTest, stop_hoisting_at_side_effect) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v0 7)
      (const v2 3)
      (goto :end)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v0 7)
      (const v2 4)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (move v4 v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v0 7)
      (if-eqz v4 :true)
      (const v2 3)
      (goto :end)
      (:true)
      (const v2 4)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 4);
}

TEST_F(BranchPrefixHoistingTest, move_result_hoist_ok) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (if-eqz v0 :true)
      (div-int v1 v2)
      (move-result-pseudo v3)
      (const v5 42)
      (goto :end)
      (:true)
      (div-int v1 v2)
      (move-result-pseudo v3)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (div-int v1 v2)
      (move-result-pseudo v3)
      (if-eqz v0 :true)
      (const v5 42)
      (goto :end)
      (:true)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, move_result_no_hoist_diff_dest) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (if-eqz v0 :true)
      (div-int v1 v2)
      (move-result-pseudo v4)
      (const v5 42)
      (goto :end)
      (:true)
      (div-int v1 v2)
      (move-result-pseudo v3)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (if-eqz v0 :true)
      (div-int v1 v2)
      (move-result-pseudo v4)
      (const v5 42)
      (goto :end)
      (:true)
      (div-int v1 v2)
      (move-result-pseudo v3)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 0);
}

TEST_F(BranchPrefixHoistingTest, move_result_no_hoist_on_side_effect) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (if-eqz v0 :true)
      (div-int v1 v2)
      (move-result-pseudo v0)
      (const v5 42)
      (goto :end)
      (:true)
      (div-int v1 v2)
      (move-result-pseudo v0)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 16)
      (const v2 8)
      (if-eqz v0 :true)
      (div-int v1 v2)
      (move-result-pseudo v0)
      (const v5 42)
      (goto :end)
      (:true)
      (div-int v1 v2)
      (move-result-pseudo v0)
      (const v6 43)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, one_block_becomes_empty) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 1)
      (const v2 2)
      (goto :end)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :true)
      (goto :end)
      (:true)
      (const v3 3)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, both_blocks_becomes_empty) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (goto :end)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (if-eqz v0 :true)
      (goto :end)
      (:true)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 3);
}

TEST_F(BranchPrefixHoistingTest, move_result_wide) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (const-wide v1 2)
      (const-wide v2 10)
      (if-ge v3 v0 :true)
      (invoke-static (v1 v2) "LCls;.max:(JJ)J")
      (move-result-wide v0)
      (goto :end)
      (:true)
      (invoke-static (v1 v2) "LCls;.max:(JJ)J")
      (move-result-wide v0)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const-wide v1 2)
      (const-wide v2 10)
      (if-ge v3 v0 :true)
      (invoke-static (v1 v2) "LCls;.max:(JJ)J")
      (move-result-wide v0)
      (goto :end)
      (:true)
      (invoke-static (v1 v2) "LCls;.max:(JJ)J")
      (move-result-wide v0)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, branch_goes_to_same_block) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 7)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 7)
      (if-eqz v0 :true)
      (:true)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 6);
}

TEST_F(BranchPrefixHoistingTest, switch_two_same_cases) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (switch v0 (:case1 :case2))
      (:case1 1)
      (const v1 1)
      (const v2 2)
      (goto :end)
      (:case2 2)
      (const v1 1)
      (const v2 2)
      (goto :end)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (switch v0 (:case1 :case2))
      (:case1 1)
      (goto :end)
      (:case2 2)
      (goto :end)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, switch_with_same_cases) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (switch v0 (:a :b :c :d :e :f))

      (:a 0)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v2 v1)
      (goto :end)

      (:b 1)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v2 v1)
      (goto :end)

      (:c 2)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v2 v1)
      (goto :end)

      (:d 3)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v1 v1)
      (goto :end)

      (:e 4)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v1 v1)
      (goto :end)

      (:f 5)
      (const v1 1)
      (add-int v2 v1 v1)
      (add-int v2 v1 v1)
      (goto :end)

      (:end)
      (return-void)
    )
  )";

  const auto* expected_str = R"(
     (
      (load-param v0)
      (const v1 1)
      (add-int v2 v1 v1)
      (switch v0 (:a :b :c :d :e :f))

      (:a 0)
      (add-int v2 v2 v1)
      (goto :end)

      (:b 1)
      (add-int v2 v2 v1)
      (goto :end)

      (:c 2)
      (add-int v2 v2 v1)
      (goto :end)

      (:d 3)
      (add-int v2 v1 v1)
      (goto :end)

      (:e 4)
      (add-int v2 v1 v1)
      (goto :end)

      (:f 5)
      (add-int v2 v1 v1)
      (goto :end)

      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, branch_with_same_return) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (return-void)
      (:true)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (return-void)
    )
  )";

  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (return-void)
      (if-eqz v0 :true)
      (:true)
    )
  )";
  test(code_str, expected_str, 4);
}

TEST_F(BranchPrefixHoistingTest, branch_with_clber_wide) {

  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const-wide v0 1)
      (add-int v2 v0 v1)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (const-wide v0 1)
      (add-int v2 v0 v1)
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (move v3 v0)
      (const-wide v0 1)
      (add-int v2 v1 v1)
      (if-eqz v3 :true)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, branch_with_clber_wide_cannot_alloc) {

  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const-wide v0 1)
      (add-int v2 v0 v1)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (const-wide v0 1)
      (add-int v2 v0 v1)
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  test(code_str, code_str, 0, /* full_validation */ true,
       /*can_allocate_regs */ false);
}

TEST_F(BranchPrefixHoistingTest, branch_with_const_zero) {

  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 0)
      (add-int v2 v1 v1)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (const v1 0)
      (add-int v2 v1 v1)
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 0)
      (add-int v2 v1 v1)
      (if-eqz v0 :true)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 2);
}

TEST_F(BranchPrefixHoistingTest, branch_with_const_zero_2) {

  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const v1 0)
      (add-int v2 v1 v1)
      (goto :end)
      (:true)
      (const v1 0)
      (invoke-static (v1) "Ljava/lang/System;.arraycopy:(Ljava/lang/Object;)V")
      (add-int v2 v2 v1)
      (:end)
      (return-void)
    )
  )";
  test(code_str, code_str, 0);
}

TEST_F(BranchPrefixHoistingTest,
       branch_with_const_wide_with_different_type_demands) {

  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (const-wide v1 123)
      (add-long v2 v1 v1)
      (goto :end)
      (:true)
      (const-wide v1 123)
      (add-double v2 v1 v1)
      (:end)
      (return-void)
    )
  )";
  test(code_str, code_str, 0);
}

TEST_F(BranchPrefixHoistingTest, positions_no_throw) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 6)
      (goto :end)
      (:true)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (const v1 1)
      (const v2 2)
      (.pos:dbg_2 "LFoo;.caller:()V" "Foo.java" 30)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 7)
      (:end)
      (.pos:dbg_3 "LFoo;.caller:()V" "Foo.java" 40)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (if-eqz v0 :true)
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v6 6)
      (goto :end)
      (:true)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (.pos:dbg_2 "LFoo;.caller:()V" "Foo.java" 30)
      (const v6 7)
      (:end)
      (.pos:dbg_3 "LFoo;.caller:()V" "Foo.java" 40)
      (return-void)
    )
  )";
  test(code_str, expected_str, 5, /* full_validation */ true);
}

TEST_F(BranchPrefixHoistingTest, positions_may_throw) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v1 1)
      (invoke-static () "LWhat;.ever:()V")
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (invoke-static () "LWhat;.ever:()V")
      (const v5 5)
      (const v6 6)
      (goto :end)
      (:true)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (const v1 1)
      (invoke-static () "LWhat;.ever:()V")
      (const v2 2)
      (.pos:dbg_2 "LFoo;.caller:()V" "Foo.java" 30)
      (const v3 3)
      (const v4 4)
      (invoke-static () "LWhat;.ever:()V")
      (const v5 5)
      (const v6 7)
      (:end)
      (.pos:dbg_3 "LFoo;.caller:()V" "Foo.java" 40)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 20)
      (invoke-static () "LWhat;.ever:()V")
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 30)
      (invoke-static () "LWhat;.ever:()V")
      (const v5 5)
      (if-eqz v0 :true)
      (.pos:dbg_2 "LFoo;.caller:()V" "Foo.java" 10)
      (const v6 6)
      (goto :end)
      (:true)
      (.pos:dbg_3 "LFoo;.caller:()V" "Foo.java" 20)
      (.pos:dbg_4 "LFoo;.caller:()V" "Foo.java" 30)
      (const v6 7)
      (:end)
      (.pos:dbg_5 "LFoo;.caller:()V" "Foo.java" 40)
      (return-void)
    )
  )";
  test(code_str, expected_str, 7, /* full_validation */ true);
}

TEST_F(BranchPrefixHoistingTest, try_catch_in_succ_block) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (.try_start foo)
      (const v1 1)
      (const v2 2)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v3)
      (throw v3)
      (.try_end foo)
      (goto :end)
      (:true)
      (.try_start foo)
      (const v1 1)
      (const v2 2)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v3)
      (throw v3)
      (.try_end foo)
      (goto :end)
      (.catch (foo))
      (return-void)
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :true)
      (.try_start foo)
      (const v1 1)
      (const v2 2)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v3)
      (throw v3)
      (.try_end foo)
      (goto :end)
      (:true)
      (.try_start foo)
      (const v1 1)
      (const v2 2)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v3)
      (throw v3)
      (.try_end foo)
      (goto :end)
      (.catch (foo))
      (return-void)
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 0, /* full_validation */ true);
}

TEST_F(BranchPrefixHoistingTest, fill_array_data) {
  const auto& code_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (new-array v1 "[I")
      (move-result-pseudo-object v1)
      (if-eqz v0 :true)
      (fill-array-data v1 #4 (0))
      (fill-array-data v1 #4 (1))
      (goto :end)
      (:true)
      (fill-array-data v1 #4 (0))
      (fill-array-data v1 #4 (2))
      (:end)
      (return-void)
    )
  )";
  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (new-array v1 "[I")
      (move-result-pseudo-object v1)
      (fill-array-data v1 #4 (0))
      (if-eqz v0 :true)
      (fill-array-data v1 #4 (1))
      (goto :end)
      (:true)
      (fill-array-data v1 #4 (2))
      (:end)
      (return-void)
    )
  )";
  test(code_str, expected_str, 1);
}

namespace {

// Counts the positions in the whole method that have been marked as no longer
// identifying a unique source.
size_t count_unreliable_positions(cfg::ControlFlowGraph& cfg) {
  size_t count = 0;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION && mie.pos->is_unreliable()) {
        ++count;
      }
    }
  }
  return count;
}

DexMethod* make_two_arm_method(const char* class_name,
                               uint32_t left_line,
                               uint32_t right_line) {
  DexType* type = DexType::make_type(class_name);
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  auto src = std::string(R"(
    (
      (load-param v0)
      (if-eqz v0 :true)

      (.pos "LX;.test:(I)V" "X.java" )") +
             std::to_string(right_line) + R"()
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (.pos "LX;.test:(I)V" "X.java" )" +
             std::to_string(left_line) + R"()
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(src));
  return method;
}

DexMethod* make_position_test_method(const char* class_name,
                                     const std::string& code) {
  DexType* type = DexType::make_type(class_name);
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  method->set_code(assembler::ircode_from_string(code));
  return method;
}

struct HoistedSgetResult {
  size_t count{0};
  DexPosition* position{nullptr};
  positions::JoinStats join_stats;
};

HoistedSgetResult process_and_find_hoisted_sget(DexMethod* method) {
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();
  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  HoistedSgetResult result;
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses,
                                           /* can_allocate_regs */ true,
                                           &result.join_stats);
  for (auto* block : cfg.blocks()) {
    for (auto it = block->begin(); it != block->end(); ++it) {
      if (it->type != MFLOW_OPCODE || it->insn->opcode() != OPCODE_SGET) {
        continue;
      }
      ++result.count;
      result.position = cfg.get_dbg_pos(block->to_cfg_instruction_iterator(it));
    }
  }
  return result;
}

} // namespace

// `sget` can throw, so the hoisted copy is a PC a stack trace can land on. It
// runs for both arms but can carry only one line, so the copy is marked. The
// originals stay in the arms and still describe the code left there, so they
// are left alone -- which is what the count of exactly one checks.
TEST_F(BranchPrefixHoistingTest, hoisting_marks_only_the_copy_it_creates) {
  auto* method = make_two_arm_method("LHoistPosDiffer;", 30, 20);
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  positions::JoinStats join_stats;
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses,
                                           /* can_allocate_regs */ true,
                                           &join_stats);

  EXPECT_EQ(join_stats.marked_unreliable, 1u);
  EXPECT_EQ(count_unreliable_positions(cfg), 1u);

  // The copy remains primary; its candidate set names the one alternate arm.
  DexPosition* marked = nullptr;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION && mie.pos->is_unreliable()) {
        marked = mie.pos.get();
      }
    }
  }
  ASSERT_NE(marked, nullptr);
  ASSERT_NE(marked->alt_id(), 0u);
  EXPECT_EQ(g_redex->get_position_pattern_switch_manager()
                ->get_alt_set(marked->alt_id())
                .total_candidates(),
            1u);
}

// Both arms report the same line, so the hoisted copy names a place that was
// correct for both and nothing is recorded.
TEST_F(BranchPrefixHoistingTest, hoisting_records_nothing_when_the_arms_agree) {
  auto* method = make_two_arm_method("LHoistPosAgree;", 20, 20);
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  positions::JoinStats join_stats;
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses,
                                           /* can_allocate_regs */ true,
                                           &join_stats);

  EXPECT_EQ(join_stats.marked_unreliable, 0u);
  EXPECT_EQ(count_unreliable_positions(cfg), 0u);
}

TEST_F(BranchPrefixHoistingTest, hoisting_agrees_with_an_inherited_position) {
  auto* method = make_position_test_method("LHoistPosInheritedAgree;", R"(
    (
      (load-param v0)
      (.pos "LX;.test:(I)V" "X.java" 10)
      (if-eqz v0 :true)

      (.pos "LX;.test:(I)V" "X.java" 10)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");

  auto result = process_and_find_hoisted_sget(method);
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 10u);
  EXPECT_FALSE(result.position->is_unreliable());
  EXPECT_EQ(result.join_stats.marked_unreliable, 0u);
  EXPECT_EQ(result.join_stats.not_recorded, 0u);
}

TEST_F(BranchPrefixHoistingTest,
       hoisting_leaves_code_under_the_position_all_arms_inherit) {
  auto* method = make_position_test_method("LHoistPosAllInherited;", R"(
    (
      (load-param v0)
      (.pos "LX;.test:(I)V" "X.java" 20)
      (if-eqz v0 :true)

      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");

  auto result = process_and_find_hoisted_sget(method);
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 20u);
  EXPECT_FALSE(result.position->is_unreliable());
  EXPECT_EQ(result.join_stats.marked_unreliable, 0u);
  EXPECT_EQ(result.join_stats.not_recorded, 0u);
}

TEST_F(BranchPrefixHoistingTest,
       hoisting_marks_an_explicit_position_disagreeing_with_inherited) {
  auto* method = make_position_test_method("LHoistPosInheritedDiffer;", R"(
    (
      (load-param v0)
      (.pos "LX;.test:(I)V" "X.java" 30)
      (if-eqz v0 :true)

      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (.pos "LX;.test:(I)V" "X.java" 40)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");

  auto result = process_and_find_hoisted_sget(method);
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 40u);
  EXPECT_TRUE(result.position->is_unreliable());
  EXPECT_EQ(result.join_stats.marked_unreliable, 1u);
  EXPECT_EQ(result.join_stats.not_recorded, 0u);
}

TEST_F(BranchPrefixHoistingTest,
       hoisting_inherits_position_through_a_goto_predecessor) {
  auto* method = make_position_test_method("LHoistPosGotoInherited;", R"(
    (
      (load-param v0)
      (.pos "LX;.test:(I)V" "X.java" 50)
      (goto :branch)

      (:true)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:branch)
      (if-eqz v0 :true)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");

  auto result = process_and_find_hoisted_sget(method);
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 50u);
  EXPECT_FALSE(result.position->is_unreliable());
  EXPECT_EQ(result.join_stats.marked_unreliable, 0u);
  EXPECT_EQ(result.join_stats.not_recorded, 0u);
}

// Both arms run inlined code at Y.java:20 under the same callsite object,
// which an earlier fold already marked with a recorded candidate set. The
// hoisted copy names exactly what both arms named, so it must not be marked --
// least of all as "merged, sites not recorded", which is absorbing.
TEST_F(BranchPrefixHoistingTest,
       hoisting_under_a_shared_merged_callsite_records_nothing) {
  auto* method = make_position_test_method("LHoistPosSharedMergedParent;", R"(
    (
      (load-param v0)
      (.pos:dbg_0 "LX;.test:(I)V" "X.java" 5)
      (.pos:dbg_1 "LY;.callee:()V" "Y.java" 20 dbg_0)
      (if-eqz v0 :true)

      (.pos:dbg_2 "LY;.callee:()V" "Y.java" 20 dbg_0)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  DexPosition* callsite = nullptr;
  for (auto* block : code->cfg().blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION && mie.pos->line == 5 &&
          callsite == nullptr) {
        callsite = mie.pos.get();
      }
    }
  }
  ASSERT_NE(callsite, nullptr);
  auto other_callsite =
      std::make_unique<DexPosition>(DexString::make_string("LX;.test:(I)V"),
                                    DexString::make_string("X.java"), 7);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(callsite, {other_callsite.get()});
  ASSERT_NE(callsite->alt_id(), 0u);
  code->clear_cfg();

  auto result = process_and_find_hoisted_sget(method);
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 20u);
  EXPECT_EQ(result.position->parent, callsite);
  EXPECT_FALSE(result.position->is_unreliable());
  EXPECT_EQ(result.join_stats.marked_unreliable, 0u);
}

// No position governs either arm, so the hoisted `sget` is exactly as
// position-less as both originals were: nothing disagreed, nothing is cloned,
// and there is no gap to count.
TEST_F(BranchPrefixHoistingTest,
       hoisting_without_any_position_records_nothing) {
  DexType* type = DexType::make_type("LHoistPosNone;");
  auto* cls = create_class(type, type::java_lang_Object(), {}, ACC_PUBLIC);
  auto* args = DexTypeList::make_type_list({type::_int()});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* method =
      DexMethod::make_method(type, DexString::make_string("test"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  cls->add_method(method);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :true)

      (sget "LHoistPosNone;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (sget "LHoistPosNone;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )"));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  Lazy<const constant_uses::ConstantUses> constant_uses([&] {
    return std::make_unique<const constant_uses::ConstantUses>(
        cfg, method, /* force_type_inference */ true);
  });
  positions::JoinStats join_stats;
  branch_prefix_hoisting_impl::process_cfg(cfg, constant_uses,
                                           /* can_allocate_regs */ true,
                                           &join_stats);

  EXPECT_EQ(join_stats.marked_unreliable, 0u);
  EXPECT_EQ(join_stats.not_recorded, 0u);
  size_t positions = 0;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : *block) {
      positions += mie.type == MFLOW_POSITION ? 1 : 0;
    }
  }
  EXPECT_EQ(positions, 0u);
}

// A class without a SourceFile attribute binds its positions with no file
// (`DexDebugItem::bind_positions`). Hoisting out of such a method must not
// hand a fileless position to the candidate-set registry, which requires a
// file on every member.
TEST_F(BranchPrefixHoistingTest, hoisting_in_a_fileless_method_does_not_crash) {
  auto* method = make_position_test_method("LHoistPosFileless;", R"(
    (
      (load-param v0)
      (.pos "LX;.test:(I)V" "X.java" 30)
      (if-eqz v0 :true)

      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)

      (:true)
      (.pos "LX;.test:(I)V" "X.java" 40)
      (sget "LX;.f:I")
      (move-result-pseudo v1)
      (return-void)
    )
  )");
  for (auto& mie : *method->get_code()) {
    if (mie.type == MFLOW_POSITION) {
      mie.pos->file = nullptr;
    }
  }

  HoistedSgetResult result;
  ASSERT_NO_THROW(result = process_and_find_hoisted_sget(method));
  EXPECT_EQ(result.count, 1u);
  ASSERT_NE(result.position, nullptr);
  EXPECT_EQ(result.position->line, 40u);
  EXPECT_TRUE(result.position->is_unreliable());
  EXPECT_EQ(result.position->alt_id(), 0u);
}
