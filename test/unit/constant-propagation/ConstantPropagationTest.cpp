/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagationAnalysis.h"
#include "SignedConstantDomain.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "ConstantPropagationTestUtil.h"
#include "IRAssembler.h"
#include "SourceBlocks.h"

using ::testing::AnyNumber;
using ::testing::AtLeast;
using ::testing::Return;

TEST_F(ConstantPropagationTest, SourceBlockTargetMutating) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (.src_block "LTail;.duplication:(I)V" 0 (1.0 1.0))
     (if-eqz v0 :nine)
     (.src_block "LTail;.duplication:(I)V" 1 (0 0))
     (move-object v0 v1)
     (:two)
     (.src_block "LTail;.duplication:(I)V" 2 (1.0 1.0))
     (if-nez v0 :end2)
     (:end1)
     (.src_block "LTail;.duplication:(I)V" 3 (1.0 1.0))
     (return v0)
     (:end2)
     (.src_block "LTail;.duplication:(I)V" 4 (0 0))
     (add-int v0 v0 v1)
     (return v0)
     (:nine)
     (.src_block "LTail;.duplication:(I)V" 5 (1.0 1.0))
     (goto :two)
    )
  )");

  code->build_cfg();

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::All);

  code->build_cfg();

  for (auto* block : code->cfg().blocks()) {
    for (auto* sb : source_blocks::gather_source_blocks(block)) {
      if (sb->id == 2) {
        auto value = sb->get_at(0);
        ASSERT_TRUE(value);
        ASSERT_EQ(value->val, 0);
        ASSERT_EQ(value->appear100, 0);
      }
    }
  }
}

TEST_F(ConstantPropagationTest, ArrayLengthNonNegative) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (array-length v0)
      (move-result-pseudo v0)
      (if-ltz v0 :next)
      (:next)
      (return-void)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (array-length v0)
      (move-result-pseudo v0)
      (return-void)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, DereferenceWithoutThrowBlock) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (array-length v0)
      (move-result-pseudo v1)
      (if-eqz v0 :next)
      (:next)
      (return-void)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (array-length v0)
      (move-result-pseudo v1)
      (return-void)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, DereferenceWithThrowBlock) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (.try_start a)
      (array-length v0)
      (move-result-pseudo v1)
      (.try_end a)
      (if-eqz v0 :next1)
      (:next1)
      (return-void)
      (.catch (a))
      (if-eqz v0 :next2)
      (:next2)
      (return-void)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (.try_start a)
      (array-length v0)
      (move-result-pseudo v1)
      (return-void)
      (.try_end a)
      (.catch (a))
      (if-eqz v0 :next2)
      (:next2)
      (return-void)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, NullCheckCastYieldsNull) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (check-cast v0 "LFoo;")
     (move-result-pseudo v1)
     (if-eqz v1 :next)
     (const v2 1)
     (goto :end)
     (:next)
     (const v2 2)
     (:end)
     (return-void)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 2)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// A non-null value (from new-instance, which is NEZ) retains its non-nullness
// through a check-cast, so the following null check folds to the non-null path.
TEST_F(ConstantPropagationTest, NonNullSurvivesCheckCast) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (check-cast v0 "LFoo;")
     (move-result-pseudo-object v1)
     (if-eqz v1 :next)
     (const v2 1)
     (goto :end)
     (:next)
     (const v2 2)
     (:end)
     (return v2)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (const v2 1)
      (return v2)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// A check-cast applied to a known object constant (e.g. from const-string or
// const-class) is kept, not deleted -- removing a cast that can throw at
// runtime would change behavior.
TEST_F(ConstantPropagationTest, CheckCastPreservedWhenOperandIsConstant) {
  const auto* code_str = R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (check-cast v0 "LBar;")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )";
  auto code = assembler::ircode_from_string(code_str);

  auto state = cp::StringAnalyzerState::make_default();
  do_const_prop(
      code.get(),
      InstructionAnalyzerCombiner<cp::StringAnalyzer, cp::PrimitiveAnalyzer>(
          &state, nullptr));

  auto expected_code = assembler::ircode_from_string(code_str);
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// The exact string constant reaches the check-cast's result register in the
// abstract state, not merely non-nullness.
TEST_F(ConstantPropagationTest, CheckCastResultRetainsExactConstant) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (check-cast v0 "LBar;")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  cp::NullCheckMethods null_check_methods;
  auto state = cp::StringAnalyzerState::make_default();
  cp::intraprocedural::FixpointIterator intra_cp(
      cfg,
      InstructionAnalyzerCombiner<cp::StringAnalyzer, cp::PrimitiveAnalyzer>(
          &state, nullptr),
      cp::intraprocedural::make_default_no_throw_analyzer(&null_check_methods));
  intra_cp.run(ConstantEnvironment());

  auto exit_state = intra_cp.get_exit_state_at(cfg.exit_block());
  auto v1 = exit_state.get(1u).maybe_get<StringDomain>();
  ASSERT_TRUE(v1 && v1->get_constant());
  EXPECT_EQ(*v1->get_constant(), DexString::make_string("foo"));
}

// A non-null object constant whose type is castable to the target passes the
// check-cast, so the cast never throws and is deleted (its result
// materialized).
TEST_F(ConstantPropagationTest, CheckCastDeletedWhenProvablySucceeds) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (check-cast v0 "Ljava/lang/String;")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )");

  auto state = cp::StringAnalyzerState::make_default();
  do_const_prop(
      code.get(),
      InstructionAnalyzerCombiner<cp::StringAnalyzer, cp::PrimitiveAnalyzer>(
          &state, nullptr));

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (const-string "foo")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, JumpToImmediateNext) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :next) ; This jumps to the next opcode regardless of whether
                       ; the test is true or false. So in this case we cannot
                       ; conclude that v0 == 0 in the 'true' block, since that
                       ; is identical to the 'false' block.
     (:next)
     (if-eqz v0 :end)
     (const v0 1)
     (:end)
     (return-void)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :next)
     (:next)
     (if-eqz v0 :end)
     (const v0 1)
     (:end)
     (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// An analysis that tracks r-const as a resource id finds neither successor of
// `if-nez` on it feasible, so the transform counts that branch. A branch on a
// const has one feasible successor and is not counted. (When resource ids are
// modeled as non-zero, the r-const case stops being a trigger.)
TEST_F(ConstantPropagationTest, BranchWithBothSuccessorsInfeasible) {
  auto run =
      [](const std::string& load_opcode,
         const std::function<void(const IRInstruction*, ConstantEnvironment*)>&
             analyzer) {
        auto code = assembler::ircode_from_string("((" + load_opcode +
                                                  " v0 2131230721)" + R"(
      (if-nez v0 :non_zero)
      (const v1 0)
      (return v1)
      (:non_zero)
      (const v1 1)
      (return v1)
    ))");
        code->build_cfg();
        cp::NullCheckMethods null_check_methods;
        cp::intraprocedural::FixpointIterator intra_cp(
            code->cfg(), analyzer,
            cp::intraprocedural::make_default_no_throw_analyzer(
                &null_check_methods));
        intra_cp.run(ConstantEnvironment());
        cp::Transform tf(cp::Transform::Config(), null_check_methods);
        tf.legacy_apply_constants_and_prune_unreachable(
            intra_cp, cp::WholeProgramState(), code->cfg(), nullptr, nullptr);
        return tf.get_stats();
      };

  using RConstAwareAnalyzer =
      InstructionAnalyzerCombiner<cp::ResourceIdAnalyzer,
                                  cp::PrimitiveAnalyzer>;
  auto r_const_stats = run("r-const", RConstAwareAnalyzer(nullptr, nullptr));
  EXPECT_EQ(r_const_stats.branches_removed, 1);
  EXPECT_EQ(r_const_stats.branches_with_both_successors_infeasible, 1);

  auto const_stats = run("const", cp::ConstantPrimitiveAnalyzer());
  EXPECT_EQ(const_stats.branches_removed, 1);
  EXPECT_EQ(const_stats.branches_with_both_successors_infeasible, 0);
}

TEST_F(ConstantPropagationTest, InstanceOfNull) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (instance-of v0 "Ljava/lang/String;")
     (move-result-pseudo v1)
     (if-eqz v1 :next)
     (const v2 1)
     (goto :end)
     (:next)
     (const v2 2)
     (:end)
     (return-void)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 2)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, InstanceOfEvaluatedToTrueWhenEvaluableToTrue) {
  // There is no evaluated-to-false counterpart test case when v0 is a nonnull
  // constant: an object constant is only ever a java.lang.String or a
  // java.lang.Class, and evaluate_type_check returns nullopt for external
  // types, so instance-of on one never folds to 0.
  auto code = assembler::ircode_from_string(R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (instance-of v0 "Ljava/lang/String;")
     (move-result-pseudo v1)
     (return v1)
    )
  )");

  auto state = cp::StringAnalyzerState::make_default();
  do_const_prop(
      code.get(),
      InstructionAnalyzerCombiner<cp::StringAnalyzer, cp::PrimitiveAnalyzer>(
          &state, nullptr));

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (const v1 1)
     (return v1)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, InstanceOfPreservedWhenRelationUndecidable) {
  const auto* code_str = R"(
    (
     (const-string "foo")
     (move-result-pseudo-object v0)
     (instance-of v0 "LBar;")
     (move-result-pseudo v1)
     (return v1)
    )
  )";
  auto code = assembler::ircode_from_string(code_str);

  auto state = cp::StringAnalyzerState::make_default();
  do_const_prop(
      code.get(),
      InstructionAnalyzerCombiner<cp::StringAnalyzer, cp::PrimitiveAnalyzer>(
          &state, nullptr));

  auto expected_code = assembler::ircode_from_string(code_str);
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// A typical case where a non-default block is uniquely reachable.
TEST_F(ConstantPropagationTest, Switch1) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c))
     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (const v1 300)
     (return v1)
  )

  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 200)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Default block also has a unreachable label.
TEST_F(ConstantPropagationTest, Switch2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:a :b :c))

     (:a 0) ; default or unreachable
     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (const v1 300)
     (return v1)
  )

  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 200)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Multiple unreachables labels fall into a block
TEST_F(ConstantPropagationTest, Switch3) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c :d))

     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 200)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// When reachable and unreachable fall into a same block
TEST_F(ConstantPropagationTest, Switch4) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c :d))

     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (:c 3) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 200)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Except default block, all are unreachable
// Switch is just deleted.
TEST_F(ConstantPropagationTest, Switch5) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 3)
     (switch v0 (:b :d))

     (const v1 100)
     (return v1)

     (:b 1) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 3)

     (const v1 100)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Except default block with a switch target, all are unreachable.
// Switch is just deleted.
TEST_F(ConstantPropagationTest, Switch6) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 2)
     (switch v0 (:a :b :d))

     (:a 2)
     (const v1 100)
     (return v1)

     (:b 1) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 2)

     (const v1 100)
     (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// A uniquely non-default case with constant.
TEST_F(ConstantPropagationTest, SwitchOnExactConstant) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (switch v0 (:b))
      ; unreachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (const v1 200)
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, SwitchOnInterval) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-gez v0 :a)
      (const v0 0)
      (:a)
      ; at this point, we know v0 is >= 0

      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)
      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
  )");

  auto original = assembler::to_s_expr(code.get());
  do_const_prop(code.get());

  EXPECT_EQ(assembler::to_s_expr(code.get()), original) << show(code.get());
}

// A uniquely non-default case with non-constant.
// Do not optimize this since default is reachable.
TEST_F(ConstantPropagationTest, Switch8) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Remove dead switch if no non-default block exists.
TEST_F(ConstantPropagationTest, Switch9) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0  (:a :b))
      (:b 1) ; reachable
      (:a 2) ;
      (const v1 200)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 200)
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Constant-propagation recognizes and propagates information about infeasible
// switch non-default cases
TEST_F(ConstantPropagationTest, SwitchInfeasibleNonDefault) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (switch v0 (:a))
      (const v0 0)
      (goto :b)
      (:a 0) ; unreachable
      (:b)
      (move v1 v0)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (const v0 0)
      (const v1 0) ; replacement from move
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, SwitchExtremeCaseKeys) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 -2000000000)
      (if-lt v0 v1 :exit)
      (const v1 2000000000)
      (if-gt v0 v1 :exit)
      (switch v0 (:a :b))
      (:a -2000000000) ; reachable
      (:b 2000000000) ; reachable
      (:exit)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 -2000000000)
      (if-lt v0 v1 :exit)
      (const v1 2000000000)
      (if-gt v0 v1 :exit)
      (:exit)
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Constant-propagation recognizes and propagates information about infeasible
// switch default cases
TEST_F(ConstantPropagationTest, SwitchInfeasibleDefault) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (switch v0 (:a))
      ; unreachable
      (const v0 1)
      (:a 0) ; reachable
      (move v1 v0)
      (return v1)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0) ; replacement from move, as we know the other const is unreachable
      (return v1)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Constant-propagation rewrites switches with dead default cases to use the
// most popular branch target instead.
TEST_F(ConstantPropagationTest, SwitchInfeasibleDefaultManyFeasibleBranches) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a :b :c :d))
      ; unreachable
      (const v0 200)
      (return v0)

      (:a 0) ; reachable
      (const v0 300)

      (return v0)
      (:b 1) ; reachable
      (:c 2) ; reachable
      (:d 3) ; reachable
      (const v0 400)
      (return v0)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a))
      ; reachable, combined b,c,d
      (const v0 400)
      (return v0)

      (:a 0) ; reachable
      (const v0 300)
      (return v0)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Constant-propagation rewrites switches with dead default cases to use the
// most popular branch target instead.
TEST_F(ConstantPropagationTest,
       SwitchInfeasibleDefaultManyFeasibleBranchesRegression) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a :b :c :d))
      ; unreachable

      (:a 0) ; reachable
      (const v0 300)

      (return v0)
      (:b 1) ; reachable
      (:c 2) ; reachable
      (:d 3) ; reachable
      (const v0 400)
      (return v0)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a))
      ; reachable, combined b,c,d
      (const v0 400)
      (return v0)

      (:a 0) ; reachable
      (const v0 300)
      (return v0)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Constant-propagation rewrites switches with dead default cases to use the
// most popular branch target instead, preferring to keep the smallest case
// keys.
TEST_F(ConstantPropagationTest,
       SwitchInfeasibleDefaultManyFeasibleBranchesKeepSmallCaseKeys) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v1 4)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a :b :c :d :e))
      ; unreachable
      (const v0 200)
      (return v0)

      (:a 0) ; reachable
      (const v0 300)
      (return v0)

      (:b 1) ; reachable
      (:c 2) ; reachable
      (const v0 400)
      (return v0)

      (:d 3) ; reachable
      (:e 4) ; reachable
      (const v0 450)
      (return v0)
    )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v1 0)
      (if-eq v0 v1 :selected)
      (const v1 1)
      (if-eq v0 v1 :selected)
      (const v1 2)
      (if-eq v0 v1 :selected)
      (const v1 3)
      (if-eq v0 v1 :selected)
      (const v1 4)
      (if-eq v0 v1 :selected)
      (const v0 100)
      (return v0)

      (:selected)
      (switch v0 (:a :b :c))
      ; reachable, combined d,e
      (const v0 450)
      (return v0)

      (:c 2) ; reachable
      (:b 1) ; reachable
      (const v0 400)
      (return v0)

      (:a 0) ; reachable
      (const v0 300)
      (return v0)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, WhiteBox1) {
  auto code = assembler::ircode_from_string(R"( (
     (load-param v0)

     (const v1 0)
     (const v2 1)
     (move v3 v1)
     (if-eqz v0 :if-true-label)

     (const v2 0)
     (if-gez v0 :if-true-label)

     (:if-true-label)
     (return-void)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  cp::NullCheckMethods null_check_methods;
  cp::intraprocedural::FixpointIterator intra_cp(
      cfg, cp::ConstantPrimitiveAnalyzer(),
      cp::intraprocedural::make_default_no_throw_analyzer(&null_check_methods));
  intra_cp.run(ConstantEnvironment());

  auto exit_state = intra_cp.get_exit_state_at(cfg.exit_block());
  // Specifying `0u` here to avoid any ambiguity as to whether it is the null
  // pointer
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(0u),
            SignedConstantDomain::top());
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(1), SignedConstantDomain(0));
  // v2 can contain either the value 0 or 1
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(2),
            SignedConstantDomain::from_constants({0, 1}));
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(3), SignedConstantDomain(0));
}

TEST_F(ConstantPropagationTest, WhiteBox2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :if-true-label)
     (goto :loop)
     ; if we get here, that means v0 >= 0

     (:if-true-label)
     (return-void)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  cp::NullCheckMethods null_check_methods;
  cp::intraprocedural::FixpointIterator intra_cp(
      cfg, cp::ConstantPrimitiveAnalyzer(),
      cp::intraprocedural::make_default_no_throw_analyzer(&null_check_methods));
  intra_cp.run(ConstantEnvironment());

  auto exit_state = intra_cp.get_exit_state_at(cfg.exit_block());
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(0u),
            SignedConstantDomain(sign_domain::Interval::GEZ));
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(1), SignedConstantDomain(0));
}

TEST_F(ConstantPropagationTest, ForwardBranchesIf) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (const v0 1)
      (goto :L2)
      (:L1)
      (const v0 0)
      (:L2)
      (if-eqz v0 :L3)
      (:L4)
      (const v0 0)
      (:L3)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::OnlyForwardTargets);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (:L1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ForwardBranchesIfSideEffectFreeComputation) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (const v0 1)
      (goto :L2)
      (:L1)
      (const v0 42)
      (sub-int v0 v0 v0)
      (:L2)
      (if-eqz v0 :L3)
      (:L4)
      (const v0 0)
      (:L3)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::OnlyForwardTargets);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (:L1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ForwardBranchesIfSideEffectingComputation) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (const v0 1)
      (goto :L2)
      (:L1)
      (const v0 42)
      (div-int v0 v0)
      (move-result-pseudo v0) ; thiss instruction isn't supported yet
      (:L2)
      (if-eqz v0 :L3)
      (:L4)
      (const v0 0)
      (:L3)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::OnlyForwardTargets);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (:L3)
      (return-void)
      (:L1)
      (const v0 42)
      (div-int v0 v0)
      (move-result-pseudo v0) ; thiss instruction isn't supported yet
      (goto :L3)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ForwardBranchesSwitch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L0)
      (if-eqz v1 :L1)
      (const v0 2)
      (goto :SWITCH)
      (:L0)
      (const v0 0)
      (goto :SWITCH)
      (:L1)
      (const v0 1)
      (goto :SWITCH)

      (:SWITCH)
      (switch v0 (:S0 :S1))
      (:FALLTHROUGH)
      (const v0 2)
      (goto :END)
      (:S0 0)
      (const v0 0)
      (goto :END)
      (:S1 1)
      (const v0 1)
      (goto :END)
      (:END)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::OnlyForwardTargets);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L0)
      (if-eqz v1 :L1)
      (:L0)
      (:L1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ForwardBranchesWithTwoLevelsOfBottom) {
  using signed_constant_domain_internal::Bitset;
  using signed_constant_domain_internal::Bounds;
  using signed_constant_domain_internal::Low6Bits;
  // This test requires most optimization turned off to be reliably reproduced.
  // Without this, the test may still succeed in the future but tests nothing.
  // BottomSettingMinimizeSubdomains only enforces the normality of bottomness
  // across subdomains.
  class BottomSettingMinimizeSubdomains
      : public signed_constant_domain_internal::MinimizeSubdomainsBase {
   public:
    MOCK_METHOD(void, call, (Bounds&, Low6Bits&, Bitset&), (const));

    void operator()(Bounds& bounds,
                    Low6Bits& low6bits,
                    Bitset& bitset) const override {
      call(bounds, low6bits, bitset);
      set_all_to_bottom_if_any(bounds, low6bits, bitset);
    }
  };
  ScopedMinimizeSubdomains scoped_minimize_subdomains(
      new BottomSettingMinimizeSubdomains());

  // Sanity check: Make sure v0 = [1, 2]{9} (not bottom but equals bottom) has
  // appeared at least once, so we know there are two levels of bottom.
  EXPECT_CALL(scoped_minimize_subdomains.get(),
              call(::testing::_, ::testing::_, ::testing::_))
      .Times(testing::AnyNumber());
  Bounds bounds = Bounds::from_range(1, 2);
  EXPECT_CALL(scoped_minimize_subdomains.get(),
              call(bounds, Low6Bits(0).join_with(Low6Bits(3)), ::testing::_))
      .Times(AtLeast(1u));

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L0)
      (const v0 0)
      (goto :end-setup)
      (:L0)
      (const v0 3)
      (:end-setup)  ;; v0 is [0,3]{9}

      (const v1 3)
      (if-eq v0 v1 :end)
      (if-eqz v0 :end)
      ;; v0 is [1, 2]{9}. It equals _|_ but is not _|_.
      (const v1 2)
      (if-eq v0 v1 :end)  ;; _|_ on both branches.
      (:end)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::OnlyForwardTargets);

  // The full optimization still takes place because the offending
  // forward_targets invokation (i.e., with a false only_feasible) only
  // starts visiting in (const v1 2). See P2034419723 for the full log.
  const auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (:L1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, RedundantNullCheck) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (invoke-static (v1) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (invoke-static (v1) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, RedundantNullCheckCmp) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (if-eqz v0 :L0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (:L0)
      (return-void)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ArithmeticFolding) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 0)

      (add-int v2 v0 v1)
      (add-int v3 v1 v0)

      (mul-int v4 v0 v1)
      (mul-int v5 v0 v1)

      (const v1 1)

      (mul-int v4 v0 v1)
      (mul-int v5 v0 v1)

      (const v1 -1)

      (mul-int v4 v0 v1)
      (mul-int v5 v0 v1)

      (const v1 0)

      (or-int v6 v0 v1)
      (or-int v7 v0 v1)

      (const v1 -1)

      (or-int v6 v0 v1)
      (or-int v7 v0 v1)

      (const v1 0)

      (and-int v8 v0 v1)
      (and-int v9 v0 v1)

      (const v1 -1)

      (and-int v8 v0 v1)
      (and-int v9 v0 v1)

      (const v1 0)

      (xor-int v10 v0 v1)
      (xor-int v11 v0 v1)

      (return v2)
    )
  )");

  DexMethod::make_method("LFoo;.bar:(I)I");
  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 0)

      (move v2 v0)
      (move v3 v0)

      (const v4 0)
      (const v5 0)

      (const v1 1)

      (move v4 v0)
      (move v5 v0)

      (const v1 -1)

      (neg-int v4 v0)
      (neg-int v5 v0)

      (const v1 0)

      (move v6 v0)
      (move v7 v0)

      (const v1 -1)

      (const v6 -1)
      (const v7 -1)

      (const v1 0)

      (const v8 0)
      (const v9 0)

      (const v1 -1)

      (move v8 v0)
      (move v9 v0)

      (const v1 0)

      (move v10 v0)
      (move v11 v0)

      (return v2)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ArithmeticFoldingLong) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const-wide v2 0)

      (add-long v4 v0 v2)
      (add-long v6 v2 v0)

      (mul-long v8 v0 v2)
      (mul-long v10 v0 v2)

      (const-wide v2 1)

      (mul-long v8 v0 v2)
      (mul-long v10 v0 v2)

      (const-wide v2 -1)

      (mul-long v8 v0 v2)
      (mul-long v10 v0 v2)

      (const-wide v2 0)

      (or-long v12 v0 v2)
      (or-long v14 v0 v2)

      (const-wide v2 -1)

      (or-long v12 v0 v2)
      (or-long v14 v0 v2)

      (const-wide v2 0)

      (and-long v16 v0 v2)
      (and-long v18 v0 v2)

      (const-wide v2 -1)

      (and-long v16 v0 v2)
      (and-long v18 v0 v2)

      (const-wide v2 0)

      (xor-long v20 v0 v2)
      (xor-long v22 v0 v2)

      (return v4)
    )
  )");

  DexMethod::make_method("LFoo;.bar:(I)I");
  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const-wide v2 0)

      (move-wide v4 v0)
      (move-wide v6 v0)

      (const-wide v8 0)
      (const-wide v10 0)

      (const-wide v2 1)

      (move-wide v8 v0)
      (move-wide v10 v0)

      (const-wide v2 -1)

      (neg-long v8 v0)
      (neg-long v10 v0)

      (const-wide v2 0)

      (move-wide v12 v0)
      (move-wide v14 v0)

      (const-wide v2 -1)

      (const-wide v12 -1)
      (const-wide v14 -1)

      (const-wide v2 0)

      (const-wide v16 0)
      (const-wide v18 0)

      (const-wide v2 -1)

      (move-wide v16 v0)
      (move-wide v18 v0)

      (const-wide v2 0)

      (move-wide v20 v0)
      (move-wide v22 v0)

      (return v4)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ArithmeticFoldingFromLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (add-int/lit v2 v0 0)
      (add-int/lit v3 v1 0)

      (rsub-int/lit v4 v0 0)
      (rsub-int/lit v5 v0 0)

      (mul-int/lit v6 v0 0)
      (mul-int/lit v7 v0 0)

      (mul-int/lit v8 v0 1)
      (mul-int/lit v9 v0 1)

      (mul-int/lit v10 v0 -1)
      (mul-int/lit v11 v0 -1)

      (or-int/lit v12 v0 0)
      (or-int/lit v13 v0 0)

      (or-int/lit v14 v0 -1)
      (or-int/lit v15 v0 -1)

      (and-int/lit v1 v0 0)
      (and-int/lit v2 v0 0)

      (and-int/lit v3 v0 -1)
      (and-int/lit v4 v0 -1)

      (xor-int/lit v16 v0 0)
      (xor-int/lit v17 v0 0)

      (return v0)
    )
  )");

  DexMethod::make_method("LFoo;.bar:(I)I");
  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (move v2 v0)
      (move v3 v1)

      (neg-int v4 v0)
      (neg-int v5 v0)

      (const v6 0)
      (const v7 0)

      (move v8 v0)
      (move v9 v0)

      (neg-int v10 v0)
      (neg-int v11 v0)

      (move v12 v0)
      (move v13 v0)

      (const v14 -1)
      (const v15 -1)

      (const v1 0)
      (const v2 0)

      (move v3 v0)
      (move v4 v0)

      (move v16 v0)
      (move v17 v0)

      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ArithmeticFoldingToLit8) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v127 127)
      (const v128 -128)

      (add-int v2 v0 v127)
      (add-int v3 v128 v0)

      (mul-int v4 v0 v127)
      (mul-int v5 v128 v0)

      (or-int v6 v0 v127)
      (or-int v7 v128 v0)

      (and-int v8 v0 v127)
      (and-int v9 v128 v0)

      (xor-int v10 v0 v127)
      (xor-int v11 v128 v0)

      (return v0)
    )
  )");

  DexMethod::make_method("LFoo;.bar:(I)I");
  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v127 127)
      (const v128 -128)

      (add-int/lit v2 v0 127)
      (add-int/lit v3 v0 -128)

      (mul-int/lit v4 v0 127)
      (mul-int/lit v5 v0 -128)

      (or-int/lit v6 v0 127)
      (or-int/lit v7 v0 -128)

      (and-int/lit v8 v0 127)
      (and-int/lit v9 v0 -128)

      (xor-int/lit v10 v0 127)
      (xor-int/lit v11 v0 -128)

      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ArithmeticFoldingToLit16) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v127 32767)
      (const v128 -32768)

      (add-int v2 v0 v127)
      (add-int v3 v128 v0)

      (mul-int v4 v0 v127)
      (mul-int v5 v128 v0)

      (or-int v6 v0 v127)
      (or-int v7 v128 v0)

      (and-int v8 v0 v127)
      (and-int v9 v128 v0)

      (xor-int v10 v0 v127)
      (xor-int v11 v128 v0)

      (return v0)
    )
  )");

  DexMethod::make_method("LFoo;.bar:(I)I");
  auto config = cp::Transform::Config();
  config.to_int_lit16 = true;
  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(), config);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const v127 32767)
      (const v128 -32768)

      (add-int/lit v2 v0 32767)
      (add-int/lit v3 v0 -32768)

      (mul-int/lit v4 v0 32767)
      (mul-int/lit v5 v0 -32768)

      (or-int/lit v6 v0 32767)
      (or-int/lit v7 v0 -32768)

      (and-int/lit v8 v0 32767)
      (and-int/lit v9 v0 -32768)

      (xor-int/lit v10 v0 32767)
      (xor-int/lit v11 v0 -32768)

      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ComparisonRefinesNumericInterval) {
  // v0: [200, +inf)
  // v1: (-inf, 100)
  // ==> v0 > v1, v0 >= v1, v0 != v1
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 200)
      (if-lt v0 v2 :exit)
      (const v2 100)
      (if-gt v1 v2 :exit)

      (if-gt v0 v1 :exit)
      (if-ge v0 v1 :exit)
      (if-ne v0 v1 :exit)
      (const-string "unreachable")
      (move-result-pseudo-object v3)
      (return-object v3)

      (:exit)
      (const v3 0)
      (return-object v3)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 200)
      (if-lt v0 v2 :exit)
      (const v2 100)
      (if-gt v1 v2 :exit)

      (:exit)
      (const v3 0)
      (return-object v3)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest, NEChopsOffNumericInterval) {
  // If we have x >= 200 and x != 200, then we know that x > 200.
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v2 200)
      (if-lt v0 v2 :exit)
      (if-eq v0 v2 :exit)

      (if-gt v0 v2 :exit)
      (const-string "unreachable")
      (move-result-pseudo-object v3)
      (return-object v3)

      (:exit)
      (const v3 0)
      (return-object v3)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v2 200)
      (if-lt v0 v2 :exit)
      (if-eq v0 v2 :exit)

      (:exit)
      (const v3 0)
      (return-object v3)
    )
  )");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(ConstantPropagationTest,
       ForwardAfterReplacingMoveResultWithThrowBlockRegression) {
  // The bug was that "(move-result-pseudo v1)" gets folded to "const v1 2", but
  // in the wrong block, so that the earlier assigned value 23 leaked through.
  // This caused the forwarding logic to apply a wrong transformation.
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v3)
      (const v1 23)
      (if-ge v3 v1 :exit)

    (.try_start a)
    (:start)
      (const v0 6)
      (div-int/lit v0 3)
      (move-result-pseudo v1)
      (if-lt v1 v3 :exit)
      (const v0 42)
      (return v0)
    (:exit)
      (return v0)
    (.try_end a)
    (.catch (a))
    (:loop)
      (goto :loop)
    )
  )");

  do_const_prop(code.get(), cp::ConstantPrimitiveAnalyzer(),
                cp::Transform::Config(), ConstPropMode::All);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v3)
      (const v1 23)
      (if-ge v3 v1 :exit)
      (const v0 6)
      (const v1 2)
      (if-lt v1 v3 :exit)
      (const v0 42)
      (return v0)
    (:exit)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// Verify that null checks on new-instance results are eliminated when
// NewObjectAnalyzer runs (as in ConstantPrimitiveAndBoxedAnalyzer). The
// NewObjectAnalyzer sets RESULT_REGISTER to NewObjectDomain and short-circuits
// PrimitiveAnalyzer, so the value is not a SignedConstantDomain(NEZ). The
// transform must recognize object domains as non-null.
TEST_F(ConstantPropagationTest, NewInstanceNullCheckElimination) {
  // Create the Kotlin null check method so cp::NullCheckMethods picks it up.
  auto* null_check = DexMethod::make_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:"
      "(Ljava/lang/Object;Ljava/lang/String;)V");
  null_check->make_concrete(ACC_PUBLIC | ACC_STATIC, true);

  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (const-string "param")
      (move-result-pseudo-object v1)
      (invoke-static (v0 v1) "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/Object;Ljava/lang/String;)V")
      (return-void)
    )
  )");

  // do_const_prop's default analyzer is ConstantPrimitiveAnalyzer (just
  // PrimitiveAnalyzer), which handles new-instance by setting RESULT_REGISTER
  // to SignedConstantDomain(NEZ). That would make the null check elimination
  // succeed via is_nez() alone, never exercising the is_object() path. We
  // include NewObjectAnalyzer in the combiner so it short-circuits
  // PrimitiveAnalyzer and produces a NewObjectDomain value instead, verifying
  // that even without PrimitiveAnalyzer's NEZ fallback, is_object() recognizes
  // object domains as non-null and eliminates the null check.
  cp::ImmutableAttributeAnalyzerState immut_analyzer_state;
  using Analyzer =
      InstructionAnalyzerCombiner<cp::NewObjectAnalyzer, cp::PrimitiveAnalyzer>;
  Analyzer analyzer(&immut_analyzer_state, nullptr);

  do_const_prop(code.get(), analyzer);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (const-string "param")
      (move-result-pseudo-object v1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// Verify that checkNotNull teaches constant propagation that the value is
// non-null, enabling elimination of a subsequent null check branch.
TEST_F(ConstantPropagationTest, CheckNotNullEnablesNullCheckElimination) {
  auto* check_not_null = DexMethod::make_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkNotNull:"
      "(Ljava/lang/Object;)V");
  check_not_null->make_concrete(ACC_PUBLIC | ACC_STATIC, true);

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.checkNotNull:(Ljava/lang/Object;)V")
      (if-eqz v0 :is_null)
      (const v1 1)
      (goto :end)
      (:is_null)
      (const v1 0)
      (:end)
      (return v1)
    )
  )");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.checkNotNull:(Ljava/lang/Object;)V")
      (const v1 1)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}
