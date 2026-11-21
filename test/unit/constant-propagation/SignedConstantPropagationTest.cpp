/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <boost/algorithm/string/replace.hpp>

#include "AbstractDomainPropertyTest.h"
#include "ConstantPropagationTestUtil.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "SignedConstantDomain.h"

struct Constants {
  SignedConstantDomain one{SignedConstantDomain(1)};

  SignedConstantDomain minus_one{SignedConstantDomain(-1)};

  SignedConstantDomain zero{SignedConstantDomain(0)};

  SignedConstantDomain max_val{
      SignedConstantDomain(std::numeric_limits<int64_t>::max())};

  SignedConstantDomain min_val{
      SignedConstantDomain(std::numeric_limits<int64_t>::min())};

  SignedConstantDomain positive{
      SignedConstantDomain(sign_domain::Interval::GTZ)};

  SignedConstantDomain negative{
      SignedConstantDomain(sign_domain::Interval::LTZ)};

  SignedConstantDomain not_zero{
      SignedConstantDomain(sign_domain::Interval::NEZ)};
};

INSTANTIATE_TYPED_TEST_SUITE_P(SignedConstantDomain,
                               AbstractDomainPropertyTest,
                               SignedConstantDomain);

template <>
std::vector<SignedConstantDomain>
AbstractDomainPropertyTest<SignedConstantDomain>::non_extremal_values() {
  Constants constants;
  return {constants.one,      constants.minus_one, constants.zero,
          constants.max_val,  constants.min_val,   constants.positive,
          constants.negative, constants.not_zero};
}

class SignedConstantDomainOperationsTest : public testing::Test,
                                           public Constants {};

TEST_F(SignedConstantDomainOperationsTest, intervals) {
  using namespace sign_domain;

  EXPECT_EQ(one.interval(), Interval::GTZ);
  EXPECT_EQ(minus_one.interval(), Interval::LTZ);
  EXPECT_EQ(zero.interval(), Interval::EQZ);
  EXPECT_EQ(SignedConstantDomain(Interval::EQZ), zero);
  EXPECT_EQ(max_val.interval(), Interval::GTZ);
  EXPECT_EQ(min_val.interval(), Interval::LTZ);
  EXPECT_EQ(not_zero.interval(), Interval::NEZ);

  EXPECT_EQ(one.join(minus_one).interval(), Interval::NEZ);
  EXPECT_EQ(one.join(zero).interval(), Interval::GEZ);
  EXPECT_EQ(minus_one.join(zero).interval(), Interval::LEZ);
  EXPECT_EQ(max_val.join(zero).interval(), Interval::GEZ);
  EXPECT_EQ(min_val.join(zero).interval(), Interval::LEZ);
  EXPECT_EQ(min_val.join(max_val).interval(), Interval::NEZ);
}

TEST_F(SignedConstantDomainOperationsTest, numeric_intervals) {
  using namespace sign_domain;

  EXPECT_EQ(one.numeric_interval_domain(), NumericIntervalDomain::finite(1, 1));
  EXPECT_EQ(minus_one.numeric_interval_domain(),
            NumericIntervalDomain::finite(-1, -1));
  EXPECT_EQ(zero.numeric_interval_domain(),
            NumericIntervalDomain::finite(0, 0));
  EXPECT_EQ(NumericIntervalDomain::finite(0, 0),
            zero.numeric_interval_domain());
  EXPECT_EQ(max_val.numeric_interval_domain(), NumericIntervalDomain::high());
  EXPECT_EQ(min_val.numeric_interval_domain(), NumericIntervalDomain::low());
  EXPECT_EQ(not_zero.numeric_interval_domain(), NumericIntervalDomain::top());

  EXPECT_EQ(one.join(minus_one).numeric_interval_domain(),
            NumericIntervalDomain::finite(-1, 1));
  EXPECT_EQ(one.join(zero).numeric_interval_domain(),
            NumericIntervalDomain::finite(0, 1));
  EXPECT_EQ(minus_one.join(zero).numeric_interval_domain(),
            NumericIntervalDomain::finite(-1, 0));
  EXPECT_EQ(max_val.join(zero).numeric_interval_domain(),
            NumericIntervalDomain::bounded_below(0));
  EXPECT_EQ(min_val.join(zero).numeric_interval_domain(),
            NumericIntervalDomain::bounded_above(0));
  EXPECT_EQ(min_val.join(max_val).numeric_interval_domain(),
            NumericIntervalDomain::top());
}

TEST_F(SignedConstantDomainOperationsTest, binaryOperations) {
  using namespace sign_domain;

  EXPECT_EQ(one.join(positive), positive);
  EXPECT_EQ(max_val.join(positive), positive);
  EXPECT_EQ(minus_one.join(negative), negative);
  EXPECT_EQ(min_val.join(negative), negative);
  EXPECT_EQ(zero.join(positive).interval(), Interval::GEZ);
  EXPECT_EQ(zero.join(negative).interval(), Interval::LEZ);
  EXPECT_EQ(zero.join(not_zero).interval(), Interval::ALL);

  EXPECT_EQ(one.meet(positive), one);
  EXPECT_TRUE(one.meet(negative).is_bottom());
  EXPECT_EQ(max_val.meet(positive), max_val);
  EXPECT_TRUE(max_val.meet(negative).is_bottom());
  EXPECT_EQ(minus_one.meet(negative), minus_one);
  EXPECT_TRUE(minus_one.meet(positive).is_bottom());
  EXPECT_EQ(min_val.meet(negative), min_val);
  EXPECT_TRUE(min_val.meet(positive).is_bottom());
  EXPECT_TRUE(zero.meet(not_zero).is_bottom());
  EXPECT_EQ(not_zero.meet(positive), positive);
  EXPECT_EQ(not_zero.meet(max_val), max_val);
  EXPECT_EQ(not_zero.meet(min_val), min_val);
}

class ConstantNezTest : public ConstantPropagationTest {};

TEST_F(ConstantNezTest, DeterminableNezTrue) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")

     (if-nez v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")

     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantNezTest, DeterminableNezFalse) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (const v0 0)

     (if-nez v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (const v0 0)

     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantNezTest, DeterminableEZFalse) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)

     (if-eqz v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)

     (const v0 1)

     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantNezTest, NonDeterminableNEZ) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")
     (iget v0 "LBoo;.a:I")
     (move-result-pseudo v0)

     (if-nez v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")
     (iget v0 "LBoo;.a:I")
     (move-result-pseudo v0)

     (if-nez v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, IfToGoto) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)

     (if-eqz v0 :if-true-label)
     (const v0 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)

     (const v0 2)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

class ConstantBitwiseTest : public ConstantPropagationTest {
 public:
  struct Case {
    std::string name;
    int64_t operand;
    int64_t comparee;

    std::string format_code(std::string code_str) const {
      boost::replace_first(code_str, "{operand}", std::to_string(operand));
      boost::replace_first(code_str, "{comparee}", std::to_string(comparee));
      return code_str;
    }
  };
};

class ConstantBitwiseAndTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<ConstantBitwiseTest::Case> {};

TEST_P(ConstantBitwiseAndTest, DeterminableZeroLit) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (const v1 {comparee})
     (load-param v0)
     (and-int/lit v0 v0 {operand})  ; Some bits of v0 must be 0 now, can infer v0 != v1

     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (const v1 {comparee})
     (load-param v0)
     (and-int/lit v0 v0 {operand})

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_P(ConstantBitwiseAndTest, DeterminableZeroInt) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param v0)
     (load-param v1)
     (and-int/lit v1 v1 {operand})  ; Some bits of v1 must be 0 now
     (and-int v0 v0 v1)  ; Some bits of v0 must be 0 now

     (const v1 {comparee})
     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param v0)
     (load-param v1)
     (and-int/lit v1 v1 {operand})
     (and-int v0 v0 v1)

     (const v1 {comparee})
     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_P(ConstantBitwiseAndTest, DeterminableZeroLong) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param-wide v0)
     (const-wide v1 {operand})
     (and-long v0 v0 v1)  ; Some bits of v0 must be 0 now

     (const-wide v1 {comparee})
     (cmp-long v2 v0 v1)
     (if-nez v2 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param-wide v0)
     (const-wide v1 {operand})
     (and-long v0 v0 v1)  ; Some bits of v0 must be 0 now

     (const-wide v1 {comparee})
     (cmp-long v2 v0 v1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  // Make sure that the and-long instruction is not optimized away with
  // and-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("and-long"));
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseAndDeterminableZeroTests,
    ConstantBitwiseAndTest,
    ::testing::ValuesIn(
        std::initializer_list<ConstantBitwiseAndTest::ParamType>{
            {.name = "SingleBitIsZero",
             .operand = -3 /* 11..01 */,
             .comparee = 2 /* 00..10 */},
            {.name = "MultipleBitsAreZero",
             .operand = -6 /* 11..010 */,
             .comparee = 1 /* 00..001 */},
        }),
    [](const testing::TestParamInfo<ConstantBitwiseAndTest::ParamType>& info) {
      return info.param.name;
    });

TEST_F(ConstantBitwiseAndTest, UndeterminableZeroLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v2)

     (const v1 -2)  ;; only the lowest bit is 0
     (and-int/lit v0 v0 -2)  ; lowest bit v0 must be 0 now, but can't infer v0 != v1

     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)

     (const v3 2147483647) ;; only the highest bit is 0
     (and-int/lit v2 v2 2147483647)  ; highest bit v2 must be 0 now, but can't infer v2 != v3
     (if-ne v2 v3 :if-true-label2)
     (const v1 2)
     (:if-true-label2)

     (return-void)
    )
)");
  do_const_prop(code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v0 v1 :.*\\)[[:space:]]*\\(const v1 1\\)"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v2 v3 :.*\\)[[:space:]]*\\(const v1 2\\)"));
}

TEST_F(ConstantBitwiseAndTest, UndeterminableZeroInt) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param v2)
     (load-param v3)

     (and-int/lit v1 v1 -2)  ;; only the lowest bit is 0
     (and-int v0 v0 v1)  ; lowest bit v0 must be 0 now, but can't infer v0 != 0

     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)

     (and-int/lit v2 v2 2147483647)  ;; only the highest bit is 0
     (and-int v3 v3 v2)  ; highest bit v3 must be 0 now, but can't infer v3 != v2
     (if-ne v3 v2 :if-true-label2)
     (const v1 2)
     (:if-true-label2)

     (return-void)
    )
)");
  do_const_prop(code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-nez v0 :.*\\)[[:space:]]*\\(const v1 1\\)"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v3 v2 :.*\\)[[:space:]]*\\(const v1 2\\)"));
}

TEST_F(ConstantBitwiseAndTest, UndeterminableZeroLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -2)  ;; only the lowest bit is 0
     (and-long v0 v0 v1)  ; lowest bit v0 must be 0 now, but can't infer v0 != 0

     (const-wide v1 0)
     (cmp-long v0 v0 v1)
     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());
  // Make sure that the and-long instruction is not optimized away with
  // and-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("and-long"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-nez v0 :.*\\)[[:space:]]*\\(const v1 1\\)"));
}

class ConstantBitwiseOrTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<ConstantBitwiseTest::Case> {};

TEST_F(ConstantBitwiseOrTest, NezLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (or-int/lit v0 v0 8)  ; 4th lowest bit of v0 must be 1, can infer v0 != 0

     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (or-int/lit v0 v0 8)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseOrTest, NezInt) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (or-int/lit v1 v1 8)  ; 4th lowest bit of v1 must be 1
     (or-int v0 v0 v1)  ; 4th lowest bit of v0 must be 1

     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (or-int/lit v1 v1 8)
     (or-int v0 v0 v1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseOrTest, NezLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 8)
     (or-long v0 v0 v1)  ; 4th lowest bit of v0 must be 1, can infer v0 != 0
     (const-wide v1 0)
     (cmp-long v0 v0 v1)

     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 8)
     (or-long v0 v0 v1)
     (const-wide v1 0)
     (cmp-long v0 v0 v1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");

  // Make sure that the or-long instruction is not optimized away with
  // or-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("or-long"));
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_P(ConstantBitwiseOrTest, DeterminableOneLit) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (const v1 {comparee})
     (load-param v0)
     (or-int/lit v0 v0 {operand})  ; some bits of v0 must be 1 now, can infer v0 != v1

     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (const v1 {comparee})
     (load-param v0)
     (or-int/lit v0 v0 {operand})

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_P(ConstantBitwiseOrTest, DeterminableOneInt) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param v0)
     (load-param v1)
     (or-int/lit v1 v1 {operand})  ; Some bits of v1 must be 1 now
     (or-int v0 v0 v1)  ; Some bits of v0 must be 1 now

     (const v1 {comparee})
     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param v0)
     (load-param v1)
     (or-int/lit v1 v1 {operand})
     (or-int v0 v0 v1)

     (const v1 {comparee})
     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_P(ConstantBitwiseOrTest, DeterminableOneLong) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param-wide v0)
     (const-wide v1 {operand})
     (or-long v0 v0 v1)  ; some bits of v0 must be 1 now, can infer v0 != comparee
     (const-wide v1 {comparee})
     (cmp-long v0 v0 v1)

     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(param.format_code(R"(
    (
     (load-param-wide v0)
     (const-wide v1 {operand})
     (or-long v0 v0 v1)
     (const-wide v1 {comparee})
     (cmp-long v0 v0 v1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)"));

  // Make sure that the or-long instruction is not optimized away with
  // or-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("or-long"));
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseOrDeterminableOneTests,
    ConstantBitwiseOrTest,
    ::testing::ValuesIn(std::initializer_list<ConstantBitwiseOrTest::ParamType>{
        {.name = "SingleBitIsOne",
         .operand = 2 /* 00..10 */,
         .comparee = 1 /* 00..01 */},
        {.name = "MultipleBitsAreOne",
         .operand = -5 /* 11..101 */,
         .comparee = 4 /* 00..100 */},
    }),
    [](const testing::TestParamInfo<ConstantBitwiseOrTest::ParamType>& info) {
      return info.param.name;
    });

TEST_F(ConstantBitwiseOrTest, UndeterminableOneLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v2)

     (const v1 1)  ;; only lowest bit is 1
     (or-int/lit v0 v0 1)  ; lowest bit v0 must be 1 now, but can't infer v0 != v1

     (if-ne v0 v1 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (or-int/lit v2 v2 -2147483648)  ; highest bit v0 must be 1 now, but can't infer v0 != -1
     (const v3 -1)
     (if-ne v2 v3 :if-true-label2)
     (const v3 1)
     (:if-true-label2)
     (return-void)
    )
)");
  do_const_prop(code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v0 v1 :.*\\)[[:space:]]*\\(const v1 1\\)"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v2 v3 :.*\\)[[:space:]]*\\(const v3 1\\)"));
}

TEST_F(ConstantBitwiseOrTest, UndeterminableOneInt) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param v4)
     (load-param v5)
     (or-int/lit v1 v1 1)  ; lowest bit v1 must be 1 now
     (or-int v0 v0 v1)  ; lowest bit v0 must be 1 now, but can't infer v0 != 1

     (const v3 1)
     (if-ne v0 v3 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (or-int/lit v4 v4 -2147483648)  ; highest bit v4 must be 1
     (or-int v5 v5 v4)  ; highest bit v5 must be 1, but can't infer v5 != -1
     (const v6 -1)
     (if-ne v5 v6 :if-true-label2)
     (const v6 1)
     (:if-true-label2)
     (return-void)
    )
)");
  do_const_prop(code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v0 v3 :.*\\)[[:space:]]*\\(const v1 1\\)"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v5 v6 :.*\\)[[:space:]]*\\(const v6 1\\)"));
}

TEST_F(ConstantBitwiseOrTest, UndeterminableOneLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 1)
     (or-long v0 v0 v1)  ; lowest bit v0 must be 1 now, but can't infer v0 != 1

     (cmp-long v0 v0 v1)
     (if-nez v0 :if-true-label)
     (const v1 1)

     (:if-true-label)
     (const v0 2)

     (return-void)
    )
)");
  do_const_prop(code.get());

  // Make sure that the or-long instruction is not optimized away with
  // or-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("or-long"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-nez v0 :.*\\)[[:space:]]*\\(const v1 1\\)"));
}

TEST_F(ConstantBitwiseTest, DeterminableBitsWithXorLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     (xor-int/lit v0 v0 5)  ;; Lowest 4 bits: 1001

     ;; Test each for the lowest 4 bits

     (const v1 8)  ;; binary 0...01000
     (if-ne v0 v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const v1 11)  ;; binary 0...01011
     (if-ne v0 v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const v1 13)  ;; binary 0...01101
     (if-ne v0 v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const v1 1)  ;; binary 0...00001
     (if-ne v0 v1 :bit-3)
     (const v5 1)
     (:bit-3)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)
     (or-int/lit v0 v0 12)
     (xor-int/lit v0 v0 5)

     (const v1 8)
     (:bit-0)

     (const v1 11)
     (:bit-1)

     (const v1 13)
     (:bit-2)

     (const v1 1)
     (:bit-3)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseTest, DeterminableBitsWithXorInt) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     (and-int/lit v1 v1 -11)  ;; 2nd and 4th lowest bits of v1 must be 0
     (or-int/lit v1 v1 5)  ;; 1st and 3nd lowest bits of v1 must be 1
     (xor-int v0 v0 v1)  ;; Lowest 4 bits: 1001

     ;; Test each for the lowest 4 bits

     (const v1 8)  ;; binary 0...01000
     (if-ne v0 v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const v1 11)  ;; binary 0...01011
     (if-ne v0 v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const v1 13)  ;; binary 0...01101
     (if-ne v0 v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const v1 1)  ;; binary 0...00001
     (if-ne v0 v1 :bit-3)
     (const v5 1)
     (:bit-3)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (and-int/lit v0 v0 -4)
     (or-int/lit v0 v0 12)
     (and-int/lit v1 v1 -11)
     (or-int/lit v1 v1 5)
     (xor-int v0 v0 v1)

     (const v1 8)
     (:bit-0)

     (const v1 11)
     (:bit-1)

     (const v1 13)
     (:bit-2)

     (const v1 1)
     (:bit-3)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseTest, DeterminableBitsWithXorLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)  ;; 1st and 2nd lowest bits of v0 must be 0
     (const-wide v1 12)
     (or-long v0 v0 v1)  ;; 3rd and 4th lowest bits of v0 must be 1
     (const-wide v1 5)
     (xor-long v0 v0 v1)  ;; Lowest 4 bits: 1001

     ;; Test each for the lowest 4 bits

     (const-wide v1 8)  ;; binary 0...01000
     (cmp-long v2 v0 v1)
     (if-nez v2 :bit-0)
     (const v3 1)
     (:bit-0)

     (const-wide v1 11)  ;; binary 0...01011
     (cmp-long v2 v0 v1)
     (if-nez v2 :bit-1)
     (const v4 1)
     (:bit-1)

     (const-wide v1 13)  ;; binary 0...01101
     (cmp-long v2 v0 v1)
     (if-nez v2 :bit-2)
     (const v5 1)
     (:bit-2)

     (const-wide v1 1)  ;; binary 0...00001
     (cmp-long v2 v0 v1)
     (if-nez v2 :bit-3)
     (const v6 1)
     (:bit-3)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)
     (const-wide v1 12)
     (or-long v0 v0 v1)
     (const-wide v1 5)
     (xor-long v0 v0 v1)

     (const-wide v1 8)
     (cmp-long v2 v0 v1)
     (:bit-0)

     (const-wide v1 11)
     (cmp-long v2 v0 v1)
     (:bit-1)

     (const-wide v1 13)
     (cmp-long v2 v0 v1)
     (:bit-2)

     (const-wide v1 1)
     (cmp-long v2 v0 v1)
     (:bit-3)

     (return-void)
    )
)");

  // Make sure that the xor-long instruction is not optimized away with
  // xor-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("xor-long"));
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseTest, UndeterminableBitsWithXorLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     (or-int/lit v0 v0 -2147483648)  ;; Highest bit of v0 must be 1
     (xor-int/lit v0 v0 5)  ;; Lowest 4 bits: 1001
     (xor-int/lit v0 v0 -2147483648) ;; Highest bit of v0 must be 0

     (const v1 9)  ;; binary 0...01001
     (if-ne v0 v1 :if-true-label)
     (const v2 1)
     (:if-true-label)

     (return-void)
    )
)");
  do_const_prop(code.get());

  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v0 v1 :.*\\)[[:space:]]*\\(const v2 1\\)"));
}

TEST_F(ConstantBitwiseTest, UndeterminableBitsWithXorInt) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     (or-int/lit v0 v0 -2147483648)  ;; Highest bit of v0 must be 1
     (and-int/lit v1 v1 -11)  ;; 2nd and 4th lowest bits of v1 must be 0
     (or-int/lit v1 v1 5)  ;; 1st and 3nd lowest bits of v1 must be 1
     (or-int/lit v1 v1 -2147483648)  ;; Highest bit of v1 must be 1
     (xor-int v0 v0 v1)  ;; Lowest 4 bits: 1001, highest bit: 0

     (const v1 9)  ;; binary 0...01001
     (if-ne v0 v1 :if-true-label)
     (const v2 1)
     (:if-true-label)

     (return-void)
    )
)");
  do_const_prop(code.get());

  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v0 v1 :.*\\)[[:space:]]*\\(const v2 1\\)"));
}

TEST_F(ConstantBitwiseTest, UndeterminableBitsWithXorLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)  ;; 1st and 2nd lowest bits of v0 must be 0
     (const-wide v1 12)
     (or-long v0 v0 v1)  ;; 3rd and 4th lowest bits of v0 must be 1
     (const-wide v1 5)
     (xor-long v0 v0 v1)  ;; Lowest 4 bits: 1001

     (const v1 9)  ;; binary 0...01001
     (cmp-long v2 v0 v1)
     (if-nez v2 :if-true-label)
     (const v2 1)
     (:if-true-label)

     (return-void)
    )
)");
  do_const_prop(code.get());

  // Make sure that the xor-long instruction is not optimized away with
  // xor-int/lit.
  ASSERT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("xor-long"));
  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-nez v2 :.*\\)[[:space:]]*\\(const v2 1\\)"));
}

TEST_F(ConstantBitwiseTest, DeterminableBitJoinedFromConstants) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :if-true-label)
     (const v1 0)
     (goto :end-if)
     (:if-true-label)
     (const v1 2)
     (:end-if)
     ;; Joining the two branches, the lowest bit of v1 must be 0, thus v1 != 1
     (const v2 1)
     (if-ne v1 v2 :end)
     (const v0 10)
     (:end)
     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :end-if)
     (const v1 0)
     (:if-true-label)
     (const v2 1)
     (return-void)
     (:end-if)
     (const v1 2)
     (goto :if-true-label)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

struct ConstantBitwiseShiftTestCase {
  std::string name;
  std::string shift_instruction;
};
class ConstantBitwiseLeftShiftTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<ConstantBitwiseShiftTestCase> {};

TEST_P(ConstantBitwiseLeftShiftTest, DeterminableBitsAfterLeftShiftInt) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     (or-int/lit v0 v0 -2147483648)  ;; Highest bit of v0 must be 1
     {shift_instruction}  ;; Lowest 5 bits: 11000

     (const v1 25)  ;; binary 0...011001
     (if-ne v0 v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const v1 26)  ;; binary 0...011010
     (if-ne v0 v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const v1 28)  ;; binary 0...011100
     (if-ne v0 v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const v1 16)  ;; binary 0...010000
     (if-ne v0 v1 :bit-3)
     (const v5 1)
     (:bit-3)

     (const v1 8)  ;; binary 0...001000
     (if-ne v0 v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (const v1 24)  ;; binary 0...011000
     (if-ne v0 v1 :bit-5)
     (const v7 1)
     (:bit-5)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)
     (or-int/lit v0 v0 12)
     (or-int/lit v0 v0 -2147483648)
     {shift_instruction}

     (const v1 25)
     (:bit-0)

     (const v1 26)
     (:bit-1)

     (const v1 28)
     (:bit-2)

     (const v1 16)
     (:bit-3)

     (const v1 8)
     (:bit-4)

     (const v1 24)
     (if-ne v0 v1 :bit-5)
     (const v7 1)
     (:bit-5)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("(const v7 1)"))
      << "Higest bit is determined to be 1, but it shouldn't";
}

TEST_P(ConstantBitwiseLeftShiftTest, LeftIntShiftDoesNotRetainHigher32Bits) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (load-param-wide v1)
     (or-int/lit v0 v0 -2147483648)  ;; highest bit of v0 must be 1
     {shift_instruction}  ;; highest bit should be shifted out now

     (if-nez v0 :first)
     (const v3 1)  ; feasible, since v0 should have no determined one-bit
     (:first)

     (const v2 -2)
     (if-ne v0 v2 :end)
     ;; feasible, since v0 should have no determined zero-bit other than the lowest bit
     (const v3 2)
     (:end)

     ; Long will keep the states of the higher 32 bits.
     (const-wide v2 2147483648)
     (or-long v1 v1 v2)  ;; bit 31 of v1 must be 1
     (const-wide v2 1)
     (shl-long v1 v1 v2)
     (const-wide v2 0)
     (cmp-long v2 v1 v2)
     (if-nez v2 :second)
     (const v4 1)  ; infeasible
     (:second)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (load-param-wide v1)
     (or-int/lit v0 v0 -2147483648)
     {shift_instruction}

     (if-nez v0 :first)
     (const v3 1)
     (:first)

     (const v2 -2)
     (if-ne v0 v2 :end)
     (const v3 2)
     (:end)

     (const-wide v2 2147483648)
     (or-long v1 v1 v2)
     (const-wide v2 1)
     (shl-long v1 v1 v2)
     (const-wide v2 0)
     (cmp-long v2 v1 v2)
     (:second)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseLeftShiftTests,
    ConstantBitwiseLeftShiftTest,
    ::testing::ValuesIn(
        std::initializer_list<ConstantBitwiseLeftShiftTest::ParamType>{
            {
                .name = "shl_int_lit",
                .shift_instruction = "(shl-int/lit v0 v0 33)", // 0x21
            },
            {.name = "shl_int",
             .shift_instruction = "(const v9 33)(shl-int v0 v0 v9)"},
        }),
    [](const testing::TestParamInfo<ConstantBitwiseLeftShiftTest::ParamType>&
           info) { return info.param.name; });

TEST_F(ConstantBitwiseLeftShiftTest, DeterminableBitsAfterLeftShiftLong) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)  ;; 1st and 2nd lowest bits of v0 must be 0
     (const-wide v1 12)
     (or-long v0 v0 v1)  ;; 3rd and 4th lowest bits of v0 must be 1
     (const-wide v1 -9223372036854775808)
     (or-long v0 v0 v1)  ;; Highest bit of v0 must be 1
     (const-wide v1 65)  ;; 0x41
     (shl-long v0 v0 v1)  ;; Lowest 5 bits: 11000

     (const-wide v1 25)  ;; binary 0...011001
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const-wide v1 26)  ;; binary 0...011010
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const-wide v1 28)  ;; binary 0...011100
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const-wide v1 16)  ;; binary 0...010000
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-3)
     (const v5 1)
     (:bit-3)

     (const-wide v1 8)  ;; binary 0...001000
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (const-wide v1 24)  ;; binary 0...011000
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-5)
     (const v7 1)
     (:bit-5)

     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)
     (const-wide v1 12)
     (or-long v0 v0 v1)
     (const-wide v1 -9223372036854775808)
     (or-long v0 v0 v1)
     (const-wide v1 65)
     (shl-long v0 v0 v1)

     (const-wide v1 25)
     (cmp-long v1 v0 v1)
     (:bit-0)

     (const-wide v1 26)
     (cmp-long v1 v0 v1)
     (:bit-1)

     (const-wide v1 28)
     (cmp-long v1 v0 v1)
     (:bit-2)

     (const-wide v1 16)
     (cmp-long v1 v0 v1)
     (:bit-3)

     (const-wide v1 8)
     (cmp-long v1 v0 v1)
     (:bit-4)

     (const-wide v1 24)
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-5)
     (const v7 1)
     (:bit-5)

     (return-void)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("(const v7 1)"))
      << "Higest bit is determined to be 1, but it shouldn't";
}

class ConstantBitwiseRightShiftIntTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<ConstantBitwiseShiftTestCase> {};

TEST_P(ConstantBitwiseRightShiftIntTest, DeterminableBitsAfterRightShift) {
  const auto& param = GetParam();

  auto code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)  ;; 1st and 2nd lowest bits of v0 must be 0
     (or-int/lit v0 v0 12)  ;; 3rd and 4th lowest bits of v0 must be 1
     {shift_instruction}  ;; Lowest 3 bits: 110

     (const v1 7)  ;; binary 0...0111
     (if-ne v0 v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const v1 4)  ;; binary 0...0100
     (if-ne v0 v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const v1 2)  ;; binary 0...0010
     (if-ne v0 v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const v1 6)  ;; binary 0...0110, 4th bit should no longer be 1
     (if-ne v0 v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(
      boost::replace_first_copy<std::string>(R"(
    (
     (load-param v0)
     (and-int/lit v0 v0 -4)
     (or-int/lit v0 v0 12)
     {shift_instruction}

     (const v1 7)
     (:bit-0)

     (const v1 4)
     (:bit-1)

     (const v1 2)
     (:bit-2)

     (const v1 6)
     (if-ne v0 v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (return-void)
    )
)",
                                             "{shift_instruction}",
                                             param.shift_instruction));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("(const v6 1)"))
      << "4th bit is determined to be 1 but it shouldn't";
}

INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseRightShiftIntTests,
    ConstantBitwiseRightShiftIntTest,
    ::testing::ValuesIn(
        std::initializer_list<ConstantBitwiseRightShiftIntTest::ParamType>{
            {
                .name = "ushr_int_lit",
                // shifted 0x21 & 0x1F = 0x1
                .shift_instruction = "(ushr-int/lit v0 v0 33)",
            },
            {.name = "ushr_int",
             .shift_instruction = "(const v1 33)(ushr-int v0 v0 v1)"},
            {
                .name = "shr_int_lit",
                // shifted 0x21 & 0x1F = 0x1
                .shift_instruction = "(shr-int/lit v0 v0 33)",
            },
            {.name = "shr_int",
             .shift_instruction = "(const v1 33)(shr-int v0 v0 v1)"},
        }),
    [](const testing::TestParamInfo<
        ConstantBitwiseRightShiftIntTest::ParamType>& info) {
      return info.param.name;
    });

class ConstantBitwiseRightShiftLongTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<ConstantBitwiseShiftTestCase> {};
TEST_P(ConstantBitwiseRightShiftLongTest, DeterminableBitsAfterRightShift) {
  const auto& param = GetParam();
  auto code =
      assembler::ircode_from_string(boost::replace_first_copy<std::string>(
          R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)  ;; 1st and 2nd lowest bits of v0 must be 0
     (const-wide v1 12)
     (or-long v0 v0 v1)  ;; 3rd and 4th lowest bits of v0 must be 1
     (const-wide v1 65)  ;; 0x41
     ({shift_instruction} v0 v0 v1)  ;; Lowest 3 bits: 110

     (const-wide v1 7)  ;; binary 0...0111
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-0)
     (const v2 1)
     (:bit-0)

     (const-wide v1 4)  ;; binary 0...0100
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-1)
     (const v3 1)
     (:bit-1)

     (const-wide v1 2)  ;; binary 0...0100
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-2)
     (const v4 1)
     (:bit-2)

     (const-wide v1 6)  ;; binary 0...0110, 4th bit should no longer be 1
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (return-void)
    )
)",
          "{shift_instruction}", param.shift_instruction));
  do_const_prop(code.get());

  auto expected_code =
      assembler::ircode_from_string(boost::replace_first_copy<std::string>(
          R"(
    (
     (load-param-wide v0)
     (const-wide v1 -4)
     (and-long v0 v0 v1)
     (const-wide v1 12)
     (or-long v0 v0 v1)
     (const-wide v1 65)
     ({shift_instruction} v0 v0 v1)

     (const-wide v1 7)
     (cmp-long v1 v0 v1)
     (:bit-0)

     (const-wide v1 4)
     (cmp-long v1 v0 v1)
     (:bit-1)

     (const-wide v1 2)
     (cmp-long v1 v0 v1)
     (:bit-2)

     (const-wide v1 6)
     (cmp-long v1 v0 v1)
     (if-nez v1 :bit-4)
     (const v6 1)
     (:bit-4)

     (return-void)
    )
)",
          "{shift_instruction}", param.shift_instruction));

  EXPECT_CODE_EQ(code.get(), expected_code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("(const v6 1)"))
      << "4th bit is determined to be 1 but it shouldn't";
}
INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseRightShiftLongTests,
    ConstantBitwiseRightShiftLongTest,
    ::testing::ValuesIn(
        std::initializer_list<ConstantBitwiseRightShiftLongTest::ParamType>{
            {
                .name = "ushr_long",
                .shift_instruction = "ushr-long",
            },
            {.name = "shr_long", .shift_instruction = "shr-long"},
        }),
    [](const testing::TestParamInfo<
        ConstantBitwiseRightShiftLongTest::ParamType>& info) {
      return info.param.name;
    });

struct ConstantBitwiseUnsignedRightShiftPrependingZeroTestCase {
  std::string name;
  std::string highest_bit_setting_instructions;
};
class ConstantBitwiseUnsignedRightShiftPrependingZeroTest
    : public ConstantBitwiseTest,
      public ::testing::WithParamInterface<
          ConstantBitwiseUnsignedRightShiftPrependingZeroTestCase> {};
TEST_P(ConstantBitwiseUnsignedRightShiftPrependingZeroTest,
       UnsignedRightShiftPrependsZero) {
  auto code =
      assembler::ircode_from_string(boost::replace_first_copy<std::string>(
          R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-wide v2)
     {highest_bit_setting_instructions}

     (ushr-int/lit v0 v0 1)  ; highest bit is 0
     (and-int/lit v0 v0 -2147483648) ; wiping out lower bits, equivalent to (const v0 0)

     (const v5 1)
     (ushr-int v1 v1 v5)  ; highest bit is 0
     (and-int/lit v1 v1 -2147483648) ; wiping out lower bits, equivalent to (const v1 0)

     (const v5 1)
     (ushr-long v2 v2 v5)  ; highest bit is 0
     (const-wide v5 -9223372036854775808)
     (and-long v2 v2 v5)  ; wiping out lower bits, equivalent to (const-wide v2 0)

     (return-void)
    )
)",
          "{highest_bit_setting_instructions}",
          GetParam().highest_bit_setting_instructions));

  do_const_prop(code.get());

  auto expected_code =
      assembler::ircode_from_string(boost::replace_first_copy<std::string>(
          R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-wide v2)
     {highest_bit_setting_instructions}

     (ushr-int/lit v0 v0 1)
     (const v0 0)

     (const v5 1)
     (ushr-int v1 v1 v5)
     (const v1 0)

     (const v5 1)
     (ushr-long v2 v2 v5)  ; highest bit is 0
     (const-wide v5 -9223372036854775808)
     (const-wide v2 0)

     (return-void)
    )
)",
          "{highest_bit_setting_instructions}",
          GetParam().highest_bit_setting_instructions));
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}
INSTANTIATE_TEST_SUITE_P(
    ConstantBitwiseUnsignedRightShiftPrependingZeroTests,
    ConstantBitwiseUnsignedRightShiftPrependingZeroTest,
    ::testing::ValuesIn(
        std::initializer_list<
            ConstantBitwiseUnsignedRightShiftPrependingZeroTest::ParamType>{
            {
                .name = "undetermined",
                .highest_bit_setting_instructions = "",
            },
            {.name = "highest_bit_0", .highest_bit_setting_instructions = R"(
              (and-int/lit v0 v0 2147483647)
              (and-int/lit v1 v1 2147483647)
              (const-wide v3 9223372036854775807)
              (and-long v2 v2 v3)
             )"},
            {.name = "highest_bit_1", .highest_bit_setting_instructions = R"(
                 (or-int/lit v0 v0 -2147483648)
                 (or-int/lit v1 v1 -2147483648)
                 (const-wide v3  -9223372036854775808)
                 (or-long v2 v2 v3)
            )"},
        }),
    [](const testing::TestParamInfo<
        ConstantBitwiseUnsignedRightShiftPrependingZeroTest::ParamType>& info) {
      return info.param.name;
    });

TEST_F(ConstantBitwiseTest,
       SignedRightShiftPrependsUndeterminedBitWithUndeterminedSignBit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-wide v2)

     (shr-int/lit v0 v0 1)
     (and-int/lit v0 v0 -2147483648)  ; only highest bit is undetermined, others are 0
     (if-nez v0 :intlit-0)
     (const v9 1) ; feasible
     (:intlit-0)
     (const v5 -2147483648)
     (if-ne v0 v5 :intlit-1)
     (const v9 2) ; feasible
     (:intlit-1)

     (const v5 1)
     (shr-int v1 v1 v5)
     (and-int/lit v1 v1 -2147483648)  ; only highest bit is undetermined, others are 0
     (if-nez v1 :int-0)
     (const v9 3) ; feasible
     (:int-0)
     (const v5 -2147483648)
     (if-ne v1 v5 :int-1)
     (const v9 4) ; feasible
     (:int-1)

     (const v5 1)
     (shr-long v2 v2 v5)
     (const-wide v5 -9223372036854775808)
     (and-long v2 v2 v5)  ; only highest bit is undetermined, others are 0
     (cmp-long v5 v2 v5)
     (if-nez v5 :long-1)
     (const v9 5) ; feasible
     (:long-1)
     (const-wide v5 0)
     (cmp-long v5 v2 v5)
     (if-nez v5 :long-0)
     (const v9 6) ; feasible
     (:long-0)

     (return-void)
    )
)");

  do_const_prop(code.get());

  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::AllOf(::testing::HasSubstr("(const v9 1)"),
                               ::testing::HasSubstr("(const v9 2)")))
      << "Highest bit in shr-int/lit is unexpectedly determined";
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::AllOf(::testing::HasSubstr("(const v9 3)"),
                               ::testing::HasSubstr("(const v9 4)")))
      << "Highest bit in shr-int is unexpectedly determined";
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::AllOf(::testing::HasSubstr("(const v9 5)"),
                               ::testing::HasSubstr("(const v9 6)")))
      << "Highest bit in shr-long is unexpectedly determined";
}

TEST_F(ConstantBitwiseTest, SignedRightShiftPrependsSignBitWhenDetermined) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-wide v2)

     (or-int/lit v0 v0 -2147483648)  ; highest bit is 1
     (shr-int/lit v0 v0 1)  ; highest bit is still 1
     (if-nez v0 :intlit-1)
     (const v9 1) ; infeasible
     (:intlit-1)

     (ushr-int/lit v0 v0 1)  ; highest bit is 0
     (shr-int/lit v0 v0 1)  ; highest bit is still 0
     (const v5 -2147483648)
     (if-ne v0 v5 :intlit-0)
     (const v9 2) ; infeasible
     (:intlit-0)

     (or-int/lit v1 v1 -2147483648)  ; highest bit is 1
     (const v5 1)
     (shr-int v0 v0 v5)  ; highest bit is still 1
     (if-nez v0 :int-1)
     (const v9 3) ; infeasible
     (:int-1)

     (ushr-int/lit v0 v0 1)  ; highest bit is 0
     (shr-int v0 v0 v5)  ; highest bit is still 0
     (const v5 -2147483648)
     (if-ne v0 v5 :int-0)
     (const v9 4) ; infeasible
     (:int-0)

     (const-wide v5 -9223372036854775808)
     (or-long v2 v2 v5)  ; highest bit is 1
     (const v5 1)
     (shr-long v2 v2 v5)  ; highest bit is still 1
     (const-wide v5 0)
     (cmp-long v5 v2 v5)
     (if-nez v5 :long-1)
     (const v9 5) ; infeasible
     (:long-1)

     (const v5 1)
     (ushr-long v2 v2 v5)  ; highest bit is 0
     (shr-long v2 v2 v5)  ; highest bit is still 0
     (const-wide v5 -9223372036854775808)
     (cmp-long v5 v2 v5)
     (if-nez v5 :long-0)
     (const v9 6) ; infeasible
     (:long-0)

     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-wide v2)

     (or-int/lit v0 v0 -2147483648)
     (shr-int/lit v0 v0 1)
     (:intlit-1)

     (ushr-int/lit v0 v0 1)
     (shr-int/lit v0 v0 1)
     (const v5 -2147483648)
     (:intlit-0)

     (or-int/lit v1 v1 -2147483648)
     (const v5 1)
     (shr-int v0 v0 v5)
     (:int-1)

     (ushr-int/lit v0 v0 1)
     (shr-int v0 v0 v5)
     (const v5 -2147483648)
     (:int-0)

     (const-wide v5 -9223372036854775808)
     (or-long v2 v2 v5)
     (const v5 1)
     (shr-long v2 v2 v5)
     (const-wide v5 0)
     (cmp-long v5 v2 v5)
     (:long-1)

     (const v5 1)
     (ushr-long v2 v2 v5)
     (shr-long v2 v2 v5)
     (const-wide v5 -9223372036854775808)
     (cmp-long v5 v2 v5)
     (:long-0)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantBitwiseTest, UndeterminableBitJoinedFromConstants) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :if-true-label)
     (const v1 0)
     (goto :end-if)
     (:if-true-label)
     (const v1 2)
     (:end-if)
     ;; Joining the two branches, the lowest bit of v1 must be 0, thus can't infer v1 != 0
     (if-nez v1 :end)
     (const v0 10)
     (:end)
     (return-void)
    )
)");
  do_const_prop(code.get());
  EXPECT_THAT(assembler::to_string(code.get()),
              ::testing::HasSubstr("(if-nez v1"));
}

TEST_F(ConstantPropagationTest, FoldArithmeticAddLit) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 2147483646)
     (add-int/lit v0 v0 1) ; this should be converted to a const opcode
     (const v1 2147483647)
     (if-eq v0 v1 :end)
     (const v0 2147483647)
     (add-int/lit v0 v0 1) ; we don't handle overflows, so this should be
                            ; unchanged
     (:end)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 2147483646)
     (const v0 2147483647)
     (const v1 2147483647)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, AnalyzeCmp) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :b1) ; make sure all blocks appear reachable to constprop
      (if-gez v0 :b2)

      (:b0) ; case v0 < v1
      (const-wide v0 0)
      (const-wide v1 1)
      (cmp-long v2 v0 v1)
      (const v3 -1)
      (if-eq v2 v3 :end)

      (:b1) ; case v0 == v1
      (const-wide v0 1)
      (const-wide v1 1)
      (cmp-long v2 v0 v1)
      (const v3 0)
      (if-eq v2 v3 :end)

      (:b2) ; case v0 > v1
      (const-wide v0 1)
      (const-wide v1 0)
      (cmp-long v2 v0 v1)
      (const v3 1)
      (if-eq v2 v3 :end)

      (:end)
      (return v2)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :b1)
      (if-gez v0 :b2)

      (:b0)
      (const-wide v0 0)
      (const-wide v1 1)
      (cmp-long v2 v0 v1)
      (const v3 -1)

      (:end)
      (return v2)

      (:b2)
      (const-wide v0 1)
      (const-wide v1 0)
      (cmp-long v2 v0 v1)
      (const v3 1)
      (goto :end)

      (:b1)
      (const-wide v0 1)
      (const-wide v1 1)
      (cmp-long v2 v0 v1)
      (const v3 0)
      (goto :end)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstant_EqualsAlwaysTrue) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (const v1 0)

     (if-eqz v0 :if-true-label-1)
     (const v1 1) ; the preceding opcode always jumps, so this is unreachable

     (:if-true-label-1)
     (if-eqz v1 :if-true-label-2) ; therefore this is always true
     (const v1 2)

     (:if-true-label-2)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (const v1 0)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstant_EqualsAlwaysFalse) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 1)

     (if-eqz v0 :if-true-label-1)
     (const v1 0) ; the preceding opcode never jumps, so this is always
                    ; executed
     (:if-true-label-1)
     (if-eqz v1 :if-true-label-2) ; therefore this is always true
     (const v1 2)

     (:if-true-label-2)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 1)

     (const v1 0)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstant_LessThanAlwaysTrue) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (const v1 1)

     (if-lt v0 v1 :if-true-label-1)
     (const v1 0) ; the preceding opcode always jumps, so this is never
                    ; executed
     (:if-true-label-1)
     (if-eqz v1 :if-true-label-2) ; therefore this is never true
     (const v1 2)

     (:if-true-label-2)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (const v1 1)

     (const v1 2)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstant_LessThanAlwaysFalse) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 0)

     (if-lt v0 v1 :if-true-label-1)
     (const v0 0) ; the preceding opcode never jumps, so this is always
                    ; executed
     (:if-true-label-1)
     (if-eqz v0 :if-true-label-2) ; therefore this is always true
     (const v1 2)

     (:if-true-label-2)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (const v1 0)

     (const v0 0)

     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstantInferZero) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0) ; some unknown value

     (if-nez v0 :exit)
     (if-eqz v0 :exit) ; we know v0 must be zero here, so this is always true

     (const v0 1)

     (:exit)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (if-nez v0 :exit)

     (:exit)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstantInferInterval) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0) ; some unknown value

     (if-lez v0 :exit)
     (if-gtz v0 :exit) ; we know v0 must be > 0 here, so this is always true

     (const v0 1)

     (:exit)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (if-lez v0 :exit)

     (:exit)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, ConditionalConstantCompareIntervals) {
  auto code = assembler::ircode_from_string(R"( (
       (load-param v0)
       (load-param v1)

       (if-gtz v0 :if-gtz-label)
       ; here v0 is <= 0
       (if-ltz v1 :if-ltz-label)
       ; here v1 is >= 0
       (if-le v0 v1 :exit)

       (const v3 0)
       (:if-gtz-label)
       (const v4 0)
       (:if-ltz-label)
       (const v5 0)
       (:exit)
       (return-void)
      )
  )");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"( (
       (load-param v0)
       (load-param v1)

       (if-gtz v0 :if-gtz-label)
       ; here v0 is <= 0
       (if-ltz v1 :if-ltz-label)
       ; here v1 is >= 0

       (:exit)
       (return-void)

       (:if-gtz-label)
       (const v4 0)
       (:if-ltz-label)
       (const v5 0)
       (goto :exit)
      )
  )");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// This test catches the regression described in D8676637.
TEST_F(ConstantPropagationTest, MayMustCompare) {
  {
    auto code = assembler::ircode_from_string(R"( (
       (load-param v0)
       (load-param v1)

       (if-gtz v0 :if-gtz-label)
       ; here v0 is <= 0
       (if-ltz v1 :if-ltz-label)
       ; here v1 is >= 0

       (const v2 0)
       ; v0 < v1 may not be true since v0 == v1 is possible
       (if-lt v0 v1 :if-lt-label)
       (const v3 0)
       (:if-gtz-label)
       (const v4 0)
       (:if-ltz-label)
       (const v5 0)
       (:if-lt-label)
       (return-void)
      )
  )");
    auto expected = assembler::to_s_expr(code.get());
    do_const_prop(code.get());
    EXPECT_EQ(assembler::to_s_expr(code.get()), expected);
  }

  {
    auto code = assembler::ircode_from_string(R"( (
       (load-param v0)
       (load-param v1)

       (if-gtz v0 :if-gtz-label)
       ; here v0 is <= 0
       (if-ltz v1 :if-ltz-label)
       ; here v1 is >= 0

       (const v2 0)
       ; v1 > v0 may not be true since v0 == v1 is possible
       (if-gt v1 v0 :if-gt-label)
       (const v3 0)
       (:if-gtz-label)
       (const v4 0)
       (:if-ltz-label)
       (const v5 0)
       (:if-gt-label)
       (return-void)
      )
  )");
    auto expected = assembler::to_s_expr(code.get());
    do_const_prop(code.get());
    EXPECT_EQ(assembler::to_s_expr(code.get()), expected);
  }
}

TEST_F(ConstantPropagationTest, FoldBitwiseAndLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (and-int/lit v0 v0 511)
      (and-int/lit v0 v0 255)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (const v0 511)
      (const v0 255)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseOrLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 257)
      (or-int/lit v0 v0 255)
      (or-int/lit v0 v0 1024)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 257)
      (const v0 511)
      (const v0 1535)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseXorLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (xor-int/lit v0 v0 512)
      (xor-int/lit v0 v0 255)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (const v0 511)
      (const v0 256)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseShiftLeftOverflowLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 -16776961)
      (shl-int/lit v0 v0 8)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 -16776961)
      (const v0 65280)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseShiftLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (shr-int/lit v0 v0 2)
      (shl-int/lit v0 v0 1)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (const v0 255)
      (const v0 510)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseOverShiftLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (shr-int/lit v0 v0 34)
      (shl-int/lit v0 v0 33)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1023)
      (const v0 255)
      (const v0 510)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldBitwiseArithAndLogicalRightShiftLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 -1024)
      (shr-int/lit v0 v0 2)
      (ushr-int/lit v0 v0 12)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 -1024)
      (const v0 -256)
      (const v0 1048575)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldDivIntLit) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 4096)
      (div-int/lit v0 512)
      (move-result-pseudo v1)
      (const v0 15)
      (div-int/lit v0 2)
      (move-result-pseudo v1)
      (div-int/lit v0 0)
      (move-result-pseudo v2)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 4096)
      (const v1 8)
      (const v0 15)
      (const v1 7)
      (div-int/lit v0 0)
      (move-result-pseudo v2)
      (return-void)
    )
  )"); // division by 0 should not be optimized out
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldDivLongMinValueByMinusOne) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 -9223372036854775808)
      (const-wide v2 -1)
      (div-long v0 v2)
      (move-result-pseudo-wide v4)
      (return-wide v4)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 -9223372036854775808)
      (const-wide v2 -1)
      (const-wide v4 -9223372036854775808)
      (return-wide v4)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldRemLongMinValueByMinusOne) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 -9223372036854775808)
      (const-wide v2 -1)
      (rem-long v0 v2)
      (move-result-pseudo-wide v4)
      (return-wide v4)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 -9223372036854775808)
      (const-wide v2 -1)
      (const-wide v4 0)
      (return-wide v4)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, FoldDivRemIntMinValueByMinusOne) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 -2147483648)
      (const v1 -1)
      (div-int v0 v1)
      (move-result-pseudo v2)
      (rem-int v0 v1)
      (move-result-pseudo v3)
      (div-int/lit v0 -1)
      (move-result-pseudo v4)
      (rem-int/lit v0 -1)
      (move-result-pseudo v5)
      (return-void)
    )
  )");
  do_const_prop(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 -2147483648)
      (const v1 -1)
      (const v2 -2147483648)
      (const v3 0)
      (const v4 -2147483648)
      (const v5 0)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, NeAtBoundaryOfNez) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0) ; some unknown value

     (const v1 -1)
     (const v2 1)
     (if-lt v0 v1 :exit)
     (if-gt v0 v2 :exit)
     (if-eqz v0 :exit)
     ; we now know that v0 is either -1 or +1, but not 0

     (if-eq v0 v1 :exit)
     ; we now know that v0 is +1

     (if-nez v0 :exit) ; must happen

     (const v0 42) ; infeasible

     (:exit)
     (return v0)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (const v1 -1)
     (const v2 1)
     (if-lt v0 v1 :exit)
     (if-gt v0 v2 :exit)
     (if-eqz v0 :exit)
     (if-eq v0 v1 :exit)

     (:exit)
     (return v0)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, DeterminableLow6BitsJoinedFromConstants) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :if-true-label)
     (const v1 1)
     (goto :end-if)
     (:if-true-label)
     (const v1 14)
     (:end-if)
     ;; Joining the two branches, the lowest 4 bits of v1 don't equal, but bitset can't infer
     (const v2 2)
     (if-ne v1 v2 :end)
     (const v0 10)
     (:end)
     (return-void)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :end-if)
     (const v1 1)
     (:if-true-label)
     (const v2 2)
     (return-void)
     (:end-if)
     (const v1 14)
     (goto :if-true-label)
    )
)");

  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, UndeterminableLow6BitsJoinedFromConstants) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :if-true-label)
     (const v1 64)
     (goto :end-if)
     (:if-true-label)
     (const v1 191)
     (:end-if)
     ; Joining the two branches, the lowest 6 bits of v1 can't be inferred to be
     ; unequal to 128. Nor could it be inferered via bitset or bounds.
     (const v2 128)
     (if-ne v1 v2 :end)
     (const v0 10)
     (:end)
     (return-void)
    )
)");
  do_const_prop(code.get());

  EXPECT_THAT(assembler::to_string(code.get()),
              // if branch is not optimized out.
              ::testing::ContainsRegex(
                  "\\(if-ne v1 v2 :.*\\)[[:space:]]*\\(const v0 10\\)"));
}
