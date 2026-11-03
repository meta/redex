/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagationAnalysis.h"

#include <array>
#include <string_view>
#include <utility>

#include <gtest/gtest.h>

#include "ConstantPropagationTestUtil.h"
#include "Creators.h"
#include "IRAssembler.h"

struct StaticFieldTest : public ConstantPropagationTest {
 public:
  StaticFieldTest() {
    // Test 1 -- final field
    ClassCreator creator1(DexType::make_type("Lcom/facebook/R$bool;"));
    creator1.set_super(type::java_lang_Object());

    auto* boolean_should_log_I =
        DexField::make_field("Lcom/facebook/R$bool;.should_log:I")
            ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    boolean_should_log_I->get_static_value()->value(123);
    creator1.add_field(boolean_should_log_I);

    creator1.create();

    // Test 2 -- not final field
    ClassCreator creator2(DexType::make_type("Lcom/facebook/R$integer;"));
    creator2.set_super(type::java_lang_Object());

    auto* integer_loop_count =
        DexField::make_field("Lcom/facebook/R$integer;.loop_count:I")
            ->make_concrete(ACC_PUBLIC | ACC_STATIC);
    creator2.add_field(integer_loop_count);

    creator2.create();

    assembler::class_from_string(R"(
    (class (public final) "LAnother;"
      (field (public static) "LAnother;.a:J")
      (field (public static final) "LAnother;.b:J" "80000000")
    )
  )");
  }
};

using StaticFieldAnalyzer =
    InstructionAnalyzerCombiner<cp::StaticFinalFieldAnalyzer,
                                cp::HeapEscapeAnalyzer,
                                cp::PrimitiveAnalyzer>;

TEST_F(StaticFieldTest, ClinitCallsInvalidateStaticValues) {
  auto* cls = assembler::class_from_string(R"(
    (class (public) "LFoo;"
      (field (public static) "LFoo;.counter:I")
      (method (public constructor) "LFoo;.<init>:()V"
        ((load-param-object v0) (return-void)))
      (method (private) "LFoo;.update:()V"
        ((load-param-object v0) (return-void)))
      (method (public) "LFoo;.updateVirtual:()V"
        ((load-param-object v0) (return-void)))
      (method (public static) "LFoo;.updateStatic:()V"
        ((return-void)))
    )
  )");
  assembler::class_from_string(R"(
    (class (public) "LHelper;"
      (method (public static) "LHelper;.update:()V"
        ((const v0 1) (sput v0 "LFoo;.counter:I") (return-void)))
    )
  )");
  auto* field = cls->get_sfields().front();
  constexpr auto calls = std::to_array<std::pair<IROpcode, std::string_view>>({
      {OPCODE_INVOKE_DIRECT, "LFoo;.<init>:()V"},
      {OPCODE_INVOKE_DIRECT, "LFoo;.update:()V"},
      {OPCODE_INVOKE_VIRTUAL, "LFoo;.updateVirtual:()V"},
      {OPCODE_INVOKE_STATIC, "LFoo;.updateStatic:()V"},
      {OPCODE_INVOKE_STATIC, "LFoo;.unresolved:()V"},
      {OPCODE_INVOKE_STATIC, "LHelper;.update:()V"},
  });
  for (const auto& [opcode, name] : calls) {
    SCOPED_TRACE(name);
    IRInstruction insn(opcode);
    insn.set_method(DexMethod::make_method(name));
    ConstantEnvironment env;
    env.set(field, SignedConstantDomain(0));
    env.set(reg_t{0}, SignedConstantDomain(7));

    EXPECT_FALSE(cp::ClinitFieldAnalyzer::analyze_invoke(
        cp::ClinitFieldAnalyzerState(cls->get_type()), &insn, &env));

    EXPECT_TRUE(env.get(field).is_top());
    EXPECT_EQ(env.get(reg_t{0}).get<SignedConstantDomain>().get_constant(), 7);
  }
  for (auto opcode : {OPCODE_INVOKE_CUSTOM, OPCODE_INVOKE_POLYMORPHIC}) {
    SCOPED_TRACE(opcode);
    IRInstruction insn(opcode);
    ConstantEnvironment env;
    env.set(field, SignedConstantDomain(0));
    env.set(reg_t{0}, SignedConstantDomain(7));
    InstructionAnalyzerCombiner<cp::ClinitFieldAnalyzer> analyzer(
        cp::ClinitFieldAnalyzerState(cls->get_type()));

    analyzer(&insn, &env);

    EXPECT_TRUE(env.get(field).is_top());
    EXPECT_EQ(env.get(reg_t{0}).get<SignedConstantDomain>().get_constant(), 7);
  }
}

TEST_F(StaticFieldTest, ClinitCallsPreserveOnlyInitializerConfinedFields) {
  auto* cls = assembler::class_from_string(R"(
    (class (public) "LFoo;"
      (field (public static final) "LFoo;.fixed:I")
      (field (public static final) "LFoo;.changed:I")
      (field (public static volatile) "LFoo;.volatileValue:I")
      (field (public static) "LFoo;.kept:I")
      (field (public static) "LFoo;.unwritten:I")
      (method (public static constructor) "LFoo;.<clinit>:()V"
        ((const v0 7)
         (sput v0 "LFoo;.fixed:I")
         (sput v0 "LFoo;.changed:I")
         (sput v0 "LFoo;.volatileValue:I")
         (sput v0 "LFoo;.kept:I")
         (return-void)))
      (method (public constructor) "LFoo;.<init>:()V"
        ((load-param-object v0)
         (const v1 8)
         (sput v1 "LFoo;.changed:I")
         (return-void)))
    )
  )");
  auto* fixed = DexField::get_field("LFoo;.fixed:I")->as_def();
  auto* changed = DexField::get_field("LFoo;.changed:I")->as_def();
  auto* volatile_value = DexField::get_field("LFoo;.volatileValue:I")->as_def();
  auto* kept = DexField::get_field("LFoo;.kept:I")->as_def();
  auto* unwritten = DexField::get_field("LFoo;.unwritten:I")->as_def();
  kept->rstate.set_root();
  const auto fields = cp::get_clinit_only_written_fields({cls});
  EXPECT_NE(fields.count(fixed), 0);
  EXPECT_EQ(fields.count(changed), 0);
  EXPECT_EQ(fields.count(volatile_value), 0);
  EXPECT_EQ(fields.count(kept), 0);
  EXPECT_NE(fields.count(unwritten), 0);

  ConstantEnvironment env;
  for (auto* field : cls->get_sfields()) {
    env.set(field, SignedConstantDomain(7));
  }
  env.set(reg_t{0}, SignedConstantDomain(42));
  IRInstruction invoke(OPCODE_INVOKE_DIRECT);
  invoke.set_method(DexMethod::get_method("LFoo;.<init>:()V"));
  cp::ClinitFieldAnalyzerState state(cls->get_type(), &fields);

  EXPECT_FALSE(cp::ClinitFieldAnalyzer::analyze_invoke(state, &invoke, &env));

  EXPECT_EQ(env.get<SignedConstantDomain>(fixed).get_constant(), 7);
  EXPECT_TRUE(env.get(changed).is_top());
  EXPECT_TRUE(env.get(volatile_value).is_top());
  EXPECT_TRUE(env.get(kept).is_top());
  EXPECT_EQ(env.get<SignedConstantDomain>(unwritten).get_constant(), 7);
  EXPECT_EQ(env.get<SignedConstantDomain>(reg_t{0}).get_constant(), 42);
}

TEST_F(StaticFieldTest, ClinitOpaqueCallsPreserveStaticValues) {
  ClassCreator creator(DexType::make_type("LExternal;"));
  creator.set_super(type::java_lang_Object());
  creator.set_external();
  auto* method =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LExternal;.update:()V"));
  ASSERT_NE(method, nullptr);
  method->set_access(ACC_PUBLIC | ACC_STATIC);
  method->set_external();
  creator.add_method(method);
  creator.create();
  auto* field =
      type_class(DexType::get_type("LAnother;"))->get_sfields().front();
  for (const auto* name : {"LExternal;.update:()V", "LUnknown;.update:()V"}) {
    SCOPED_TRACE(name);
    IRInstruction insn(OPCODE_INVOKE_STATIC);
    insn.set_method(DexMethod::make_method(name));
    ConstantEnvironment env;
    env.set(field, SignedConstantDomain(7));

    EXPECT_FALSE(cp::ClinitFieldAnalyzer::analyze_invoke(
        cp::ClinitFieldAnalyzerState(field->get_class()), &insn, &env));

    EXPECT_EQ(env.get<SignedConstantDomain>(field).get_constant(), 7);
  }
  IRInstruction insn(OPCODE_INVOKE_CUSTOM);
  ConstantEnvironment env;
  env.set(field, SignedConstantDomain(7));

  EXPECT_FALSE(cp::ClinitFieldAnalyzer::analyze_invoke(
      cp::ClinitFieldAnalyzerState(), &insn, &env));

  EXPECT_EQ(env.get<SignedConstantDomain>(field).get_constant(), 7);
}

/*
 * This test should be optimized, and remove the if-statement, since we know
 * should log is much greater than 0, and as such the if-statement is not
 * necessary, and should_log is final!
 */
TEST_F(StaticFieldTest, FinalLessThan) {
  auto code = assembler::ircode_from_string(R"(
    (
     (sget "Lcom/facebook/R$bool;.should_log:I")
     (move-result-pseudo v0)
     (if-ltz v0 :if-true-label)
     (const v0 1)
     (return v0)
     (:if-true-label)
     (new-instance "Ljava/lang/RuntimeException;")
     (move-result-pseudo-object v0)
     (const-string "FinalLessThan")
     (move-result-pseudo-object v1)
     (invoke-direct (v0 v1) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
     (throw v0)
    )
)");

  do_const_prop(code.get(), StaticFieldAnalyzer());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 123)
     (const v0 1)
     (return v0)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

/*
 * This test should not be optimized, since loop_count is not final, and
 * therefore we cannot be sure that it is greater than 0.
 */
TEST_F(StaticFieldTest, NotFinalLessThan) {
  const auto* code_expression = R"(
  (
    (sget "Lcom/facebook/R$integer;.loop_count:I")
    (move-result-pseudo v0)
    (if-ltz v0 :if-true-label)
    (const v0 1)
    (return v0)
    (:if-true-label)
    (new-instance "Ljava/lang/RuntimeException;")
    (move-result-pseudo-object v0)
    (const-string "NotFinalLessThan")
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
    (throw v0)
  )
)";
  auto code = assembler::ircode_from_string(code_expression);
  auto expected_code = assembler::ircode_from_string(code_expression);

  do_const_prop(code.get(), StaticFieldAnalyzer());
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(StaticFieldTest, WideFinals) {
  auto code = assembler::ircode_from_string(R"(
    (
     (sget-wide "LAnother;.b:J")
     (move-result-pseudo-wide v0)
     (if-ltz v0 :if-true-label)
     (const v0 1)
     (return v0)
     (:if-true-label)
     (new-instance "Ljava/lang/RuntimeException;")
     (move-result-pseudo-object v0)
     (const-string "Oh no")
     (move-result-pseudo-object v1)
     (invoke-direct (v0 v1) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
     (throw v0)
    )
)");

  do_const_prop(code.get(), StaticFieldAnalyzer());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const-wide v0 2147483648)
     (const v0 1)
     (return v0)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}
