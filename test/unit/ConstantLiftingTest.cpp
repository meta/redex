/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConstantLifting.h"

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRTypeChecker.h"
#include "RedexTest.h"
#include "Show.h"

namespace {

// Creates a static method `sig` in a new class `cls_name` whose @MethodMeta
// annotation lists the constants `kinds`/`vals`, and builds its CFG.
DexMethod* make_meta_method(const char* cls_name,
                            const char* sig,
                            const char* kinds,
                            const char* vals,
                            const char* body) {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.create();
  ClassCreator creator(DexType::make_type(cls_name));
  creator.set_super(type::java_lang_Object());
  auto* cls = creator.create();

  auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(sig));
  always_assert(method != nullptr);
  auto anno = std::make_unique<DexAnnotation>(
      DexType::make_type("Lcom/facebook/redex/annotations/MethodMeta;"),
      DAV_BUILD);
  anno->add_element(
      "constantTypes",
      std::make_unique<DexEncodedValueString>(DexString::make_string(kinds)));
  anno->add_element(
      "constantValues",
      std::make_unique<DexEncodedValueString>(DexString::make_string(vals)));
  auto anno_set = std::make_unique<DexAnnotationSet>();
  anno_set->add_annotation(std::move(anno));
  always_assert(method->attach_annotation_set(std::move(anno_set)));
  method->make_concrete(ACC_PUBLIC | ACC_STATIC,
                        assembler::ircode_from_string(body),
                        false /* is_virtual */);
  cls->add_method(method);
  method->get_code()->build_cfg();
  return method;
}

std::string type_check(DexMethod* method) {
  IRTypeChecker checker(method);
  checker.run();
  return checker.good() ? "" : checker.what();
}

// The count of instructions in `method` with opcode `op`.
size_t count_opcode(DexMethod* method, IROpcode op) {
  size_t n = 0;
  for (auto& mie : cfg::InstructionIterable(method->get_code()->cfg())) {
    n += mie.insn->opcode() == op ? 1 : 0;
  }
  return n;
}

size_t lift(DexMethod* method) {
  ConstantLifting const_lift;
  const_lift.lift_constants_from({type_class(method->get_class())}, nullptr,
                                 {method}, 10);
  return const_lift.get_num_const_lifted_methods();
}

} // namespace

struct ConstantLiftingTest : public RedexTest {};

// The lifted int parameter replaces the `const` passed as an int, but not the
// `const-wide` with the same literal, which a narrow int cannot stand in for.
TEST_F(ConstantLiftingTest, intConstantDoesNotReplaceConstWide) {
  auto* method = make_meta_method("LC3;", "LC3;.m:()J", "I", "7", R"(
    (
     (const v0 7)
     (invoke-static (v0) "LC3;.use:(I)V")
     (const-wide v2 7)
     (return-wide v2)
    )
  )");
  ASSERT_EQ(lift(method), 1u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST), 0u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST_WIDE), 1u);
  EXPECT_EQ(type_check(method), "") << show(method->get_code()->cfg());
}

// A `const 0` returned as a String is null, not the int 0.
TEST_F(ConstantLiftingTest, intZeroDoesNotReplaceNull) {
  auto* method =
      make_meta_method("LC4;", "LC4;.m:()Ljava/lang/String;", "I", "0", R"(
    (
     (const v0 0)
     (return-object v0)
    )
  )");
  EXPECT_EQ(lift(method), 0u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST), 1u);
  EXPECT_EQ(type_check(method), "") << show(method->get_code()->cfg());
}

// A boolean argument accepts the constant 1, but the Android verifier rejects
// an int-typed register there, even one holding 1.
TEST_F(ConstantLiftingTest, intOneDoesNotReplaceBooleanArgument) {
  auto* method = make_meta_method("LC5;", "LC5;.m:()V", "I", "1", R"(
    (
     (const v0 1)
     (invoke-static (v0) "LC5;.use:(Z)V")
     (return-void)
    )
  )");
  EXPECT_EQ(lift(method), 0u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST), 1u);
}

// The same holds when the constant reaches the boolean argument through a
// move.
TEST_F(ConstantLiftingTest, intOneDoesNotReplaceBooleanArgumentBehindMove) {
  auto* method = make_meta_method("LC9;", "LC9;.m:()V", "I", "1", R"(
    (
     (const v0 1)
     (move v1 v0)
     (invoke-static (v1) "LC9;.use:(Z)V")
     (return-void)
    )
  )");
  EXPECT_EQ(lift(method), 0u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST), 1u);
}

// An unresolvable type constant does not stop the int constant 0 from
// replacing every `const 0` used as an int.
TEST_F(ConstantLiftingTest, intZeroReplacesEveryIntUseNextToInvalidType) {
  auto* method =
      make_meta_method("LC6;", "LC6;.m:()V", "TI", "LDoesNotExist;:0", R"(
    (
     (const v0 0)
     (invoke-static (v0) "LC6;.use:(I)V")
     (const v1 0)
     (invoke-static (v1) "LC6;.use:(I)V")
     (return-void)
    )
  )");
  ASSERT_EQ(lift(method), 1u);
  EXPECT_EQ(count_opcode(method, OPCODE_CONST), 0u)
      << show(method->get_code()->cfg());
  EXPECT_EQ(type_check(method), "") << show(method->get_code()->cfg());
}
