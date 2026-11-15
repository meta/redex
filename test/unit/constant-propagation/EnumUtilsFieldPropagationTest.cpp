/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConstantPropagationTestUtil.h"
#include "Creators.h"
#include "IRAssembler.h"

using AnalyzerUnderTest =
    InstructionAnalyzerCombiner<cp::EnumUtilsFieldAnalyzer,
                                cp::ImmutableAttributeAnalyzer,
                                cp::PrimitiveAnalyzer>;

struct EnumUtilsFieldTest : public ConstantPropagationTest {
 public:
  EnumUtilsFieldTest() {
    m_config.replace_move_result_with_consts = true;
    auto* integer_valueOf = method::java_lang_Integer_valueOf();
    auto* integer_intValue = method::java_lang_Integer_intValue();
    // The intValue of integer is initialized through the static invocation.
    m_immut_analyzer_state.add_initializer(integer_valueOf, integer_intValue)
        .set_src_id_of_attr(0)
        .set_obj_to_dest();
    m_immut_analyzer_state.add_cached_boxed_objects(integer_valueOf, -128, 128);
    m_analyzer = AnalyzerUnderTest(&m_immut_analyzer_state,
                                   &m_immut_analyzer_state, nullptr);
  }

  static DexClass* create_enum_utils_field() {
    auto* cls_ty = DexType::make_type("Lredex/$EnumUtils;");
    ClassCreator creator(cls_ty);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_FINAL);

    auto* f42 = dynamic_cast<DexField*>(
        DexField::make_field("Lredex/$EnumUtils;.f42:Ljava/lang/Integer;"));
    f42->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    creator.add_field(f42);
    return creator.create();
  }

  cp::ImmutableAttributeAnalyzerState m_immut_analyzer_state;
  cp::Transform::Config m_config;
  AnalyzerUnderTest m_analyzer;
};

TEST_F(EnumUtilsFieldTest, Basic) {
  Scope scope{create_enum_utils_field()};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils;.f42:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
    )
)");

  do_const_prop(code.get(), m_analyzer, m_config);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils;.f42:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (const v0 42)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(EnumUtilsFieldTest, OtherFieldDoesNotCreateTheHolderType) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  auto* field = dynamic_cast<DexField*>(
      DexField::make_field("LFoo;.fooValue:Ljava/lang/Integer;"));
  field->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  creator.add_field(field);
  Scope scope{creator.create()};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.fooValue:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
    )
)");
  do_const_prop(code.get(), m_analyzer, m_config);

  // OptimizeEnumsPass names its holder after this type only if the type does
  // not exist yet.
  EXPECT_EQ(DexType::get_type("Lredex/$EnumUtils;"), nullptr);
}
