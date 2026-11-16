/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConstantPropagationTestUtil.h"
#include "Creators.h"
#include "EnumUtilsHolders.h"
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
    return create_holder("Lredex/$EnumUtils;", 42);
  }

  // A class with one static final Integer field, generated like
  // OptimizeEnumsPass's holders unless `generated` is false.
  static DexClass* create_class(const std::string& cls_name,
                                const std::string& field_name,
                                bool generated = true) {
    auto* cls_ty = DexType::make_type(cls_name);
    ClassCreator creator(cls_ty);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_FINAL);

    auto* field = dynamic_cast<DexField*>(DexField::make_field(
        cls_name + "." + field_name + ":Ljava/lang/Integer;"));
    field->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    creator.add_field(field);
    auto* cls = creator.create();
    if (generated) {
      cls->rstate.set_generated();
    }
    return cls;
  }

  static DexClass* create_holder(const std::string& cls_name,
                                 int value,
                                 bool generated = true) {
    return create_class(cls_name, enum_utils::field_name(value), generated);
  }

  // Constant propagation leaves a read of `field` in `cls` unchanged.
  void expect_not_folded(const std::string& cls, const std::string& field) {
    auto code = assembler::ircode_from_string(R"(
      (
        (sget-object ")" + cls + "." + field +
                                              R"(:Ljava/lang/Integer;")
        (move-result-pseudo-object v0)
        (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
        (move-result v0)
      )
    )");
    auto expected_code =
        assembler::ircode_from_string(assembler::to_string(code.get()));

    do_const_prop(code.get(), m_analyzer, m_config);

    EXPECT_CODE_EQ(code.get(), expected_code.get());
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

TEST_F(EnumUtilsFieldTest, ChunkHolder) {
  Scope scope{create_holder("Lredex/$EnumUtils$2;", 300)};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils$2;.f300:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
    )
)");

  do_const_prop(code.get(), m_analyzer, m_config);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils$2;.f300:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (const v0 300)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(EnumUtilsFieldTest, OtherClassIsNotAHolder) {
  Scope scope{create_holder("Lredex/$EnumUtilsX;", 42)};
  expect_not_folded("Lredex/$EnumUtilsX;", "f42");
}

TEST_F(EnumUtilsFieldTest, NamesHolderNameNeverProducesAreNotHolders) {
  Scope scope{create_holder("Lredex/$EnumUtils$0;", 5),
              create_holder("Lredex/$EnumUtils$01;", 5)};
  expect_not_folded("Lredex/$EnumUtils$0;", "f5");
  expect_not_folded("Lredex/$EnumUtils$01;", "f5");
}

TEST_F(EnumUtilsFieldTest, InputClassWithAHolderNameIsNotAHolder) {
  // javac names the first anonymous class in an input class redex.$EnumUtils
  // redex.$EnumUtils$1.
  Scope scope{create_holder("Lredex/$EnumUtils$1;", 5, /* generated */ false)};
  expect_not_folded("Lredex/$EnumUtils$1;", "f5");
}

TEST_F(EnumUtilsFieldTest, FieldThatIsNotANumberIsNotFolded) {
  Scope scope{create_class("Lredex/$EnumUtils$1;", "foo"),
              create_class("Lredex/$EnumUtils;", "f05")};
  expect_not_folded("Lredex/$EnumUtils$1;", "foo");
  expect_not_folded("Lredex/$EnumUtils;", "f05");
}

TEST_F(EnumUtilsFieldTest, CollisionFamilyHolder) {
  Scope scope{create_holder("Lredex/$EnumUtils;", 7, /* generated */ false),
              create_holder("Lredex/$EnumUtils$u$1;", 200)};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils$u$1;.f200:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
    )
)");

  do_const_prop(code.get(), m_analyzer, m_config);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "Lredex/$EnumUtils$u$1;.f200:Ljava/lang/Integer;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (const v0 200)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
  expect_not_folded("Lredex/$EnumUtils;", "f7");
}

TEST_F(EnumUtilsFieldTest, UnusedFamily) {
  EXPECT_EQ(enum_utils::unused_family(3), "Lredex/$EnumUtils");
  DexType::make_type("Lredex/$EnumUtils$2;");
  EXPECT_EQ(enum_utils::unused_family(2), "Lredex/$EnumUtils");
  EXPECT_EQ(enum_utils::unused_family(3), "Lredex/$EnumUtils$u");
  DexType::make_type("Lredex/$EnumUtils$u;");
  EXPECT_EQ(enum_utils::unused_family(1), "Lredex/$EnumUtils");
  EXPECT_EQ(enum_utils::unused_family(3), "Lredex/$EnumUtils$u$u");
  EXPECT_EQ(enum_utils::holder_name("Lredex/$EnumUtils$u", 0),
            "Lredex/$EnumUtils$u;");
  EXPECT_EQ(enum_utils::holder_name("Lredex/$EnumUtils$u", 3),
            "Lredex/$EnumUtils$u$3;");
}
