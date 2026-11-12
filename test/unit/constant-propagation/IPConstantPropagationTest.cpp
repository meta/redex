/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IPConstantPropagation.h"

#include <signal.h>
#include <tuple>

#include <boost/algorithm/string/replace.hpp>
#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "ConstantPropagationRuntimeAssert.h"
#include "Creators.h"
#include "DebugUtils.h"
#include "DefinitelyAssignedIFields.h"
#include "DexUtil.h"
#include "IPConstantPropagationAnalysis.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "RedexTest.h"
#include "Walkers.h"

using namespace constant_propagation;
using namespace constant_propagation::interprocedural;

struct InterproceduralConstantPropagationTest : public RedexTest {
 public:
  InterproceduralConstantPropagationTest() {
    // The tests need java.lang.Object to resolve to a DexClass to build a
    // proper scope.
    create_object_class();

    auto* object_ctor =
        static_cast<DexMethod*>(method::java_lang_Object_ctor());
    object_ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
    object_ctor->set_external();
    type_class(type::java_lang_Object())->add_method(object_ctor);
    type_class(type::java_lang_Object())->set_external();
  }

  static ApiLevelAnalyzerState make_api_level_analyzer_state(int32_t min_sdk) {
    // EnumFieldAnalyzer requires that this method exists
    method::java_lang_Enum_equals();
    DexField::make_field("Landroid/os/Build$VERSION;.SDK_INT:I");
    return ApiLevelAnalyzerState(min_sdk);
  }

  static constexpr int MIN_SDK = 42;
  const std::string package_name = "com.facebook.redextest";
  ImmutableAttributeAnalyzerState m_immut_analyzer_state;
  ApiLevelAnalyzerState m_api_level_analyzer_state{
      make_api_level_analyzer_state(MIN_SDK)};
  StringAnalyzerState m_string_analyzer_state{
      constant_propagation::StringAnalyzerState::make_default()};
  PackageNameState m_package_name_state{PackageNameState::make(package_name)};
  NullCheckMethods m_null_check_methods;
  ConfigFiles conf = ConfigFiles(Json::nullValue);
};

static DexStoresVector make_simple_stores(const Scope& scope) {
  auto store = DexStore("store");
  store.add_classes(scope);
  return DexStoresVector({store});
}

class ConstructorReceiverJoinTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<std::tuple<bool, bool>> {};

TEST_P(ConstructorReceiverJoinTest, onlyDefiniteThisStoresInitializeField) {
  const auto [final_field, other_receiver] = GetParam();
  ClassCreator creator(DexType::make_type("LFoo;"));
  creator.set_super(type::java_lang_Object());
  auto* field =
      DexField::make_field("LFoo;.f:I")
          ->make_concrete(final_field ? ACC_PUBLIC | ACC_FINAL : ACC_PUBLIC);
  creator.add_field(field);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (const v1 7)
        (iput v1 v0 "LFoo;.f:I")
        (return-void)
      )
    )
  )");
  ctor->rstate.set_root();
  creator.add_method(ctor);
  auto* joined_ctor = assembler::method_from_string(
      R"((method (public constructor) "LFoo;.<init>:(LFoo;Z)V"
        (
          (load-param-object v0)
          (load-param-object v1)
          (load-param v2)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
          (if-eqz v2 :other)
          (move-object v3 v0)
          (goto :join)
          (:other)
          (move-object v3 )" +
      std::string(other_receiver ? "v1" : "v0") + R"()
          (:join)
          (const v4 7)
          (iput v4 v3 "LFoo;.f:I")
          (return-void)
        )
      ))");
  joined_ctor->rstate.set_root();
  creator.add_method(joined_ctor);
  const std::string reader_body = R"((
    (load-param-object v0)
    (iget v0 "LFoo;.f:I")
    (move-result-pseudo v1)
    (return v1)
  ))";
  auto* reader = assembler::method_from_string(
      R"((method (public static) "LFoo;.read:(LFoo;)I" )" + reader_body + ")");
  reader->rstate.set_root();
  creator.add_method(reader);
  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });
  auto assigned =
      definitely_assigned_ifields::get_definitely_assigned_ifields(scope);
  EXPECT_EQ(assigned.count(field) != 0u, !other_receiver);

  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.use_multiple_callee_callgraph = true;
  PassImpl(config).run(make_simple_stores(scope), conf);
  auto expected =
      assembler::ircode_from_string(other_receiver ? reader_body : R"((
        (load-param-object v0)
        (const v1 7)
        (return v1)
      ))");
  reader->get_code()->clear_cfg();
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

INSTANTIATE_TEST_SUITE_P(
    ReceiverAliases,
    ConstructorReceiverJoinTest,
    ::testing::Combine(::testing::Bool(), ::testing::Bool()),
    [](const auto& info) {
      return std::string(std::get<0>(info.param) ? "generated_final_"
                                                 : "java_nonfinal_") +
             (std::get<1>(info.param) ? "this_or_other" : "both_this");
    });

TEST_F(InterproceduralConstantPropagationTest,
       constructorUpdatesStaticFieldInClinit) {
  ClassCreator creator(DexType::make_type("LFoo;"));
  creator.set_super(type::java_lang_Object());
  creator.add_field(DexField::make_field("LFoo;.sNextId:I")
                        ->make_concrete(ACC_PRIVATE | ACC_STATIC));
  creator.add_field(DexField::make_field("LFoo;.DEFAULT:LFoo;")
                        ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  creator.add_field(DexField::make_field("LFoo;.NUM_TYPES:I")
                        ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  auto* clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
      (
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LFoo;.<init>:()V")
        (sput-object v0 "LFoo;.DEFAULT:LFoo;")
        (sget "LFoo;.sNextId:I")
        (move-result-pseudo v1)
        (sput v1 "LFoo;.NUM_TYPES:I")
        (return-void)
      )
    )
  )");
  clinit->rstate.set_root();
  creator.add_method(clinit);
  creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (sget "LFoo;.sNextId:I")
        (move-result-pseudo v1)
        (add-int/lit v1 v1 1)
        (sput v1 "LFoo;.sNextId:I")
        (return-void)
      )
    )
  )"));
  auto* num_types = assembler::method_from_string(R"(
    (method (public static) "LFoo;.numTypes:()I"
      (
        (sget "LFoo;.NUM_TYPES:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");
  num_types->rstate.set_root();
  creator.add_method(num_types);
  Scope scope{creator.create()};
  const auto original_clinit = assembler::to_s_expr(clinit->get_code());
  const auto original_reader = assembler::to_s_expr(num_types->get_code());
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.include_virtuals = true;
  config.use_multiple_callee_callgraph = true;

  PassImpl(config).run(make_simple_stores(scope), conf);

  clinit->get_code()->clear_cfg();
  num_types->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(clinit->get_code()), original_clinit);
  EXPECT_EQ(assembler::to_s_expr(num_types->get_code()), original_reader);
}

TEST_F(InterproceduralConstantPropagationTest, constantArgument) {
  // Let bar() be the only method calling baz(I)V, passing it a constant
  // argument. baz() should be optimized for that constant argument.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 0)
      (invoke-direct (v0 v1) "LFoo;.baz:(I)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();
  auto* m2 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(I)V"
     (
      (load-param v0) ; the `this` argument
      (load-param v1)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  auto* cls = creator.create();
  scope.push_back(cls);
  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  auto expected_code2 = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (const v1 0)
     (return-void)
    )
  )");

  m2->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m2->get_code(), expected_code2.get());
}

TEST_F(InterproceduralConstantPropagationTest, constantArgumentClass) {
  // Let bar() be the only method calling baz(...)V, passing it a constant
  // argument. baz() should be optimized for that constant argument,
  // which happens to be a type.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const-class "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1) "LFoo;.baz:(Ljava/lang/Class;)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();
  auto* m2 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(Ljava/lang/Class;)V"
     (
      (load-param v0) ; the `this` argument
      (load-param-object v1)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  auto* cls = creator.create();
  scope.push_back(cls);
  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  auto expected_code2 = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param-object v1)
     (const-class "LFoo;")
     (move-result-pseudo-object v1)
     (const v0 0)
     (return-void)
    )
  )");
  m2->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m2->get_code(), expected_code2.get());
}

// The caller passes callee the constant "" (a String), but only on a path
// guarded by a check-cast to Item that always throws (a String is never an
// Item):
//   (const-string "")
//   (move-result-pseudo-object v1)
//   (check-cast v1 "LItem;")  ; always throws
//   (invoke-direct (v0 v1) "LFoo;.callee:(LItem;)V")  ; unreachable
//
// callee thus has no reachable call and must be left unchanged. If IPCP took
// v1 == "" as callee's argument, it would materialize that constant over
// callee's Item parameter, producing an ill-typed body:
//   (const-string "")
//   (move-result-pseudo-object v1)  ; v1 is now a String, not an Item
//   (iput-object v1 v0 "LFoo;.item:LItem;")  ; String into an Item field
// which the type checker rejects.
TEST_F(InterproceduralConstantPropagationTest,
       provablyFailingCheckCastNotFoldedIntoCallee) {
  Scope scope;
  auto* item_ty = DexType::make_type("LItem;");
  ClassCreator item_creator(item_ty);
  item_creator.set_super(type::java_lang_Object());
  scope.push_back(item_creator.create());

  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  auto* field =
      dynamic_cast<DexField*>(DexField::make_field("LFoo;.item:LItem;"));
  field->make_concrete(ACC_PUBLIC);
  creator.add_field(field);

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.caller:()V"
     (
      (load-param-object v0)
      (const-string "")
      (move-result-pseudo-object v1)
      (check-cast v1 "LItem;")
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1) "LFoo;.callee:(LItem;)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();

  const auto* callee_str = R"(
    (
     (load-param-object v0)
     (load-param-object v1)
     (iput-object v1 v0 "LFoo;.item:LItem;")
     (return-void)
    )
  )";
  auto* m2 = DexMethod::make_method("LFoo;.callee:(LItem;)V")
                 ->make_concrete(ACC_PRIVATE,
                                 assembler::ircode_from_string(callee_str),
                                 /* is_virtual */ false);
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  scope.push_back(creator.create());

  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  // Only callee is checked, not the caller: IPCP finds the caller's path dead
  // but leaves deleting it to DCE, which this unit test does not run.
  m2->get_code()->clear_cfg();
  auto expected_code = assembler::ircode_from_string(callee_str);
  EXPECT_CODE_EQ(m2->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, constantArgumentClassXStore) {
  // Let bar() be the only method calling baz(...)V, passing it a constant
  // argument. However, that argument is a type defined in a different storre
  // than baz, so the type reference should not be embedded into baz(). Still,
  // the knowledge that the type value is not zero will be used to optimize the
  // conditional branching in baz.

  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const-class "LBar;")
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1) "LFoo;.baz:(Ljava/lang/Class;)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();

  auto* m2 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(Ljava/lang/Class;)V"
     (
      (load-param v0) ; the `this` argument
      (load-param-object v1)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);
  m2->get_code()->build_cfg();

  auto* cls = creator.create();
  auto store1 = DexStore("classes");
  store1.add_classes({cls});

  auto* cls_ty2 = DexType::make_type("LBar;");
  ClassCreator creator2(cls_ty2);
  creator2.set_super(type::java_lang_Object());
  auto* cls2 = creator2.create();
  auto store2 = DexStore("other_store");
  store2.add_classes({cls2});
  DexStoresVector stores({store1, store2});
  InterproceduralConstantPropagationPass().run(stores, conf);

  auto expected_code2 = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param-object v1)
     (const v0 0)
     (return-void)
    )
  )");
  m2->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m2->get_code(), expected_code2.get());
}

TEST_F(InterproceduralConstantPropagationTest, constantTwoArgument) {
  // Let bar() be the only method calling baz(ILjava/lang/String;)V, passing it
  // a constant argument. baz() should be optimized for constant arguments.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 0)
      (const-string "hello")
      (move-result-pseudo-object v2)
      (invoke-direct (v0 v1 v2) "LFoo;.baz:(ILjava/lang/String;)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();
  auto* m2 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(ILjava/lang/String;)V"
     (
      (load-param v0) ; the `this` argument
      (load-param v1)
      (load-param-object v2)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  auto* cls = creator.create();
  scope.push_back(cls);
  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  auto expected_code2 = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (load-param-object v2)
     (const v1 0)
     (const-string "hello")
     (move-result-pseudo-object v2)
     (return-void)
    )
  )");

  m2->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m2->get_code()),
            assembler::to_s_expr(expected_code2.get()));
}

TEST_F(InterproceduralConstantPropagationTest, nonConstantArgument) {
  // Let there be two methods calling baz(I)V, passing it different arguments.
  // baz() cannot be optimized for a constant argument here.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.foo:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 0)
      (invoke-direct (v0 v1) "LFoo;.baz:(I)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();
  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 1)
      (invoke-direct (v0 v1) "LFoo;.baz:(I)V")
      (return-void)
     )
    )
  )");
  m2->rstate.set_root();
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  auto* m3 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(I)V"
     (
      (load-param v0) ; the `this` argument
      (load-param v1)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m3);
  m3->get_code()->build_cfg();
  auto* cls = creator.create();
  scope.push_back(cls);

  // m3's code should be unchanged since it cannot be optimized
  m3->get_code()->clear_cfg();
  auto expected = assembler::to_s_expr(m3->get_code());
  m3->get_code()->build_cfg();
  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);
  m3->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m3->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest, argumentsGreaterThanZero) {
  // Let baz(I)V always be called with arguments > 0. baz() should be
  // optimized for that scenario.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 1)
      (invoke-direct (v0 v1) "LFoo;.baz:(I)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();
  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar2:()V"
     (
      (load-param v0) ; the `this` argument
      (const v1 2)
      (invoke-direct (v0 v1) "LFoo;.baz:(I)V")
      (return-void)
     )
    )
  )");
  m2->rstate.set_root();
  creator.add_method(m2);
  m2->get_code()->build_cfg();
  auto* m3 = assembler::method_from_string(R"(
    (method (private) "LFoo;.baz:(I)V"
     (
      (load-param v0) ; the `this` argument
      (load-param v1)
      (if-gtz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m3);
  m3->get_code()->build_cfg();
  auto* cls = creator.create();
  scope.push_back(cls);
  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  auto expected_code3 = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (load-param v1)
     (return-void)
    )
  )");
  m3->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m3->get_code(), expected_code3.get());
}

// Body templates filled per case via {ACCESS}/{SIG}/{INVOKE}.
constexpr std::string_view kParamSummaryDerefTemplate = R"(
    (method ({ACCESS}) "LFoo;.deref:{SIG}"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
      (return-void)
     )
    )
  )";

constexpr std::string_view kParamSummaryCallerTemplate = R"(
    (method (public static) "LFoo;.caller:(LFoo;LFoo;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      ({INVOKE} (v0 v1) "LFoo;.deref:{SIG}")
      (if-eqz v1 :null)
      (const v2 1)
      (return-void)
      (:null)
      (const v2 0)
      (return-void)
     )
    )
  )";

constexpr std::string_view kParamSummaryExpectedTemplate = R"(
    (
     (load-param-object v0)
     (load-param-object v1)
     ({INVOKE} (v0 v1) "LFoo;.deref:{SIG}")
     (const v2 1)
     (return-void)
    )
  )";

struct ParamSummaryCase {
  std::string name;
  std::string callee_access;
  std::string callee_descriptor;
  std::string invoke;
};

class InterproceduralConstantPropagationParamSummaryTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<std::tuple<ParamSummaryCase, bool>> {
 protected:
  std::string fill(std::string_view tmpl) {
    const auto& test_case = std::get<0>(GetParam());
    std::string s(tmpl);
    boost::replace_all(s, "{ACCESS}", test_case.callee_access);
    boost::replace_all(s, "{SIG}", test_case.callee_descriptor);
    boost::replace_all(s, "{INVOKE}", test_case.invoke);
    return s;
  }
};

// A callee that dereferences its parameter records a non-null per-parameter
// exit-value summary, so on the call's no-throw edge the caller's redundant
// null check on that argument folds away.
TEST_P(InterproceduralConstantPropagationParamSummaryTest,
       propagateRedundantArgNullCheck) {
  const bool use_call_graph = std::get<1>(GetParam());

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* deref = assembler::method_from_string(fill(kParamSummaryDerefTemplate));
  creator.add_method(deref);
  deref->get_code()->build_cfg();

  auto* caller =
      assembler::method_from_string(fill(kParamSummaryCallerTemplate));
  caller->rstate.set_root();
  creator.add_method(caller);
  caller->get_code()->build_cfg();

  scope.push_back(creator.create());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = use_call_graph;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_caller =
      assembler::ircode_from_string(fill(kParamSummaryExpectedTemplate));
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_caller.get());
}

INSTANTIATE_TEST_SUITE_P(
    InterproceduralConstantPropagationParamSummaryTests,
    InterproceduralConstantPropagationParamSummaryTest,
    ::testing::Combine(::testing::Values(
                           // Extra unused leading param so the dereferenced arg
                           // is v1, as it is for the instance callees (whose v0
                           // is the implicit `this`).
                           ParamSummaryCase{"invoke_static", "private static",
                                            "(LFoo;LFoo;)V", "invoke-static"},
                           ParamSummaryCase{"invoke_direct", "private",
                                            "(LFoo;)V", "invoke-direct"},
                           ParamSummaryCase{"invoke_virtual_final",
                                            "public final", "(LFoo;)V",
                                            "invoke-virtual"}),
                       ::testing::Bool()),
    [](const auto& info) {
      return std::get<0>(info.param).name +
             (std::get<1>(info.param) ? "_with_call_graph" : "_no_call_graph");
    });

// invoke-super is statically dispatched, so it refines the caller's argument in
// either call-graph mode.
class InterproceduralConstantPropagationSuperSummaryTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<bool> {};

TEST_P(InterproceduralConstantPropagationSuperSummaryTest,
       propagateRedundantArgNullCheckViaSuper) {
  auto* base_ty = DexType::make_type("LBase;");
  ClassCreator base_creator(base_ty);
  base_creator.set_super(type::java_lang_Object());
  auto* deref = assembler::method_from_string(R"(
    (method (public) "LBase;.deref:(LBase;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
      (return-void)
     )
    )
  )");
  base_creator.add_method(deref);
  deref->get_code()->build_cfg();

  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(base_ty);
  auto* caller = assembler::method_from_string(R"(
    (method (public) "LFoo;.caller:(LBase;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-super (v0 v1) "LBase;.deref:(LBase;)V")
      (if-eqz v1 :null)
      (const v2 1)
      (return-void)
      (:null)
      (const v2 0)
      (return-void)
     )
    )
  )");
  caller->rstate.set_root();
  creator.add_method(caller);
  caller->get_code()->build_cfg();

  Scope scope;
  scope.push_back(base_creator.create());
  scope.push_back(creator.create());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = GetParam();
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_caller = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (load-param-object v1)
     (invoke-super (v0 v1) "LBase;.deref:(LBase;)V")
     (const v2 1)
     (return-void)
    )
  )");
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_caller.get());
}

INSTANTIATE_TEST_SUITE_P(InterproceduralConstantPropagationSuperSummaryTests,
                         InterproceduralConstantPropagationSuperSummaryTest,
                         ::testing::Bool(),
                         [](const auto& info) {
                           return info.param ? "with_call_graph"
                                             : "no_call_graph";
                         });

// Per-parameter exit-value summary for a PRIMITIVE (int) parameter: bound(x)
// throws when x is negative, so on the call's no-throw edge x is known to be
// >= 0 and the caller's redundant `if (x < 0)` is eliminated -- the primitive
// analog of propagateRedundantArgNullCheck's object non-null fact, exercised
// with and without the multiple-callee call graph.
class InterproceduralConstantPropagationPrimitiveBoundTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<bool> {};

TEST_P(InterproceduralConstantPropagationPrimitiveBoundTest,
       propagateRedundantPrimitiveBoundCheck) {
  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* bound = assembler::method_from_string(R"(
    (method (private static) "LFoo;.bound:(I)V"
     (
      (load-param v0)
      (if-ltz v0 :neg)
      (return-void)
      (:neg)
      (new-instance "Ljava/lang/IllegalArgumentException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/IllegalArgumentException;.<init>:()V")
      (throw v1)
     )
    )
  )");
  creator.add_method(bound);
  bound->get_code()->build_cfg();

  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LFoo;.caller:(I)V"
     (
      (load-param v0)
      (invoke-static (v0) "LFoo;.bound:(I)V")
      (if-ltz v0 :neg)
      (const v1 1)
      (return-void)
      (:neg)
      (const v1 0)
      (return-void)
     )
    )
  )");
  caller->rstate.set_root();
  creator.add_method(caller);
  caller->get_code()->build_cfg();

  scope.push_back(creator.create());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = GetParam();
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_caller = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (invoke-static (v0) "LFoo;.bound:(I)V")
     (const v1 1)
     (return-void)
    )
  )");
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_caller.get());
}

INSTANTIATE_TEST_SUITE_P(InterproceduralConstantPropagationPrimitiveBoundTests,
                         InterproceduralConstantPropagationPrimitiveBoundTest,
                         ::testing::Bool(),
                         [](const auto& info) {
                           return info.param ? "with_call_graph"
                                             : "no_call_graph";
                         });

// Soundness check for the param-non-null summary: a method that reassigns its
// param register inside the body must NOT contribute a "param non-null"
// fact, even if the register holds a non-null value at every normal exit.
// Otherwise the caller would falsely conclude its argument was non-null.
TEST_F(InterproceduralConstantPropagationTest,
       paramNonNullSummaryUnstableRegistersDoNotPropagateParam) {
  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  // Reassigns its param register: when the arg is null on entry, v0 is
  // overwritten with a non-null string, so v0 is non-null at every exit even
  // though the entry value (what the caller passed) may have been null.
  auto* normalize = assembler::method_from_string(R"(
    (method (private static) "LFoo;.unstableNormalize:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (if-nez v0 :ok)
      (const-string "x")
      (move-result-pseudo-object v0)
      (:ok)
      (return-void)
     )
    )
  )");
  creator.add_method(normalize);
  normalize->get_code()->build_cfg();

  const std::string caller_body = R"((
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.unstableNormalize:(Ljava/lang/Object;)V")
      (if-eqz v0 :null)
      (const v1 1)
      (return-void)
      (:null)
      (const v1 0)
      (return-void)
    ))";
  auto* caller = assembler::method_from_string(
      R"((method (public static) "LFoo;.caller:(Ljava/lang/Object;)V" )" +
      caller_body + ")");
  caller->rstate.set_root();
  creator.add_method(caller);
  caller->get_code()->build_cfg();

  auto* cls = creator.create();
  scope.push_back(cls);

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(caller_body);
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_code.get());
}

// Two-level transitive param-env propagation needs the second WPS iteration:
// deref(p) dereferences p ({0 -> NEZ}); wrapper(p) only forwards to deref(p),
// so it picks up {0 -> NEZ} only on the iteration after deref's summary exists.
// With one iteration the caller's `if-eqz p` survives (sanity that the second
// iteration is load-bearing); with two it is pruned.
struct TransitiveIterationCase {
  std::string name;
  size_t iterations;
  bool prunes_null_check;
};

class InterproceduralConstantPropagationTransitiveSummaryTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<TransitiveIterationCase> {};

TEST_P(InterproceduralConstantPropagationTransitiveSummaryTest,
       propagatesParamThroughWrapper) {
  const auto& test_case = GetParam();
  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* deref = assembler::method_from_string(R"(
    (method (private static) "LFoo;.deref:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "Ljava/lang/Object;.hashCode:()I")
      (return-void)
     )
    )
  )");
  creator.add_method(deref);
  deref->get_code()->build_cfg();

  auto* wrapper = assembler::method_from_string(R"(
    (method (private static) "LFoo;.wrapper:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.deref:(LFoo;)V")
      (return-void)
     )
    )
  )");
  creator.add_method(wrapper);
  wrapper->get_code()->build_cfg();

  const std::string caller_body = R"((
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.wrapper:(LFoo;)V")
      (if-eqz v0 :null)
      (const v1 1)
      (return-void)
      (:null)
      (const v1 0)
      (return-void)
    ))";
  auto* caller = assembler::method_from_string(
      R"((method (public static) "LFoo;.caller:(LFoo;)V" )" + caller_body +
      ")");
  caller->rstate.set_root();
  creator.add_method(caller);
  caller->get_code()->build_cfg();

  auto* cls = creator.create();
  scope.push_back(cls);

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = test_case.iterations;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  const std::string pruned_body = R"((
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.wrapper:(LFoo;)V")
      (const v1 1)
      (return-void)
    ))";
  auto expected_code = assembler::ircode_from_string(
      test_case.prunes_null_check ? pruned_body : caller_body);
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    InterproceduralConstantPropagationTransitiveSummaryTests,
    InterproceduralConstantPropagationTransitiveSummaryTest,
    ::testing::Values(
        TransitiveIterationCase{"sanity_one_iteration_keeps_null_check", 1,
                                false},
        TransitiveIterationCase{"two_iterations_prune_null_check", 2, true}),
    [](const auto& info) { return info.param.name; });

// An overridable (true-virtual) callee must NOT be refined in either call-graph
// mode: a subclass override need not enforce the param's precondition.
class InterproceduralConstantPropagationOverridableVirtualTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<bool> {};

TEST_P(InterproceduralConstantPropagationOverridableVirtualTest,
       paramOverridableVirtualNotRefined) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* cls_child_ty = DexType::make_type("LBoo;");
  ClassCreator child_creator(cls_child_ty);
  child_creator.set_super(cls_ty);

  auto* deref = assembler::method_from_string(R"(
    (method (public) "LFoo;.deref:(LFoo;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
      (return-void)
     )
    )
  )");
  creator.add_method(deref);

  const std::string caller_body = R"((
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v0 v1) "LFoo;.deref:(LFoo;)V")
      (if-eqz v1 :null)
      (const v2 1)
      (return-void)
      (:null)
      (const v2 0)
      (return-void)
    ))";
  auto* caller = assembler::method_from_string(
      R"((method (public static) "LFoo;.caller:(LFoo;LFoo;)V" )" + caller_body +
      ")");
  caller->rstate.set_root();
  creator.add_method(caller);

  // Override that does not dereference the param. Its presence makes
  // LFoo;.deref a true virtual.
  auto* child_deref = assembler::method_from_string(R"(
    (method (public) "LBoo;.deref:(LFoo;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (return-void)
     )
    )
  )");
  child_creator.add_method(child_deref);

  DexStore store("classes");
  store.add_classes({creator.create()});
  store.add_classes({child_creator.create()});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = GetParam();
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  // The caller's null check must survive in both call-graph modes.
  auto expected_code = assembler::ircode_from_string(caller_body);
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    InterproceduralConstantPropagationOverridableVirtualTests,
    InterproceduralConstantPropagationOverridableVirtualTest,
    ::testing::Bool(),
    [](const auto& info) {
      return info.param ? "with_call_graph" : "no_call_graph";
    });

// invoke-interface is refined only when the call graph resolves a monomorphic
// callsite -- it is not whitelisted otherwise, and a polymorphic join is top.
struct InterfaceSummaryCase {
  std::string name;
  bool monomorphic;
  bool use_call_graph;
  bool expects_refined;
};

class InterproceduralConstantPropagationInterfaceSummaryTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<InterfaceSummaryCase> {};

TEST_P(InterproceduralConstantPropagationInterfaceSummaryTest,
       refinesInterfaceArgOnlyWhenMonomorphicWithCallGraph) {
  const auto& test_case = GetParam();

  auto* iface_ty = DexType::make_type("LIface;");
  ClassCreator iface_creator(iface_ty);
  iface_creator.set_super(type::java_lang_Object());
  iface_creator.set_access(iface_creator.get_access() | ACC_INTERFACE |
                           ACC_ABSTRACT);
  auto* iface_deref =
      DexMethod::make_method("LIface;.deref:(Ljava/lang/Object;)V")
          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /*is_virtual=*/true);
  iface_creator.add_method(iface_deref);

  Scope scope;
  scope.push_back(iface_creator.create());

  // LImpl1;.deref dereferences the arg, recording {1 -> NEZ}.
  auto* impl1_ty = DexType::make_type("LImpl1;");
  ClassCreator impl1_creator(impl1_ty);
  impl1_creator.set_super(type::java_lang_Object());
  impl1_creator.add_interface(iface_ty);
  auto* impl1_deref = assembler::method_from_string(R"(
    (method (public) "LImpl1;.deref:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
      (return-void)
     )
    )
  )");
  impl1_creator.add_method(impl1_deref);
  impl1_deref->get_code()->build_cfg();
  scope.push_back(impl1_creator.create());

  // A second implementor whose deref leaves the arg untouched makes the
  // callsite polymorphic, so the joined summary for the arg is top.
  if (!test_case.monomorphic) {
    auto* impl2_ty = DexType::make_type("LImpl2;");
    ClassCreator impl2_creator(impl2_ty);
    impl2_creator.set_super(type::java_lang_Object());
    impl2_creator.add_interface(iface_ty);
    auto* impl2_deref = assembler::method_from_string(R"(
      (method (public) "LImpl2;.deref:(Ljava/lang/Object;)V"
       (
        (load-param-object v0)
        (load-param-object v1)
        (return-void)
       )
      )
    )");
    impl2_creator.add_method(impl2_deref);
    impl2_deref->get_code()->build_cfg();
    scope.push_back(impl2_creator.create());
  }

  auto* caller_ty = DexType::make_type("LCaller;");
  ClassCreator caller_creator(caller_ty);
  caller_creator.set_super(type::java_lang_Object());
  const std::string caller_body = R"((
      (load-param-object v0)
      (load-param-object v1)
      (invoke-interface (v0 v1) "LIface;.deref:(Ljava/lang/Object;)V")
      (if-eqz v1 :null)
      (const v2 1)
      (return-void)
      (:null)
      (const v2 0)
      (return-void)
    ))";
  auto* caller = assembler::method_from_string(
      R"((method (public static) "LCaller;.caller:(LIface;Ljava/lang/Object;)V" )" +
      caller_body + ")");
  caller->rstate.set_root();
  caller_creator.add_method(caller);
  caller->get_code()->build_cfg();
  scope.push_back(caller_creator.create());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = test_case.use_call_graph;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  const std::string pruned_body = R"((
      (load-param-object v0)
      (load-param-object v1)
      (invoke-interface (v0 v1) "LIface;.deref:(Ljava/lang/Object;)V")
      (const v2 1)
      (return-void)
    ))";
  auto expected_code = assembler::ircode_from_string(
      test_case.expects_refined ? pruned_body : caller_body);
  caller->get_code()->clear_cfg();
  EXPECT_CODE_EQ(caller->get_code(), expected_code.get());
}

INSTANTIATE_TEST_SUITE_P(
    InterproceduralConstantPropagationInterfaceSummaryTests,
    InterproceduralConstantPropagationInterfaceSummaryTest,
    ::testing::Values(
        InterfaceSummaryCase{"monomorphic_no_call_graph", true, false, false},
        InterfaceSummaryCase{"monomorphic_with_call_graph", true, true, true},
        InterfaceSummaryCase{"polymorphic_no_call_graph", false, false, false},
        InterfaceSummaryCase{"polymorphic_with_call_graph", false, true,
                             false}),
    [](const auto& info) { return info.param.name; });

// We had a bug where an invoke instruction inside an unreachable block of code
// would cause the whole IPCP domain to be set to bottom. This test checks that
// we handle it correctly.
TEST_F(InterproceduralConstantPropagationTest, unreachableInvoke) {
  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 0)
      (goto :skip)
      (invoke-static (v0) "LFoo;.qux:(I)V") ; this is unreachable
      (:skip)
      (invoke-static (v0) "LFoo;.baz:(I)V") ; this is reachable
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(I)V"
     (
      (load-param v0)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);

  auto* m3 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.qux:(I)V"
      (
       (load-param v0)
       (return-void)
      )
    )
  )");
  creator.add_method(m3);

  auto* cls = creator.create();
  scope.push_back(cls);

  auto cg = std::make_shared<call_graph::Graph>(call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope));
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  NullCheckMethods null_check_methods;
  FixpointIterator fp_iter(std::move(cg),
                           [&null_check_methods](const DexMethod* method,
                                                 const WholeProgramState&,
                                                 const ArgumentDomain& args) {
                             const auto& code = *method->get_code();
                             auto env = env_with_params(is_static(method),
                                                        &code, args);
                             return std::make_unique<IntraproceduralAnalysis>(
                                 &null_check_methods,
                                 /* wps accessor */ nullptr,
                                 code.cfg(),
                                 ConstantPrimitiveAnalyzer(),
                                 std::move(env));
                           });

  fp_iter.run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});

  // Check m2 is reachable, despite m3 being unreachable
  const auto& graph = fp_iter.get_call_graph();

  signal(SIGABRT, crash_backtrace_handler);

  // Cache in variables, work around certain GCC bug. Must make a copy, as
  // intermediate domain is temporary.
  const auto res =
      fp_iter.get_entry_state_at(graph.node(m2)).get(CURRENT_PARTITION_LABEL);
  const auto exp = ArgumentDomain({{0, SignedConstantDomain(0)}});
  EXPECT_EQ(res, exp);
  EXPECT_TRUE(fp_iter.get_entry_state_at(graph.node(m3)).is_bottom());
}

struct RuntimeAssertTest : public InterproceduralConstantPropagationTest {
  DexMethodRef* m_fail_handler;

  RuntimeAssertTest() {
    m_config.max_heap_analysis_iterations = 1;
    m_config.create_runtime_asserts = true;
    m_config.runtime_assert.param_assert_fail_handler = DexMethod::make_method(
        "Lcom/facebook/redex/"
        "ConstantPropagationAssertHandler;.paramValueError:(I)V");
    m_config.runtime_assert.field_assert_fail_handler = DexMethod::make_method(
        "Lcom/facebook/redex/"
        "ConstantPropagationAssertHandler;.fieldValueError:(Ljava/lang/"
        "String;)V");
    m_config.runtime_assert.return_value_assert_fail_handler =
        DexMethod::make_method(
            "Lcom/facebook/redex/"
            "ConstantPropagationAssertHandler;.returnValueError:(Ljava/lang/"
            "String;)V");
  }

  InterproceduralConstantPropagationPass::Config m_config;
};

TEST_F(RuntimeAssertTest, RuntimeAssertEquality) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(I)V"
     (
      (load-param v0)
      (return-void)
     )
    )
  )");

  ConstantEnvironment env{{0, SignedConstantDomain(5)}};
  RuntimeAssertTransform rat(m_config.runtime_assert);
  auto* code = method->get_code();
  code->build_cfg();
  intraprocedural::FixpointIterator intra_cp(code->cfg(),
                                             ConstantPrimitiveAnalyzer());
  intra_cp.run(env);
  rat.apply(intra_cp, WholeProgramState(), method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v2 5)
      (if-eq v0 v2 :assertion-true)
      (const v1 0)
      (invoke-static (v1) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.paramValueError:(I)V")
      (:assertion-true)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertSign) {
  using sign_domain::Interval;

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(II)V"
     (
      (load-param v0)
      (load-param v1)
      (return-void)
     )
    )
  )");

  ConstantEnvironment env{{0, SignedConstantDomain(Interval::GEZ)},
                          {1, SignedConstantDomain(Interval::LTZ)}};
  RuntimeAssertTransform rat(m_config.runtime_assert);
  auto* code = method->get_code();
  code->build_cfg();
  intraprocedural::FixpointIterator intra_cp(code->cfg(),
                                             ConstantPrimitiveAnalyzer());
  intra_cp.run(env);
  EXPECT_TRUE(method->get_code()->cfg_built());
  rat.apply(intra_cp, WholeProgramState(), method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (if-ltz v1 :assertion-true-1)
      (const v3 1)
      (invoke-static (v3) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.paramValueError:(I)V")
      (:assertion-true-1)
      (if-gez v0 :assertion-true-2)
      (const v2 0)
      (invoke-static (v2) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.paramValueError:(I)V")
      (:assertion-true-2)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertCheckIntOnly) {
  using sign_domain::Interval;

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(JI)V"
     (
       (load-param v0) ; long -- we don't handle this yet
       (load-param v1) ; int
       (return-void)
     )
    )
  )");

  ConstantEnvironment env{{0, SignedConstantDomain(Interval::GEZ)},
                          {1, SignedConstantDomain(Interval::LTZ)}};
  RuntimeAssertTransform rat(m_config.runtime_assert);
  auto* code = method->get_code();
  code->build_cfg();
  intraprocedural::FixpointIterator intra_cp(code->cfg(),
                                             ConstantPrimitiveAnalyzer());
  intra_cp.run(env);
  rat.apply(intra_cp, WholeProgramState(), method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (if-ltz v1 :assertion-true-1)
      (const v2 1)
      (invoke-static (v2) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.paramValueError:(I)V")
      (:assertion-true-1)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertCheckVirtualMethod) {
  using sign_domain::Interval;

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(I)V"
     (
      (load-param v0) ; `this` argument
      (load-param v1)
      (return-void)
     )
    )
  )");

  ConstantEnvironment env{{1, SignedConstantDomain(Interval::LTZ)}};
  RuntimeAssertTransform rat(m_config.runtime_assert);
  auto* code = method->get_code();
  code->build_cfg();
  intraprocedural::FixpointIterator intra_cp(code->cfg(),
                                             ConstantPrimitiveAnalyzer());
  intra_cp.run(env);
  rat.apply(intra_cp, WholeProgramState(), method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0) ; `this` argument
      (load-param v1)
      (if-ltz v1 :assertion-true-1)
      (const v2 0)
      (invoke-static (v2) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.paramValueError:(I)V")
      (:assertion-true-1)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertField) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  // We must create a field def and attach it to the DexClass instance (instead
  // of just creating an unattached field ref) so that when IPC calls
  // resolve_field() on Foo.qux, they will find it and treat it as a known field
  auto* field =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, true)));
  creator.add_field(field);

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (return-void)
     )
    )
  )");
  creator.add_method(method);
  method->get_code()->build_cfg();
  Scope scope{creator.create()};
  InterproceduralConstantPropagationPass(m_config).run(
      make_simple_stores(scope), conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (const v2 1)
      (if-eq v0 v2 :ok)

      (const-string "qux")
      (move-result-pseudo-object v1)
      (invoke-static (v1) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.fieldValueError:(Ljava/lang/String;)V")

      (:ok)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertConstantReturnValue) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (invoke-static () "LFoo;.constantReturnValue:()I")
      (move-result v0)
      (return-void)
     )
    )
  )");
  method->get_code()->build_cfg();
  creator.add_method(method);

  auto* constant_return_method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.constantReturnValue:()I"
     (
      (const v0 1)
      (return v0)
     )
    )
  )");
  creator.add_method(constant_return_method);
  constant_return_method->get_code()->build_cfg();

  Scope scope{creator.create()};
  InterproceduralConstantPropagationPass(m_config).run(
      make_simple_stores(scope), conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (invoke-static () "LFoo;.constantReturnValue:()I")
      (move-result v0)
      (const v2 1)
      (if-eq v0 v2 :ok)

      (const-string "constantReturnValue")
      (move-result-pseudo-object v1)
      (invoke-static (v1) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.returnValueError:(Ljava/lang/String;)V")

      (:ok)
      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertNeverReturnsVoid) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (invoke-static () "LFoo;.neverReturns:()V")
      (return-void)
     )
    )
  )");
  creator.add_method(method);
  method->get_code()->build_cfg();
  auto* never_returns = assembler::method_from_string(R"(
    (method (public static) "LFoo;.neverReturns:()V"
     (
       (:loop)
       (goto :loop)
     )
    )
  )");
  creator.add_method(never_returns);
  never_returns->get_code()->build_cfg();
  Scope scope{creator.create()};
  InterproceduralConstantPropagationPass(m_config).run(
      make_simple_stores(scope), conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (invoke-static () "LFoo;.neverReturns:()V")

      (const-string "neverReturns")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.returnValueError:(Ljava/lang/String;)V")

      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(RuntimeAssertTest, RuntimeAssertNeverReturnsConstant) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (invoke-static () "LFoo;.neverReturns:()I")
      (move-result v0)
      (return-void)
     )
    )
  )");
  creator.add_method(method);
  method->get_code()->build_cfg();
  auto* never_returns = assembler::method_from_string(R"(
    (method (public static) "LFoo;.neverReturns:()I"
     (
       (:loop)
       (goto :loop)
     )
    )
  )");
  creator.add_method(never_returns);
  never_returns->get_code()->build_cfg();
  Scope scope{creator.create()};
  InterproceduralConstantPropagationPass(m_config).run(
      make_simple_stores(scope), conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (invoke-static () "LFoo;.neverReturns:()I")
      (move-result v0)

      (const-string "neverReturns")
      (move-result-pseudo-object v1)
      (invoke-static (v1) "Lcom/facebook/redex/ConstantPropagationAssertHandler;.returnValueError:(Ljava/lang/String;)V")

      (return-void)
    )
  )");
  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, constantField) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, true)));
  creator.add_field(field);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 1)
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root(); // Make this an entry point
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (if-nez v0 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  m2->rstate.set_root(); // Make this an entry point
  creator.add_method(m2);
  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code2 = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (return-void)
    )
  )");

  m2->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m2->get_code(), expected_code2.get());
}

TEST_F(InterproceduralConstantPropagationTest, nonConstantField) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, true)));
  creator.add_field(field);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 0) ; this differs from the original encoded value of Foo.qux
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root(); // Make this an entry point
  creator.add_method(m1);
  auto* m2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (if-nez v0 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  m2->rstate.set_root(); // Make this an entry point
  creator.add_method(m2);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  m2->get_code()->clear_cfg();
  auto expected = assembler::to_s_expr(m2->get_code());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  m2->get_code()->build_cfg();
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m2->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m2->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest, nonConstantFieldDueToKeep) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, true)));
  creator.add_field(field);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 1)
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root(); // Make this an entry point
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (if-nez v0 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  m2->rstate.set_root(); // Make this an entry point
  creator.add_method(m2);

  // Mark Foo.qux as a -keep field -- meaning we cannot determine if its value
  // is truly constant just by looking at Dex bytecode
  dynamic_cast<DexField*>(DexField::get_field("LFoo;.qux:I"))
      ->rstate.set_root();
  auto expected = assembler::to_s_expr(m2->get_code());

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m2->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m2->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest, constantFieldAfterClinit) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_qux =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, true)));
  creator.add_field(field_qux);

  auto* field_corge = DexField::make_field("LFoo;.corge:I")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  creator.add_field(field_corge);

  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (sget "LFoo;.qux:I")     ; Foo.qux is the constant 0 outside this clinit,
      (move-result-pseudo v0)  ; but we should check that we don't overwrite
      (sput v0 "LFoo;.corge:I") ; its initial encoded value while transforming
                               ; the clinit. I.e. this sget should be converted
                               ; to "const v0 1", not "const v0 0".

      (const v0 0) ; this differs from the original encoded value of Foo.qux,
                   ; but will be the only field value visible to other methods
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
    )
  )");
  clinit->rstate.set_root(); // Make this an entry point
  creator.add_method(clinit);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0) ; this is always zero due to <clinit>
      (if-nez v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  EXPECT_EQ(wps.get_field_value(field_qux), SignedConstantDomain(0));
  EXPECT_EQ(wps.get_field_value(field_corge), SignedConstantDomain(1));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_clinit_code = assembler::ircode_from_string(R"(
     (
      (const v0 1)
      (sput v0 "LFoo;.corge:I") ; these field writes will be removed by RMUF
      (const v0 0)
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
  )");
  clinit->get_code()->clear_cfg();
  EXPECT_CODE_EQ(clinit->get_code(), expected_clinit_code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (const v0 1)
     (return-void)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       nonConstantFieldDueToInvokeInClinit) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  auto* field_qux =
      DexField::make_field("LFoo;.qux:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_INT, false)));
  creator.add_field(field_qux);

  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (invoke-static () "LFoo;.initQux:()V")
      (return-void)
     )
    )
  )");
  clinit->rstate.set_root(); // Make this an entry point
  creator.add_method(clinit);

  auto* init_qux = assembler::method_from_string(R"(
    (method (public static) "LFoo;.initQux:()V"
     (
      (const v0 1) ; this differs from the original encoded value of Foo.qux
      (sput v0 "LFoo;.qux:I")
      (return-void)
     )
    )
  )");
  creator.add_method(init_qux);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:()V"
     (
      (sget "LFoo;.qux:I")
      (move-result-pseudo v0)
      (if-nez v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  // We expect Foo.baz() to be unchanged since Foo.qux is not a constant
  auto expected = assembler::to_s_expr(m->get_code());

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  EXPECT_EQ(wps.get_field_value(field_qux), ConstantValue::top());

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest, constantReturnValue) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (invoke-static () "LFoo;.constantReturnValue:()I")
      (move-result v0)
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.constantReturnValue:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  creator.add_method(m2);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (invoke-static () "LFoo;.constantReturnValue:()I")
     (move-result v0)
     (return-void)
    )
  )");
  m1->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m1->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, VirtualMethodReturnValue) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  creator.set_access(creator.get_access() | ACC_NATIVE);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
      (move-result v0) ; Constant value since this virtualMethod is not overridden
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LFoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  creator.add_method(m2);
  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
     (move-result v0)
     (return-void)
    )
  )");

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m1->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m1->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, RootVirtualMethodReturnValue) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  creator.set_access(creator.get_access() | ACC_NATIVE);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
      (move-result v0) ; Not propagating value because virtualMethod is root
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LFoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  m2->rstate.set_root();
  creator.add_method(m2);
  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
     (move-result v0)
     (if-eqz v0 :label)
     (const v0 1)
     (:label)
     (return-void)
    )
  )");

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m1->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m1->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, NativeImplementReturnValue) {
  auto* cls1_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls1_ty);
  creator.set_super(type::java_lang_Object());
  creator.set_access(creator.get_access() | ACC_NATIVE);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
      (move-result v0) ; Not propagating value because virtualMethod is root
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  auto* cls1 = creator.create();
  auto* void_int =
      DexProto::make_proto(type::_int(), DexTypeList::make_type_list({}));
  auto* method_base = dynamic_cast<DexMethod*>(DexMethod::make_method(
      cls1_ty, DexString::make_string("virtualMethod"), void_int));
  method_base->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                             std::unique_ptr<IRCode>(nullptr), true);
  cls1->add_method(method_base);

  auto* cls2_ty = DexType::make_type("LBoo;");
  ClassCreator creator2(cls2_ty);
  creator2.set_super(cls1_ty);
  creator2.set_access(creator2.get_access() | ACC_NATIVE);
  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LBoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  creator2.add_method(m2);
  auto* cls2 = creator2.create();

  auto* cls3_ty = DexType::make_type("LBar;");
  ClassCreator creator3(cls3_ty);
  creator3.set_super(cls1_ty);
  creator3.set_access(creator3.get_access() | ACC_NATIVE);
  DexMethodRef* m3_ref = DexMethod::make_method("LBar;.virtualMethod:()I");
  auto* m3 = m3_ref->make_concrete(ACC_PUBLIC | ACC_NATIVE, true);
  creator3.add_method(m3);
  auto* cls3 = creator3.create();

  Scope scope{cls1, cls2, cls3};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
     (move-result v0)
     (if-eqz v0 :label)
     (const v0 1)
     (:label)
     (return-void)
    )
  )");

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = true;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m1->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m1->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       NativeInterfaceImplementReturnValue) {
  auto* cls1_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls1_ty);
  creator.set_super(type::java_lang_Object());
  creator.set_access(creator.get_access() | ACC_NATIVE | ACC_INTERFACE);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
      (move-result v0) ; Not propagating value because virtualMethod is root
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  auto* cls1 = creator.create();
  auto* void_int =
      DexProto::make_proto(type::_int(), DexTypeList::make_type_list({}));
  auto* method_base = dynamic_cast<DexMethod*>(DexMethod::make_method(
      cls1_ty, DexString::make_string("virtualMethod"), void_int));
  method_base->make_concrete(ACC_PUBLIC | ACC_INTERFACE,
                             std::unique_ptr<IRCode>(nullptr), true);
  cls1->add_method(method_base);

  auto* cls2_ty = DexType::make_type("LBoo;");
  ClassCreator creator2(cls2_ty);
  creator2.set_super(type::java_lang_Object());
  creator2.add_interface(cls1_ty);
  creator2.set_access(creator2.get_access() | ACC_NATIVE);
  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LBoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  creator2.add_method(m2);
  auto* cls2 = creator2.create();

  auto* cls3_ty = DexType::make_type("LBar;");
  ClassCreator creator3(cls3_ty);
  creator3.set_super(type::java_lang_Object());
  creator3.add_interface(cls1_ty);
  creator3.set_access(creator3.get_access() | ACC_NATIVE);
  DexMethodRef* m3_ref = DexMethod::make_method("LBar;.virtualMethod:()I");
  auto* m3 = m3_ref->make_concrete(ACC_PUBLIC | ACC_NATIVE, true);
  creator3.add_method(m3);
  auto* cls3 = creator3.create();

  Scope scope{cls1, cls2, cls3};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
     (move-result v0)
     (if-eqz v0 :label)
     (const v0 1)
     (:label)
     (return-void)
    )
  )");

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = true;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m1->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m1->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       OverrideVirtualMethodReturnValue) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());
  creator.set_access(creator.get_access() | ACC_NATIVE);

  auto* cls_child_ty = DexType::make_type("LBoo;");
  ClassCreator child_creator(cls_child_ty);
  child_creator.set_super(cls_ty);
  child_creator.set_access(child_creator.get_access() | ACC_NATIVE);

  auto* m1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(LFoo;)V"
     (
      (load-param-object v0)
      (invoke-virtual (v0) "LFoo;.virtualMethod:()I")
      (move-result v0) ; not a constant value since virtualMethod can be overridden
      (if-eqz v0 :label)
      (const v0 1)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m1);

  auto* m2 = assembler::method_from_string(R"(
    (method (public) "LFoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  creator.add_method(m2);

  auto* child_m3 = assembler::method_from_string(R"(
    (method (public) "LBoo;.virtualMethod:()I"
     (
      (const v0 0)
      (return v0)
     )
    )
  )");
  child_creator.add_method(child_m3);
  DexStore store("classes");
  store.add_classes({creator.create()});
  store.add_classes({child_creator.create()});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  m1->get_code()->clear_cfg();
  auto expected = assembler::to_s_expr(m1->get_code());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  m1->get_code()->build_cfg();
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
  m1->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m1->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest, neverReturns) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(I)V"
     (
      (load-param v0)
      (if-eqz v0 :if-true-1)

      (invoke-static () "LFoo;.neverReturns:()V")
      (const v1 0) ; this never executes

      (:if-true-1)
      (const v1 1) ; this is the only instruction assigning to v1

      (const v2 1)
      (if-eq v1 v2 :if-true-2) ; this should always be true
      (const v3 2)
      (:if-true-2)
      (return-void)
     )
    )
  )");
  creator.add_method(method);
  method->rstate.set_root(); // Make this an entry point

  auto* never_returns = assembler::method_from_string(R"(
    (method (public static) "LFoo;.neverReturns:()V"
     (
       (:loop)
       (goto :loop)
     )
    )
  )");
  creator.add_method(never_returns);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :if-true-1)

     (invoke-static () "LFoo;.neverReturns:()V")
     (const v1 0)

     (:if-true-1)
     (const v1 1)

     (const v2 1)
     (return-void)
    )
  )");

  method->get_code()->clear_cfg();
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, whiteBoxReturnValues) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* returns_void = assembler::method_from_string(R"(
    (method (public static) "LFoo;.returnsVoid:()V"
     (
      (return-void)
     )
    )
  )");
  creator.add_method(returns_void);

  auto* never_returns = assembler::method_from_string(R"(
    (method (public static) "LFoo;.neverReturns:()V"
     (
       (:loop)
       (goto :loop)
     )
    )
  )");
  creator.add_method(never_returns);

  auto* returns_constant = assembler::method_from_string(R"(
    (method (public static) "LFoo;.returnsConstant:()I"
     (
      (const v0 1)
      (return v0)
     )
    )
  )");
  creator.add_method(returns_constant);

  auto* no_code =
      DexMethod::make_method("LFoo;.no_code:()V")
          ->make_concrete(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE, true);
  creator.add_method(no_code);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();

  // Make sure we mark methods that have a reachable return-void statement as
  // "returning" Top.
  // And for a method that has no implementation in dex we also want its
  // return value be Top but not Bottom.
  EXPECT_EQ(wps.get_return_value(returns_void), SignedConstantDomain::top());
  EXPECT_EQ(wps.get_return_value(no_code), SignedConstantDomain::top());
  EXPECT_EQ(wps.get_return_value(never_returns),
            SignedConstantDomain::bottom());
  EXPECT_EQ(wps.get_return_value(returns_constant), SignedConstantDomain(1));
}

TEST_F(InterproceduralConstantPropagationTest, min_sdk) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* returns_min_sdk = assembler::method_from_string(R"(
    (method (public static) "LFoo;.returnsConstant:()I"
     (
      (sget "Landroid/os/Build$VERSION;.SDK_INT:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  creator.add_method(returns_min_sdk);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();

  // Make sure we mark methods that have a reachable return-void statement as
  // "returning" Top.
  // And for a method that has no implementation in dex we also want its
  // return value be Top but not Bottom.
  EXPECT_EQ(wps.get_return_value(returns_min_sdk),
            SignedConstantDomain(MIN_SDK, std::numeric_limits<int32_t>::max()));
}

TEST_F(InterproceduralConstantPropagationTest, ghost_edges) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* does_not_return = assembler::method_from_string(R"(
    (method (public static) "LFoo;.doesNotTerminate:()I"
     (
      (load-param v0)
      (if-eqz v0 :loop2)

      (:loop1)
      (const v0 0)
      (if-eqz v0 :loop1)
      (goto :loop1)

      (:loop2)
      (const v0 0)
      (if-eqz v0 :loop2)
      (goto :loop2)
     )
    )
  )");
  creator.add_method(does_not_return);

  Scope scope{creator.create()};

  // Check that cfg will indeed have ghost edges...
  auto* code = does_not_return->get_code();
  code->build_cfg();
  code->cfg().calculate_exit_block();
  auto* exit_block = does_not_return->get_code()->cfg().exit_block();
  EXPECT_NE(exit_block, nullptr);
  EXPECT_EQ(exit_block->preds().size(), 2);
  EXPECT_EQ(exit_block->preds().front()->type(), cfg::EDGE_GHOST);

  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :loop2)

      (:loop1)
      (const v0 0)
      (goto :loop1)

      (:loop2)
      (const v0 0)
      (goto :loop2)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       nezConstantFieldAfterInit_simple) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // as the field is definitely-assigned, 0 was not added to the numeric
  // interval domain
  EXPECT_EQ(wps.get_field_value(field_f), SignedConstantDomain(42));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v0 42)
      (return v0)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       nezConstantFieldAfterInit_transient_field_not_inferred) {
  // Like nezConstantFieldAfterInit_simple, but the field is transient, so it
  // may be null/0 after deserialization and IPCP must not infer its value.
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_f = DexField::make_field("LFoo;.f:I")
                      ->make_concrete(ACC_PUBLIC | ACC_TRANSIENT);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};

  // Capture baz's IR to assert IPCP leaves it unchanged (it reads the field).
  auto expected = assembler::to_s_expr(m->get_code());

  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  EXPECT_TRUE(wps.get_field_value(field_f).is_top());

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  m->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(m->get_code()), expected);
}

TEST_F(InterproceduralConstantPropagationTest,
       nezConstantFieldAfterInit_branching) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(Z)V"
     (
      (load-param-object v0)
      (load-param v2)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (if-eqz v2 :second)
      (const v1 42) ; feasible
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
      (:second)
      (const v1 23) ; feasible
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (const v1 300)
      (if-gtz v0 :skip)
      (const v1 400)
      (:skip)
      (return v1)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // as the field is definitely-assigned, even with the branching in the
  // constructor, 0 was not added to the numeric interval domain
  EXPECT_EQ(wps.get_field_value(field_f),
            SignedConstantDomain::from_constants({23, 42}));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (const v1 300)
      (return v1)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       constantFieldAfterInit_this_escaped) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (sput-object v0 "LFoo;.some_global_field:LFoo;") ; 'this' escapes here
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // 0 is included in the numeric interval as 'this' escaped before the
  // assignment
  EXPECT_EQ(wps.get_field_value(field_f),
            SignedConstantDomain::from_constants({0, 42}));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       constantFieldAfterInit_nontrivial_external_base_ctor) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Throwable());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Throwable;.<init>:()V") ; 'this' escapes here
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // 0 is included in the numeric interval as 'this' escaped before the
  // assignment
  EXPECT_EQ(wps.get_field_value(field_f),
            SignedConstantDomain::from_constants({0, 42}));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       constantFieldAfterInit_relaxed_init) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Throwable());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // 0 is included in the numeric interval as no actual constructor was ever
  // called
  EXPECT_EQ(wps.get_field_value(field_f),
            SignedConstantDomain::from_constants({0, 42}));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
    )
  )");
  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest,
       constantFieldAfterInit_read_before_write) {
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  auto* field_f = DexField::make_field("LFoo;.f:I")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_f);

  auto* init = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget v0 "LFoo;.f:I") ; read before...
      (move-result-pseudo v1)
      (const v1 42)
      (iput v1 v0 "LFoo;.f:I") ; ...write
      (return-void)
     )
    )
  )");
  init->rstate.set_root(); // Make this an entry point
  creator.add_method(init);

  auto* m = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m->rstate.set_root(); // Make this an entry point
  creator.add_method(m);

  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 2;

  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  const auto& wps = fp_iter->get_whole_program_state();
  // 0 is included in the numeric interval as the field was read before written
  EXPECT_EQ(wps.get_field_value(field_f),
            SignedConstantDomain::from_constants({0, 42}));

  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v0)
      (return v0)
    )
  )");

  m->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m->get_code(), expected_code.get());
}

TEST_F(InterproceduralConstantPropagationTest, rConstStaticFieldPropagation) {
  // Verify that IPCP propagates resource ID constants (IOPCODE_R_CONST) through
  // static fields. A <clinit> stores a resource ID via r-const + sput, and a
  // caller reads it via sget. After IPCP, the sget should be replaced with
  // r-const.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  // Create a static field with an initial zero value.
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.bar:I"));
  field->make_concrete(ACC_PUBLIC | ACC_STATIC,
                       DexEncodedValue::zero_for_type(field->get_type()));
  creator.add_field(field);

  // <clinit> stores a resource ID constant into the static field.
  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (r-const v0 2131230721)
      (sput v0 "LFoo;.bar:I")
      (return-void)
     )
    )
  )");
  creator.add_method(clinit);
  clinit->get_code()->build_cfg();

  // A caller in a different class reads the field via sget.
  auto* cls2_ty = DexType::make_type("LBar;");
  ClassCreator creator2(cls2_ty);
  creator2.set_super(type::java_lang_Object());

  auto* getter = assembler::method_from_string(R"(
    (method (public static) "LBar;.getBar:()I"
     (
      (sget "LFoo;.bar:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  getter->rstate.set_root();
  creator2.add_method(getter);
  getter->get_code()->build_cfg();

  scope.push_back(creator.create());
  scope.push_back(creator2.create());

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);

  // The sget should be replaced with r-const carrying the resource ID.
  auto expected_code2 = assembler::ircode_from_string(R"(
    (
      (r-const v0 2131230721)
      (return v0)
    )
  )");
  getter->get_code()->clear_cfg();
  EXPECT_CODE_EQ(getter->get_code(), expected_code2.get());
}

TEST_F(InterproceduralConstantPropagationTest, rConstArgumentPropagation) {
  // Verify that IPCP propagates resource ID constants (IOPCODE_R_CONST) through
  // method arguments. A caller passes a resource ID loaded via r-const to a
  // callee. IPCP should propagate the value into the callee, allowing branch
  // folding.

  Scope scope;
  auto* cls_ty = DexType::make_type("LFoo;");
  ClassCreator creator(cls_ty);
  creator.set_super(type::java_lang_Object());

  // Caller passes a resource ID constant to the callee.
  auto* m1 = assembler::method_from_string(R"(
    (method (public) "LFoo;.caller:()V"
     (
      (load-param v0)
      (r-const v1 2131230721)
      (invoke-direct (v0 v1) "LFoo;.callee:(I)V")
      (return-void)
     )
    )
  )");
  m1->rstate.set_root();
  creator.add_method(m1);
  m1->get_code()->build_cfg();

  // Callee uses the parameter in a conditional. Since the resource ID is
  // non-zero, the branch should be folded away.
  auto* m2 = assembler::method_from_string(R"(
    (method (private) "LFoo;.callee:(I)V"
     (
      (load-param v0)
      (load-param v1)
      (if-eqz v1 :label)
      (const v0 0)
      (:label)
      (return-void)
     )
    )
  )");
  creator.add_method(m2);
  m2->get_code()->build_cfg();

  scope.push_back(creator.create());

  InterproceduralConstantPropagationPass().run(make_simple_stores(scope), conf);

  // The branch should be removed since the resource ID is known to be non-zero.
  auto expected_code2 = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (r-const v1 2131230721)
      (const v0 0)
      (return-void)
    )
  )");
  m2->get_code()->clear_cfg();
  EXPECT_CODE_EQ(m2->get_code(), expected_code2.get());
}
