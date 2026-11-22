/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IPConstantPropagation.h"

#include <limits>
#include <signal.h>
#include <tuple>

#include <boost/algorithm/string/replace.hpp>
#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "ConstantPropagationRuntimeAssert.h"
#include "ConstructorParams.h"
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

TEST_F(InterproceduralConstantPropagationTest,
       ancestorConstructorInitializesDelegatedField) {
  ClassCreator middle(DexType::make_type("LMiddle;"));
  middle.set_super(type::java_lang_Object());
  auto* middle_cls = middle.create();
  ClassCreator leaf(DexType::make_type("LLeaf;"));
  leaf.set_super(middle_cls->get_type());
  auto* field = DexField::make_field("LLeaf;.value:I")
                    ->make_concrete(ACC_PRIVATE | ACC_FINAL);
  leaf.add_field(field);
  auto* target = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:(I)V"
      (
        (load-param-object v0)
        (load-param v1)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (const v2 7)
        (iput v2 v0 "LLeaf;.value:I")
        (return-void)
      )
    )
  )");
  target->rstate.set_root();
  leaf.add_method(target);
  auto* delegating = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:()V"
      (
        (load-param-object v0)
        (const v1 0)
        (invoke-direct (v0 v1) "LLeaf;.<init>:(I)V")
        (return-void)
      )
    )
  )");
  delegating->rstate.set_root();
  leaf.add_method(delegating);
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LLeaf;.read:(LLeaf;)I"
      (
        (load-param-object v0)
        (iget v0 "LLeaf;.value:I")
        (move-result-pseudo v1)
        (return v1)
      )
    )
  )");
  reader->rstate.set_root();
  leaf.add_method(reader);
  Scope scope{middle_cls, leaf.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });
  auto assigned =
      definitely_assigned_ifields::get_definitely_assigned_ifields(scope, true);
  EXPECT_NE(assigned.count(field), 0u);
  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.use_multiple_callee_callgraph = true;
  config.analyze_ancestor_constructors = true;
  PassImpl(config).run(make_simple_stores(scope), conf);
  auto expected = assembler::ircode_from_string(R"((
    (load-param-object v0)
    (const v1 7)
    (return v1)
  ))");
  reader->get_code()->clear_cfg();
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

enum class AncestorFieldProofCase {
  Disabled,
  Enabled,
  Publication,
  NoOptimizations,
  ConditionalWrite,
  AllocationBypass,
};

class AncestorFieldProofTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<AncestorFieldProofCase> {};

TEST_P(AncestorFieldProofTest, preservesInitializationBoundaries) {
  auto scenario = GetParam();
  const bool enabled = scenario != AncestorFieldProofCase::Disabled;
  const bool inferred = scenario == AncestorFieldProofCase::Enabled;
  ClassCreator other(DexType::make_type("LOther;"));
  other.set_super(type::java_lang_Object());
  other.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LOther;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (return-void)))
  )"));
  ClassCreator middle(DexType::make_type("LMiddle;"));
  middle.set_super(type::java_lang_Object());
  ClassCreator leaf(DexType::make_type("LLeaf;"));
  leaf.set_super(middle.get_type());
  auto* field = DexField::make_field("LLeaf;.tag:Ljava/lang/String;")
                    ->make_concrete(ACC_PRIVATE | ACC_FINAL);
  leaf.add_field(field);
  auto* escaped = DexField::make_field("LLeaf;.escaped:Ljava/lang/Object;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  escaped->rstate.set_root();
  leaf.add_field(escaped);
  const std::string extra =
      scenario == AncestorFieldProofCase::Publication
          ? R"((sput-object v0 "LLeaf;.escaped:Ljava/lang/Object;"))"
      : scenario == AncestorFieldProofCase::ConditionalWrite
          ? R"((if-eqz v1 :exit))"
      : scenario == AncestorFieldProofCase::Enabled
          ? R"((new-instance "LOther;")
               (move-result-pseudo-object v5)
               (invoke-direct (v5) "LOther;.<init>:()V"))"
          : "";
  auto* target = assembler::method_from_string(
      R"((method (public constructor) "LLeaf;.<init>:(I)V"
        (
          (load-param-object v0)
          (load-param v1)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      )" +
      extra + R"(
          (const-string "Feed")
          (move-result-pseudo-object v2)
          (iput-object v2 v0 "LLeaf;.tag:Ljava/lang/String;")
          (:exit)
          (return-void)
        )
      ))");
  target->rstate.set_root();
  if (scenario == AncestorFieldProofCase::NoOptimizations) {
    target->rstate.set_no_optimizations();
  }
  leaf.add_method(target);
  auto* delegating = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:()V"
      (
        (load-param-object v0)
        (const v1 1)
        (invoke-direct (v0 v1) "LLeaf;.<init>:(I)V")
        (return-void)
      )
    )
  )");
  delegating->rstate.set_root();
  leaf.add_method(delegating);
  const std::string reader_body = R"((
    (load-param-object v0)
    (iget-object v0 "LLeaf;.tag:Ljava/lang/String;")
    (move-result-pseudo-object v1)
    (return-object v1)
  ))";
  auto* reader = assembler::method_from_string(
      R"((method (public static) "LLeaf;.read:(LLeaf;)Ljava/lang/String;" )" +
      reader_body + ")");
  reader->rstate.set_root();
  leaf.add_method(reader);
  if (scenario == AncestorFieldProofCase::AllocationBypass) {
    auto* bypass = assembler::method_from_string(R"(
      (method (public static) "LLeaf;.bypass:()LLeaf;"
        (
          (new-instance "LLeaf;")
          (move-result-pseudo-object v0)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
          (return-object v0)
        )
      )
    )");
    bypass->rstate.set_root();
    leaf.add_method(bypass);
  }
  Scope scope{other.create(), middle.create(), leaf.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });
  auto assigned = definitely_assigned_ifields::get_definitely_assigned_ifields(
      scope, enabled);
  EXPECT_EQ(assigned.count(field) != 0u, inferred);
  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.use_multiple_callee_callgraph = true;
  config.analyze_ancestor_constructors = enabled;
  PassImpl(config).run(make_simple_stores(scope), conf);
  auto expected = assembler::ircode_from_string(inferred ? R"((
    (load-param-object v0)
    (const-string "Feed")
    (move-result-pseudo-object v1)
    (return-object v1)
  ))"
                                                         : reader_body);
  reader->get_code()->clear_cfg();
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

INSTANTIATE_TEST_SUITE_P(
    AncestorInitialization,
    AncestorFieldProofTest,
    ::testing::Values(AncestorFieldProofCase::Disabled,
                      AncestorFieldProofCase::Enabled,
                      AncestorFieldProofCase::Publication,
                      AncestorFieldProofCase::NoOptimizations,
                      AncestorFieldProofCase::ConditionalWrite,
                      AncestorFieldProofCase::AllocationBypass));

enum class AncestorCalleeProofCase { Callback, NoOptimizations, External };

class AncestorCalleeProofTest
    : public InterproceduralConstantPropagationTest,
      public ::testing::WithParamInterface<AncestorCalleeProofCase> {};

TEST_P(AncestorCalleeProofTest, doesNotAssumeAncestorsAreNonEscaping) {
  auto scenario = GetParam();
  ClassCreator ancestor(DexType::make_type("LAncestor;"));
  ancestor.set_super(type::java_lang_Object());
  ancestor.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  auto* observed = DexField::make_field("LAncestor;.observed:I")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  observed->rstate.set_root();
  ancestor.add_field(observed);
  ancestor.add_method(DexMethod::make_method("LAncestor;.observe:()I")
                          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, true));
  const std::string callback =
      scenario == AncestorCalleeProofCase::Callback
          ? R"((invoke-virtual (v0) "LAncestor;.observe:()I")
               (move-result v1)
               (sput v1 "LAncestor;.observed:I"))"
          : "";
  DexMethod* ancestor_ctor;
  if (scenario == AncestorCalleeProofCase::External) {
    ancestor_ctor = dynamic_cast<DexMethod*>(
        DexMethod::make_method("LAncestor;.<init>:()V"));
    ASSERT_NE(ancestor_ctor, nullptr);
    ancestor_ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
    ancestor_ctor->set_external();
  } else {
    ancestor_ctor = assembler::method_from_string(
        R"((method (public constructor) "LAncestor;.<init>:()V"
          ((load-param-object v0)
           (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        )" +
        callback + R"((return-void))))");
  }
  ancestor_ctor->rstate.set_root();
  if (scenario == AncestorCalleeProofCase::NoOptimizations) {
    ancestor_ctor->rstate.set_no_optimizations();
  }
  ancestor.add_method(ancestor_ctor);
  auto* ancestor_cls = ancestor.create();
  if (scenario == AncestorCalleeProofCase::External) {
    ancestor_cls->set_external();
  }
  ClassCreator middle(DexType::make_type("LMiddle;"));
  middle.set_super(ancestor_cls->get_type());
  ClassCreator leaf(DexType::make_type("LLeaf;"));
  leaf.set_super(middle.get_type());
  auto* field = DexField::make_field("LLeaf;.value:I")
                    ->make_concrete(ACC_PRIVATE | ACC_FINAL);
  leaf.add_field(field);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "LAncestor;.<init>:()V")
       (const v1 7)
       (iput v1 v0 "LLeaf;.value:I")
       (return-void)))
  )");
  ctor->rstate.set_root();
  leaf.add_method(ctor);
  const std::string read_body = R"((
    (load-param-object v0)
    (iget v0 "LLeaf;.value:I")
    (move-result-pseudo v1)
    (return v1)
  ))";
  auto* observer = assembler::method_from_string(
      R"((method (public) "LLeaf;.observe:()I" )" + read_body + ")");
  observer->rstate.set_root();
  leaf.add_method(observer);
  auto* reader = assembler::method_from_string(
      R"((method (public static) "LLeaf;.read:(LLeaf;)I" )" + read_body + ")");
  reader->rstate.set_root();
  leaf.add_method(reader);
  Scope scope{middle.create(), leaf.create()};
  if (scenario != AncestorCalleeProofCase::External) {
    scope.insert(scope.begin(), ancestor_cls);
  }
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });
  auto assigned =
      definitely_assigned_ifields::get_definitely_assigned_ifields(scope, true);
  EXPECT_EQ(assigned.count(field), 0u);
  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.use_multiple_callee_callgraph = true;
  config.analyze_ancestor_constructors = true;
  PassImpl(config).run(make_simple_stores(scope), conf);
  auto expected = assembler::ircode_from_string(read_body);
  reader->get_code()->clear_cfg();
  observer->get_code()->clear_cfg();
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
  EXPECT_CODE_EQ(observer->get_code(), expected.get());
}

INSTANTIATE_TEST_SUITE_P(
    AncestorCalleeBoundaries,
    AncestorCalleeProofTest,
    ::testing::Values(AncestorCalleeProofCase::Callback,
                      AncestorCalleeProofCase::NoOptimizations,
                      AncestorCalleeProofCase::External));

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
  FixpointIterator fp_iter(
      std::move(cg),
      [&null_check_methods](const DexMethod* method,
                            const WholeProgramState&,
                            const ArgumentDomain& args) {
        const auto& code = *method->get_code();
        auto env = env_with_params(is_static(method), &code, args);
        return std::make_unique<IntraproceduralAnalysis>(
            /* wps accessor */ nullptr,
            code.cfg(),
            ConstantPrimitiveAnalyzer(),
            intraprocedural::make_default_no_throw_analyzer(
                &null_check_methods),
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

// `check` returns normally only when its argument is 5, so after the call
// `caller` passes 5 to `use`. The call sits in a try block, so that refinement
// is read only on the call's no-throw edge; a cached result of `caller` from a
// run that did not know the summary of `check` must not be reused once it does.
TEST_F(InterproceduralConstantPropagationTest,
       cachedResultIsRedoneWhenASummaryReadOnAnEdgeChanges) {
  ClassCreator creator(DexType::make_type("LFoo;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.check:(I)V"
     (
      (load-param v0)
      (const v1 5)
      (if-eq v0 v1 :ok)
      (const v2 0)
      (throw v2)
      (:ok)
      (return-void)
     )
    )
  )"));
  creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.use:(I)V"
     (
      (load-param v0)
      (return-void)
     )
    )
  )"));
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LFoo;.caller:(I)V"
     (
      (load-param v0)
      (.try_start a)
      (invoke-static (v0) "LFoo;.check:(I)V")
      (.try_end a)
      (invoke-static (v0) "LFoo;.use:(I)V")
      (return-void)
      (.catch (a))
      (return-void)
     )
    )
  )");
  caller->rstate.set_root();
  creator.add_method(caller);
  Scope scope{creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto fp_iter = InterproceduralConstantPropagationPass().analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);
  auto graph = method_override_graph::build_graph(scope);
  fp_iter->set_whole_program_state(std::make_unique<WholeProgramState>(
      scope, *fp_iter,
      method_override_graph::get_non_true_virtuals(*graph, scope),
      UnorderedSet<const DexType*>(), UnorderedSet<const DexField*>(),
      /* call_graph */ nullptr));
  fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});

  const auto* use = DexMethod::get_method("LFoo;.use:(I)V")->as_def();
  const auto& cg = fp_iter->get_call_graph();
  EXPECT_EQ(fp_iter->get_entry_state_at(cg.node(use))
                .get(CURRENT_PARTITION_LABEL)
                .get(0),
            SignedConstantDomain(5));
}

// `check`, which `LSub;` overrides, returns normally only when its argument is
// 5, so after the call `caller` passes 5 to `use`. With the multiple-callee
// call graph, IPCP reads what both overrides guarantee about their arguments
// from the whole-program state, although neither is a known method. The
// cached result of `caller` from the bootstrap, which knew nothing about
// `check`, must not be reused once the guarantee is known.
TEST_F(InterproceduralConstantPropagationTest,
       cachedResultIsRedoneWhenASummaryReadThroughTheCallGraphChanges) {
  const char* const check_body = R"(
     (
      (load-param-object v0)
      (load-param v1)
      (const v2 5)
      (if-eq v1 v2 :ok)
      (const v3 0)
      (throw v3)
      (:ok)
      (return-void)
     )
  )";
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(
      std::string(R"((method (public) "LBase;.check:(I)V")") + check_body +
      ")"));
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LBase;.use:(I)V"
     (
      (load-param v0)
      (return-void)
     )
    )
  )"));
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LBase;.caller:(LBase;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-virtual (v0 v1) "LBase;.check:(I)V")
      (invoke-static (v1) "LBase;.use:(I)V")
      (return-void)
     )
    )
  )");
  caller->rstate.set_root();
  base_creator.add_method(caller);
  auto* base_cls = base_creator.create();

  ClassCreator sub_creator(DexType::make_type("LSub;"));
  sub_creator.set_super(base_cls->get_type());
  sub_creator.add_method(assembler::method_from_string(
      std::string(R"((method (public) "LSub;.check:(I)V")") + check_body +
      ")"));
  Scope scope{base_cls, sub_creator.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 1;
  config.use_multiple_callee_callgraph = true;
  auto fp_iter = InterproceduralConstantPropagationPass(config).analyze(
      scope, &m_immut_analyzer_state, &m_api_level_analyzer_state,
      &m_string_analyzer_state, &m_package_name_state, m_null_check_methods);

  const auto* use = DexMethod::get_method("LBase;.use:(I)V")->as_def();
  const auto& cg = fp_iter->get_call_graph();
  EXPECT_EQ(fp_iter->get_entry_state_at(cg.node(use))
                .get(CURRENT_PARTITION_LABEL)
                .get(0),
            SignedConstantDomain(5));
}

namespace {

// Creates the class `type` with the instance field `field:I`, which its
// constructor `(I)V` sets to its argument, plus the root methods `roots` and
// the non-root methods `others`.
DexClass* create_class_with_int_field(
    const std::string& type,
    const std::string& field,
    const std::vector<std::string>& roots,
    const std::vector<std::string>& others = {}) {
  ClassCreator creator(DexType::make_type(type));
  creator.set_super(type::java_lang_Object());
  creator.add_field(DexField::make_field(type + "." + field + ":I")
                        ->make_concrete(ACC_PUBLIC));
  creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) ")" + type + R"(.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iput v1 v0 ")" + type + "." + field + R"(:I")
      (return-void)
     )
    )
  )"));
  for (const auto& method : roots) {
    auto* m = assembler::method_from_string(method);
    m->rstate.set_root();
    creator.add_method(m);
  }
  for (const auto& method : others) {
    creator.add_method(assembler::method_from_string(method));
  }
  return creator.create();
}

// `make` creates every Foo with f = 7, so `read` folds to 7 unless reachable
// code writes another value to `f`.
const char* const kMakeWithConst = R"(
    (method (public static) "LFoo;.make:()LFoo;"
     (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (const v1 7)
      (invoke-direct (v0 v1) "LFoo;.<init>:(I)V")
      (return-object v0)
     )
    )
)";

const char* const kRead = R"(
    (method (public static) "LFoo;.read:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v1)
      (return v1)
     )
    )
)";

void run_ipcp(const Scope& scope,
              ConfigFiles& conf,
              const InterproceduralConstantPropagationPass::Config& config) {
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  InterproceduralConstantPropagationPass(config).run(make_simple_stores(scope),
                                                     conf);
}

// With no heap-analysis iterations, every whole-program value is Top, and no
// field or method is ever Bottom.
InterproceduralConstantPropagationPass::Config config_with_heap_analysis() {
  InterproceduralConstantPropagationPass::Config config;
  config.max_heap_analysis_iterations = 3;
  return config;
}

bool contains_const(const std::string& method, int64_t value) {
  auto& cfg = DexMethod::get_method(method)->as_def()->get_code()->cfg();
  for (const auto& mie : cfg::InstructionIterable(cfg)) {
    if (mie.insn->opcode() == OPCODE_CONST &&
        mie.insn->get_literal() == value) {
      return true;
    }
  }
  return false;
}

// Wraps `insns`, which can throw, in a try block whose handler, for
// `exception`, writes 99 to `LFoo;.f:I` (the object in `foo_reg`); without
// `in_try`, the write follows `insns` directly.
std::string set_f_after(const std::string& insns,
                        const std::string& exception,
                        const std::string& foo_reg,
                        bool in_try) {
  const std::string set_f =
      "(const v9 99)\n(iput v9 " + foo_reg + " \"LFoo;.f:I\")\n(return-void)\n";
  if (!in_try) {
    return insns + set_f;
  }
  return "(.try_start a)\n" + insns + "(.try_end a)\n(return-void)\n" +
         "(.catch (a) \"" + exception + "\")\n" + set_f;
}

// `fail` never returns. Returns whether `LFoo;.read` folds to 7 after a method
// calls `fail` and then writes 99 to `f`, in a handler when `in_try`.
bool read_folds_after_call_of_fail(ConfigFiles& conf, bool in_try) {
  const char* const fail = R"(
    (method (public static) "LFoo;.fail:()I"
     (
      (new-instance "Ljava/lang/RuntimeException;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/RuntimeException;.<init>:()V")
      (throw v0)
     )
    )
  )";
  const std::string call_and_set =
      R"((method (public static) "LFoo;.callAndSet:(LFoo;)V" (
      (load-param-object v0)
      )" +
      set_f_after("(invoke-static () \"LFoo;.fail:()I\")\n(move-result v1)\n",
                  "Ljava/lang/RuntimeException;", "v0", in_try) +
      "))";
  run_ipcp({create_class_with_int_field(
               "LFoo;", "f", {kMakeWithConst, kRead, call_and_set}, {fail})},
           conf, config_with_heap_analysis());
  return contains_const("LFoo;.read:(LFoo;)I", 7);
}

// Bar's only constructor calls `fail`, which never returns, before it assigns
// `g`. Since every constructor assigns `g` before any read, IPCP does not start
// it at 0, and that one write is unreachable. So no Bar is ever constructed,
// `g` never holds a value, and a read of it can only throw a
// `NullPointerException`. Returns whether `LFoo;.read` folds to 7 after a
// method reads `g` and then writes 99 to `f`, in a handler when `in_try`.
bool read_folds_after_read_of_field_without_value(ConfigFiles& conf,
                                                  bool in_try) {
  const char* const fail = R"(
    (method (public static) "LBar;.fail:()V"
     (
      (new-instance "Ljava/lang/RuntimeException;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/RuntimeException;.<init>:()V")
      (throw v0)
     )
    )
  )";
  const char* const make_bar = R"(
    (method (public static) "LBar;.make:()LBar;"
     (
      (new-instance "LBar;")
      (move-result-pseudo-object v0)
      (const v1 5)
      (invoke-direct (v0 v1) "LBar;.<init>:(I)V")
      (return-object v0)
     )
    )
  )";
  const std::string read_and_set =
      R"((method (public static) "LBar;.readAndSet:(LBar;LFoo;)V" (
      (load-param-object v0)
      (load-param-object v1)
      )" +
      set_f_after("(iget v0 \"LBar;.g:I\")\n(move-result-pseudo v2)\n",
                  "Ljava/lang/NullPointerException;", "v1", in_try) +
      "))";
  ClassCreator bar(DexType::make_type("LBar;"));
  bar.set_super(type::java_lang_Object());
  bar.add_field(DexField::make_field("LBar;.g:I")->make_concrete(ACC_PUBLIC));
  bar.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBar;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-static () "LBar;.fail:()V")
      (iput v1 v0 "LBar;.g:I")
      (return-void)
     )
    )
  )"));
  bar.add_method(assembler::method_from_string(fail));
  for (const std::string& root : {std::string(make_bar), read_and_set}) {
    auto* m = assembler::method_from_string(root);
    m->rstate.set_root();
    bar.add_method(m);
  }
  run_ipcp({bar.create(),
            create_class_with_int_field("LFoo;", "f", {kMakeWithConst, kRead})},
           conf, config_with_heap_analysis());
  return contains_const("LFoo;.read:(LFoo;)I", 7);
}

} // namespace

// The exception of `fail` reaches the handler, so `f` is not always 7.
TEST_F(InterproceduralConstantPropagationTest,
       callOfMethodThatNeverReturnsKeepsItsHandler) {
  EXPECT_FALSE(read_folds_after_call_of_fail(conf, /* in_try */ true));
}

// The write after the call never runs, so `f` is always 7.
TEST_F(InterproceduralConstantPropagationTest,
       callOfMethodThatNeverReturnsCutsOffWhatFollows) {
  EXPECT_TRUE(read_folds_after_call_of_fail(conf, /* in_try */ false));
}

// The NullPointerException of the read reaches the handler, so `f` is not
// always 7.
TEST_F(InterproceduralConstantPropagationTest,
       readOfInstanceFieldThatNeverHoldsAValueKeepsItsHandler) {
  EXPECT_FALSE(
      read_folds_after_read_of_field_without_value(conf, /* in_try */ true));
}

// The write after the read never runs, so `f` is always 7.
TEST_F(InterproceduralConstantPropagationTest,
       readOfInstanceFieldThatNeverHoldsAValueCutsOffWhatFollows) {
  EXPECT_TRUE(
      read_folds_after_read_of_field_without_value(conf, /* in_try */ false));
}

// `LFoo;.<clinit>` sets `x` to 1, calls `LHelper;.copy`, and then calls a
// method on null, so it never completes normally and `x` holds no value after
// it. `copy` runs while the initializer is still running: its read of `x`
// completes, so it copies 1 to `LBar;.z`, and reads of `z` must not fold to its
// initial value, 0.
TEST_F(InterproceduralConstantPropagationTest,
       staticFieldReadWhileItsFailingClassInitializerRunsCompletes) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  bar_creator.add_field(DexField::make_field("LBar;.z:I")
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  auto* read = assembler::method_from_string(R"(
    (method (public static) "LBar;.read:()I"
      (
        (sget "LBar;.z:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");
  read->rstate.set_root();
  bar_creator.add_method(read);

  ClassCreator helper_creator(DexType::make_type("LHelper;"));
  helper_creator.set_super(type::java_lang_Object());
  helper_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LHelper;.copy:()V"
      (
        (sget "LFoo;.x:I")
        (move-result-pseudo v0)
        (sput v0 "LBar;.z:I")
        (return-void)
      )
    )
  )"));

  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.add_field(DexField::make_field("LFoo;.x:I")
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  foo_creator.add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
      (
        (const v0 1)
        (sput v0 "LFoo;.x:I")
        (invoke-static () "LHelper;.copy:()V")
        (const v1 0)
        (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
        (return-void)
      )
    )
  )"));
  Scope scope{bar_creator.create(), helper_creator.create(),
              foo_creator.create()};
  const auto original_read = assembler::to_s_expr(read->get_code());
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  PassImpl::Config config;
  config.max_heap_analysis_iterations = 3;
  config.use_multiple_callee_callgraph = true;

  PassImpl(config).run(make_simple_stores(scope), conf);

  read->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(read->get_code()), original_read);
}

// The WholeProgramState and FixpointIterator operations behind a search for
// field values, on two instance fields: `Foo.f`, assigned 7 by every
// constructor call and so definitely assigned, and `Bar.h`, not assigned by the
// constructor and set to 3 by `set`. The static field `Bar.s` is 5, and
// `Bar.t` is 1 or, after `setT`, 2.
namespace {

// Adds `methods` and the root methods `roots` to `creator`.
void add_methods(ClassCreator* creator,
                 const std::vector<std::string>& methods,
                 const std::vector<std::string>& roots = {}) {
  for (const auto& method : methods) {
    creator->add_method(assembler::method_from_string(method));
  }
  for (const auto& root : roots) {
    auto* m = assembler::method_from_string(root);
    m->rstate.set_root();
    creator->add_method(m);
  }
}

// The constructor `<init>:()V` of `type`, which only calls Object's.
std::string default_constructor(const std::string& type) {
  return R"((method (public constructor) ")" + type + R"(.<init>:()V" (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )))";
}

// Creates the class `type` with the public instance fields `fields`, its
// default constructor, the methods `methods` and the root methods `roots`.
DexClass* create_class(const std::string& type,
                       const std::vector<std::string>& fields,
                       const std::vector<std::string>& methods,
                       const std::vector<std::string>& roots) {
  ClassCreator creator(DexType::make_type(type));
  creator.set_super(type::java_lang_Object());
  for (const auto& field : fields) {
    creator.add_field(DexField::make_field(field)->make_concrete(ACC_PUBLIC));
  }
  add_methods(&creator, methods);
  add_methods(&creator, {default_constructor(type)}, roots);
  return creator.create();
}

void build_cfgs(const Scope& scope) {
  walk::code(scope, [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.cfg().calculate_exit_block();
  });
}

// Runs the first IPCP run over `scope`, which assumes nothing about fields and
// methods, recording what the methods write to instance fields.
std::unique_ptr<FixpointIterator> bootstrap_recording_field_writes(
    InterproceduralConstantPropagationTest* test, const Scope& scope) {
  auto fp_iter = InterproceduralConstantPropagationPass().analyze(
      scope, &test->m_immut_analyzer_state, &test->m_api_level_analyzer_state,
      &test->m_string_analyzer_state, &test->m_package_name_state,
      test->m_null_check_methods);
  fp_iter->start_recording_field_writes(scope);
  fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
  return fp_iter;
}

} // namespace

struct FieldSearchTest : public InterproceduralConstantPropagationTest {
  FieldSearchTest() {
    ClassCreator bar(DexType::make_type("LBar;"));
    bar.set_super(type::java_lang_Object());
    bar.add_field(DexField::make_field("LBar;.h:I")->make_concrete(ACC_PUBLIC));
    for (const char* name : {"LBar;.s:I", "LBar;.t:I"}) {
      bar.add_field(
          DexField::make_field(name)->make_concrete(ACC_PUBLIC | ACC_STATIC));
    }
    bar.add_field(DexField::make_field("LBar;.v:I")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_VOLATILE));
    bar.add_method(assembler::method_from_string(R"(
      (method (public static constructor) "LBar;.<clinit>:()V"
       (
        (const v0 5)
        (sput v0 "LBar;.s:I")
        (const v0 1)
        (sput v0 "LBar;.t:I")
        (const v0 6)
        (sput v0 "LBar;.v:I")
        (return-void)
       )
      )
    )"));
    add_methods(&bar, {default_constructor("LBar;")},
                {R"(
      (method (public static) "LBar;.setT:()V"
       (
        (const v0 2)
        (sput v0 "LBar;.t:I")
        (return-void)
       )
      )
    )",
                 R"(
      (method (public static) "LBar;.make:()LBar;"
       (
        (new-instance "LBar;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LBar;.<init>:()V")
        (return-object v0)
       )
      )
    )",
                 R"(
      (method (public static) "LBar;.set:(LBar;)V"
       (
        (load-param-object v0)
        (const v1 3)
        (iput v1 v0 "LBar;.h:I")
        (return-void)
       )
      )
    )"});
    scope = {create_class_with_int_field("LFoo;", "f", {kMakeWithConst, kRead}),
             bar.create()};
    build_cfgs(scope);
    definitely_assigned =
        definitely_assigned_ifields::get_definitely_assigned_ifields(scope);
    f = DexField::get_field("LFoo;.f:I")->as_def();
    h = DexField::get_field("LBar;.h:I")->as_def();
  }

  // Runs only the first IPCP run, which assumes nothing about fields and
  // methods, recording what the methods write to instance fields.
  std::unique_ptr<FixpointIterator> bootstrap() {
    return bootstrap_recording_field_writes(this, scope);
  }

  std::unique_ptr<WholeProgramState> collect(const FixpointIterator& fp_iter) {
    auto graph = method_override_graph::build_graph(scope);
    return std::make_unique<WholeProgramState>(
        scope, fp_iter,
        method_override_graph::get_non_true_virtuals(*graph, scope),
        UnorderedSet<const DexType*>(), definitely_assigned,
        /* call_graph */ nullptr);
  }

  std::unique_ptr<WholeProgramState> start(const FixpointIterator& fp_iter) {
    auto graph = method_override_graph::build_graph(scope);
    return WholeProgramState::make_field_search_start(
        scope, fp_iter,
        method_override_graph::get_non_true_virtuals(*graph, scope),
        UnorderedSet<const DexType*>(), definitely_assigned,
        /* call_graph */ nullptr);
  }

  static SignedConstantDomain zero_or_three() {
    return SignedConstantDomain(0).join(SignedConstantDomain(3));
  }

  Scope scope;
  UnorderedSet<const DexField*> definitely_assigned;
  const DexField* f{nullptr};
  const DexField* h{nullptr};
};

// `f` is assigned by every constructor before any read, so it starts with no
// value; `h` starts at 0. The statics `s` and `v` keep the values of the class
// initializer, as collecting a run's field values keeps them, volatile or not;
// `t` is unknown, because `setT` writes it too.
TEST_F(FieldSearchTest, searchStartsAtInitialAndClassInitializerValues) {
  auto fp_iter = bootstrap();
  const auto* s = DexField::get_field("LBar;.s:I")->as_def();
  const auto* t = DexField::get_field("LBar;.t:I")->as_def();
  auto start_state = start(*fp_iter);
  EXPECT_TRUE(start_state->get_field_value(f).is_bottom());
  EXPECT_EQ(start_state->get_field_value(h), SignedConstantDomain(0));
  EXPECT_EQ(start_state->get_field_value(s), SignedConstantDomain(5));
  EXPECT_TRUE(start_state->get_field_value(t).is_top());
  const auto* v = DexField::get_field("LBar;.v:I")->as_def();
  EXPECT_EQ(start_state->get_field_value(v), SignedConstantDomain(6));
  EXPECT_EQ(collect(*fp_iter)->get_field_value(v), SignedConstantDomain(6));
  EXPECT_TRUE(start_state
                  ->get_return_value(
                      DexMethod::get_method("LFoo;.make:()LFoo;")->as_def())
                  .is_top());
}

// The first run writes 7 to `f` (the constructor called by `make`) and 3 to
// `h` (`set`); the initial values are not writes. The run's state tracks no
// fields, yet the writes are recorded, because a later state may reuse the
// cached results.
TEST_F(FieldSearchTest, collectFieldWritesReturnsWhatTheRunWrites) {
  auto fp_iter = bootstrap();
  auto writes = fp_iter->collect_field_writes();
  EXPECT_EQ(writes.bindings().size(), 2u);
  EXPECT_EQ(writes.get(f), SignedConstantDomain(7));
  EXPECT_EQ(writes.get(h), SignedConstantDomain(3));
}

// `set9` is neither a root nor called, so no call graph node represents it,
// yet its write of 9 to `v` counts, as it does when collecting a run's field
// values.
TEST_F(InterproceduralConstantPropagationTest,
       fieldWritesIncludeMethodsWithoutCallGraphNode) {
  Scope scope{create_class("LOrph;", {"LOrph;.v:I"}, {R"(
    (method (public static) "LOrph;.set9:(LOrph;)V"
     (
      (load-param-object v0)
      (const v1 9)
      (iput v1 v0 "LOrph;.v:I")
      (return-void)
     )
    )
  )"},
                           {})};
  build_cfgs(scope);
  auto fp_iter = bootstrap_recording_field_writes(this, scope);
  const auto* v = DexField::get_field("LOrph;.v:I")->as_def();
  EXPECT_EQ(fp_iter->collect_field_writes().get(v), SignedConstantDomain(9));
  EXPECT_EQ(fp_iter->rerun_incrementally(/* max_growing_sweeps */ 20).get(v),
            SignedConstantDomain(9));
}

// The collected writes joined into the start give what collecting the run's
// field values gives.
TEST_F(FieldSearchTest, fieldWritesJoinedIntoTheStartGiveTheCollectedValues) {
  auto fp_iter = bootstrap();
  auto collected = collect(*fp_iter);
  auto start_state = start(*fp_iter);
  start_state->grow_field_values(fp_iter->collect_field_writes(),
                                 std::numeric_limits<size_t>::max());
  for (const auto* field : {f, h}) {
    EXPECT_EQ(start_state->get_field_value(field),
              collected->get_field_value(field))
        << show(field);
  }
}

// From the start, `f` gets its first value, which is not growth, and `h` grows
// from 0 to [0, 3]. With no growth allowed, `h` is widened to Top.
TEST_F(FieldSearchTest, growFieldValuesWidensAFieldGrownMoreThanTheDelay) {
  auto fp_iter = bootstrap();
  auto writes = fp_iter->collect_field_writes();
  fp_iter->set_whole_program_state(start(*fp_iter));
  auto growth = fp_iter->grow_field_values(writes, /* widening_delay */ 0);
  EXPECT_EQ(growth.grown, 2u);
  EXPECT_EQ(growth.widened, 1u);
  const auto& wps = fp_iter->get_whole_program_state();
  EXPECT_EQ(wps.get_field_value(f), SignedConstantDomain(7));
  EXPECT_TRUE(wps.get_field_value(h).is_top());
  EXPECT_EQ(fp_iter->grow_field_values(writes, 0).grown, 0u);
}

// With one growth allowed, `h` keeps its value [0, 3].
TEST_F(FieldSearchTest, growFieldValuesKeepsAFieldGrownWithinTheDelay) {
  auto fp_iter = bootstrap();
  auto writes = fp_iter->collect_field_writes();
  fp_iter->set_whole_program_state(start(*fp_iter));
  auto growth = fp_iter->grow_field_values(writes, /* widening_delay */ 1);
  EXPECT_EQ(growth.grown, 2u);
  EXPECT_EQ(growth.widened, 0u);
  const auto& wps = fp_iter->get_whole_program_state();
  EXPECT_EQ(wps.get_field_value(f), SignedConstantDomain(7));
  EXPECT_EQ(wps.get_field_value(h), zero_or_three());
  EXPECT_EQ(fp_iter->grow_field_values(writes, 1).grown, 0u);
}

namespace {

// `relay` passes `Foo.g` (0, or 7 once `setG` ran) to `Qux.make`, whose
// constructor stores it in `q`, and starts `count`, which stores its growing
// argument in `r` and calls itself. So `g`'s growth reaches `q` only through
// arguments, and `count`'s argument grows along a recursive call.
DexClass* create_qux() {
  ClassCreator qux(DexType::make_type("LQux;"));
  qux.set_super(type::java_lang_Object());
  for (const char* name : {"LQux;.q:I", "LQux;.r:I"}) {
    qux.add_field(DexField::make_field(name)->make_concrete(ACC_PUBLIC));
  }
  add_methods(&qux, {R"(
    (method (public constructor) "LQux;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iput v1 v0 "LQux;.q:I")
      (return-void)
     )
    )
  )",
                     R"(
    (method (public static) "LQux;.make:(I)LQux;"
     (
      (load-param v0)
      (new-instance "LQux;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1 v0) "LQux;.<init>:(I)V")
      (return-object v1)
     )
    )
  )",
                     R"(
    (method (public static) "LQux;.count:(LQux;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LQux;.r:I")
      (const v2 100)
      (if-ge v1 v2 :done)
      (add-int/lit v3 v1 1)
      (invoke-static (v0 v3) "LQux;.count:(LQux;I)V")
      (:done)
      (return-void)
     )
    )
  )"});
  return qux.create();
}

const char* const kSetG = R"(
    (method (public static) "LFoo;.setG:(LFoo;)V"
     (
      (load-param-object v0)
      (const v1 7)
      (iput v1 v0 "LFoo;.g:I")
      (return-void)
     )
    )
)";

const char* const kRelay = R"(
    (method (public static) "LFoo;.relay:(LFoo;)V"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.g:I")
      (move-result-pseudo v1)
      (invoke-static (v1) "LQux;.make:(I)LQux;")
      (move-result-object v2)
      (const v3 0)
      (invoke-static (v2 v3) "LQux;.count:(LQux;I)V")
      (return-void)
     )
    )
)";

} // namespace

namespace {

constexpr size_t kMaxGrowingSweeps = 20;

// The outcome of a search for the values of the instance fields of a scope.
struct FieldSearch {
  std::unique_ptr<FixpointIterator> fp_iter;
  // For each requested field, its final value and the writes to it collected
  // under the final entry arguments.
  std::vector<ConstantValue> values;
};

// Searches for the values of the instance fields of `scope`, bringing the
// analysis up to date after each growth either with rerun_incrementally() or
// with a full run. With `collect_before_rerun`, also collects the writes
// before each incremental rerun, which must not change its outcome.
FieldSearch search_field_values(InterproceduralConstantPropagationTest* test,
                                const Scope& scope,
                                bool incremental,
                                const std::vector<std::string>& fields,
                                size_t max_growing_sweeps = kMaxGrowingSweeps,
                                bool collect_before_rerun = false) {
  auto fp_iter = bootstrap_recording_field_writes(test, scope);
  auto definitely_assigned =
      definitely_assigned_ifields::get_definitely_assigned_ifields(scope);
  auto graph = method_override_graph::build_graph(scope);
  fp_iter->set_whole_program_state(WholeProgramState::make_field_search_start(
      scope, *fp_iter,
      method_override_graph::get_non_true_virtuals(*graph, scope),
      UnorderedSet<const DexType*>(), definitely_assigned,
      /* call_graph */ nullptr));
  fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
  auto writes = fp_iter->collect_field_writes();
  size_t rounds = 0;
  while (fp_iter->grow_field_values(writes, 2).grown != 0) {
    always_assert(++rounds < 50);
    if (incremental) {
      if (collect_before_rerun) {
        fp_iter->collect_field_writes();
      }
      writes = fp_iter->rerun_incrementally(max_growing_sweeps);
    } else {
      fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
      writes = fp_iter->collect_field_writes();
    }
  }
  auto collected = fp_iter->collect_field_writes();
  FieldSearch search;
  for (const auto& name : fields) {
    const auto* field = DexField::get_field(name)->as_def();
    search.values.push_back(
        fp_iter->get_whole_program_state().get_field_value(field));
    search.values.push_back(collected.get(field));
  }
  search.fp_iter = std::move(fp_iter);
  return search;
}

// Whether every method of `scope` has the same entry and exit states in `a`
// as in `b`, or with `at_least`, states in `a` at least as large as in `b`.
bool states_match(const FieldSearch& a,
                  const FieldSearch& b,
                  const Scope& scope,
                  bool at_least = false) {
  auto matches = [&](const Domain& x, const Domain& y) {
    return at_least ? y.leq(x) : x.equals(y);
  };
  bool match = true;
  walk::methods(scope, [&](DexMethod* method) {
    const auto& graph_a = a.fp_iter->get_call_graph();
    const auto& graph_b = b.fp_iter->get_call_graph();
    if (!graph_a.has_node(method) || !graph_b.has_node(method)) {
      match = match && !graph_a.has_node(method) && !graph_b.has_node(method);
      return;
    }
    const auto& node_a = graph_a.node(method);
    const auto& node_b = graph_b.node(method);
    match = match &&
            matches(a.fp_iter->get_entry_state_at(node_a),
                    b.fp_iter->get_entry_state_at(node_b)) &&
            matches(a.fp_iter->get_exit_state_at(node_a),
                    b.fp_iter->get_exit_state_at(node_b));
  });
  return match;
}

// `writeG` writes 1 to `Rev.g` unless `Rev.f` is 0, and `setF` writes an
// unknown value to `Rev.f`. The run before the search, where `Rev.f` is
// unknown, caches a result of `writeG` that writes `Rev.g`; the search starts
// with `Rev.f` at 0, where `writeG` writes nothing, until `Rev.f` grows back to
// unknown and the first cached result matches again.
Scope create_revived_cache_entry() {
  return {create_class("LRev;", {"LRev;.f:I", "LRev;.g:I"}, {},
                       {R"(
    (method (public static) "LRev;.writeG:(LRev;)V"
     (
      (load-param-object v0)
      (iget v0 "LRev;.f:I")
      (move-result-pseudo v1)
      (if-eqz v1 :done)
      (const v2 1)
      (iput v2 v0 "LRev;.g:I")
      (:done)
      (return-void)
     )
    )
  )",
                        R"(
    (method (public static) "LRev;.setF:(LRev;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LRev;.f:I")
      (return-void)
     )
    )
  )"})};
}

// `a(c, x)` writes x to `Cyc.r` and, once `Cyc.flag` is set, calls `b(c, 5)`;
// `b(c, y)` calls `a(c, y)`; `start` calls both with 0. Only `setFlag` sets the
// flag, so the recursive call first grows the argument of `a` in an
// incremental rerun.
Scope create_flagged_recursion() {
  return {create_class("LCyc;", {"LCyc;.flag:I", "LCyc;.r:I"},
                       {R"(
    (method (public static) "LCyc;.a:(LCyc;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LCyc;.r:I")
      (iget v0 "LCyc;.flag:I")
      (move-result-pseudo v2)
      (if-eqz v2 :done)
      (const v3 5)
      (invoke-static (v0 v3) "LCyc;.b:(LCyc;I)V")
      (:done)
      (return-void)
     )
    )
  )",
                        R"(
    (method (public static) "LCyc;.b:(LCyc;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-static (v0 v1) "LCyc;.a:(LCyc;I)V")
      (return-void)
     )
    )
  )"},
                       {R"(
    (method (public static) "LCyc;.start:()LCyc;"
     (
      (new-instance "LCyc;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LCyc;.<init>:()V")
      (const v1 0)
      (invoke-static (v0 v1) "LCyc;.a:(LCyc;I)V")
      (invoke-static (v0 v1) "LCyc;.b:(LCyc;I)V")
      (return-object v0)
     )
    )
  )",
                        R"(
    (method (public static) "LCyc;.setFlag:(LCyc;)V"
     (
      (load-param-object v0)
      (const v1 1)
      (iput v1 v0 "LCyc;.flag:I")
      (return-void)
     )
    )
  )"})};
}

// `count(x)` writes x to `Counter.r` and calls `count(x + 1)` while x is
// below `Counter.limit`, which only `setLimit` writes. The search learns the
// limit in its second round; from then on, each pass over the call graph
// grows the argument of the recursive call by one.
Scope create_counter(int limit) {
  return {create_class("LCounter;", {"LCounter;.limit:I", "LCounter;.r:I"}, {R"(
    (method (public static) "LCounter;.count:(LCounter;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iget v0 "LCounter;.limit:I")
      (move-result-pseudo v2)
      (if-ge v1 v2 :done)
      (iput v1 v0 "LCounter;.r:I")
      (add-int/lit v3 v1 1)
      (invoke-static (v0 v3) "LCounter;.count:(LCounter;I)V")
      (:done)
      (return-void)
     )
    )
  )"},
                       {R"(
    (method (public static) "LCounter;.start:()LCounter;"
     (
      (new-instance "LCounter;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LCounter;.<init>:()V")
      (const v1 0)
      (invoke-static (v0 v1) "LCounter;.count:(LCounter;I)V")
      (return-object v0)
     )
    )
  )",
                        R"(
    (method (public static) "LCounter;.setLimit:(LCounter;)V"
     (
      (load-param-object v0)
      (const v1 )" + std::to_string(limit) +
                            R"()
      (iput v1 v0 "LCounter;.limit:I")
      (return-void)
     )
    )
  )"})};
}

// `Bar.setViaImm` reads the final field `Imm.a` of an object it constructs, in
// a try block, and then writes 9 to `Bar.g`. The immutable-attribute analysis
// answers the read itself, so the whole-program value of `Imm.a` is read only
// by the no-throw edge, which cuts off the rest of the block while `Imm.a` has
// no value. `Bar.callSet` calls it with `Bar.h`, which differs between the
// first run and a search, so a search cannot reuse the first run's result.
Scope create_write_behind_immutable_read() {
  ClassCreator imm(DexType::make_type("LImm;"));
  imm.set_super(type::java_lang_Object());
  imm.add_field(
      DexField::make_field("LImm;.a:I")->make_concrete(ACC_PUBLIC | ACC_FINAL));
  imm.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LImm;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iput v1 v0 "LImm;.a:I")
      (return-void)
     )
    )
  )"));
  auto* bar = create_class("LBar;", {"LBar;.g:I", "LBar;.h:I"}, {R"(
    (method (public static) "LBar;.setViaImm:(LBar;I)V"
     (
      (load-param-object v0)
      (load-param v5)
      (new-instance "LImm;")
      (move-result-pseudo-object v1)
      (const v2 5)
      (invoke-direct (v1 v2) "LImm;.<init>:(I)V")
      (.try_start a)
      (iget v1 "LImm;.a:I")
      (move-result-pseudo v3)
      (.try_end a)
      (const v4 9)
      (iput v4 v0 "LBar;.g:I")
      (return-void)
      (.catch (a) "Ljava/lang/NullPointerException;")
      (return-void)
     )
    )
  )"},
                           {R"(
    (method (public static) "LBar;.callSet:(LBar;)V"
     (
      (load-param-object v0)
      (iget v0 "LBar;.h:I")
      (move-result-pseudo v1)
      (invoke-static (v0 v1) "LBar;.setViaImm:(LBar;I)V")
      (return-void)
     )
    )
  )"});
  return {imm.create(), bar};
}

} // namespace

// Searching for field values with rerun_incrementally() after each growth
// reaches the same field values and analysis states as with a full run after
// each growth.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallyMatchesFullRuns) {
  auto* foo = create_class_with_int_field("LFoo;", "f",
                                          {kMakeWithConst, kSetG, kRelay});
  foo->add_field(DexField::make_field("LFoo;.g:I")->make_concrete(ACC_PUBLIC));
  Scope scope{foo, create_qux()};
  build_cfgs(scope);
  std::vector<std::string> fields{"LFoo;.g:I", "LQux;.q:I", "LQux;.r:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  auto incremental =
      search_field_values(this, scope, /* incremental */ true, fields);
  EXPECT_EQ(incremental.values, full.values);
  EXPECT_TRUE(states_match(incremental, full, scope));
  // `q` holds `g`'s values; `r` keeps growing and is widened.
  ConstantValue zero_or_seven =
      SignedConstantDomain(0).join(SignedConstantDomain(7));
  EXPECT_EQ(full.values[0], zero_or_seven);
  EXPECT_EQ(full.values[2], zero_or_seven);
  EXPECT_EQ(full.values[4], ConstantValue::top());
}

// Allowed no growing sweep at all, the incremental rerun sets the argument of
// `a` to Top as soon as the recursive call grows it, so `r` is Top where the
// full runs find 0 or 5: less precise, but sound.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallySetsArgumentsThatRecursionGrowsToTop) {
  auto scope = create_flagged_recursion();
  build_cfgs(scope);
  std::vector<std::string> fields{"LCyc;.r:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  EXPECT_EQ(
      full.values[0],
      ConstantValue(SignedConstantDomain(0).join(SignedConstantDomain(5))));
  auto incremental =
      search_field_values(this, scope, /* incremental */ true, fields);
  EXPECT_EQ(incremental.values, full.values);
  EXPECT_TRUE(states_match(incremental, full, scope));
  auto capped = search_field_values(this, scope, /* incremental */ true, fields,
                                    /* max_growing_sweeps */ 0);
  EXPECT_EQ(capped.values[0], ConstantValue::top());
  EXPECT_TRUE(states_match(capped, full, scope, /* at_least */ true));
}

// With a limit of 40, the argument of the recursive call grows for 40 passes
// over the call graph, longer than incremental reruns follow such growth
// before they set the argument to Top. Here the full runs lose the same
// precision, so both reach the same values.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallyMatchesFullRunsForALongRecursion) {
  auto scope = create_counter(40);
  build_cfgs(scope);
  std::vector<std::string> fields{"LCounter;.r:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  auto incremental =
      search_field_values(this, scope, /* incremental */ true, fields);
  EXPECT_EQ(incremental.values, full.values);
  EXPECT_TRUE(states_match(incremental, full, scope, /* at_least */ true));
}

// A method that calls itself counts as recursion too: allowed no growing sweep
// at all, the incremental reruns set the argument of `count` to Top as soon as
// its recursive call grows it, where the full runs know it is not negative.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallySetsArgumentsThatSelfRecursionGrowsToTop) {
  auto scope = create_counter(5);
  build_cfgs(scope);
  std::vector<std::string> fields{"LCounter;.r:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  auto capped = search_field_values(this, scope, /* incremental */ true, fields,
                                    /* max_growing_sweeps */ 0);
  EXPECT_TRUE(states_match(capped, full, scope, /* at_least */ true));
  EXPECT_FALSE(states_match(capped, full, scope));
}

// With a limit of 5, the incremental reruns follow the recursion to the end.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallyMatchesFullRunsForAShortRecursion) {
  auto scope = create_counter(5);
  build_cfgs(scope);
  std::vector<std::string> fields{"LCounter;.r:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  auto incremental =
      search_field_values(this, scope, /* incremental */ true, fields);
  EXPECT_EQ(incremental.values, full.values);
  EXPECT_TRUE(states_match(incremental, full, scope));
}

// When `Rev.f` grows back to unknown, `writeG` switches to the result cached
// before the search, and its write to `Rev.g` must be seen.
TEST_F(InterproceduralConstantPropagationTest,
       rerunIncrementallySeesTheWritesOfACacheEntryThatMatchesAgain) {
  auto scope = create_revived_cache_entry();
  build_cfgs(scope);
  std::vector<std::string> fields{"LRev;.g:I"};
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  EXPECT_EQ(
      full.values[0],
      ConstantValue(SignedConstantDomain(0).join(SignedConstantDomain(1))));
  auto incremental =
      search_field_values(this, scope, /* incremental */ true, fields);
  EXPECT_EQ(incremental.values, full.values);
  EXPECT_TRUE(states_match(incremental, full, scope));
}

// When `Imm.a` gets its value, the cached result of `setViaImm` must be redone,
// or its write of 9 to `Bar.g` would stay unseen.
TEST_F(InterproceduralConstantPropagationTest,
       cachedResultIsRedoneWhenAValueReadOnAnEdgeGrows) {
  auto scope = create_write_behind_immutable_read();
  build_cfgs(scope);
  immutable_state::analyze_constructors(scope, &m_immut_analyzer_state);
  ConstantValue zero_or_nine =
      SignedConstantDomain(0).join(SignedConstantDomain(9));
  for (bool incremental : {false, true}) {
    auto search = search_field_values(this, scope, incremental, {"LBar;.g:I"});
    EXPECT_EQ(search.values[0], zero_or_nine) << incremental;
  }
}

// `copyPlusOne` writes `Foo.f + 1` to `f`. After `f` grows from no value to 7,
// its cached result no longer matches, so the incremental rerun analyzes it
// again and sees the write of 8.
TEST_F(FieldSearchTest, rerunIncrementallyAnalyzesAStaleMethodAgain) {
  ClassCreator copier(DexType::make_type("LCopier;"));
  copier.set_super(type::java_lang_Object());
  add_methods(&copier, {}, {R"(
    (method (public static) "LCopier;.copyPlusOne:(LFoo;)V"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v1)
      (add-int/lit v1 v1 1)
      (iput v1 v0 "LFoo;.f:I")
      (return-void)
     )
    )
  )"});
  scope.push_back(copier.create());
  build_cfgs(scope);
  auto fp_iter = bootstrap();
  fp_iter->set_whole_program_state(start(*fp_iter));
  fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
  auto writes = fp_iter->collect_field_writes();
  EXPECT_EQ(writes.get(f), SignedConstantDomain(7));
  fp_iter->grow_field_values(writes, 2);
  EXPECT_EQ(fp_iter->rerun_incrementally(kMaxGrowingSweeps).get(f),
            SignedConstantDomain(8));
}

// `send(p, z)` writes `z` to `Loop.w` and, unless `z` is 0, calls `send(p, 0)`;
// `start` calls it only on a path that cannot run. The run first analyzes
// `send` with no arguments, which the analysis treats as unknown ones, so its
// recursive call passes 0. Analyzed with 0, `send` no longer calls itself, so
// the run ends with no arguments for `send`, which its latest analysis did not
// use. The collected writes are those under no arguments.
TEST_F(InterproceduralConstantPropagationTest,
       collectFieldWritesUsesTheFinalArgumentsOfARecursion) {
  Scope scope{create_class("LLoop;", {"LLoop;.w:I"}, {R"(
    (method (public static) "LLoop;.send:(LLoop;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LLoop;.w:I")
      (if-eqz v1 :done)
      (const v2 0)
      (invoke-static (v0 v2) "LLoop;.send:(LLoop;I)V")
      (:done)
      (return-void)
     )
    )
  )"},
                           {R"(
    (method (public static) "LLoop;.start:(LLoop;)V"
     (
      (load-param-object v0)
      (const v1 0)
      (if-eqz v1 :done)
      (invoke-static (v0 v1) "LLoop;.send:(LLoop;I)V")
      (:done)
      (return-void)
     )
    )
  )"})};
  build_cfgs(scope);
  auto fp_iter = bootstrap_recording_field_writes(this, scope);
  const auto* send = DexMethod::get_method("LLoop;.send:(LLoop;I)V")->as_def();
  EXPECT_TRUE(fp_iter->get_entry_state_at(fp_iter->get_call_graph().node(send))
                  .get(CURRENT_PARTITION_LABEL)
                  .is_bottom());
  const auto* w = DexField::get_field("LLoop;.w:I")->as_def();
  EXPECT_TRUE(fp_iter->collect_field_writes().get(w).is_top());
}

// `pass` passes `P.f`, which `setF` sets to 7, to `sink`, which writes it to
// `P.h`. Collecting the writes after `f` grows analyzes `pass` again; the
// incremental rerun must still pass the grown argument on to `sink`.
TEST_F(InterproceduralConstantPropagationTest,
       collectFieldWritesBeforeARerunKeepsTheGrowth) {
  Scope scope{create_class("LP;", {"LP;.f:I", "LP;.h:I"}, {R"(
    (method (public static) "LP;.sink:(LP;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LP;.h:I")
      (return-void)
     )
    )
  )"},
                           {R"(
    (method (public static) "LP;.setF:(LP;)V"
     (
      (load-param-object v0)
      (const v1 7)
      (iput v1 v0 "LP;.f:I")
      (return-void)
     )
    )
  )",
                            R"(
    (method (public static) "LP;.pass:(LP;)V"
     (
      (load-param-object v0)
      (iget v0 "LP;.f:I")
      (move-result-pseudo v1)
      (invoke-static (v0 v1) "LP;.sink:(LP;I)V")
      (return-void)
     )
    )
  )"})};
  build_cfgs(scope);
  std::vector<std::string> fields{"LP;.h:I"};
  auto search = search_field_values(this, scope, /* incremental */ true, fields,
                                    kMaxGrowingSweeps,
                                    /* collect_before_rerun */ true);
  EXPECT_EQ(
      search.values[0],
      ConstantValue(SignedConstantDomain(0).join(SignedConstantDomain(7))));
  auto full = search_field_values(this, scope, /* incremental */ false, fields);
  EXPECT_EQ(search.values, full.values);
  EXPECT_TRUE(states_match(search, full, scope));
}

namespace {

const char* const kCopyPreservingField = R"(
    (method (public static) "LFoo;.copy:(LFoo;)LFoo;"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v1) "LFoo;.<init>:(I)V")
      (return-object v2)
     )
    )
)";

// IPCP's configuration with the field search allowed `rounds` rounds.
InterproceduralConstantPropagationPass::Config config_with_field_search(
    size_t rounds, size_t widening_delay = 2) {
  auto config = config_with_heap_analysis();
  config.field_search_max_rounds = rounds;
  config.field_search_widening_delay = widening_delay;
  return config;
}

// Runs IPCP with `config` over `scope`, and returns whether `LFoo;.read` then
// returns the constant 7.
bool read_folds(const Scope& scope,
                ConfigFiles& conf,
                const InterproceduralConstantPropagationPass::Config& config) {
  run_ipcp(scope, conf, config);
  return contains_const("LFoo;.read:(LFoo;)I", 7);
}

bool read_folds_with_copy(
    ConfigFiles& conf,
    const InterproceduralConstantPropagationPass::Config& config) {
  return read_folds(
      {create_class_with_int_field(
          "LFoo;", "f", {kMakeWithConst, kRead, kCopyPreservingField})},
      conf, config);
}

} // namespace

// The field is 7 in every instance: `copy` passes the field of an existing
// instance back to the constructor. Descending from Top cannot show this,
// because the value written depends on the value read.
TEST_F(InterproceduralConstantPropagationTest,
       fieldPreservedByCopyStaysUnknownWithoutFieldSearch) {
  EXPECT_FALSE(read_folds_with_copy(conf, config_with_field_search(0)));
}

TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldPreservedByCopy) {
  EXPECT_TRUE(read_folds_with_copy(conf, config_with_field_search(4)));
}

// Two rounds are exactly enough: the first adds the 7 that the constructor
// call writes, and the second finds that `copy` writes back only 7.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldPreservedByCopyInTwoRounds) {
  EXPECT_TRUE(read_folds_with_copy(conf, config_with_field_search(2)));
}

// Without the refinement after the search, the field values the search proves
// are what the transformation uses.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldPreservedByCopyWithoutRefinement) {
  auto config = config_with_field_search(4);
  config.max_heap_analysis_iterations = 0;
  EXPECT_TRUE(read_folds_with_copy(conf, config));
}

// Apps run IPCP with the multiple-callee call graph, which the whole-program
// state then also uses. The search proves the field there too, and a search
// cut short by the limit is discarded there too.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchWorksWithTheMultipleCalleeCallGraph) {
  auto config = config_with_field_search(4);
  config.use_multiple_callee_callgraph = true;
  EXPECT_TRUE(read_folds_with_copy(conf, config));
}

TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchCutShortIsDiscardedWithTheMultipleCalleeCallGraph) {
  auto config = config_with_field_search(1);
  config.use_multiple_callee_callgraph = true;
  EXPECT_FALSE(read_folds_with_copy(conf, config));
}

// The value comes from a static field set by its class initializer, like a
// Kotlin companion object's `val` used as a constructor default.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldFromAStaticPreservedByCopy) {
  ClassCreator bar(DexType::make_type("LBar;"));
  bar.set_super(type::java_lang_Object());
  bar.add_field(DexField::make_field("LBar;.s:I")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  bar.add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LBar;.<clinit>:()V"
     (
      (const v0 7)
      (sput v0 "LBar;.s:I")
      (return-void)
     )
    )
  )"));
  const char* make_from_static = R"(
    (method (public static) "LFoo;.make:()LFoo;"
     (
      (sget "LBar;.s:I")
      (move-result-pseudo v1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LFoo;.<init>:(I)V")
      (return-object v0)
     )
    )
  )";
  EXPECT_TRUE(read_folds(
      {bar.create(),
       create_class_with_int_field(
           "LFoo;", "f", {make_from_static, kRead, kCopyPreservingField})},
      conf, config_with_field_search(4)));
}

// `f` goes from Bottom to 7 and stays there. Getting a first value is not
// growth, so even with no widening delay `f` is not widened.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchDoesNotCountFirstValueAsGrowth) {
  EXPECT_TRUE(read_folds_with_copy(conf, config_with_field_search(4, 0)));
}

// The Kotlin `copy$default` shape: each parameter is either the caller's
// argument or, when its mask bit is set, the field of the source instance.
// Every caller sets the bit for `f`, so `f` keeps its value.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldPreservedByMaskedCopy) {
  const char* const masked_copy = R"(
    (method (public static) "LFoo;.copy:(LFoo;II)LFoo;"
     (
      (load-param-object v0)
      (load-param v1)
      (load-param v2)
      (and-int/lit v3 v2 1)
      (if-eqz v3 :use_arg)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v1)
      (:use_arg)
      (new-instance "LFoo;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v1) "LFoo;.<init>:(I)V")
      (return-object v4)
     )
    )
  )";
  const char* const update = R"(
    (method (public static) "LFoo;.update:(LFoo;)LFoo;"
     (
      (load-param-object v0)
      (const v1 0)
      (const v2 3)
      (invoke-static (v0 v1 v2) "LFoo;.copy:(LFoo;II)LFoo;")
      (move-result-object v0)
      (const v2 1)
      (invoke-static (v0 v1 v2) "LFoo;.copy:(LFoo;II)LFoo;")
      (move-result-object v0)
      (return-object v0)
     )
    )
  )";
  EXPECT_TRUE(read_folds(
      {create_class_with_int_field(
          "LFoo;", "f", {kMakeWithConst, kRead, update}, {masked_copy})},
      conf, config_with_field_search(4)));
}

namespace {

// `f` is 7 or 8, but it reaches 8 only in the second round: `make8` reads it
// from `Bar.g`, which has no value until the first round records `Bar`'s
// constructor. One growth is within the widening delay, so `f` keeps the range
// [7, 8] and `positive` folds its branch; with no delay, `f` is widened to Top
// instead.
Scope make_field_growing_once() {
  const char* const make8 = R"(
    (method (public static) "LFoo;.make8:()LFoo;"
     (
      (new-instance "LBar;")
      (move-result-pseudo-object v2)
      (const v1 8)
      (invoke-direct (v2 v1) "LBar;.<init>:(I)V")
      (iget v2 "LBar;.g:I")
      (move-result-pseudo v1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LFoo;.<init>:(I)V")
      (return-object v0)
     )
    )
  )";
  const char* const positive = R"(
    (method (public static) "LFoo;.positive:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.f:I")
      (move-result-pseudo v1)
      (if-lez v1 :not_positive)
      (const v2 1)
      (return v2)
      (:not_positive)
      (const v2 0)
      (return v2)
     )
    )
  )";
  return {create_class_with_int_field("LBar;", "g", {}),
          create_class_with_int_field(
              "LFoo;", "f",
              {kMakeWithConst, make8, positive, kCopyPreservingField})};
}

} // namespace

TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchKeepsFieldThatGrowsWithinTheDelay) {
  run_ipcp(make_field_growing_once(), conf, config_with_field_search(8, 1));
  EXPECT_FALSE(contains_const("LFoo;.positive:(LFoo;)I", 0));
}

TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchWidensFieldThatGrowsBeyondTheDelay) {
  run_ipcp(make_field_growing_once(), conf, config_with_field_search(8, 0));
  EXPECT_TRUE(contains_const("LFoo;.positive:(LFoo;)I", 0));
}

namespace {

// `Baz.h` doubles in every round: `make` writes 1 and `inc` writes the field
// shifted left by one, and the analysis keeps the known bits of each value,
// so `h` keeps growing for many rounds. `Foo.f` is preserved by a copy, so it
// is proven once the search converges.
Scope make_field_growing_every_round() {
  const char* const make_baz = R"(
    (method (public static) "LBaz;.make:()LBaz;"
     (
      (new-instance "LBaz;")
      (move-result-pseudo-object v0)
      (const v1 1)
      (invoke-direct (v0 v1) "LBaz;.<init>:(I)V")
      (return-object v0)
     )
    )
  )";
  const char* const inc = R"(
    (method (public static) "LBaz;.inc:(LBaz;)LBaz;"
     (
      (load-param-object v0)
      (iget v0 "LBaz;.h:I")
      (move-result-pseudo v1)
      (shl-int/lit v1 v1 1)
      (new-instance "LBaz;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v1) "LBaz;.<init>:(I)V")
      (return-object v2)
     )
    )
  )";
  return {create_class_with_int_field("LBaz;", "h", {make_baz, inc}),
          create_class_with_int_field(
              "LFoo;", "f", {kMakeWithConst, kRead, kCopyPreservingField})};
}

} // namespace

// Widening `Baz.h` lets the search converge within the limit.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchWidensFieldThatKeepsGrowing) {
  EXPECT_TRUE(read_folds(make_field_growing_every_round(), conf,
                         config_with_field_search(10)));
}

// Without widening within the limit, `Baz.h` keeps the search from
// converging, so it is discarded and `Foo.f` stays unknown as well.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchDiscardsSearchThatKeepsGrowing) {
  EXPECT_FALSE(read_folds(make_field_growing_every_round(), conf,
                          config_with_field_search(10, 10)));
}

// `Bar` is only ever constructed from another `Bar`, so the search proves
// that `Bar.g` never holds a value: no Bar can exist. Reading `g` therefore
// always throws, here into a handler that writes 99 to `Foo.f`, so `f` is not
// always 7.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchKeepsHandlerOfReadOfFieldWithoutValue) {
  const char* const copy_ctor = R"(
    (method (public constructor) "LBar;.<init>:(LBar;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget v1 "LBar;.g:I")
      (move-result-pseudo v2)
      (iput v2 v0 "LBar;.g:I")
      (return-void)
     )
    )
  )";
  const char* const copy = R"(
    (method (public static) "LBar;.copy:(LBar;)LBar;"
     (
      (load-param-object v0)
      (new-instance "LBar;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1 v0) "LBar;.<init>:(LBar;)V")
      (return-object v1)
     )
    )
  )";
  const char* const read_g_or_set_f = R"(
    (method (public static) "LBar;.readGOrSetF:(LBar;LFoo;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (.try_start a)
      (iget v0 "LBar;.g:I")
      (move-result-pseudo v2)
      (.try_end a)
      (return-void)
      (.catch (a) "Ljava/lang/NullPointerException;")
      (const v3 99)
      (iput v3 v1 "LFoo;.f:I")
      (return-void)
     )
    )
  )";
  ClassCreator bar(DexType::make_type("LBar;"));
  bar.set_super(type::java_lang_Object());
  bar.add_field(DexField::make_field("LBar;.g:I")->make_concrete(ACC_PUBLIC));
  bar.add_method(assembler::method_from_string(copy_ctor));
  for (const auto* root : {copy, read_g_or_set_f}) {
    auto* m = assembler::method_from_string(root);
    m->rstate.set_root();
    bar.add_method(m);
  }
  run_ipcp({bar.create(),
            create_class_with_int_field("LFoo;", "f", {kMakeWithConst, kRead})},
           conf, config_with_field_search(4));
  EXPECT_FALSE(contains_const("LFoo;.read:(LFoo;)I", 7));
}

// One round only reaches the field's first written value; the round that
// would show the copy preserves it does not run, so the search is discarded
// and the field stays unknown.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchDiscardsSearchCutShortByTheLimit) {
  EXPECT_FALSE(read_folds_with_copy(conf, config_with_field_search(1)));
}

namespace {

// Runs IPCP with the search, but without the refinement after it, over the
// recursion of create_flagged_recursion(), and returns whether `isNegative`
// still returns 1 somewhere, that is, whether its branch on `Cyc.r` stayed.
bool is_negative_keeps_branch(ConfigFiles& conf, size_t max_growing_sweeps) {
  auto scope = create_flagged_recursion();
  auto* is_negative = assembler::method_from_string(R"(
    (method (public static) "LCyc;.isNegative:(LCyc;)I"
     (
      (load-param-object v0)
      (iget v0 "LCyc;.r:I")
      (move-result-pseudo v1)
      (if-gez v1 :not_negative)
      (const v2 1)
      (return v2)
      (:not_negative)
      (const v2 0)
      (return v2)
     )
    )
  )");
  is_negative->rstate.set_root();
  type_class(DexType::get_type("LCyc;"))->add_method(is_negative);
  auto config = config_with_field_search(10);
  config.max_heap_analysis_iterations = 0;
  config.field_search_max_growing_sweeps = max_growing_sweeps;
  run_ipcp(scope, conf, config);
  return contains_const("LCyc;.isNegative:(LCyc;)I", 1);
}

} // namespace

// `Cyc.r` is 0 or 5, so `isNegative` always returns 0.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchProvesFieldWrittenAlongARecursion) {
  EXPECT_FALSE(is_negative_keeps_branch(conf, /* max_growing_sweeps */ 20));
}

// Allowed no growing sweep, the search's incremental reruns set the argument
// of `a` to Top as soon as the recursive call grows it, so `Cyc.r` is unknown
// and the branch stays.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchPassesTheGrowingSweepsLimitToTheReruns) {
  EXPECT_TRUE(is_negative_keeps_branch(conf, /* max_growing_sweeps */ 0));
}

// `Bar.g` is 9 once `callSet` ran, so its read must not fold to 0. Without the
// refinement after the search, the search's result is what the read sees.
TEST_F(InterproceduralConstantPropagationTest,
       fieldSearchSeesWriteBehindACutOffRead) {
  auto config = config_with_heap_analysis();
  config.max_heap_analysis_iterations = 0;
  config.field_search_max_rounds = 4;
  auto scope = create_write_behind_immutable_read();
  auto* read_g = assembler::method_from_string(R"(
    (method (public static) "LBar;.readG:(LBar;)I"
     (
      (load-param-object v0)
      (iget v0 "LBar;.g:I")
      (move-result-pseudo v1)
      (return v1)
     )
    )
  )");
  read_g->rstate.set_root();
  type_class(DexType::get_type("LBar;"))->add_method(read_g);
  run_ipcp(scope, conf, config);
  EXPECT_FALSE(contains_const("LBar;.readG:(LBar;)I", 0));
}
