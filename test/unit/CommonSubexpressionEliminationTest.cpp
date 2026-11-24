/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "CommonSubexpressionElimination.h"
#include "Creators.h"
#include "Debug.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "Purity.h"
#include "RedexTest.h"
#include "Walkers.h"

class CommonSubexpressionEliminationTest : public RedexTest {
 public:
  CommonSubexpressionEliminationTest() {
    // The tests need java.lang.Object to resolve to a DexClass to build a
    // proper scope.
    create_object_class();
  }
};

void test(const Scope& scope,
          const std::string& code_str,
          const std::string& expected_str,
          size_t expected_instructions_eliminated,
          bool is_static = true,
          bool is_init_or_clinit = false,
          DexType* declaring_type = nullptr,
          DexTypeList* args = DexTypeList::make_type_list({}),
          const UnorderedSet<const DexString*>& finalish_field_names = {}) {
  [[maybe_unused]] auto* field_a =
      DexField::make_field("LFoo;.a:I")->make_concrete(ACC_PUBLIC);

  [[maybe_unused]] auto* field_b =
      DexField::make_field("LFoo;.b:I")->make_concrete(ACC_PUBLIC);

  [[maybe_unused]] auto* field_s =
      DexField::make_field("LFoo;.s:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);

  [[maybe_unused]] auto* field_t =
      DexField::make_field("LFoo;.t:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);

  [[maybe_unused]] auto* field_u =
      DexField::make_field("LFoo;.u:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);

  [[maybe_unused]] auto* field_v =
      DexField::make_field("LFoo;.v:I")
          ->make_concrete(ACC_PUBLIC | ACC_VOLATILE);

  auto code = assembler::ircode_from_string(code_str);
  auto expected = assembler::ircode_from_string(expected_str);

  code->build_cfg();
  walk::code(scope, [&](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto pure_methods = get_pure_methods();
  UnorderedSet<const DexField*> finalish_fields;
  cse_impl::SharedState shared_state(pure_methods, finalish_field_names,
                                     finalish_fields);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  method::ClInitHasNoSideEffectsPredicate clinit_has_no_side_effects =
      [&](const DexType* type) {
        return init_classes_with_side_effects.refine(type) == nullptr;
      };
  shared_state.init_scope(scope, clinit_has_no_side_effects);
  cse_impl::CommonSubexpressionElimination cse(&shared_state, code->cfg(),
                                               is_static, is_init_or_clinit,
                                               declaring_type, args);
  cse.patch();
  code->clear_cfg();
  walk::code(scope, [&](DexMethod*, IRCode& code) { code.clear_cfg(); });
  auto stats = cse.get_stats();

  EXPECT_EQ(expected_instructions_eliminated, stats.instructions_eliminated)
      << assembler::to_string(code.get()).c_str();

  EXPECT_CODE_EQ(code.get(), expected.get());
};

TEST_F(CommonSubexpressionEliminationTest, simple) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (add-int v1 v0 v0)
      (add-int v2 v0 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (add-int v1 v0 v0)
      (move v3 v1)
      (add-int v2 v0 v0)
      (move v2 v3)
    )
  )";

  always_assert(type::java_lang_Object());
  always_assert(type_class(type::java_lang_Object()));
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, pre_values) {
  // By not initializing v0, it will start out as 'top', and a pre-value will
  // be used internally to recover from that situation and still unify the
  // add-int instructions.
  const auto* code_str = R"(
    (
      (add-int v1 v0 v0)
      (add-int v2 v0 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (add-int v1 v0 v0)
      (move v3 v1)
      (add-int v2 v0 v0)
      (move v2 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, mix) {
  const auto* code_str = R"(
    (
      (const v0 1)
      (const v1 2)
      (add-int v2 v0 v0)
      (add-int v3 v1 v1)
      (add-int v4 v0 v0)
      (add-int v5 v1 v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 1)
      (const v1 2)
      (add-int v2 v0 v0)
      (move v6 v2)
      (add-int v3 v1 v1)
      (move v7 v3)
      (add-int v4 v0 v0)
      (move v4 v6)
      (add-int v5 v1 v1)
      (move v5 v7)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, many) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (add-int v1 v0 v0)
      (add-int v2 v0 v0)
      (add-int v3 v0 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (add-int v1 v0 v0)
      (move v4 v1)
      (add-int v2 v0 v0)
      (move v2 v4)
      (add-int v3 v0 v0)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, registers_dont_matter) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (add-int v2 v0 v1)
      (add-int v3 v1 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (add-int v2 v0 v1)
      (move v4 v2)
      (add-int v3 v1 v0)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, commutative) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 1)
      (add-int v2 v0 v1)
      (add-int v3 v1 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 1)
      (add-int v2 v0 v1)
      (move v4 v2)
      (add-int v3 v1 v0)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, wide) {
  const auto* code_str = R"(
    (
      (const-wide v0 0)
      (add-long v2 v0 v0)
      (add-long v4 v0 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const-wide v0 0)
      (add-long v2 v0 v0)
      (move-wide v6 v2)
      (add-long v4 v0 v0)
      (move-wide v4 v6)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, object) {
  const auto* code_str = R"(
    (
      (const-string "hello")
      (move-result-pseudo-object v0)
      (const-string "hello")
      (move-result-pseudo-object v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (const-string "hello")
      (move-result-pseudo-object v0)
      (move-object v2 v0)
      (const-string "hello")
      (move-result-pseudo-object v1)
      (move-object v1 v2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, iget) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, iget_volatile) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.v:I")
      (move-result-pseudo v1)
      (iget v0 "LFoo;.v:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, affected_by_barrier) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, safe_methods_are_not_barriers) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static (v1) "Ljava/lang/Math;.abs:(I)I")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static (v1) "Ljava/lang/Math;.abs:(I)I")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest,
       safe_virtual_methods_with_exact_types_are_not_barriers) {
  ClassCreator creator(DexType::make_type("Ljava/util/ArrayList;"));
  creator.set_super(type::java_lang_Object());

  auto* method = dynamic_cast<DexMethod*>(
      DexMethod::make_method("Ljava/util/ArrayList;.<init>:()V"));
  method->set_access(ACC_PUBLIC);
  method->set_external();
  // method->set_code(assembler::ircode_from_string("((return-void))"));
  creator.add_method(method);

  method = dynamic_cast<DexMethod*>(DexMethod::make_method(
      "Ljava/util/ArrayList;.add:(Ljava/lang/Object;)Z"));
  method->set_access(ACC_PUBLIC);
  method->set_virtual(true);
  method->set_external();
  // method->set_code(assembler::ircode_from_string("((return-void))"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (new-instance "Ljava/util/ArrayList;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/util/ArrayList;.<init>:()V")
      (invoke-virtual (v2 v0) "Ljava/util/ArrayList;.add:(Ljava/lang/Object;)Z")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v3)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v4 v1)
      (new-instance "Ljava/util/ArrayList;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/util/ArrayList;.<init>:()V")
      (invoke-virtual (v2 v0) "Ljava/util/ArrayList;.add:(Ljava/lang/Object;)Z")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v3)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object()), creator.create()}, code_str,
       expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, recovery_after_barrier) {
  // at a barrier, the mappings have been reset, but afterwards cse kicks in as
  // expected
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v3)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v4 v2)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v3)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, unaffected_by_barrier) {
  const auto* code_str = R"(
    (
      (const-string "hello")
      (move-result-pseudo-object v0)
      (invoke-static () "LWhat;.ever:()V")
      (const-string "hello")
      (move-result-pseudo-object v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (const-string "hello")
      (move-result-pseudo-object v0)
      (move-object v2 v0)
      (invoke-static () "LWhat;.ever:()V")
      (const-string "hello")
      (move-result-pseudo-object v1)
      (move-object v1 v2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, top_move_tracking) {
  const auto* code_str = R"(
    (
      (move-object v1 v0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v3)
    )
  )";
  const auto* expected_str = R"(
    (
      (move-object v1 v0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v4 v2)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v3)
      (move v3 v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest,
       empty_non_true_virtual_methods_are_not_barriers) {
  ClassCreator creator(DexType::make_type("LTest0;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest0;.test0:()V")
                     ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-virtual (v0) "LTest0;.test0:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-virtual (v0) "LTest0;.test0:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest,
       empty_true_virtual_methods_are_not_barriers) {

  // define base type

  ClassCreator base_creator(DexType::make_type("LTestBase;"));
  base_creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTestBase;.m:()V")
                     ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  base_creator.add_method(method);
  DexClass* base_class = base_creator.create();

  // define derived type

  ClassCreator derived_creator(DexType::make_type("LTestDerived;"));
  derived_creator.set_super(base_class->get_type());

  method = DexMethod::make_method("LTestDerived;.m:()V")
               ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  derived_creator.add_method(method);
  DexClass* derived_class = derived_creator.create();

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-virtual (v0) "LTestBase;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-virtual (v0) "LTestBase;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), base_class, derived_class},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest,
       non_empty_overriding_virtual_methods_are_barriers) {

  // define base type

  ClassCreator base_creator(DexType::make_type("LTestBase;"));
  base_creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTestBase;.m:()V")
                     ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  base_creator.add_method(method);
  DexClass* base_class = base_creator.create();

  // define derived type

  ClassCreator derived_creator(DexType::make_type("LTestDerived;"));
  derived_creator.set_super(base_class->get_type());

  method = DexMethod::make_method("LTestDerived;.m:()V")
               ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.a:I")
      (return-void)
    )
  )"));
  derived_creator.add_method(method);
  DexClass* derived_class = derived_creator.create();

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-virtual (v0) "LTestBase;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;

  test(Scope{type_class(type::java_lang_Object()), base_class, derived_class},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest,
       empty_static_methods_are_not_barriers) {
  ClassCreator creator(DexType::make_type("LTest1;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest1;.test1:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LTest1;.test1:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LTest1;.test1:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest, benign_after_inlining_once) {
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LA;.m:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
     (
       (const v0 0)
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v1)
       (invoke-static () "LB;.m:()V")
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v2)
     )
   )"));
  a_creator.add_method(method);

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(type::java_lang_Object());

  method = DexMethod::make_method("LB;.m:()V")
               ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  b_creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), a_creator.create(),
             b_creator.create()},
       code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, benign_after_inlining_twice) {
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LA;.m:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
     (
       (const v0 0)
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v1)
       (invoke-static () "LB;.m:()V")
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v2)
     )
   )"));
  a_creator.add_method(method);

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(type::java_lang_Object());

  method = DexMethod::make_method("LB;.m:()V")
               ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
     (
       (const v0 0)
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v1)
       (invoke-static () "LC;.m:()V")
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v2)
     )
   )"));
  b_creator.add_method(method);

  ClassCreator c_creator(DexType::make_type("LC;"));
  c_creator.set_super(type::java_lang_Object());

  method = DexMethod::make_method("LC;.m:()V")
               ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string("((return-void))"));
  c_creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), a_creator.create(),
             b_creator.create(), c_creator.create()},
       code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, not_benign_after_inlining_once) {
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LA;.m:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
     (
       (const v0 0)
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v1)
       (invoke-static () "LB;.m:()V")
       (iget v0 "LFoo;.a:I")
       (move-result-pseudo v2)
     )
   )"));
  a_creator.add_method(method);

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(type::java_lang_Object());

  method = DexMethod::make_method("LB;.m:()V")
               ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.a:I")
      (return-void)
    )
  )"));
  b_creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;

  test(Scope{type_class(type::java_lang_Object()), a_creator.create(),
             b_creator.create()},
       code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_relevant_i_barrier) {
  ClassCreator creator(DexType::make_type("LTest2;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest2;.test2:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.a:I")
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LTest2;.test2:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_relevant_s_barrier) {
  ClassCreator creator(DexType::make_type("LTest3;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest3;.test3:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
      (invoke-static () "LTest3;.test3:()V")
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = code_str;

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_relevant_a_barrier) {
  ClassCreator creator(DexType::make_type("LTest4;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest4;.test4:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput v0 v1 v2)
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (aget v0 v1)
      (move-result-pseudo v2)
      (invoke-static () "LTest4;.test4:()V")
      (aget v0 v1)
      (move-result-pseudo v3)
    )
  )";
  const auto* expected_str = code_str;

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_irrelevant_i_barrier) {
  ClassCreator creator(DexType::make_type("LTest2;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest2;.test2:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.b:I")
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LTest2;.test2:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LTest2;.test2:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_irrelevant_s_barrier) {
  ClassCreator creator(DexType::make_type("LTest5;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest5;.test5:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (sget "LFoo;.t:I")
      (move-result-pseudo v0)
      (invoke-static () "LTest5;.test5:()V")
      (sget "LFoo;.t:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (sget "LFoo;.t:I")
      (move-result-pseudo v0)
      (move v2 v0)
      (invoke-static () "LTest5;.test5:()V")
      (sget "LFoo;.t:I")
      (move-result-pseudo v1)
      (move v1 v2)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_irrelevant_a_barrier) {
  ClassCreator creator(DexType::make_type("LTest6;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest6;.test6:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput-object v0 v1 v2)
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (aget v0 v1)
      (move-result-pseudo v2)
      (invoke-static () "LTest6;.test6:()V")
      (aget v0 v1)
      (move-result-pseudo v3)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (aget v0 v1)
      (move-result-pseudo v2)
      (move v4 v2)
      (invoke-static () "LTest6;.test6:()V")
      (aget v0 v1)
      (move-result-pseudo v3)
      (move v3 v4)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest, iget_unrelated_iput) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (iput v1 v0 "LFoo;.b:I")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (iput v1 v0 "LFoo;.b:I")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, aget_unrelated_aput) {
  const auto* code_str = R"(
    (
      (aget v0 v1)
      (move-result-pseudo v2)
      (aput-object v0 v0 v1)
      (aget v0 v1)
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (aget v0 v1)
      (move-result-pseudo v2)
      (move v3 v2)
      (aput-object v0 v0 v1)
      (aget v0 v1)
      (move-result-pseudo v2)
      (move v2 v3)    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, aget_related_aput) {
  const auto* code_str = R"(
    (
      (aget v0 v1)
      (move-result-pseudo v2)
      (aput v2 v0 v3)
      (aget v0 v1)
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, aput_related_aget) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput v0 v1 v2)
      (aget v1 v2)
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput v0 v1 v2)
      (move v3 v0)
      (aget v1 v2)
      (move-result-pseudo v0)
      (move v0 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, aput_object_related_aget_object) {
  // We don't forward aput-object values to aget-object. (In general, a
  // check-cast instruction needs to get introduced, but that isn't implemented
  // yet.)
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput-object v0 v1 v2)
      (aget-object v1 v2)
      (move-result-pseudo v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, code_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, iput_related_iget) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.a:I")
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.a:I")
      (move v2 v0)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v0)
      (move v0 v2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, sput_related_sget) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (move v1 v0)
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
      (move v0 v1)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, sput_related_sget_with_barrier) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (invoke-static () "LWhat;.ever:()V")
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, volatile_iput_related_iget) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (const v1 0)
      (iput v0 v1 "LFoo;.v:I")
      (iget v1 "LFoo;.v:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, simple_with_put) {
  // The initial sget is there just so that CSE actually tracks the sput as a
  // potentially interesting operation
  const auto* code_str = R"(
    (
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
      (const v0 0)
      (add-int v1 v0 v0)
      (sput v0 "LFoo;.s:I")
      (add-int v1 v0 v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
      (const v0 0)
      (add-int v1 v0 v0)
      (move v3 v1)
      (sput v0 "LFoo;.s:I")
      (add-int v1 v0 v0)
      (move v1 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap) {
  const auto* code_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (return-wide v0)
    )
  )";

  const auto* expected_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (const-wide v0 3)
      (return-wide v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap_1) {
  const auto* code_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Number;.longValue:()J")
      (move-result-wide v0)
      (return-wide v0)
    )
  )";

  const auto* expected_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (check-cast v0 "Ljava/lang/Long;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (const-wide v0 3)
      (return-wide v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap_2) {
  const auto* code_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (const-wide v2 4)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v2)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (invoke-virtual (v2) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v2)
      (add-long v4 v0 v2)
      (return-wide v4)
    )
  )";

  const auto* expected_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (const-wide v2 4)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v2)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (const-wide v0 3)
      (invoke-virtual (v2) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v2)
      (const-wide v2 4)
      (add-long v4 v0 v2)
      (return-wide v4)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap_3) {
  const auto* code_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (const-wide v2 4)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v2)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (invoke-virtual (v2) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v2)
      (add-long v4 v0 v2)
      (return-wide v4)
    )
  )";

  const auto* expected_str = R"(
    (
      (const-wide v0 3)
      (invoke-static (v0) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v0)
      (const-wide v2 4)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v2)
      (invoke-virtual (v0) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v0)
      (const-wide v0 3)
      (invoke-virtual (v2) "Ljava/lang/Long;.longValue:()J")
      (move-result-wide v2)
      (const-wide v2 4)
      (add-long v4 v0 v2)
      (return-wide v4)
    )
  )";

  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap_4) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (iput-boolean v0 v4 "LX/002;.chromeVisibility:Z")
    )
  )";

  const auto* expected_str = R"(
    (
      (const v0 0)
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (const v0 0)
      (iput-boolean v0 v4 "LX/002;.chromeVisibility:Z")
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, wrap_and_unwrap_5) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 1)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (iput-boolean v0 v4 "LX/002;.chromeVisibility:Z")
    )
  )";

  const auto* expected_str = R"(
    (
      (const v0 0)
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 1)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (const v0 1)
      (iput-boolean v0 v4 "LX/002;.chromeVisibility:Z")
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

// The boxing-unboxing pattern only holds on the first iteration of the loop:
// v4 is a Long on entry, but a Double on every subsequent iteration. The
// fixpoint sees the matching pattern in its first (not yet converged) pass, so
// the unboxing rewrite must not be applied - refining the receiver to
// Long.longValue() behind a check-cast would throw ClassCastException.
// The unrelated add-int pair is there so that CSE has something to forward and
// therefore gets as far as applying the unboxing rewrites.
TEST_F(CommonSubexpressionEliminationTest, no_unwrap_across_loop_with_retype) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (const-wide v2 3)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v4)
      (const v5 7)
      (:loop)
      (invoke-virtual (v4) "Ljava/lang/Number;.longValue:()J")
      (move-result-wide v6)
      (const-wide v8 4)
      (invoke-static (v8) "Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;")
      (move-result-object v4)
      (add-int v10 v5 v5)
      (add-int v11 v5 v5)
      (add-int/lit v0 v0 -1)
      (if-gtz v0 :loop)
      (return-wide v6)
    )
  )";

  const auto* expected_str = R"(
    (
      (load-param v0)
      (const-wide v2 3)
      (invoke-static (v2) "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;")
      (move-result-object v4)
      (const v5 7)
      (:loop)
      (invoke-virtual (v4) "Ljava/lang/Number;.longValue:()J")
      (move-result-wide v6)
      (const-wide v8 4)
      (invoke-static (v8) "Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;")
      (move-result-object v4)
      (add-int v10 v5 v5)
      (move v12 v10)
      (add-int v11 v5 v5)
      (move v11 v12)
      (add-int/lit v0 v0 -1)
      (if-gtz v0 :loop)
      (return-wide v6)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str,
       /* expected_instructions_eliminated */ 1,
       /* is_static */ true,
       /* is_init_or_clinit */ false,
       /* declaring_type */ nullptr,
       DexTypeList::make_type_list({type::_int()}));
}

// The unboxing rewrite must not depend on there being an unrelated forwarding
// opportunity in the same method. Here the boxed value comes from a parameter,
// so nothing is forwardable and m_forward stays empty - the rewrite is still
// due.
TEST_F(CommonSubexpressionEliminationTest, unwrap_without_any_forwarding) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v1)
      (invoke-virtual (v1) "Ljava/lang/Number;.intValue:()I")
      (move-result v2)
      (return v2)
    )
  )";

  const auto* expected_str = R"(
    (
      (load-param v0)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v1)
      (check-cast v1 "Ljava/lang/Integer;")
      (move-result-pseudo-object v1)
      (invoke-virtual (v1) "Ljava/lang/Integer;.intValue:()I")
      (move-result v2)
      (return v2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str,
       /* expected_instructions_eliminated */ 0,
       /* is_static */ true,
       /* is_init_or_clinit */ false,
       /* declaring_type */ nullptr,
       DexTypeList::make_type_list({type::_int()}));
}

TEST_F(CommonSubexpressionEliminationTest, unwrap_and_wrap) {
  const auto* code_str = R"(
    (
      (const-wide v2 0)
      (invoke-virtual (v2) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v1)
      (return-object v1)
    )
  )";

  const auto* expected_str = R"(
    (
      (const-wide v2 0)
      (invoke-virtual (v2) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v1)
      (const-wide v1 0)
      (return-object v1)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, array_length) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (new-array v0 "[I")
      (move-result-pseudo-object v0)
      (array-length v0)
      (move-result-pseudo v0)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (move v1 v0)
      (new-array v0 "[I")
      (move-result-pseudo-object v0)
      (array-length v0)
      (move-result-pseudo v0)
      (move v0 v1)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, cmp) {
  // See T46241704. We do not want to deduplicate cmp instructions.
  const auto* code_str = R"(
    (
      (const-wide v0 0)
      (const-wide v2 0)
      (cmp-long v4 v0 v2)
      (cmp-long v5 v0 v2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, pure_methods) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Math;.abs:(I)I")
      (move-result v1)
      (invoke-static (v0) "Ljava/lang/Math;.abs:(I)I")
      (move-result v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Math;.abs:(I)I")
      (move-result v1)
      (move v2 v1)
      (invoke-static (v0) "Ljava/lang/Math;.abs:(I)I")
      (move-result v1)
      (move v1 v2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, conditionally_pure_methods) {
  // Calling a conditionally pure method twice with no relevant writes in
  // between means that the second call can be cse'ed.
  ClassCreator o_creator(DexType::make_type("LO;"));
  o_creator.set_super(type::java_lang_Object());

  [[maybe_unused]] auto* field_x =
      DexField::make_field("LO;.x:I")->make_concrete(ACC_PRIVATE);

  auto* get_method = DexMethod::make_method("LO;.getX:()I")
                         ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  get_method->set_code(assembler::ircode_from_string(R"(
    (
      (iget v2 "LO;.x:I")
      (return v2)
    )
  )"));
  o_creator.add_method(get_method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
      (move v2 v1)
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
      (move v1 v2)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), o_creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest,
       conditionally_pure_methods_with_mutation) {
  // Calling a conditionally pure method twice with a relevant write in
  // between means that the second call can NOT be cse'ed.
  ClassCreator o_creator(DexType::make_type("LO;"));
  o_creator.set_super(type::java_lang_Object());

  [[maybe_unused]] auto* field_x =
      DexField::make_field("LO;.x:I")->make_concrete(ACC_PRIVATE);

  auto* get_method = DexMethod::make_method("LO;.getX:()I")
                         ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  get_method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (iget v0 "LO;.x:I")
      (move-result-pseudo v1)
      (return v1)
    )
  )"));
  o_creator.add_method(get_method);
  // set_method exists so that it cannot be inferred that x is finalizable
  auto* set_method = DexMethod::make_method("LO;.setX:(I)V")
                         ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  set_method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param v1)
      (iput v1 v0 "LO;.x:I")
      (return-void)
    )
  )"));
  o_creator.add_method(set_method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
      (iput v0 v0 "LO;.x:I")
      (invoke-virtual (v0) "LO;.getX:()I")
      (move-result v1)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object()), o_creator.create()},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest,
       overridden_conditionally_pure_methods) {
  // A virtual base method is not actually conditionally pure if there is an
  // overriding method in a derived class that performs writes.

  // define base type

  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());

  [[maybe_unused]] auto* field_x =
      DexField::make_field("LBase;.x:I")->make_concrete(ACC_PRIVATE);

  auto* get_method = DexMethod::make_method("LBase;.getX:()I")
                         ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  get_method->set_code(assembler::ircode_from_string(R"(
    (
      (iget v2 "LBase;.x:I")
      (return v2)
    )
  )"));
  base_creator.add_method(get_method);
  DexClass* base_class = base_creator.create();

  // define derived type

  ClassCreator derived_creator(DexType::make_type("LDerived;"));
  derived_creator.set_super(base_class->get_type());

  get_method = DexMethod::make_method("LDerived;.getX:()I")
                   ->make_concrete(ACC_PUBLIC, true /* is_virtual */);
  get_method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (iget v0 "LBase;.x:I")
      (move-result-pseudo v1)
      (const v2 1)
      (add-int v1 v1 v2)
      (iput v1 v0 "LBase;.x:I")
      (return v1)
    )
  )"));
  derived_creator.add_method(get_method);
  DexClass* derived_class = derived_creator.create();

  const auto* code_str = R"(
    (
      (const v0 0)
      (invoke-virtual (v0) "LBase;.getX:()I")
      (move-result v1)
      (invoke-virtual (v0) "LBase;.getX:()I")
      (move-result v1)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object()), base_class, derived_class},
       code_str,
       expected_str,
       0);
}

TEST_F(CommonSubexpressionEliminationTest, recursion_is_benign) {
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());

  auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method("LA;.m:()V"));
  method->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
     (
       (invoke-static () "LA;.m:()V")
     )
   )"));
  a_creator.add_method(method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LA;.m:()V")
      (iget v0 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), a_creator.create()},
       code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest,
       invoked_static_method_with_somewhat_relevant_s_barrier) {
  ClassCreator creator(DexType::make_type("LTest7;"));
  creator.set_super(type::java_lang_Object());

  auto* method = DexMethod::make_method("LTest7;.test7:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (sput v0 "LFoo;.s:I")
      (const v0 0)
      (sput v0 "LFoo;.u:I")
      (return-void)
    )
  )"));
  creator.add_method(method);

  const auto* code_str = R"(
    (
      (sget "LFoo;.u:I")
      (move-result-pseudo v0)
      (sget "LFoo;.t:I")
      (move-result-pseudo v0)
      (invoke-static () "LTest7;.test7:()V")
      (sget "LFoo;.t:I")
      (move-result-pseudo v1)
      (sget "LFoo;.u:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (sget "LFoo;.u:I")
      (move-result-pseudo v0)
      (sget "LFoo;.t:I")
      (move-result-pseudo v0)
      (move v2 v0)
      (invoke-static () "LTest7;.test7:()V")
      (sget "LFoo;.t:I")
      (move-result-pseudo v1)
      (move v1 v2)
      (sget "LFoo;.u:I")
      (move-result-pseudo v1)
    )
  )";

  test(Scope{type_class(type::java_lang_Object()), creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest, tracked_final_field_within_clinit) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  DexField::make_field("LBar;.x:I")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);

  const auto* code_str = R"(
    (
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
      (invoke-static () "LWhat;.ever:()V")
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = code_str;
  bool is_static = true;
  bool is_init_or_clinit = true;
  DexType* declaring_type = bar_creator.create()->get_type();
  test(Scope{type_class(type::java_lang_Object()), type_class(declaring_type)},
       code_str, expected_str, 0, is_static, is_init_or_clinit, declaring_type);
}

TEST_F(CommonSubexpressionEliminationTest,
       untracked_final_field_outside_clinit) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  DexField::make_field("LBar;.x:I")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);

  const auto* code_str = R"(
    (
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
      (invoke-static () "LWhat;.ever:()V")
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
      (move v1 v0)
      (invoke-static () "LWhat;.ever:()V")
      (sget "LBar;.x:I")
      (move-result-pseudo v0)
      (move v0 v1)
    )
  )";
  bool is_static = true;
  bool is_init_or_clinit = false;
  DexType* declaring_type = bar_creator.create()->get_type();
  test(Scope{type_class(type::java_lang_Object()), type_class(declaring_type)},
       code_str, expected_str, 1, is_static, is_init_or_clinit, declaring_type);
}

TEST_F(CommonSubexpressionEliminationTest, tracked_final_field_within_init) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  DexField::make_field("LBar;.x:I")->make_concrete(ACC_PUBLIC | ACC_FINAL);

  const auto* code_str = R"(
    (
      (load-param-object v0)
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = code_str;
  bool is_static = false;
  bool is_init_or_clinit = true;
  DexType* declaring_type = bar_creator.create()->get_type();
  test(Scope{type_class(type::java_lang_Object()), type_class(declaring_type)},
       code_str, expected_str, 0, is_static, is_init_or_clinit, declaring_type);
}

TEST_F(CommonSubexpressionEliminationTest, untracked_final_field_outside_init) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  DexField::make_field("LBar;.x:I")->make_concrete(ACC_PUBLIC | ACC_FINAL);

  const auto* code_str = R"(
    (
      (load-param-object v0)
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param-object v0)
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
        (move v2 v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
      (move v1 v2)
    )
  )";
  bool is_static = false;
  bool is_init_or_clinit = false;
  DexType* declaring_type = bar_creator.create()->get_type();
  test(Scope{type_class(type::java_lang_Object()), type_class(declaring_type)},
       code_str, expected_str, 1, is_static, is_init_or_clinit, declaring_type);
}

TEST_F(CommonSubexpressionEliminationTest, phi_node) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :L1)
      (add-int v3 v1 v2)
      (:L2)
      (add-int v5 v1 v2)
      (return v5)
      (:L1)
      (add-int v4 v1 v2)
      (goto :L2)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :L1)
      (add-int v3 v1 v2)
      (move v6 v3)
      (:L2)
      (add-int v5 v1 v2)
      (move v5 v6)
      (return v5)
      (:L1)
      (add-int v4 v1 v2)
      (move v6 v4)
      (goto :L2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, no_phi_node) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :L1)
      (add-int v3 v1 v2)
      (:L2)
      (add-int v5 v1 v2)
      (return v5)
      (:L1)
      (sub-int v4 v1 v2)
      (goto :L2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, phi_node_sget) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (return v1)
      (:L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
      (goto :L2)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
      (move v3 v0)
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (move v1 v3)
      (return v1)
      (:L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
      (move v3 v2)
      (goto :L2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, phi_node_sget_memory_barrier) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v0)
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (return v3)
      (:L1)
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
      (invoke-static () "LWhat;.ever:()V")
      (goto :L2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, phi_node_sput_sget_forwarding) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L1)
      (sput v1 "LFoo;.s:I")
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (return v1)
      (:L1)
      (sput v1 "LFoo;.s:I")
      (goto :L2)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L1)
      (sput v1 "LFoo;.s:I")
      (move v2 v1)
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (move v1 v2)
      (return v1)
      (:L1)
      (sput v1 "LFoo;.s:I")
      (move v2 v1)
      (goto :L2)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, phi_node_sput_sget_forwarding_try) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L1)
      (sput v1 "LFoo;.s:I")
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (return v1)
      (.try_start foo)
      (:L1)
      (sput v1 "LFoo;.s:I")
      (goto :L2)
      (.try_end foo)
      (.catch (foo))
      (move-exception v0)
      (goto :L2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest,
       phi_node_sput_sget_forwarding_memory_barrier) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eqz v0 :L1)
      (sput v1 "LFoo;.s:I")
      (:L2)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (return v1)
      (:L1)
      (sput v1 "LFoo;.s:I")
      (invoke-static () "LWhat;.ever:()V")
      (goto :L2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, untracked_finalish_field) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  auto* finalish_field =
      DexField::make_field("LBar;.x:I")->make_concrete(ACC_PUBLIC);

  const auto* code_str = R"(
    (
      (load-param-object v0)
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param-object v0)
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
        (move v2 v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LBar;.x:I")
      (move-result-pseudo v1)
      (move v1 v2)
    )
  )";
  bool is_static = false;
  bool is_init_or_clinit = false;
  auto* declaring_type = bar_creator.create()->get_type();
  auto* args = DexTypeList::make_type_list({});
  const auto* finalish_field_name = finalish_field->get_name();
  test(Scope{type_class(type::java_lang_Object()), type_class(declaring_type)},
       code_str, expected_str, 1, is_static, is_init_or_clinit, declaring_type,
       args, {finalish_field_name});
}

TEST_F(CommonSubexpressionEliminationTest, finalizable) {
  // CSE still happens for finalizable fields across barriers
  ClassCreator o_creator(DexType::make_type("LO;"));
  o_creator.set_super(type::java_lang_Object());

  // CSE will infer that x is finalizable
  [[maybe_unused]] auto* field_x =
      DexField::make_field("LO;.x:I")->make_concrete(ACC_PRIVATE);

  auto* init_method =
      DexMethod::make_method("LO;.<init>:()V")
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false /* is_virtual */);
  init_method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 0)
      (iput v1 v0 "LO;.x:I")
      (return-void)
    )
  )"));
  o_creator.add_method(init_method);

  const auto* code_str = R"(
    (
      (const v0 0)
      (iget v0 "LO;.x:I")
      (move-result-pseudo v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LO;.x:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = R"(
    (
      (const v0 0)
      (iget v0 "LO;.x:I")
      (move-result-pseudo v1)
      (move v3 v1)
      (invoke-static () "LWhat;.ever:()V")
      (iget v0 "LO;.x:I")
      (move-result-pseudo v2)
      (move v2 v3)
    )
  )";
  test(Scope{type_class(type::java_lang_Object()), o_creator.create()},
       code_str,
       expected_str,
       1);
}

TEST_F(CommonSubexpressionEliminationTest, const_regression) {
  const auto* code_str = R"(
    (
      (load-param-object v3)
      (const v0 0)
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v1)
      (invoke-virtual (v1) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param-object v3)
      (const v0 0)
      ; (move v4 v0) -- this spurious move with a non-object type, competing
      ;                 with the -object use below, must not be introduced here
      (iput-object v0 v3 "Lcom/facebook/litho/Output;.mT:Ljava/lang/Object;")
      (const v0 0)
      (invoke-static (v0) "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
      (move-result-object v1)
      (invoke-virtual (v1) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
      (const v0 0)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, if_lt) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (if-lt v0 v1 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v0 3)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, if_ltz) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (const v1 0)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (if-ltz v0 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (const v1 0)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v0 3)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, if_eq_commutative) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eq v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (if-eq v1 v0 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eq v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v0 3)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, if_lt_negation) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (if-ge v0 v1 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-lt v0 v1 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v0 2)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, if_ne) {
  const auto* code_str = R"(
    (
      (load-param v0)
      (if-eq v0 v0 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v0 2)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (const v0 2)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 2);
}

TEST_F(CommonSubexpressionEliminationTest, if_lt_after_join) {
  // When control-flow joints from two paths, we lose the branch conditions.
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param v1)
      (if-lt v0 v1 :L1)
    (:L1)
      (if-lt v0 v1 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}

TEST_F(CommonSubexpressionEliminationTest, if_lt_memory) {
  // When branch condition involve memory locations that get written to, we
  // cannot eliminate branches.
  const auto* code_str = R"(
    (
      (load-param v0)
      (load-param-object v1)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v2)
      (if-lt v0 v2 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v3 42)
      (iput v3 v1 "LFoo;.a:I")
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v2)
      (if-lt v0 v2 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  const auto* expected_str = R"(
    (
      (load-param v0)
      (load-param-object v1)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v2)
      (if-lt v0 v2 :L1)
      (const v0 1)
      (return v0)
    (:L1)
      (const v3 42)
      (iput v3 v1 "LFoo;.a:I")
      (move v4 v3)
      (iget v1 "LFoo;.a:I")
      (move-result-pseudo v2)
      (move v2 v4)
      (if-lt v0 v2 :L2)
      (const v0 2)
      (return v0)
    (:L2)
      (const v0 3)
      (return v0)
    )
  )";
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 1);
}

TEST_F(CommonSubexpressionEliminationTest, invoke_polymorphic_is_barrier) {
  const auto* code_str = R"(
    (
      (const v0 0)
      (sget "LFoo;.s:I")
      (move-result-pseudo v1)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (sget "LFoo;.s:I")
      (move-result-pseudo v2)
    )
  )";
  const auto* expected_str = code_str;
  test(Scope{type_class(type::java_lang_Object())}, code_str, expected_str, 0);
}
