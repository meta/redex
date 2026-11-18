/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <json/json.h>

#include "IRCode.h"
#include "MethodUtil.h"
#include "RedexTest.h"

#include "DexUtil.h"
#include "ObjectSensitiveDcePass.h"
#include "Show.h"
#include "TypeUtil.h"

class ObjectSensitiveDceTest : public RedexIntegrationTest {
 public:
  ObjectSensitiveDceTest() {
    // The tests need java.lang.Object to resolve to a DexClass to build a
    // proper scope.
    create_object_class();

    auto* object_ctor = method::java_lang_Object_ctor();
    object_ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
    object_ctor->set_external();
    type_class(type::java_lang_Object())->add_method(object_ctor);
  }
  void run_passes(const std::vector<Pass*>& passes) {
    RedexIntegrationTest::run_passes(passes);
  }
};

TEST_F(ObjectSensitiveDceTest, basic) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/ObjectSensitiveDceTest;.basic:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

// The code of a method marked `no_optimizations` may not be what runs, so an
// object passed to it may be kept and read later, and writes to it stay.
TEST_F(ObjectSensitiveDceTest, passed_to_no_optimizations_method) {
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "ObjectSensitiveDceTest;.passed_to_no_optimizations_"
                     "method:()V")
                     ->as_def();
  ASSERT_NE(method, nullptr);
  auto* take = DexMethod::get_method(
                   "Lcom/facebook/redextest/"
                   "NoOptimizations;.take:(Ljava/lang/Object;)V")
                   ->as_def();
  ASSERT_NE(take, nullptr);
  take->rstate.set_no_optimizations();

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  EXPECT_TRUE(std::any_of(ii.begin(), ii.end(), [](const auto& mie) {
    return mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL &&
           mie.insn->get_method()->get_name()->str() == "foo";
  }));
}

TEST_F(ObjectSensitiveDceTest, invoke_super) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/ObjectSensitiveDceTest;.invoke_super:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, invoke_virtual_with_overrides) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.invoke_virtual_with_overrides:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, invoke_virtual_with_overrides_with_side_effect) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.invoke_virtual_with_overrides_with_side_effect:("
      ")V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  // Nothing could get optimized away, because the invoke-virtual to bar
  // has an override with side-effects, so it couldn't get removed, and thus
  // the object creation itself is required.
  auto* code = method->get_code();
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_VIRTUAL}), 1);
}

TEST_F(ObjectSensitiveDceTest, invoke_virtual_with_too_many_overrides) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.invoke_virtual_with_too_many_overrides:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  // Nothing could get optimized away, because the invoke-virtual to bar
  // has an override with side-effects, so it couldn't get removed, and thus
  // the object creation itself is required.
  auto* code = method->get_code();
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_VIRTUAL}), 1);
}

TEST_F(ObjectSensitiveDceTest, non_termination) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/ObjectSensitiveDceTest;.non_termination:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, recursive) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/ObjectSensitiveDceTest;.recursive:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, mutually_recursive) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/ObjectSensitiveDceTest;.mutually_recursive:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, clinit_with_side_effects) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.clinit_with_side_effects:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), IOPCODE_INIT_CLASS);
  ASSERT_EQ(it->insn->get_type(),
            DexType::get_type(
                "Lcom/facebook/redextest/UselessWithClInitWithSideEffects;"));
  it++;
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, method_needing_init_class) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.method_needing_init_class:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  // Nothing could get optimized away, because the invoke-virtual to foo
  // triggers a clinit with side-effects, so it couldn't get removed, and thus
  // the object creation itself is required.
  auto* code = method->get_code();
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_VIRTUAL}), 1);
}

TEST_F(ObjectSensitiveDceTest, pure_method_object) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.pure_method_object:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  // We are verifying that we need to *keep* the object creation, as we are not
  // treating the pure Object.getClass() are truly pure, as we need to track the
  // effects on its object result.
  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_NEW_INSTANCE);
}

TEST_F(ObjectSensitiveDceTest, array_clone) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.array_clone:()V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto ii = InstructionIterable(method->get_code());
  auto it = ii.begin();
  ASSERT_TRUE(it != ii.end());
  ASSERT_EQ(it->insn->opcode(), OPCODE_RETURN_VOID);
}

TEST_F(ObjectSensitiveDceTest, do_not_reduce_finalize) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.do_not_reduce_finalize:("
      ")V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto* code = method->get_code();

  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_VIRTUAL}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_RETURN_VOID}), 1);
}

TEST_F(ObjectSensitiveDceTest, do_not_reduce_finalize_field) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.do_not_reduce_finalize_field:("
      ")V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto* code = method->get_code();

  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_IPUT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_RETURN_VOID}), 1);
}

TEST_F(ObjectSensitiveDceTest, do_not_reduce_finalize_derived) {
  auto* method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "ObjectSensitiveDceTest;.do_not_reduce_finalize_derived:("
      ")V");
  EXPECT_NE(method_ref, nullptr);
  auto* method = method_ref->as_def();
  EXPECT_NE(method, nullptr);

  std::vector<Pass*> passes = {
      new ObjectSensitiveDcePass(),
  };

  run_passes(passes);

  auto* code = method->get_code();

  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_NEW_INSTANCE}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_DIRECT}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_INVOKE_VIRTUAL}), 1);
  ASSERT_EQ(method::count_opcode_of_types(code, {OPCODE_RETURN_VOID}), 1);
}
