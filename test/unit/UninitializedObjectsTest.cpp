/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "UninitializedObjects.h"

using namespace uninitialized_objects;

class UninitializedObjectsTest : public RedexTest {};

namespace {

// Whether `reg` may hold an uninitialized object just before the first
// instruction of `m` with opcode `op`: true, false, or nullopt when the
// analysis cannot tell.
std::optional<bool> uninitialized_before(DexMethod* m, IROpcode op, reg_t reg) {
  auto envs = get_uninitialized_object_environments(m);
  for (const auto& mie : cfg::InstructionIterable(m->get_code()->cfg())) {
    if (mie.insn->opcode() == op) {
      auto uninitialized = envs.at(mie.insn).get(reg).get_constant();
      if (!uninitialized) {
        return std::nullopt;
      }
      return *uninitialized;
    }
  }
  ADD_FAILURE() << "no instruction with opcode " << SHOW(op);
  return std::nullopt;
}

DexMethod* make(const std::string& code_str) {
  auto* m = assembler::method_from_string(code_str);
  m->get_code()->build_cfg();
  return m;
}

} // namespace

// A constructor that throws leaves its object uninitialized: the handler sees
// the registers as they were before the call.
TEST_F(UninitializedObjectsTest, ThrowingInitLeavesTheObjectUninitialized) {
  auto* m = make(R"(
    (method (public static) "LFoo;.throwing:()V"
      (
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (.try_start t)
        (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
        (.try_end t)
        (return-void)
        (.catch (t))
        (move-exception v3)
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_MOVE_EXCEPTION, 1), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 1), false);
}

// The `<init>` called through a copy of the allocation's register initializes
// the object in the original register too:
//   Object o = new Object();  // new-instance into v1, `<init>` through v2
TEST_F(UninitializedObjectsTest, InitThroughACopyInitializesTheOriginal) {
  auto* m = make(R"(
    (method (public static) "LFoo;.alias:()V"
      (
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (move-object v2 v1)
        (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
        (invoke-virtual (v1) "Ljava/lang/Object;.hashCode:()I")
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_INVOKE_VIRTUAL, 1), false);
  EXPECT_EQ(uninitialized_before(m, OPCODE_INVOKE_VIRTUAL, 2), false);
}

// Initializing one allocation leaves another one uninitialized.
TEST_F(UninitializedObjectsTest, InitLeavesAnotherAllocationUninitialized) {
  auto* m = make(R"(
    (method (public static) "LFoo;.two:()V"
      (
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 1), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 2), false);
}

// A constructor that calls its superclass constructor through a copy of its
// receiver initializes the receiver register too.
TEST_F(UninitializedObjectsTest, SuperInitThroughACopyInitializesTheReceiver) {
  auto* m = make(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      (
        (load-param-object v0)
        (move-object v1 v0)
        (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_INVOKE_DIRECT, 0), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 0), false);
}

// After two paths that hold different allocations in `v1` meet, `v1` holds an
// unknown one, so an `<init>` through a copy of it does not initialize `v1`.
TEST_F(UninitializedObjectsTest, MergedAllocationsStayUninitialized) {
  auto* m = make(R"(
    (method (public static) "LFoo;.merge:(I)V"
      (
        (load-param v0)
        (if-eqz v0 :other)
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (goto :join)
        (:other)
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (:join)
        (move-object v2 v1)
        (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 1), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 2), false);
}

// A constructor that throws through a copy leaves the object uninitialized in
// the handler, in the copy as well as in the original.
TEST_F(UninitializedObjectsTest,
       ThrowingInitThroughACopyLeavesBothUninitialized) {
  auto* m = make(R"(
    (method (public static) "LFoo;.throwing:()V"
      (
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (move-object v2 v1)
        (.try_start t)
        (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
        (.try_end t)
        (return-void)
        (.catch (t))
        (move-exception v3)
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_MOVE_EXCEPTION, 1), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_MOVE_EXCEPTION, 2), true);
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 1), false);
}

// An allocation in a loop whose object nothing initializes or reads: the next
// iteration's `new-instance` creates another object. A register still holding
// the previous one is not taken for the new one, so initializing the new
// object leaves the stale register uninitialized.
TEST_F(UninitializedObjectsTest, AllocationInALoopIsAnotherObjectEachTime) {
  auto* m = make(R"(
    (method (public static) "LFoo;.loop:(I)V"
      (
        (load-param v0)
        (:loop)
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (if-eqz v0 :init)
        (move-object v2 v1)
        (add-int/lit v0 v0 -1)
        (goto :loop)
        (:init)
        (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )
    )
  )");
  EXPECT_EQ(uninitialized_before(m, OPCODE_RETURN_VOID, 1), false);
  EXPECT_NE(uninitialized_before(m, OPCODE_RETURN_VOID, 2), false);
}
