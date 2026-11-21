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
