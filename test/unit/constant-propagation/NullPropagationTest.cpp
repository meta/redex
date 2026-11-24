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
#include "OpcodeList.h"
#include "Show.h"

struct NullPropagationTest : public ConstantPropagationTest {
 public:
  NullPropagationTest() {
    ClassCreator creator(DexType::make_type("Ljava/lang/Boolean;"));
    creator.set_super(type::java_lang_Object());
    creator.set_external();

    auto* booleanvalue =
        DexMethod::make_method("Ljava/lang/Boolean;.booleanValue:()Z")
            ->make_concrete(ACC_PUBLIC, true);
    creator.add_method(booleanvalue);

    creator.create();
  }
};

// Simplify null-dereference attempts to use throw instruction
TEST_F(NullPropagationTest, NullMonitorEnter) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (monitor-enter v0)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const-string "monitor-enter")
      (move-result-pseudo-object v1)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
      (throw v2)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Simplify null-dereference attempts to use throw instruction
TEST_F(NullPropagationTest, NullInvokeVirtual) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
      (move-result v0)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const-string "booleanValue")
      (move-result-pseudo-object v1)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
      (throw v2)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Simplify null-dereference attempts to use throw instruction
TEST_F(NullPropagationTest, AputInvokeVirtual) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (aput v0 v1 v2)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (const-string "array access")
      (move-result-pseudo-object v3)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v3) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
      (throw v4)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// After an instruction that would have thrown on a null object, the analysis
// marks the object register non-null. That is sound only because no such
// instruction writes a register itself; any result goes to a separate
// move-result(-pseudo). The null-check method paths are all invoke-static.
TEST_F(NullPropagationTest, NullCheckedInstructionsWriteNoDest) {
  size_t checked = 0;
  for (auto op : all_opcodes) {
    IRInstruction insn(op);
    if (op != OPCODE_INVOKE_STATIC &&
        !constant_propagation::get_dereferenced_object_src_index(&insn)) {
      continue;
    }
    EXPECT_FALSE(insn.has_dest()) << SHOW(op);
    ++checked;
  }
  EXPECT_GT(checked, 1u);
}
