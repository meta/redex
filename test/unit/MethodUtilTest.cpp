/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodUtil.h"

#include "IRAssembler.h"
#include "RedexTest.h"

class MethodUtilTest : public RedexTest {};

TEST_F(MethodUtilTest, test_count_opcodes) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 6)
    )
  )");

  EXPECT_EQ(6, method::count_opcode_of_types(code.get(), {OPCODE_CONST}));
  code->build_cfg();
  EXPECT_EQ(6, method::count_opcode_of_types(code->cfg(), {OPCODE_CONST}));
  EXPECT_EQ(
      6,
      method::count_opcode_of_types(code->cfg().entry_block(), {OPCODE_CONST}));
  code->clear_cfg();
}

TEST_F(MethodUtilTest, can_change_signature) {
  auto make = [](const char* signature, DexAccessFlags access) {
    return DexMethod::make_method(signature)->make_concrete(access, false);
  };
  auto* plain = make("LA;.plain:()V", ACC_PUBLIC | ACC_STATIC);
  EXPECT_TRUE(method::can_change_signature(plain));

  auto* kept = make("LA;.kept:()V", ACC_PUBLIC | ACC_STATIC);
  kept->rstate.set_root();
  EXPECT_FALSE(method::can_change_signature(kept));

  auto* native = make("LA;.jni:()V", ACC_PUBLIC | ACC_STATIC | ACC_NATIVE);
  EXPECT_FALSE(method::can_change_signature(native));

  auto* no_optimizations = make("LA;.noOpt:()V", ACC_PUBLIC | ACC_STATIC);
  no_optimizations->rstate.set_no_optimizations();
  EXPECT_FALSE(method::can_change_signature(no_optimizations));
}
