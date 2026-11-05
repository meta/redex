/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "verify/VerifyUtil.h"

TEST_F(PreVerify, SimpleBuilder) {
  auto* loop_builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/LoopModel$Builder;");
  EXPECT_NE(nullptr, loop_builder);
  auto* previous_builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/PreviousModel$Builder;");
  EXPECT_NE(nullptr, previous_builder);
  auto* builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/Model$Builder;");
  EXPECT_NE(nullptr, builder);
}

TEST_F(PostVerify, SimpleBuilder) {
  auto* loop_builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/LoopModel$Builder;");
  EXPECT_EQ(nullptr, loop_builder);
  auto* previous_builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/PreviousModel$Builder;");
  EXPECT_NE(nullptr, previous_builder);
  auto* builder = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/Model$Builder;");
  EXPECT_EQ(nullptr, builder);
}
