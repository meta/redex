/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "UnknownVirtuals.h"

#include "RedexTest.h"

class UnknownVirtualsTest : public RedexTest {};

TEST_F(UnknownVirtualsTest, knownPublicMethodsInEveryRedexContext) {
  auto is_public = [](const char* method) {
    return unknown_virtuals::is_method_known_to_be_public(
        DexMethod::make_method(method));
  };
  for (int i = 0; i < 2; ++i) {
    SCOPED_TRACE(i);
    EXPECT_TRUE(is_public("Landroid/view/View;.getContext:()V"));
    EXPECT_TRUE(is_public("Ljava/lang/Object;.hashCode:()I"));
    EXPECT_FALSE(is_public("Landroid/view/View;.onDraw:()V"));
    delete g_redex;
    g_redex = new RedexContext();
  }
}
