/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <array>

#include "Show.h"
#include "verify/VerifyUtil.h"

TEST_F(PostVerify, UnanimousCaptureStorageTypes) {
  constexpr auto expected = std::to_array<std::pair<const char*, const char*>>(
      {{"TypedCaptureBase",
        "Lcom/facebook/redextest/ClassMergingFieldTypesTest$CapturePayload;"},
       {"MixedCaptureBase", "Ljava/lang/Object;"},
       {"ArrayCaptureBase",
        "[[Lcom/facebook/redextest/"
        "ClassMergingFieldTypesTest$CapturePayload;"}});
  for (const auto& [base, field_type] : expected) {
    auto* parent =
        DexType::get_type(std::string("Lcom/facebook/redextest/") + base + ";");
    ASSERT_NE(parent, nullptr);
    DexField* slot = nullptr;
    for (auto* cls : classes) {
      if (cls->get_super_class() != parent) {
        continue;
      }
      for (auto* field : cls->get_ifields()) {
        if (field->get_name()->str() == "l0") {
          ASSERT_EQ(slot, nullptr);
          slot = field;
        }
      }
    }
    ASSERT_NE(slot, nullptr);
    EXPECT_EQ(slot->get_type(), DexType::get_type(field_type));
  }
}
