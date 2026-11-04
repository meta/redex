/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexAccess.h"
#include "Show.h"
#include "TypeUtil.h"
#include "verify/VerifyUtil.h"

TEST_F(PostVerify, MergerClassGenerated) {
  auto* cls_a = find_class_named(classes, "Lcom/facebook/redextest/A;");
  auto* cls_b = find_class_named(classes, "Lcom/facebook/redextest/B;");
  auto* cls_c = find_class_named(classes, "Lcom/facebook/redextest/C;");
  verify_class_merged(cls_a);
  verify_class_merged(cls_b);
  verify_class_merged(cls_c);
}

TEST_F(PostVerify, MergedFieldModifiers) {
  for (const auto* name :
       {"Lcom/facebook/redextest/A;", "Lcom/facebook/redextest/B;",
        "Lcom/facebook/redextest/E;"}) {
    verify_class_merged(find_class_named(classes, name));
  }

  auto* merger = find_class_named(classes, [](const char* name) {
    auto* cls = type_class(DexType::get_type(name));
    if (cls->get_super_class() !=
        DexType::get_type("Lcom/facebook/redextest/Base;")) {
      return false;
    }
    for (auto* field : cls->get_ifields()) {
      if (field->get_type() == type::_long()) {
        return true;
      }
    }
    return false;
  });
  ASSERT_NE(merger, nullptr);
  ASSERT_EQ(merger->get_ifields().size(), 5);
  for (auto* field : merger->get_ifields()) {
    auto* field_type = field->get_type();
    bool expected_volatile = field_type == type::_int() ||
                             field_type == type::_long() ||
                             field_type == type::_double();
    EXPECT_EQ(is_volatile(field), expected_volatile) << show(field);
    EXPECT_EQ(is_final(field), field_type == type::_float()) << show(field);
  }
}

TEST_F(PostVerify, ClassWithStaticFields) {
  auto* cls_d = find_class_named(classes, "Lcom/facebook/redextest/D;");
  verify_class_merged(cls_d, 1 /* clinit */);
  auto& static_fields = cls_d->get_sfields();
  ASSERT_EQ(static_fields.size(), 1);
}
