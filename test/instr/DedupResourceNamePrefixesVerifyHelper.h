/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <gtest/gtest.h>

#include "DexAnnotation.h"
#include "RedexResources.h"
#include "verify/VerifyUtil.h"

// Verifies that DedupResourcesPass keeps every resource whose name starts with
// a disallowed_resource_prefixes entry, so that it can still be looked up by
// name.
//
// Test setup:
// - icon.png, js_referenced_icon.png and x_icon.png are identical files, and
//   so are prickly.png and x_prickly.png.
// - The config disallows the prefix "x_".
//
// Expected behavior:
// - icon and js_referenced_icon are deduped (same ID after the pass).
// - x_icon and x_prickly keep their own IDs and names.

inline void dedupresource_name_prefixes_preverify(
    const DexClasses& classes, ResourceTableFile* res_table) {
  auto* drawable_cls = find_class_named(classes, "Lcom/facebook/R$drawable;");
  ASSERT_NE(nullptr, drawable_cls);

  auto* icon = find_sfield_named(*drawable_cls, "icon");
  auto* x_icon = find_sfield_named(*drawable_cls, "x_icon");
  auto* prickly = find_sfield_named(*drawable_cls, "prickly");
  auto* x_prickly = find_sfield_named(*drawable_cls, "x_prickly");
  ASSERT_NE(nullptr, icon);
  ASSERT_NE(nullptr, x_icon);
  ASSERT_NE(nullptr, prickly);
  ASSERT_NE(nullptr, x_prickly);

  EXPECT_NE(icon->get_static_value()->value(),
            x_icon->get_static_value()->value());
  EXPECT_NE(prickly->get_static_value()->value(),
            x_prickly->get_static_value()->value());

  EXPECT_EQ(res_table->get_res_ids_by_name("x_icon").size(), 1);
  EXPECT_EQ(res_table->get_res_ids_by_name("x_prickly").size(), 1);
}

inline void dedupresource_name_prefixes_postverify(
    const DexClasses& classes, ResourceTableFile* res_table) {
  auto* drawable_cls = find_class_named(classes, "Lcom/facebook/R$drawable;");
  ASSERT_NE(nullptr, drawable_cls);

  auto* icon = find_sfield_named(*drawable_cls, "icon");
  auto* js_icon = find_sfield_named(*drawable_cls, "js_referenced_icon");
  auto* x_icon = find_sfield_named(*drawable_cls, "x_icon");
  auto* prickly = find_sfield_named(*drawable_cls, "prickly");
  auto* x_prickly = find_sfield_named(*drawable_cls, "x_prickly");
  ASSERT_NE(nullptr, icon);
  ASSERT_NE(nullptr, js_icon);
  ASSERT_NE(nullptr, x_icon);
  ASSERT_NE(nullptr, prickly);
  ASSERT_NE(nullptr, x_prickly);

  EXPECT_EQ(icon->get_static_value()->value(),
            js_icon->get_static_value()->value());

  EXPECT_NE(icon->get_static_value()->value(),
            x_icon->get_static_value()->value());
  EXPECT_NE(prickly->get_static_value()->value(),
            x_prickly->get_static_value()->value());

  auto x_icon_ids = res_table->get_res_ids_by_name("x_icon");
  auto x_prickly_ids = res_table->get_res_ids_by_name("x_prickly");
  ASSERT_EQ(x_icon_ids.size(), 1);
  ASSERT_EQ(x_prickly_ids.size(), 1);
  EXPECT_EQ(x_icon_ids[0], x_icon->get_static_value()->value());
  EXPECT_EQ(x_prickly_ids[0], x_prickly->get_static_value()->value());
}
