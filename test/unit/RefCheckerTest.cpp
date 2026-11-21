/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexStore.h"
#include "RedexTest.h"
#include "RefChecker.h"

class RefCheckerTest : public RedexTest {};

// A hierarchy may end in a `java.lang.Object` that the input defines, as in
// tests, rather than in the external one of the SDK.
TEST_F(RefCheckerTest, typeWhoseHierarchyEndsInDefinedObject) {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.set_access(ACC_PUBLIC);
  auto* object = object_creator.create();
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.set_access(ACC_PUBLIC);
  auto* foo = foo_creator.create();
  DexStore store("classes");
  store.add_classes({object, foo});
  DexStoresVector stores({store});
  XStoreRefs xstores(stores, /* normal_primary_dex */ false);
  RefChecker checker(&xstores, xstores.get_store_idx(foo->get_type()),
                     /* min_sdk_api */ nullptr);

  EXPECT_TRUE(checker.check_type(foo->get_type()));
  EXPECT_TRUE(checker.check_type(DexType::make_type("[LFoo;")));
}
