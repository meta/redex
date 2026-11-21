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

// Code in a package may name a public class, or a package-private class of
// the same package, and arrays of either.
TEST_F(RefCheckerTest, typeFromPackage) {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.set_access(ACC_PUBLIC);
  auto* object = object_creator.create();
  std::vector<DexClass*> classes{object};
  for (const auto& [name, access] :
       std::vector<std::pair<const char*, DexAccessFlags>>{
           {"Lcom/a/Public;", ACC_PUBLIC}, {"Lcom/a/Hidden;", ACC_FINAL}}) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.set_access(access);
    classes.push_back(creator.create());
  }
  DexStore store("classes");
  store.add_classes(classes);
  DexStoresVector stores({store});
  XStoreRefs xstores(stores, /* normal_primary_dex */ false);
  RefChecker checker(&xstores, 0, /* min_sdk_api */ nullptr);

  EXPECT_TRUE(checker.check_type_from_package(
      DexType::get_type("Lcom/a/Public;"), "Lcom/b/"));
  EXPECT_TRUE(checker.check_type_from_package(
      DexType::make_type("[Lcom/a/Hidden;"), "Lcom/a/"));
  EXPECT_FALSE(checker.check_type_from_package(
      DexType::get_type("Lcom/a/Hidden;"), "Lcom/b/"));
  EXPECT_TRUE(checker.check_type_from_package(type::_int(), "Lcom/b/"));
  EXPECT_FALSE(checker.check_type_from_package(
      DexType::make_type("Lcom/a/Unknown;"), "Lcom/a/"));
}
