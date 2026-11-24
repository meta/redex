/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AccessibilityChecker.h"

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexException.h"
#include "RedexTest.h"

class AccessibilityCheckerTest : public RedexTest {};

namespace {

// Runs the checker, as it runs while `NeedsEverythingPublic` is not
// established, over a class holding a method that creates a `p.Hidden[]`.
void check_new_array_in(const char* host) {
  auto* method = assembler::method_from_string(std::string(R"(
    (method (public static) ")") + host + R"(.run:()V"
      (
        (const v0 1)
        (new-array v0 "[Lp/Hidden;")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )
  )");
  ClassCreator creator(method->get_class());
  creator.set_super(type::java_lang_Object());
  creator.add_method(method);
  DexStore store("classes");
  store.add_classes({creator.create()});
  DexStoresVector stores{store};
  ConfigFiles conf(Json::nullValue);
  PassManager mgr({}, conf);
  redex_properties::AccessibilityChecker().run_checker(stores, conf, mgr,
                                                       /* established */ false);
}

} // namespace

// The device checks access to an array's element class, so only a method of
// package `p` may create an array of the package-private `p.Hidden`.
TEST_F(AccessibilityCheckerTest, array_of_a_class_of_another_package) {
  ClassCreator hidden(DexType::make_type("Lp/Hidden;"));
  hidden.set_super(type::java_lang_Object());
  hidden.set_access(DexAccessFlags(0));
  hidden.create();

  EXPECT_NO_THROW(check_new_array_in("Lp/User;"));
  EXPECT_THROW(check_new_array_in("Lq/User;"), RedexException);
}
