/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BuilderAnalysis.h"

#include <gtest/gtest.h>

#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

class BuilderAnalysisTest : public RedexTest {};

namespace {

// Whether `method` must keep the `LFoo$Builder;` instances it creates.
bool builder_is_not_removable(DexMethod* method) {
  auto* builder = DexType::make_type("LFoo$Builder;");
  ConstTypeHashSet builder_types{builder};
  ConstTypeHashSet excluded_types;
  builder_pattern::BuilderAnalysis analysis(builder_types, excluded_types,
                                            method);
  analysis.run_analysis();
  EXPECT_TRUE(analysis.has_usage());
  return analysis.non_removable_types().count(builder) != 0;
}

} // namespace

// The handle may keep the builder:
//
//   Foo.Builder builder = new Foo.Builder();
//   KEEP.invokeExact(builder);
TEST_F(BuilderAnalysisTest, builderPassedToMethodHandleCallIsNotRemovable) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.make:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (new-instance "LFoo$Builder;")
      (move-result-pseudo-object v1)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LFoo$Builder;)V")
      (return-void)
     )
    )
  )");
  method->get_code()->build_cfg();
  EXPECT_TRUE(builder_is_not_removable(method));
}

// The same for a call site.
TEST_F(BuilderAnalysisTest, builderPassedToCallSiteIsNotRemovable) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.make:()V"
     (
      (new-instance "LFoo$Builder;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LUser;.placeholder:(LFoo$Builder;)V")
      (return-void)
     )
    )
  )");
  // The `invoke-static` becomes an `invoke-custom`.
  redex::make_invoke_custom(method->get_code(), "keep", "(LFoo$Builder;)V");
  method->get_code()->build_cfg();
  EXPECT_TRUE(builder_is_not_removable(method));
}

// A builder that only reaches field accesses can be removed.
TEST_F(BuilderAnalysisTest, builderOnlyReachingFieldsIsRemovable) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.make:(I)I"
     (
      (load-param v0)
      (new-instance "LFoo$Builder;")
      (move-result-pseudo-object v1)
      (iput v0 v1 "LFoo$Builder;.x:I")
      (iget v1 "LFoo$Builder;.x:I")
      (move-result-pseudo v2)
      (return v2)
     )
    )
  )");
  method->get_code()->build_cfg();
  EXPECT_FALSE(builder_is_not_removable(method));
}
