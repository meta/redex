/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "DexUtil.h"
#include "PrintKotlinStats.h"
#include "RedexTest.h"

using ::testing::NotNull;

class KotlinStatsTest : public RedexIntegrationTest {};

namespace {
TEST_F(KotlinStatsTest, MethodHasNoEqDefined) {
  // Set deobfuscated names for lambda classes so is_kotlin_lambda works.
  // Integration tests don't set deobfuscated names by default.
  const std::vector<const char*> lambda_class_names = {
      "LKotlinLambdaInline$foo$1;",
      "LKotlinLambdaInline$bar$1;",
      "LKotlinLambdaInline$baz$1;",
  };
  for (const auto* name : lambda_class_names) {
    auto* cls = type_class(DexType::get_type(name));
    ASSERT_THAT(cls, NotNull()) << "Lambda class not found: " << name;
    cls->set_deobfuscated_name(name);
  }

  // Mark one method as a root so that its param null check is counted in
  // the in-root-method bucket. `Delegate1.getValue` has one non-nullable
  // parameter (`property: KProperty<*>`) and so contributes one
  // `checkParameterIsNotNull` call.
  auto* root_method = DexMethod::get_method(
                          "LDelegate1;.getValue:(Ljava/lang/Object;Lkotlin/"
                          "reflect/KProperty;)Ljava/lang/String;")
                          ->as_def();
  ASSERT_THAT(root_method, NotNull());
  root_method->rstate.set_root();

  auto* klr = new PrintKotlinStats();
  std::vector<Pass*> passes{klr};
  run_passes(passes);

  PrintKotlinStats::Stats stats = klr->get_stats();

  EXPECT_EQ(stats.kotlin_null_check_param_insns_in_root_method, 1);
  EXPECT_EQ(stats.kotlin_null_check_param_insns_in_non_root_method, 15);
  EXPECT_EQ(stats.kotlin_null_check_expr_insns, 0);
  // KotlinCheckNotNull: 1 from !!, 1 from `as` cast to non-null type
  EXPECT_EQ(stats.kotlin_null_check_notnull_insns, 2);
  // +2 from KotlinCheckNotNull (notNullAssert, castToNonNull)
  EXPECT_EQ(stats.kotlin_public_param_objects, 67);

  // LExample;.$$delegatedProperties:[Lkotlin/reflect/KProperty;
  // LFooDelagates;.lazyValue$delegate:Lkotlin/Lazy;
  // Lfoo;.unsafeLazy:Lkotlin/Lazy;
  EXPECT_EQ(stats.kotlin_delegates, 1);
  EXPECT_EQ(stats.kotlin_lazy_delegates, 2);

  // LKotlinLambdaInline$foo$1;
  // LKotlinLambdaInline$bar$1;
  // LKotlinLambdaInline$baz$1;
  // LFooDelagates$lazyValue$2;
  EXPECT_EQ(stats.kotlin_lambdas, 4);

  // LKotlinLambdaInline$foo$1;
  // LKotlinLambdaInline$bar$1;
  // LKotlinLambdaInline$baz$1;
  EXPECT_EQ(stats.kotlin_class_with_instance, 3);

  // LKotlinLambdaInline$foo$1;
  // LKotlinLambdaInline$bar$1;
  // LKotlinLambdaInline$baz$1;
  EXPECT_EQ(stats.kotlin_non_capturing_lambda_with_singleton, 3);
  EXPECT_EQ(stats.kotlin_non_capturing_lambda_without_singleton, 0);

  // All three lambdas in LKotlinLambdaInline are trivial
  EXPECT_EQ(stats.kotlin_trivial_non_capturing_lambdas, 3u);
  // foo$1 and bar$1 have same body (a+b), baz$1 has different body (a-b)
  EXPECT_EQ(stats.kotlin_unique_trivial_non_capturing_lambdas, 2u);

  // LDelegate1;
  // LKotlinLambdaInline$foo$1;
  // LKotlinLambdaInline$bar$1;
  // LKotlinLambdaInline$baz$1;
  // LKotlinLayzyKt;
  // LCompanionClass$Companion;
  // LKotlinLambdaInline;
  // LKotlinDefaultArgs;
  // LCompanionClass;
  // LDelegateTest;
  // LExample;
  // LAnotherCompanionClass$Companion;
  // LFooDelagates$lazyValue$2;
  // LFooDelagates;
  // LKotlinCompanionOptimizationKt;
  // Lfoo;
  // LAnotherCompanionClass;
  // LCompanionWithMethodCollision;
  // LCompanionWithMethodCollision$Companion;
  // LCollisionTestCaller;
  // LNamedCompanionClass;
  // LNamedCompanionClass$Custom;
  // LNamedCompanionCaller;
  // LCompanionWithInterCalls;
  // LCompanionWithInterCalls$Companion;
  // LInterCallsCaller;
  // LCompanionWithJvmStaticBridge;
  // LCompanionWithJvmStaticBridge$Companion;
  // LJvmStaticBridgeCaller;
  // LCompanionWithDefaults;
  // LCompanionWithDefaults$Companion;
  // LDefaultArgsCaller;
  // LAbstractOuterClass;
  // LAbstractOuterClass$Companion;
  // LConcreteSubclass;
  // LAbstractOuterCaller;
  // LCompanionWithConstVal;
  // LCompanionWithConstVal$Companion;
  // LConstValCaller;
  // LCompanionEscapes;
  // LCompanionEscapes$Companion;
  // LEscapesCaller;
  // + LCompanionWithSynchronized;
  // + LCompanionWithSynchronized$Companion;
  // + LSynchronizedCaller;
  // + LCompanionWithNativeMethod;
  // + LCompanionWithNativeMethod$Companion;
  // + LNativeMethodCaller;
  // + LCompanionWithKeptBridge;
  // + LCompanionWithKeptBridge$Companion;
  // + LKeptBridgeCaller;
  // + LInterfaceOuter;
  // + LInterfaceOuter$Companion;
  // + LInterfaceOuterCaller;
  EXPECT_EQ(stats.kotlin_class, 59);

  // LCompanionClass$Companion;
  // LCompanionWithMethodCollision$Companion;
  // LNamedCompanionClass$Custom;
  // LCompanionWithInterCalls$Companion;
  // LCompanionWithJvmStaticBridge$Companion;
  // LCompanionWithDefaults$Companion;
  // LAbstractOuterClass$Companion;
  // LCompanionWithConstVal$Companion;
  // LCompanionEscapes$Companion;
  // + LCompanionWithSynchronized$Companion;
  // + LCompanionWithNativeMethod$Companion;
  // + LCompanionWithKeptBridge$Companion;
  // + LInterfaceOuter$Companion;
  EXPECT_EQ(stats.kotlin_companion_class, 14);

  // LKotlinLambdaInline$foo$1;
  // LKotlinLambdaInline$bar$1;
  // LKotlinLambdaInline$baz$1;
  // LFooDelagates$lazyValue$2;
  EXPECT_EQ(stats.kotlin_anonymous_class, 4);

  // LKotlinDefaultArgs.greet$default, with 2 default args
  // LCompanionWithDefaults$Companion.greet$default, with 1 default arg
  EXPECT_EQ(stats.kotlin_default_arg_method, 2);
  EXPECT_EQ(stats.kotlin_default_arg_check_insns, 3);
  EXPECT_EQ(stats.kotlin_and_lit_insns, 3);

  // LKotlinLambdaInline;.doCalc takes `(Long, Long) -> Long` (Function2).
  // LKotlinLayzyKt;.lazyFn and LFoo;.<init> each take `() -> T` (Function0).
  EXPECT_EQ(stats.kotlin_lambda_type_method_params, 3u);
}
} // namespace
