/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeAnalysisTransform.h"
#include "GlobalTypeAnalyzer.h"

#include "Creators.h"
#include "IRAssembler.h"
#include "KotlinNullCheckMethods.h"
#include "RedexTest.h"
#include "Walkers.h"

using namespace type_analyzer;

struct TypeAnalysisTransformTest : public RedexTest {
 public:
  TypeAnalysisTransformTest() {
    auto* cls_arg = DexType::make_type("LARG;");
    ClassCreator creator_arg(cls_arg);
    creator_arg.set_super(type::java_lang_Object());

    auto* method_arg_init = assembler::method_from_string(R"(
      (method (public constructor) "LARG;.<init>:()V"
       (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
       )
      )
    )");
    creator_arg.add_method(method_arg_init);
    m_cls_arg = creator_arg.create();

    auto* cls_o = DexType::make_type("LO;");
    ClassCreator creator(cls_o);
    creator.set_super(type::java_lang_Object());

    m_method_call = assembler::method_from_string(R"(
      (method (public static) "LO;.bar:(LARG;)V"
       (
        (load-param-object v0)
        (const-string "args")
        (move-result-pseudo v1)
        (invoke-static (v0 v1) "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/Object;Ljava/lang/String;)V")
        (return-void)
       )
      )
    )");
    creator.add_method(m_method_call);
    m_cls_o = creator.create();
  }

 protected:
  void prepare_scope(Scope& scope) {
    scope.push_back(m_cls_arg);
    scope.push_back(m_cls_o);
  }

  void run_opt(Scope& scope) {
    global::GlobalTypeAnalysis analysis(10);
    auto gta = analysis.analyze(scope);
    auto wps = gta->get_whole_program_state();
    type_analyzer::Transform::Config config;
    config.remove_kotlin_null_check_assertions = true;
    type_analyzer::Transform::Stats transform_stats;

    transform_stats = walk::parallel::methods<type_analyzer::Transform::Stats>(
        scope, [&](DexMethod* method) {
          if (method->get_code() == nullptr) {
            return type_analyzer::Transform::Stats();
          }

          type_analyzer::Transform::NullAssertionSet null_assertion_set =
              kotlin_nullcheck_wrapper::get_kotlin_null_assertions();
          auto lta = gta->get_replayable_local_analysis(method);
          Transform tf(config);
          return tf.apply(*lta, wps, method, null_assertion_set);
        });
  }

  DexClass* m_cls_arg;
  DexClass* m_cls_o;
  DexMethod* m_method_call;
};

TEST_F(TypeAnalysisTransformTest, SimpleArgumentPassingTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:(LO;)V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LARG;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LO;.bar:(LARG;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());
  run_opt(scope);
  m_method_call->get_code()->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
       (
        (load-param-object v0)
        (const-string "args")
        (move-result-pseudo v1)
        (return-void)
       )
    )");

  EXPECT_CODE_EQ(m_method_call->get_code(), expected_code.get());
}

TEST_F(TypeAnalysisTransformTest, NegativeArgumentPassingTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:(LO;)V"
     (
      (const v0 0)
      (invoke-static (v0) "LO;.bar:(LARG;)V")
      (return-void)
     )
    )
  )");
  meth_bar->rstate.set_root();
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LARG;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LO;.bar:(LARG;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());
  run_opt(scope);

  m_method_call->get_code()->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
       (
        (load-param-object v0)
        (const-string "args")
        (move-result-pseudo v1)
        (invoke-static (v0 v1) "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/Object;Ljava/lang/String;)V")
        (return-void)
       )
    )");

  EXPECT_CODE_EQ(m_method_call->get_code(), expected_code.get());
}

TEST_F(TypeAnalysisTransformTest, MultiArgumentPassingTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:(LO;)V"
     (
      (new-instance "LARG;")
      (move-result-pseudo-object v1)
      (invoke-static (v1) "LO;.bar:(LARG;)V")
      (return-void)
     )
    )
  )");
  meth_bar->rstate.set_root();
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LARG;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LO;.bar:(LARG;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());
  run_opt(scope);
  m_method_call->get_code()->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
       (
        (load-param-object v0)
        (const-string "args")
        (move-result-pseudo v1)
        (return-void)
       )
    )");

  EXPECT_CODE_EQ(m_method_call->get_code(), expected_code.get());
}
