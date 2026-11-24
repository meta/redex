/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "GlobalTypeAnalyzer.h"

#include "CallGraph.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "RedexTest.h"
#include "Walkers.h"

using namespace type_analyzer;
using namespace type_analyzer::global;

struct GlobalTypeAnalysisTest : public RedexTest {
 public:
  GlobalTypeAnalysisTest() {
    auto* cls_o = DexType::make_type("LO;");
    ClassCreator creator(cls_o);
    creator.set_super(type::java_lang_Object());

    auto* m_init = assembler::method_from_string(R"(
      (method (public constructor) "LO;.<init>:()V"
       (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
       )
      )
    )");
    creator.add_method(m_init);
    m_cls_o = creator.create();
  }

 protected:
  void prepare_scope(Scope& scope) { scope.push_back(m_cls_o); }

  // Analyzes a constructor `LFoo;.<init>:(LFoo;Z)V` with body `ctor_body`,
  // whose class extends `LBase;`, has a kept field `f`, a static field
  // `sInstance` and a method `mutate` that stores a `B` into `f`, and returns
  // the argument types of `take`, which the constructor may call.
  // `LBase;.<init>:()V` keeps `this`. The class also gets the methods in
  // `extra_methods`.
  ArgumentTypeEnvironment arguments_of_take(
      const std::string& ctor_body,
      const std::vector<std::string>& extra_methods = {}) {
    Scope scope;
    prepare_scope(scope);
    ClassCreator b(DexType::make_type("LB;"));
    b.set_super(type::java_lang_Object());
    b.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LB;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (return-void))))"));
    scope.push_back(b.create());
    ClassCreator base(DexType::make_type("LBase;"));
    base.set_super(type::java_lang_Object());
    base.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LBase;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (return-void))))"));
    scope.push_back(base.create());
    ClassCreator foo(DexType::make_type("LFoo;"));
    foo.set_super(DexType::make_type("LBase;"));
    auto* f = DexField::make_field("LFoo;.f:Ljava/lang/Object;")
                  ->make_concrete(ACC_PUBLIC);
    f->rstate.set_root();
    foo.add_field(f);
    // Only constructors write `g`.
    foo.add_field(DexField::make_field("LFoo;.g:Ljava/lang/Object;")
                      ->make_concrete(ACC_PUBLIC));
    foo.add_field(DexField::make_field("LFoo;.sInstance:LFoo;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    foo.add_method(assembler::method_from_string(
        R"((method (public constructor) "LFoo;.<init>:(LFoo;Z)V" ()" +
        ctor_body + "))"));
    foo.add_method(assembler::method_from_string(R"(
      (method (public static) "LFoo;.mutate:(LFoo;)V"
       (
        (load-param-object v0)
        (new-instance "LB;")
        (move-result-pseudo-object v1)
        (invoke-direct (v1) "LB;.<init>:()V")
        (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
        (return-void)
       )
      )
    )"));
    foo.add_method(assembler::method_from_string(R"(
      (method (public) "LFoo;.reset:()V"
       (
        (load-param-object v0)
        (new-instance "LB;")
        (move-result-pseudo-object v1)
        (invoke-direct (v1) "LB;.<init>:()V")
        (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
        (return-void)
       )
      )
    )"));
    auto* take = assembler::method_from_string(R"(
      (method (public static) "LFoo;.take:(Ljava/lang/Object;)V"
       ((load-param-object v0) (return-void)))
    )");
    foo.add_method(take);
    for (const auto& method : extra_methods) {
      foo.add_method(assembler::method_from_string(method));
    }
    auto* main = assembler::method_from_string(R"(
      (method (public static) "LFoo;.main:(LFoo;Z)V"
       (
        (load-param-object v0)
        (load-param v1)
        (new-instance "LFoo;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LFoo;.<init>:(LFoo;Z)V")
        (return-void)
       )
      )
    )");
    main->rstate.set_root();
    foo.add_method(main);
    scope.push_back(foo.create());
    walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
    // As GlobalTypeAnalysisPass runs it, with a call graph that resolves
    // calls.
    GlobalTypeAnalysis analysis(/* max_global_analysis_iteration */ 10,
                                /* use_multiple_callee_callgraph */ true);
    auto gta = analysis.analyze(scope);
    const auto& graph = gta->get_call_graph();
    return gta->get_entry_state_at(graph.node(take))
        .get(CURRENT_PARTITION_LABEL);
  }

  DexTypeDomain get_type_domain(const std::string& type_name) {
    return DexTypeDomain::create_not_null(
        DexType::make_type(DexString::make_string(type_name)));
  }

  SingletonDexTypeDomain get_singleton_type_domain(
      const std::string& type_name) {
    return SingletonDexTypeDomain(
        DexType::make_type(DexString::make_string(type_name)));
  }

  DexClass* m_cls_o;
};

TEST_F(GlobalTypeAnalysisTest, SimpleArgumentPassingTest) {
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
      (new-instance "LO;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (invoke-static (v0) "LA;.bar:(LO;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  auto cg = std::make_shared<call_graph::Graph>(call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope));
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  GlobalTypeAnalyzer gta(cg, {}, {});
  gta.run(ArgumentTypePartition{
      {CURRENT_PARTITION_LABEL, ArgumentTypeEnvironment()}});

  const auto& graph = gta.get_call_graph();

  auto foo_arg_env =
      gta.get_entry_state_at(graph.node(meth_foo)).get(CURRENT_PARTITION_LABEL);
  EXPECT_TRUE(foo_arg_env.is_top());
  auto bar_arg_env =
      gta.get_entry_state_at(graph.node(meth_bar)).get(CURRENT_PARTITION_LABEL);
  EXPECT_EQ(bar_arg_env,
            ArgumentTypeEnvironment({{0, get_type_domain("LO;")}}));
}

// A method handle call has no callee to resolve, so the type of what it
// returns is unknown.
TEST_F(GlobalTypeAnalysisTest, MethodHandleCallResultTest) {
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
    (method (public static) "LA;.foo:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()LO;")
      (move-result-object v1)
      (invoke-static (v1) "LA;.bar:(LO;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  auto cg = std::make_shared<call_graph::Graph>(call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope));
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  GlobalTypeAnalyzer gta(cg, {}, {});
  gta.run(ArgumentTypePartition{
      {CURRENT_PARTITION_LABEL, ArgumentTypeEnvironment()}});

  const auto& graph = gta.get_call_graph();
  auto bar_arg_env =
      gta.get_entry_state_at(graph.node(meth_bar)).get(CURRENT_PARTITION_LABEL);
  EXPECT_TRUE(bar_arg_env.get(0).is_top());
}

TEST_F(GlobalTypeAnalysisTest, ArgumentPassingJoinWithNullTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:(LO;LO;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (return-void)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (const v0 0)
      (const v1 0)
      (new-instance "LO;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "LO;.<init>:()V")

      (if-eqz v0 :lb0)
      (new-instance "LO;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LO;.<init>:()V")
      (goto :lb0)

      (:lb0)
      (invoke-static (v1 v2) "LA;.bar:(LO;LO;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  auto cg = std::make_shared<call_graph::Graph>(call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope));
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  GlobalTypeAnalyzer gta(cg, {}, {});
  gta.run(ArgumentTypePartition{
      {CURRENT_PARTITION_LABEL, ArgumentTypeEnvironment()}});

  const auto& graph = gta.get_call_graph();

  auto foo_arg_env =
      gta.get_entry_state_at(graph.node(meth_foo)).get(CURRENT_PARTITION_LABEL);
  EXPECT_TRUE(foo_arg_env.is_top());
  auto bar_arg_env =
      gta.get_entry_state_at(graph.node(meth_bar)).get(CURRENT_PARTITION_LABEL);
  auto arg0 = bar_arg_env.get(0);
  EXPECT_FALSE(arg0.is_top());
  EXPECT_EQ(arg0.get_single_domain(), get_singleton_type_domain("LO;"));
  EXPECT_TRUE(arg0.is_nullable());
  auto arg1 = bar_arg_env.get(1);
  EXPECT_EQ(arg1, get_type_domain("LO;"));
}

TEST_F(GlobalTypeAnalysisTest, CaughtExceptionArgumentTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_may_throw = assembler::method_from_string(R"(
    (method (public static) "LA;.mayThrow:()V"
     (
      (return-void)
     )
    )
  )");
  creator.add_method(meth_may_throw);

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:(Ljava/lang/Throwable;)V"
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
      (.try_start t)
      (invoke-static () "LA;.mayThrow:()V")
      (.try_end t)
      (return-void)
      (.catch (t))
      (move-exception v0)
      (invoke-static (v0) "LA;.bar:(Ljava/lang/Throwable;)V")
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  auto cg = std::make_shared<call_graph::Graph>(call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope));
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  GlobalTypeAnalyzer gta(cg, {}, {});
  gta.run(ArgumentTypePartition{
      {CURRENT_PARTITION_LABEL, ArgumentTypeEnvironment()}});

  const auto& graph = gta.get_call_graph();
  auto bar_arg_env =
      gta.get_entry_state_at(graph.node(meth_bar)).get(CURRENT_PARTITION_LABEL);
  auto arg0 = bar_arg_env.get(0);
  EXPECT_TRUE(arg0.is_not_null());
  EXPECT_EQ(arg0.get_dex_type(),
            std::optional<const DexType*>(type::java_lang_Throwable()));
  // The handler can catch any subclass, so j.l.Throwable must not become the
  // exact class set that TypeAnalysisAwareRemoveUnreachable prunes with.
  EXPECT_TRUE(arg0.get_set_domain().is_top());
}

TEST_F(GlobalTypeAnalysisTest, ReturnTypeTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public static) "LA;.bar:()LO;"
     (
      (new-instance "LO;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LO;.<init>:()V")
      (return-object v1)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (invoke-static () "LA;.bar:()LO;")
      (move-result-object v0)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  call_graph::Graph cg = call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  EXPECT_EQ(wps.get_return_type(meth_bar), get_type_domain("LO;"));

  auto lta = gta->get_replayable_local_analysis(meth_foo);
  auto* code = meth_foo->get_code();
  auto bar_exit_env = lta->get_exit_state_at(code->cfg().exit_block());
  EXPECT_EQ(bar_exit_env.get_reg_environment().get(0), get_type_domain("LO;"));
}

// The value of a method handle or method type constant is not modeled, so its
// move-result-pseudo gets an unknown type, not the type of an earlier result.
TEST_F(GlobalTypeAnalysisTest, MethodConstantTypeTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (const-string "x")
      (move-result-pseudo-object v0)
      (const-method-handle invoke-static "LA;.foo:()V")
      (move-result-pseudo-object v1)
      (const-method-type "(I)V")
      (move-result-pseudo-object v2)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto lta = gta->get_replayable_local_analysis(meth_foo);
  auto* code = meth_foo->get_code();
  auto exit_env = lta->get_exit_state_at(code->cfg().exit_block());
  EXPECT_EQ(exit_env.get_reg_environment().get(0),
            get_type_domain("Ljava/lang/String;"));
  EXPECT_TRUE(exit_env.get_reg_environment().get(1).is_top());
  EXPECT_TRUE(exit_env.get_reg_environment().get(2).is_top());
}

TEST_F(GlobalTypeAnalysisTest, SimpleFieldTypeTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* field_1 = DexField::make_field("LA;.f1:LO;")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_1);

  auto* meth_init = assembler::method_from_string(R"(
    (method (public constructor) "LA;.<init>:()V"
     (
      (load-param-object v1) ; 'this' argument
      (new-instance "LO;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (iput-object v0 v1 "LA;.f1:LO;")
      (return-void)
     )
    )
  )");
  creator.add_method(meth_init);

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public) "LA;.bar:()LO;"
     (
      (load-param-object v1) ; 'this' argument
      (iget-object v1 "LA;.f1:LO;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LA;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LA;.<init>:()V")
      (invoke-virtual (v0) "LA;.bar:()LO;")
      (move-result-object v1)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  call_graph::Graph cg = call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  EXPECT_EQ(wps.get_field_type(field_1),
            get_type_domain("LO;").join(DexTypeDomain::null()));
  EXPECT_EQ(wps.get_return_type(meth_bar),
            get_type_domain("LO;").join(DexTypeDomain::null()));
  auto lta = gta->get_replayable_local_analysis(meth_foo);
  auto* code = meth_foo->get_code();
  auto foo_exit_env = lta->get_exit_state_at(code->cfg().exit_block());
  EXPECT_EQ(foo_exit_env.get_reg_environment().get(1),
            get_type_domain("LO;").join(DexTypeDomain::null()));
}

TEST_F(GlobalTypeAnalysisTest, FieldStoredOnOtherObjectByConstructorTest) {
  // Java: class A { O f1; A(A other) { O o = new O(); f1 = o; other.f1 = o; } }
  // Every store to f1 comes from A's constructor, so the type of every store
  // in the program bounds the type of f1, even though one store goes to
  // another A.
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* field_1 = DexField::make_field("LA;.f1:LO;")->make_concrete(ACC_PUBLIC);
  creator.add_field(field_1);

  auto* meth_init = assembler::method_from_string(R"(
    (method (public constructor) "LA;.<init>:(LA;)V"
     (
      (load-param-object v1) ; 'this' argument
      (load-param-object v2)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (new-instance "LO;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (iput-object v0 v1 "LA;.f1:LO;")
      (iput-object v0 v2 "LA;.f1:LO;")
      (return-void)
     )
    )
  )");
  creator.add_method(meth_init);

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public) "LA;.bar:()LO;"
     (
      (load-param-object v1) ; 'this' argument
      (iget-object v1 "LA;.f1:LO;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:(LA;)V"
     (
      (load-param-object v2)
      (new-instance "LA;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v2) "LA;.<init>:(LA;)V")
      (invoke-virtual (v0) "LA;.bar:()LO;")
      (move-result-object v1)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  EXPECT_EQ(wps.get_field_type(field_1),
            get_type_domain("LO;").join(DexTypeDomain::null()));
  EXPECT_EQ(wps.get_return_type(meth_bar),
            get_type_domain("LO;").join(DexTypeDomain::null()));
}

TEST_F(GlobalTypeAnalysisTest, ClinitSimpleTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* field_1 = DexField::make_field("LA;.f1:LO;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  creator.add_field(field_1);

  auto* meth_clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LA;.<clinit>:()V"
     (
      (new-instance "LO;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (sput-object v0 "LA;.f1:LO;")
      (return-void)
     )
    )
  )");
  creator.add_method(meth_clinit);

  auto* meth_init = assembler::method_from_string(R"(
    (method (public constructor) "LA;.<init>:()V"
     (
      (load-param-object v1) ; 'this' argument
      (return-void)
     )
    )
  )");
  creator.add_method(meth_init);

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public) "LA;.bar:()LO;"
     (
      (load-param-object v1) ; 'this' argument
      (sget-object "LA;.f1:LO;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LA;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LA;.<init>:()V")
      (invoke-virtual (v0) "LA;.bar:()LO;")
      (move-result-object v1)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  call_graph::Graph cg = call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  EXPECT_TRUE(wps.get_field_type(field_1).is_top());
  EXPECT_TRUE(wps.get_return_type(meth_bar).is_top());
  auto lta = gta->get_replayable_local_analysis(meth_foo);
  auto* code = meth_foo->get_code();
  auto foo_exit_env = lta->get_exit_state_at(code->cfg().exit_block());
  EXPECT_TRUE(foo_exit_env.get_reg_environment().get(1).is_top());
}

TEST_F(GlobalTypeAnalysisTest, StaticFieldWithEncodedValueTest) {
  Scope scope;
  prepare_scope(scope);

  auto* cls_a = DexType::make_type("LA;");
  ClassCreator creator(cls_a);
  creator.set_super(type::java_lang_Object());

  auto* field_1 =
      DexField::make_field("LA;.f1:LO;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::unique_ptr<DexEncodedValue>(
                              new DexEncodedValueBit(DEVT_NULL, false)));
  creator.add_field(field_1);

  auto* field_2 =
      DexField::make_field("LA;.f2:Ljava/lang/String;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::unique_ptr<DexEncodedValue>(
                  new DexEncodedValueString(DexString::make_string("yoyo"))));
  creator.add_field(field_2);

  auto* field_3 =
      DexField::make_field("LA;.f3:Ljava/lang/Class;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::unique_ptr<DexEncodedValue>(
                  new DexEncodedValueType(DexType::make_type("L0"))));
  creator.add_field(field_3);

  // No clinit
  auto* meth_init = assembler::method_from_string(R"(
    (method (public constructor) "LA;.<init>:()V"
     (
      (load-param-object v1) ; 'this' argument
      (return-void)
     )
    )
  )");
  creator.add_method(meth_init);

  auto* meth_bar = assembler::method_from_string(R"(
    (method (public) "LA;.bar:()LO;"
     (
      (load-param-object v1) ; 'this' argument
      (sget-object "LA;.f1:LO;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_bar);

  auto* meth_baz = assembler::method_from_string(R"(
    (method (public) "LA;.baz:()Ljava/lang/String;"
     (
      (load-param-object v1) ; 'this' argument
      (sget-object "LA;.f2:Ljava/lang/String;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_baz);

  auto* meth_buk = assembler::method_from_string(R"(
    (method (public) "LA;.buk:()Ljava/lang/Class;"
     (
      (load-param-object v1) ; 'this' argument
      (sget-object "LA;.f3:Ljava/lang/Class;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  creator.add_method(meth_buk);

  auto* meth_foo = assembler::method_from_string(R"(
    (method (public static) "LA;.foo:()V"
     (
      (new-instance "LA;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LA;.<init>:()V")
      (invoke-virtual (v0) "LA;.bar:()LO;")
      (move-result-object v1)
      (invoke-virtual (v0) "LA;.baz:()Ljava/lang/String;")
      (move-result-object v2)
      (invoke-virtual (v0) "LA;.buk:()Ljava/lang/Class;")
      (move-result-object v3)
      (return-void)
     )
    )
  )");
  meth_foo->rstate.set_root();
  creator.add_method(meth_foo);
  scope.push_back(creator.create());

  call_graph::Graph cg = call_graph::single_callee_graph(
      *method_override_graph::build_graph(scope), scope);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  EXPECT_EQ(wps.get_field_type(field_1), DexTypeDomain::null());
  EXPECT_EQ(wps.get_return_type(meth_bar), DexTypeDomain::null());

  EXPECT_EQ(wps.get_field_type(field_2),
            DexTypeDomain::create_not_null(type::java_lang_String())
                .join(DexTypeDomain::null()));
  EXPECT_EQ(wps.get_return_type(meth_baz),
            DexTypeDomain::create_not_null(type::java_lang_String())
                .join(DexTypeDomain::null()));

  EXPECT_EQ(wps.get_field_type(field_3),
            DexTypeDomain::create_not_null(type::java_lang_Class())
                .join(DexTypeDomain::null()));
  EXPECT_EQ(wps.get_return_type(meth_buk),
            DexTypeDomain::create_not_null(type::java_lang_Class())
                .join(DexTypeDomain::null()));
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadAfterEscapeSeesOtherStores) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (invoke-static (v0) "LFoo;.mutate:(LFoo;)V")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // `mutate` stored a `B`, so nothing is known about what `take` receives.
  EXPECT_TRUE(args.get(0).is_top()) << args;
}

TEST_F(GlobalTypeAnalysisTest,
       ConstructorReadOfConstructorOnlyFieldAfterEscape) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (invoke-direct (v0) "LBase;.<init>:()V")
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.g:Ljava/lang/Object;")
    (sput-object v0 "LFoo;.sInstance:LFoo;")
    (iget-object v0 "LFoo;.g:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // Code that sees the published `this` cannot store to `g`.
  EXPECT_EQ(args, ArgumentTypeEnvironment({{0, get_type_domain("LO;")}}))
      << args;
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadBeforeOwnStoreUsesWholeProgram) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (iget-object v0 "LFoo;.g:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.g:Ljava/lang/Object;")
    (return-void)
  )");
  // The constructor has stored nothing yet, so the field's type comes from
  // the whole program.
  EXPECT_FALSE(args.get(0).is_top()) << args;
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadAfterOwnMethodCallOnThis) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (invoke-virtual (v0) "LFoo;.reset:()V")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // `this.reset()` stored a `B`, so nothing is known about what `take`
  // receives.
  EXPECT_TRUE(args.get(0).is_top()) << args;
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadAfterOwnMethodCallOnOther) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (invoke-virtual (v3) "LFoo;.reset:()V")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // `other.reset()` cannot store into `this`.
  EXPECT_EQ(args, ArgumentTypeEnvironment({{0, get_type_domain("LO;")}}))
      << args;
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadAfterMaybeThisStore) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (move-object v5 v3)
    (if-eqz v4 :other)
    (move-object v5 v0)
    (:other)
    (new-instance "LB;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LB;.<init>:()V")
    (iput-object v1 v5 "LFoo;.f:Ljava/lang/Object;")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // The store may have written a `B` to `this`.
  EXPECT_EQ(args.get(0), get_type_domain("LO;").join(get_type_domain("LB;")))
      << args;
}

TEST_F(GlobalTypeAnalysisTest,
       ConstructorReadAfterSuperConstructorKeepingThis) {
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (invoke-direct (v0) "LBase;.<init>:()V")
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )");
  // The superclass constructor keeps `this`, so the read sees the store.
  EXPECT_EQ(args, ArgumentTypeEnvironment({{0, get_type_domain("LO;")}}))
      << args;
}

TEST_F(GlobalTypeAnalysisTest, ConstructorReadAfterOwnConstructorCall) {
  // `Foo()` keeps `this` but stores a `B` into `f`.
  const auto args = arguments_of_take(R"(
    (load-param-object v0)
    (load-param-object v3)
    (load-param v4)
    (new-instance "LO;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LO;.<init>:()V")
    (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
    (invoke-direct (v0) "LFoo;.<init>:()V")
    (iget-object v0 "LFoo;.f:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-static (v2) "LFoo;.take:(Ljava/lang/Object;)V")
    (return-void)
  )",
                                      {R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (new-instance "LB;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LB;.<init>:()V")
      (iput-object v1 v0 "LFoo;.f:Ljava/lang/Object;")
      (return-void)
     )
    )
  )"});
  EXPECT_TRUE(args.get(0).is_top()) << args;
}

// Tool-generated: set() writes a P, a subclass of O, to A.f1 through a put
// method handle, so A.f1 does not hold only the O that the program writes
// with put instructions.
class PutHandleFieldTypeTest : public GlobalTypeAnalysisTest,
                               public ::testing::WithParamInterface<bool> {};

TEST_P(PutHandleFieldTypeTest, fieldWrittenThroughPutHandle) {
  const bool is_static_field = GetParam();
  Scope scope;
  prepare_scope(scope);

  ClassCreator p_creator(DexType::make_type("LP;"));
  p_creator.set_super(DexType::make_type("LO;"));
  p_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LP;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (return-void)
     )
    )
  )"));
  scope.push_back(p_creator.create());

  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  auto* field_1 = DexField::make_field("LA;.f1:LO;")
                      ->make_concrete(is_static_field ? ACC_PUBLIC | ACC_STATIC
                                                      : ACC_PUBLIC);
  creator.add_field(field_1);

  // The constructor or, for the static field, init() writes an O to f1; set(a)
  // writes a P to f1 through a handle.
  auto* meth_init = assembler::method_from_string(is_static_field ? R"(
    (method (public static) "LA;.init:()V"
     (
      (new-instance "LO;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LO;.<init>:()V")
      (sput-object v1 "LA;.f1:LO;")
      (return-void)
     )
    )
  )"
                                                                  : R"(
    (method (public constructor) "LA;.<init>:()V"
     (
      (load-param-object v0)
      (new-instance "LO;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LO;.<init>:()V")
      (iput-object v1 v0 "LA;.f1:LO;")
      (return-void)
     )
    )
  )");
  meth_init->rstate.set_root();
  creator.add_method(meth_init);

  const std::string handle =
      is_static_field ? R"((const-method-handle static-put "LA;.f1:LO;")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v2 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LO;)V"))"
                      : R"((const-method-handle instance-put "LA;.f1:LO;")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v2 v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LA;LO;)V"))";
  auto* meth_set = assembler::method_from_string(R"(
    (method (public static) "LA;.set:(LA;)V"
     (
      (load-param-object v0)
      (new-instance "LP;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LP;.<init>:()V")
      )" + handle + R"(
      (return-void)
     )
    )
  )");
  meth_set->rstate.set_root();
  creator.add_method(meth_set);
  scope.push_back(creator.create());

  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis(/* max_global_analysis_iteration */ 10,
                              /* use_multiple_callee_callgraph */ false,
                              /* only_aggregate_safely_inferrable_fields */
                              false);
  auto gta = analysis.analyze(scope);
  EXPECT_TRUE(gta->get_whole_program_state().get_field_type(field_1).is_top());
}

INSTANTIATE_TEST_SUITE_P(FieldKind,
                         PutHandleFieldTypeTest,
                         ::testing::Bool(),
                         [](const ::testing::TestParamInfo<bool>& info) {
                           return info.param ? "Static" : "Instance";
                         });

// Tool-generated: set() writes a P through a static-put method handle of
// LB;.f1, which ART resolves to the static A.f1, past the instance field B.f1.
// So A.f1 does not hold only the O that init() writes.
TEST_F(GlobalTypeAnalysisTest, inheritedFieldWrittenThroughPutHandle) {
  Scope scope;
  prepare_scope(scope);

  ClassCreator p_creator(DexType::make_type("LP;"));
  p_creator.set_super(DexType::make_type("LO;"));
  p_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LP;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LO;.<init>:()V")
      (return-void)
     )
    )
  )"));
  scope.push_back(p_creator.create());

  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());
  auto* a_f1 = DexField::make_field("LA;.f1:LO;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a_creator.add_field(a_f1);
  auto* meth_init = assembler::method_from_string(R"(
    (method (public static) "LA;.init:()V"
     (
      (new-instance "LO;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LO;.<init>:()V")
      (sput-object v1 "LA;.f1:LO;")
      (return-void)
     )
    )
  )");
  meth_init->rstate.set_root();
  a_creator.add_method(meth_init);
  auto* a_cls = a_creator.create();
  scope.push_back(a_cls);

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(a_cls->get_type());
  b_creator.add_field(
      DexField::make_field("LB;.f1:LO;")->make_concrete(ACC_PUBLIC));
  auto* meth_set = assembler::method_from_string(R"(
    (method (public static) "LB;.set:()V"
     (
      (new-instance "LP;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LP;.<init>:()V")
      (const-method-handle static-put "LB;.f1:LO;")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v2 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LO;)V")
      (return-void)
     )
    )
  )");
  meth_set->rstate.set_root();
  b_creator.add_method(meth_set);
  scope.push_back(b_creator.create());

  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  GlobalTypeAnalysis analysis(/* max_global_analysis_iteration */ 10,
                              /* use_multiple_callee_callgraph */ false,
                              /* only_aggregate_safely_inferrable_fields */
                              false);
  auto gta = analysis.analyze(scope);
  EXPECT_TRUE(gta->get_whole_program_state().get_field_type(a_f1).is_top());
}
