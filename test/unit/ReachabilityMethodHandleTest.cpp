/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAnnotation.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "Reachability.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Walkers.h"

namespace {

DexClass* make_class(std::string_view name,
                     DexType* super = type::java_lang_Object(),
                     DexAccessFlags access = ACC_PUBLIC) {
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(super);
  cc.set_access(access);
  return cc.create();
}

DexMethod* add_method(DexClass* cls,
                      const std::string& spec,
                      DexAccessFlags access,
                      bool is_virtual,
                      const std::string& code) {
  auto* m = DexMethod::make_method(spec)->make_concrete(
      access, assembler::ircode_from_string(code), is_virtual);
  cls->add_method(m);
  return m;
}

void add_init(DexClass* cls, std::string_view super_init) {
  add_method(cls, show(cls->get_type()) + ".<init>:()V",
             ACC_PUBLIC | ACC_CONSTRUCTOR, false,
             "((load-param-object v0) (invoke-direct (v0) \"" +
                 std::string(super_init) + "\") (return-void))");
}

DexMethod* add_root_main(Scope& scope, const std::string& code) {
  auto* main_cls = make_class("LMain;");
  auto* main = add_method(main_cls, "LMain;.main:()V", ACC_PUBLIC | ACC_STATIC,
                          false, code);
  main->rstate.set_root();
  main_cls->rstate.set_root();
  scope.push_back(main_cls);
  return main;
}

// LBase; declares m(), LSub; extends LBase; and overrides it.
struct Hierarchy {
  DexMethod* sub_m;
  Scope scope;
};

Hierarchy make_hierarchy() {
  auto* base = make_class("LBase;");
  add_init(base, "Ljava/lang/Object;.<init>:()V");
  add_method(base, "LBase;.m:()V", ACC_PUBLIC, true,
             "((load-param-object v0) (return-void))");
  auto* sub = make_class("LSub;", base->get_type());
  add_init(sub, "LBase;.<init>:()V");
  auto* sub_m = add_method(sub, "LSub;.m:()V", ACC_PUBLIC, true,
                           "((load-param-object v0) (return-void))");
  return {sub_m, Scope{base, sub}};
}

constexpr std::string_view kNewSub = R"(
    (new-instance "LSub;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LSub;.<init>:()V")
)";

constexpr std::string_view kInvokeExact =
    "\"Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)"
    "Ljava/lang/Object;\"";

// Whether `target` is reachable and keeps its body (a zombie method's body is
// replaced by a throw), first with every optional reachability refinement off,
// then with those that app builds turn on. The returning check stays off: the
// test's Object.<init> has no code, so it never returns.
std::pair<bool, bool> is_live(const Scope& scope, const DexMethod* target) {
  walk::code(scope, [](auto*, IRCode& code) {
    if (!code.cfg_built()) {
      code.build_cfg();
    }
  });
  auto graph = method_override_graph::build_graph(scope);
  std::pair<bool, bool> res;
  for (bool refined : {false, true}) {
    int num_ignore_check_strings = 0;
    reachability::IgnoreSets ig_sets;
    reachability::ReachableAspects aspects;
    auto reachables = reachability::compute_reachable_objects(
        scope, *graph, ig_sets, &num_ignore_check_strings, &aspects,
        /* record_reachability */ false,
        /* relaxed_keep_class_members */ refined,
        /* relaxed_keep_interfaces */ refined,
        /* cfg_gathering_check_instantiable */ refined,
        /* cfg_gathering_check_instance_callable */ refined,
        /* cfg_gathering_check_returning */ false);
    reachability::compute_zombie_methods(*graph, *reachables, aspects);
    (refined ? res.second : res.first) =
        reachables->marked_unsafe(target) &&
        std::find(aspects.zombie_methods.begin(), aspects.zombie_methods.end(),
                  target) == aspects.zombie_methods.end();
  }
  return res;
}

} // namespace

class ReachabilityMethodHandleTest : public RedexTest {
 public:
  ReachabilityMethodHandleTest() {
    DexMethod::make_method("Ljava/lang/Object;.<init>:()V")
        ->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, false);
  }
};

TEST_F(ReachabilityMethodHandleTest, InvokeVirtualMarksOverride) {
  auto h = make_hierarchy();
  add_root_main(h.scope, std::string("(") + std::string(kNewSub) + R"(
    (invoke-virtual (v0) "LBase;.m:()V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(h.scope, h.sub_m), std::make_pair(true, true));
}

TEST_F(ReachabilityMethodHandleTest, InvokeInstanceHandleMarksOverride) {
  auto h = make_hierarchy();
  add_root_main(h.scope, std::string("(") + std::string(kNewSub) + R"(
    (const-method-handle invoke-instance "LBase;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )" +
                             std::string(kInvokeExact) +
                             R"( "(LBase;)V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(h.scope, h.sub_m), std::make_pair(true, true));
}

TEST_F(ReachabilityMethodHandleTest,
       InvokeInstanceHandleBootstrapArgumentMarksOverride) {
  auto h = make_hierarchy();
  auto* main =
      add_root_main(h.scope, std::string("(") + std::string(kNewSub) + R"(
    (invoke-static (v0) "LBoot;.placeholder:(LBase;)V")
    (return-void)
  ))");
  std::vector<std::unique_ptr<DexEncodedValue>> bsm_args;
  bsm_args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_INSTANCE, "LBase;.m:()V")));
  redex::make_invoke_custom(main->get_code(), "run", "(LBase;)V",
                            std::move(bsm_args));
  EXPECT_EQ(is_live(h.scope, h.sub_m), std::make_pair(true, true));
}

TEST_F(ReachabilityMethodHandleTest, InvokeInterfaceHandleMarksImplementation) {
  auto* intf = make_class("LI;", type::java_lang_Object(),
                          ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  intf->add_method(DexMethod::make_method("LI;.m:()V")
                       ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, true));
  auto* impl = make_class("LImpl;");
  impl->set_interfaces(DexTypeList::make_type_list({intf->get_type()}));
  add_init(impl, "Ljava/lang/Object;.<init>:()V");
  auto* impl_m = add_method(impl, "LImpl;.m:()V", ACC_PUBLIC, true,
                            "((load-param-object v0) (return-void))");
  Scope scope{intf, impl};
  add_root_main(scope, std::string(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (const-method-handle invoke-interface "LI;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )") +
                           std::string(kInvokeExact) +
                           R"( "(LI;)V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(scope, impl_m), std::make_pair(true, true));
}

namespace {

// LSub;.callSuper runs `call_super`, which calls LBase;.m without virtual
// dispatch. Only LBase;.m's body references LHelper;.h. LSub; overrides m if
// `sub_overrides`.
struct SuperCall {
  DexMethod* helper_h;
  Scope scope;
};

SuperCall make_super_call(std::string_view call_super,
                          bool sub_overrides = true) {
  auto* helper = make_class("LHelper;");
  auto* helper_h = add_method(helper, "LHelper;.h:()V", ACC_PUBLIC | ACC_STATIC,
                              false, "((return-void))");
  auto* base = make_class("LBase;");
  add_init(base, "Ljava/lang/Object;.<init>:()V");
  add_method(base, "LBase;.m:()V", ACC_PUBLIC, true, R"((
    (load-param-object v0)
    (invoke-static () "LHelper;.h:()V")
    (return-void)
  ))");
  auto* sub = make_class("LSub;", base->get_type());
  add_init(sub, "LBase;.<init>:()V");
  if (sub_overrides) {
    add_method(sub, "LSub;.m:()V", ACC_PUBLIC, true,
               "((load-param-object v0) (return-void))");
  }
  auto* call = add_method(sub, "LSub;.callSuper:()V", ACC_PUBLIC, true,
                          std::string("((load-param-object v0)") +
                              std::string(call_super) + "(return-void))");
  call->rstate.set_root();
  Scope scope{helper, base, sub};
  add_root_main(scope, std::string("(") + std::string(kNewSub) + R"(
    (invoke-virtual (v0) "LSub;.callSuper:()V")
    (return-void)
  ))");
  return {helper_h, std::move(scope)};
}

} // namespace

TEST_F(ReachabilityMethodHandleTest, InvokeSuperMarksSuperBody) {
  auto s = make_super_call(R"((invoke-super (v0) "LBase;.m:()V"))");
  EXPECT_EQ(is_live(s.scope, s.helper_h), std::make_pair(true, true));
}

// An invoke-direct handle of a non-private instance method runs the
// implementation in the class holding the handle without virtual dispatch,
// here LBase;.m, which LSub; inherits.
TEST_F(ReachabilityMethodHandleTest, InvokeDirectHandleMarksInheritedBody) {
  auto s = make_super_call(std::string(R"(
    (const-method-handle invoke-direct "LBase;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )") +
                               std::string(kInvokeExact) + R"( "(LBase;)V"))",
                           /* sub_overrides */ false);
  EXPECT_EQ(is_live(s.scope, s.helper_h), std::make_pair(true, true));
}

// LSub; overrides m of LBase;, which overrides m of LTop;. An invoke-direct
// handle of LBase;.m held by LSub; runs LSub;.m on Android 9 and LTop;.m on
// Android 10 and later (see `resolve_method_handle`), so both keep their
// bodies.
TEST_F(ReachabilityMethodHandleTest,
       InvokeDirectHandleMarksBodiesThatEveryVersionRuns) {
  auto* helper = make_class("LHelper;");
  auto* helper_top =
      add_method(helper, "LHelper;.top:()V", ACC_PUBLIC | ACC_STATIC, false,
                 "((return-void))");
  auto* helper_sub =
      add_method(helper, "LHelper;.sub:()V", ACC_PUBLIC | ACC_STATIC, false,
                 "((return-void))");
  auto* top = make_class("LTop;");
  add_init(top, "Ljava/lang/Object;.<init>:()V");
  add_method(top, "LTop;.m:()V", ACC_PUBLIC, true, R"((
    (load-param-object v0)
    (invoke-static () "LHelper;.top:()V")
    (return-void)
  ))");
  auto* base = make_class("LBase;", top->get_type());
  add_init(base, "LTop;.<init>:()V");
  add_method(base, "LBase;.m:()V", ACC_PUBLIC, true,
             "((load-param-object v0) (return-void))");
  auto* sub = make_class("LSub;", base->get_type());
  add_init(sub, "LBase;.<init>:()V");
  add_method(sub, "LSub;.m:()V", ACC_PUBLIC, true, R"((
    (load-param-object v0)
    (invoke-static () "LHelper;.sub:()V")
    (return-void)
  ))");
  auto* call = add_method(sub, "LSub;.callSuper:()V", ACC_PUBLIC, true,
                          std::string(R"((
    (load-param-object v0)
    (const-method-handle invoke-direct "LBase;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )") +
                              std::string(kInvokeExact) + R"( "(LSub;)V")
    (return-void)
  ))");
  call->rstate.set_root();
  Scope scope{helper, top, base, sub};
  add_root_main(scope, std::string("(") + std::string(kNewSub) + R"(
    (invoke-virtual (v0) "LSub;.callSuper:()V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(scope, helper_top), std::make_pair(true, true));
  EXPECT_EQ(is_live(scope, helper_sub), std::make_pair(true, true));
}

// An invoke-direct handle of a non-private method that the class holding the
// handle declares calls that method itself.
TEST_F(ReachabilityMethodHandleTest, InvokeDirectHandleOfOwnMethodMarksBody) {
  auto* helper = make_class("LHelper;");
  auto* helper_h = add_method(helper, "LHelper;.h:()V", ACC_PUBLIC | ACC_STATIC,
                              false, "((return-void))");
  auto* base = make_class("LBase;");
  add_init(base, "Ljava/lang/Object;.<init>:()V");
  add_method(base, "LBase;.m:()V", ACC_PUBLIC, true,
             "((load-param-object v0) (return-void))");
  auto* sub = make_class("LSub;", base->get_type());
  add_init(sub, "LBase;.<init>:()V");
  add_method(sub, "LSub;.m:()V", ACC_PUBLIC, true, R"((
    (load-param-object v0)
    (invoke-static () "LHelper;.h:()V")
    (return-void)
  ))");
  auto* call = add_method(sub, "LSub;.callOwn:()V", ACC_PUBLIC, true,
                          std::string(R"((
    (load-param-object v0)
    (const-method-handle invoke-direct "LSub;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )") +
                              std::string(kInvokeExact) + R"( "(LSub;)V")
    (return-void)
  ))");
  call->rstate.set_root();
  Scope scope{helper, base, sub};
  add_root_main(scope, std::string("(") + std::string(kNewSub) + R"(
    (invoke-virtual (v0) "LSub;.callOwn:()V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(scope, helper_h), std::make_pair(true, true));
}

// `Lp/B;.m` is package-private, so `Lq/C;.m` in another package cannot
// override it and takes a slot of its own. An invoke-direct handle of
// `Lp/B;.m` held by `Lp/D; extends Lq/C;` runs `Lp/B;.m`, so its body is live.
TEST_F(ReachabilityMethodHandleTest,
       InvokeDirectHandlePastPackagePrivateMethodMarksBody) {
  auto* helper = make_class("LHelper;");
  auto* helper_h = add_method(helper, "LHelper;.h:()V", ACC_PUBLIC | ACC_STATIC,
                              false, "((return-void))");
  auto* b = make_class("Lp/B;");
  add_init(b, "Ljava/lang/Object;.<init>:()V");
  add_method(b, "Lp/B;.m:()V", DexAccessFlags(0), true, R"((
    (load-param-object v0)
    (invoke-static () "LHelper;.h:()V")
    (return-void)
  ))");
  auto* c = make_class("Lq/C;", b->get_type());
  add_init(c, "Lp/B;.<init>:()V");
  add_method(c, "Lq/C;.m:()V", DexAccessFlags(0), true,
             "((load-param-object v0) (return-void))");
  auto* d = make_class("Lp/D;", c->get_type());
  add_init(d, "Lq/C;.<init>:()V");
  auto* call = add_method(d, "Lp/D;.callB:()V", ACC_PUBLIC, true,
                          std::string(R"((
    (load-param-object v0)
    (const-method-handle invoke-direct "Lp/B;.m:()V")
    (move-result-pseudo-object v1)
    (invoke-polymorphic (v1 v0) )") +
                              std::string(kInvokeExact) + R"( "(Lp/B;)V")
    (return-void)
  ))");
  call->rstate.set_root();
  Scope scope{helper, b, c, d};
  add_root_main(scope, R"((
    (new-instance "Lp/D;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "Lp/D;.<init>:()V")
    (invoke-virtual (v0) "Lp/D;.callB:()V")
    (return-void)
  ))");
  EXPECT_EQ(is_live(scope, helper_h), std::make_pair(true, true));
}
