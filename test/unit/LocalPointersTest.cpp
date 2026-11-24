/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LocalPointersAnalysis.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "Creators.h"
#include "DexCallSite.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypeUtil.h"

namespace ptrs = local_pointers;

using namespace testing;

class LocalPointersTest : public RedexTest {};

TEST_F(LocalPointersTest, domainOperations) {
  ptrs::Environment env1;
  ptrs::Environment env2;
  auto* insn1 = (new IRInstruction(OPCODE_NEW_INSTANCE))
                    ->set_type(DexType::make_type("LFoo;"));
  auto* insn2 = (new IRInstruction(OPCODE_NEW_INSTANCE))
                    ->set_type(DexType::make_type("LBar;"));
  auto* insn3 = (new IRInstruction(OPCODE_NEW_INSTANCE))
                    ->set_type(DexType::make_type("LBaz;"));

  env1.set_fresh_pointer(0, insn1);
  env2.set_fresh_pointer(0, insn1);
  env2.set_may_escape(0, nullptr);

  env1.set_fresh_pointer(1, insn1);
  env2.set_fresh_pointer(1, insn2);

  auto joined_env = env1.join(env2);

  EXPECT_EQ(joined_env.get_pointers(0).size(), 1);
  EXPECT_EQ(*joined_env.get_pointers(0).elements().begin(), insn1);
  EXPECT_EQ(joined_env.get_pointers(1).size(), 2);
  EXPECT_THAT(joined_env.get_pointers(1).elements(),
              UnorderedElementsAre(insn1, insn2));
  EXPECT_TRUE(joined_env.may_have_escaped(insn1));
  EXPECT_FALSE(joined_env.may_have_escaped(insn2));
  EXPECT_FALSE(joined_env.may_have_escaped(insn3));
}

ptrs::InvokeToSummaryMap mark_all_invokes_as_non_escaping(const IRCode& code) {
  ptrs::InvokeToSummaryMap invoke_to_summary_map;
  for (const auto& mie : InstructionIterable(code.cfg())) {
    if (opcode::is_a_method_invoke(mie.insn->opcode())) {
      ptrs::ParamSet returned_params;
      if (!type::is_primitive(
              mie.insn->get_method()->get_proto()->get_rtype())) {
        returned_params.emplace(ptrs::FRESH_RETURN);
      }
      invoke_to_summary_map.emplace(mie.insn,
                                    ptrs::EscapeSummary(returned_params, {}));
    }
  }
  return invoke_to_summary_map;
}

TEST_F(LocalPointersTest, simple) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (if-nez v0 :true)
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")
     (:true)
     (return-void)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  auto invoke_to_summary_map = mark_all_invokes_as_non_escaping(*code);
  ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  EXPECT_EQ(exit_env.get_pointers(0).size(), 2);
  EXPECT_THAT(exit_env.get_pointers(0).elements(),
              UnorderedElementsAre(
                  Pointee(Eq(*(IRInstruction(OPCODE_NEW_INSTANCE)
                                   .set_type(DexType::get_type("LFoo;"))))),
                  Pointee(Eq(*(
                      IRInstruction(IOPCODE_LOAD_PARAM_OBJECT).set_dest(0))))));
  const auto& pointers = exit_env.get_pointers(0);
  for (const auto* insn : pointers.elements()) {
    if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT ||
        insn->opcode() == OPCODE_NEW_INSTANCE) {
      EXPECT_FALSE(exit_env.may_have_escaped(insn));
    }
  }
}

TEST_F(LocalPointersTest, aliasEscape) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (load-param-object v1)
     (if-nez v0 :true)
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")
     (:true)
     (move-object v1 v0)
     (sput-object v1 "LFoo;.bar:LFoo;")
     (return v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  auto invoke_to_summary_map = mark_all_invokes_as_non_escaping(*code);
  ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto& returned_ptrs = exit_env.get_pointers(0);
  EXPECT_EQ(returned_ptrs.size(), 2);
  EXPECT_THAT(
      returned_ptrs.elements(),
      UnorderedElementsAre(
          Pointee(*(IRInstruction(OPCODE_NEW_INSTANCE)
                        .set_type(DexType::get_type("LFoo;")))),
          Pointee(*(IRInstruction(IOPCODE_LOAD_PARAM_OBJECT).set_dest(0)))));
  for (const auto* insn : returned_ptrs.elements()) {
    EXPECT_TRUE(exit_env.may_have_escaped(insn));
  }
}

TEST_F(LocalPointersTest, filledNewArrayEscape) {
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "LFoo;.<init>:()V")
     (filled-new-array (v0) "[LFoo;")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  auto invoke_to_summary_map = mark_all_invokes_as_non_escaping(*code);
  ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto& foo_ptr_set = exit_env.get_pointers(0);
  EXPECT_EQ(foo_ptr_set.size(), 1);
  const auto& foo_ptr = *foo_ptr_set.elements().begin();
  EXPECT_EQ(*foo_ptr,
            *(IRInstruction(OPCODE_NEW_INSTANCE)
                  .set_type(DexType::get_type("LFoo;"))));
  EXPECT_TRUE(exit_env.may_have_escaped(foo_ptr));
}

TEST_F(LocalPointersTest, invokePolymorphicArgumentsEscape) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-object v1)
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-polymorphic (v1 v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(LFoo;)Ljava/lang/Object;")
     (move-result-object v2)
     (return-object v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto& foo_ptr_set = exit_env.get_pointers(0);
  ASSERT_EQ(foo_ptr_set.size(), 1);
  EXPECT_TRUE(exit_env.may_have_escaped(*foo_ptr_set.elements().begin()));
}

TEST_F(LocalPointersTest, invokeCustomArgumentsEscape) {
  auto* bootstrap =
      DexMethod::make_method(
          "LFoo;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;"
          "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
          "Ljava/lang/invoke/CallSite;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_NATIVE, false);
  auto* call_site = new DexCallSite(
      new DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_STATIC, bootstrap),
      DexString::make_string("consume"),
      DexProto::make_proto(
          type::_void(),
          DexTypeList::make_type_list({DexType::make_type("LFoo;")})),
      {});
  auto code = assembler::ircode_from_string(R"(
    (
     (new-instance "LFoo;")
     (move-result-pseudo-object v0)
     (invoke-static (v0) "LFoo;.consume:(LFoo;)V")
     (return-object v0)
    )
  )");
  for (auto& mie : InstructionIterable(*code)) {
    if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
      mie.insn->set_opcode(OPCODE_INVOKE_CUSTOM);
      mie.insn->set_callsite(call_site);
    }
  }

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto& foo_ptr_set = exit_env.get_pointers(0);
  ASSERT_EQ(foo_ptr_set.size(), 1);
  EXPECT_TRUE(exit_env.may_have_escaped(*foo_ptr_set.elements().begin()));
}

TEST_F(LocalPointersTest, methodTypeConstantIsAnObject) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const-class "Ljava/lang/Object;")
     (move-result-pseudo-object v0)
     (return-object v0)
    )
  )");
  for (auto& mie : InstructionIterable(*code)) {
    if (mie.insn->opcode() == OPCODE_CONST_CLASS) {
      mie.insn->set_opcode(OPCODE_CONST_METHOD_TYPE);
      mie.insn->set_proto(
          DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})));
    }
  }

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();

  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto& ptr_set = exit_env.get_pointers(0);
  ASSERT_EQ(ptr_set.size(), 1);
  EXPECT_TRUE(exit_env.may_have_escaped(*ptr_set.elements().begin()));
}

TEST_F(LocalPointersTest, generateEscapeSummary) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (load-param-object v1)
     (sput-object v1 "LFoo;.bar:LFoo;")
     (return-object v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  bool result_may_be_pointer = true;
  auto summary =
      ptrs::get_escape_summary(fp_iter, *code, result_may_be_pointer);
  EXPECT_EQ(summary.returned_parameters, ptrs::ParamSet({0}));
  EXPECT_THAT(unordered_unsafe_unwrap(summary.escaping_parameters),
              UnorderedElementsAre(1));

  // Test (de)serialization.
  std::stringstream ss;
  ss << to_s_expr(summary);
  EXPECT_EQ(ss.str(), "((#1) (#0))");

  sparta::s_expr_istream s_expr_in(ss);
  sparta::s_expr summary_s_expr;
  s_expr_in >> summary_s_expr;
  auto summary_copy = ptrs::EscapeSummary::from_s_expr(summary_s_expr);
  EXPECT_THAT(unordered_unsafe_unwrap(summary_copy.returned_parameters),
              UnorderedElementsAre(0));
  EXPECT_THAT(unordered_unsafe_unwrap(summary_copy.escaping_parameters),
              UnorderedElementsAre(1));
}

TEST_F(LocalPointersTest, generateEscapeSummary2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (sget-object "LFoo;.bar:LFoo;")
     (move-result-pseudo-object v0)
     (return-object v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  bool result_may_be_pointer = true;
  auto summary =
      ptrs::get_escape_summary(fp_iter, *code, result_may_be_pointer);
  EXPECT_EQ(summary.returned_parameters,
            ptrs::ParamSet({ptrs::ESCAPED_FRESH_RETURN}));
  EXPECT_THAT(unordered_unsafe_unwrap(summary.escaping_parameters),
              UnorderedElementsAre());

  // Test (de)serialization.
  std::stringstream ss;
  ss << to_s_expr(summary);
  EXPECT_EQ(ss.str(), "(() (#65534))");

  sparta::s_expr_istream s_expr_in(ss);
  sparta::s_expr summary_s_expr;
  s_expr_in >> summary_s_expr;
  auto summary_copy = ptrs::EscapeSummary::from_s_expr(summary_s_expr);
  EXPECT_EQ(summary.returned_parameters,
            ptrs::ParamSet({ptrs::ESCAPED_FRESH_RETURN}));
  EXPECT_THAT(unordered_unsafe_unwrap(summary_copy.escaping_parameters),
              UnorderedElementsAre());
}

TEST_F(LocalPointersTest, collectExitingPointersWithThrow) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param-object v0)
     (throw v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  ptrs::FixpointIterator fp_iter(cfg);
  fp_iter.run(ptrs::Environment());

  ptrs::PointerSet returned_ptrs;
  ptrs::PointerSet thrown_ptrs;
  ptrs::collect_exiting_pointers(fp_iter, *code, &returned_ptrs, &thrown_ptrs);
  EXPECT_EQ(returned_ptrs, ptrs::PointerSet::bottom());
  EXPECT_THAT(thrown_ptrs.elements(),
              UnorderedElementsAre(Pointee(
                  *(IRInstruction(IOPCODE_LOAD_PARAM_OBJECT)).set_dest(0))));

  bool result_may_be_pointer = true;
  auto summary =
      ptrs::get_escape_summary(fp_iter, *code, result_may_be_pointer);
  EXPECT_EQ(summary.returned_parameters, ptrs::ParamSet());
  EXPECT_THAT(unordered_unsafe_unwrap(summary.escaping_parameters),
              UnorderedElementsAre(0));
}

/*
 * Given the following code snippet:
 *
 *   class Foo {
 *      public static Foo newInstance() {
 *        Foo instance = new Foo();
 *        instance.setValue(123);
 *        return instance;
 *      }
 *   }
 *
 * We wish the callers of newInstance() to be able to treat its return value as
 * non-escaping.
 */
TEST_F(LocalPointersTest, returnFreshValue) {
  ptrs::EscapeSummary fresh_return_summary;
  // First, check that we generate the right summary from the callee.
  {
    auto code = assembler::ircode_from_string(R"(
      (
       (new-instance "LFoo;")
       (move-result-pseudo-object v0)
       (invoke-direct (v0) "LFoo;.<init>:()V")
       (return-object v0)
      )
    )");

    code->build_cfg();
    auto& cfg = code->cfg();
    cfg.calculate_exit_block();

    auto invoke_to_summary_map = mark_all_invokes_as_non_escaping(*code);
    ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
    fp_iter.run(ptrs::Environment());

    bool result_may_be_pointer = true;
    fresh_return_summary =
        ptrs::get_escape_summary(fp_iter, *code, result_may_be_pointer);
    EXPECT_THAT(
        unordered_unsafe_unwrap(fresh_return_summary.returned_parameters),
        UnorderedElementsAre(ptrs::FRESH_RETURN));
    EXPECT_THAT(
        unordered_unsafe_unwrap(fresh_return_summary.escaping_parameters),
        UnorderedElementsAre());
  }

  // Now check that the caller handles the summary correctly.
  {
    auto code = assembler::ircode_from_string(R"(
      (
       (invoke-static () "LFoo;.newInstance:()LFoo;")
       (move-result-object v0)
       (return v0)
      )
    )");

    code->build_cfg();
    auto& cfg = code->cfg();
    cfg.calculate_exit_block();

    ptrs::InvokeToSummaryMap invoke_to_summary_map;
    const IRInstruction* invoke_insn{nullptr};
    for (const auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (opcode::is_a_method_invoke(insn->opcode())) {
        invoke_insn = insn;
        invoke_to_summary_map.emplace(insn, fresh_return_summary);
      }
    }

    ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
    fp_iter.run(ptrs::Environment());

    const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
    EXPECT_THAT(exit_env.get_pointers(0).elements(),
                UnorderedElementsAre(Pointee(Eq(*invoke_insn))));
    EXPECT_FALSE(exit_env.may_have_escaped(invoke_insn));
  }
}

/*
 * Check that we correctly analyze the cases where we return a newly-allocated
 * value that has escaped.
 */
TEST_F(LocalPointersTest, returnEscapedValue) {
  ptrs::EscapeSummary fresh_return_summary;
  // First, check that we generate the right summary from the callee.
  {
    auto code = assembler::ircode_from_string(R"(
      (
       (new-instance "LFoo;")
       (move-result-pseudo-object v0)
       (invoke-direct (v0) "LFoo;.<init>:()V")
       (sput-object v0 "LFoo;.a:LFoo;") ; v0 escapes here
       (return-object v0)
      )
    )");

    code->build_cfg();
    auto& cfg = code->cfg();
    cfg.calculate_exit_block();

    auto invoke_to_summary_map = mark_all_invokes_as_non_escaping(*code);
    ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
    fp_iter.run(ptrs::Environment());

    bool result_may_be_pointer = true;
    fresh_return_summary =
        ptrs::get_escape_summary(fp_iter, *code, result_may_be_pointer);
    EXPECT_EQ(fresh_return_summary.returned_parameters,
              ptrs::ParamSet({ptrs::ESCAPED_FRESH_RETURN}));
    EXPECT_THAT(
        unordered_unsafe_unwrap(fresh_return_summary.escaping_parameters),
        UnorderedElementsAre());
  }

  // Now check that the caller handles the summary correctly.
  {
    auto code = assembler::ircode_from_string(R"(
      (
       (invoke-static () "LFoo;.newEscapedInstance:()LFoo;")
       (move-result-object v0)
       (return-object v0)
      )
    )");

    code->build_cfg();
    auto& cfg = code->cfg();
    cfg.calculate_exit_block();

    ptrs::InvokeToSummaryMap invoke_to_summary_map;
    const IRInstruction* invoke_insn{nullptr};
    for (const auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (opcode::is_a_method_invoke(insn->opcode())) {
        invoke_insn = insn;
        invoke_to_summary_map.emplace(insn, fresh_return_summary);
      }
    }

    ptrs::FixpointIterator fp_iter(cfg, invoke_to_summary_map);
    fp_iter.run(ptrs::Environment());

    const auto& exit_env = fp_iter.get_exit_state_at(cfg.exit_block());
    EXPECT_THAT(exit_env.get_pointers(0).elements(),
                UnorderedElementsAre(Pointee(Eq(*invoke_insn))));
    EXPECT_TRUE(exit_env.may_have_escaped(invoke_insn));
  }
}

// interface Listener { default void onEvent(Object event) {} }  // kept
// static void notify(Listener listener, Object event) {
//   listener.onEvent(event);
// }
// No class in the app overrides `onEvent`, but `Listener` is kept, so a
// `java.lang.reflect.Proxy` created at runtime may implement it and hand
// `event` to its `InvocationHandler`.
TEST_F(LocalPointersTest, argumentToKeptInterfaceDefaultMethodEscapes) {
  ClassCreator ic(DexType::make_type("LListener;"));
  ic.set_super(type::java_lang_Object());
  ic.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* on_event = assembler::method_from_string(R"(
    (method (public) "LListener;.onEvent:(Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (return-void)
      )
    )
  )");
  on_event->rstate.set_root();
  ic.add_method(on_event);
  auto* listener = ic.create();
  listener->rstate.set_root();

  ClassCreator nc(DexType::make_type("LNotifier;"));
  nc.set_super(type::java_lang_Object());
  nc.set_access(ACC_PUBLIC);
  auto* notify = assembler::method_from_string(R"(
    (method (public static) "LNotifier;.notify:(LListener;Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-interface (v0 v1) "LListener;.onEvent:(Ljava/lang/Object;)V")
        (return-void)
      )
    )
  )");
  nc.add_method(notify);
  Scope scope{listener, nc.create()};
  for (auto* method : {on_event, notify}) {
    method->get_code()->build_cfg();
    method->get_code()->cfg().calculate_exit_block();
  }

  auto override_graph = method_override_graph::build_graph(scope);
  call_graph::Graph call_graph(
      ptrs::EscapeCallGraphStrategy(*override_graph, scope));
  ptrs::SummaryMap summaries;
  ptrs::analyze_scope(scope, call_graph, &summaries);
  EXPECT_THAT(unordered_unsafe_unwrap(summaries.at(notify).escaping_parameters),
              UnorderedElementsAre(0, 1));
}

TEST_F(LocalPointersTest, argumentToInvokeSuperOfAbstractMethodEscapes) {
  // `Sub` was compiled against a version of `Base` in which `make` had code.
  ClassCreator bc(DexType::make_type("LBase;"));
  bc.set_super(type::java_lang_Object());
  bc.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  auto* base_make =
      DexMethod::make_method(
          "LBase;.make:(Ljava/lang/Object;)Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true);
  bc.add_method(base_make);
  auto* base = bc.create();

  ClassCreator sc(DexType::make_type("LSub;"));
  sc.set_super(base->get_type());
  sc.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  auto* sub_make = assembler::method_from_string(R"(
    (method (public) "LSub;.make:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-super (v0 v1) "LBase;.make:(Ljava/lang/Object;)Ljava/lang/Object;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )");
  sc.add_method(sub_make);
  Scope scope{base, sc.create()};
  sub_make->get_code()->build_cfg();
  sub_make->get_code()->cfg().calculate_exit_block();

  auto override_graph = method_override_graph::build_graph(scope);
  call_graph::Graph call_graph(
      ptrs::EscapeCallGraphStrategy(*override_graph, scope));
  ptrs::SummaryMap summaries;
  ptrs::analyze_scope(scope, call_graph, &summaries);
  const auto& summary = summaries.at(sub_make);
  EXPECT_THAT(unordered_unsafe_unwrap(summary.escaping_parameters),
              UnorderedElementsAre(0, 1));
  EXPECT_THAT(unordered_unsafe_unwrap(summary.returned_parameters),
              UnorderedElementsAre(ptrs::ESCAPED_FRESH_RETURN));
}

TEST_F(LocalPointersTest,
       argumentToInvokeSuperOfInterfaceDefaultMethodEscapes) {
  // `C.make` calls `I.super.make(o)`, which runs `I.make`; `B.make`, which an
  // `invoke-super` search through the superclass finds instead, is abstract.
  ClassCreator ic(DexType::make_type("LI;"));
  ic.set_super(type::java_lang_Object());
  ic.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* i_make = assembler::method_from_string(R"(
    (method (public) "LI;.make:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (sput-object v1 "LI;.kept:Ljava/lang/Object;")
        (return-object v1)
      )
    )
  )");
  ic.add_method(i_make);
  auto* i_cls = ic.create();

  ClassCreator bc(DexType::make_type("LB;"));
  bc.set_super(type::java_lang_Object());
  bc.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  auto* b_make =
      DexMethod::make_method("LB;.make:(Ljava/lang/Object;)Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true);
  bc.add_method(b_make);
  auto* b_cls = bc.create();

  ClassCreator cc(DexType::make_type("LC;"));
  cc.set_super(b_cls->get_type());
  cc.add_interface(i_cls->get_type());
  cc.set_access(ACC_PUBLIC);
  auto* c_make = assembler::method_from_string(R"(
    (method (public) "LC;.make:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-super (v0 v1) "LI;.make:(Ljava/lang/Object;)Ljava/lang/Object;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )");
  cc.add_method(c_make);
  Scope scope{i_cls, b_cls, cc.create()};
  for (auto* method : {i_make, c_make}) {
    method->get_code()->build_cfg();
    method->get_code()->cfg().calculate_exit_block();
  }

  auto override_graph = method_override_graph::build_graph(scope);
  call_graph::Graph call_graph(
      ptrs::EscapeCallGraphStrategy(*override_graph, scope));
  ptrs::SummaryMap summaries;
  ptrs::analyze_scope(scope, call_graph, &summaries);
  EXPECT_THAT(unordered_unsafe_unwrap(summaries.at(c_make).escaping_parameters),
              Contains(1));
}
