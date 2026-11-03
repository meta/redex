/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <vector>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "CallGraph.h"
#include "DexClass.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"

struct CallGraphTest : public RedexIntegrationTest {
 protected:
  DexMethod* clinit;
  DexMethod* extended_init;
  DexMethod* more_impl1_init;
  DexMethod* less_impl3_init;
  DexMethod* calls_returns_int;
  DexMethod* base_returns_int;
  DexMethod* base_foo;
  DexMethod* extended_returns_int;
  DexMethod* extendedextended_returns_int;
  DexMethod* more_intf_return;
  DexMethod* more_impl1_return;
  DexMethod* more_impl2_return;
  DexMethod* more_impl3_return;
  DexMethod* more_impl4_return;
  DexMethod* more_impl5_return;
  DexMethod* more_impl6_return;
  DexMethod* less_impl1_return;
  DexMethod* less_impl2_return;
  DexMethod* less_impl3_return;
  DexMethod* less_impl4_return;
  DexMethod* pure_ref_intf_return;
  DexMethod* pure_ref_3_return;
  DexMethod* pure_ref_3_init;
  DexMethod* more_than_5_class_extends_1_init;
  DexMethod* more_than_5_class_extends_1_return_super_num;
  DexMethod* more_than_5_class_return_num;

  Scope scope;
  std::unique_ptr<const method_override_graph::Graph> method_override_graph;
  std::unique_ptr<call_graph::Graph> complete_graph;
  std::unique_ptr<call_graph::Graph> multiple_graph;

 public:
  CallGraphTest() {}
  void SetUp() override {
    scope = build_class_scope(stores);
    method_override_graph = method_override_graph::build_graph(scope);
    complete_graph = std::make_unique<call_graph::Graph>(
        call_graph::complete_call_graph(*method_override_graph, scope));
    multiple_graph = std::make_unique<call_graph::Graph>(
        call_graph::multiple_callee_graph(*method_override_graph, scope, 5));
    clinit = DexMethod::get_method(
                 "Lcom/facebook/redextest/CallGraphTest;.<clinit>:()V")
                 ->as_def();

    calls_returns_int = DexMethod::get_method(
                            "Lcom/facebook/redextest/CallGraphTest;"
                            ".callsReturnsInt:(Lcom/facebook/redextest/Base;)I")
                            ->as_def();

    base_returns_int =
        DexMethod::get_method("Lcom/facebook/redextest/Base;.returnsInt:()I")
            ->as_def();
    base_foo = DexMethod::get_method("Lcom/facebook/redextest/Base;.foo:()I")
                   ->as_def();
    extended_returns_int =
        DexMethod::get_method(
            "Lcom/facebook/redextest/Extended;.returnsInt:()I")
            ->as_def();

    extendedextended_returns_int =
        DexMethod::get_method(
            "Lcom/facebook/redextest/ExtendedExtended;.returnsInt:()I")
            ->as_def();

    more_intf_return = DexMethod::get_method(
                           "Lcom/facebook/redextest/MoreThan5;.returnNum:()I")
                           ->as_def();
    more_impl1_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl1;.returnNum:()I")
            ->as_def();
    more_impl2_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl2;.returnNum:()I")
            ->as_def();
    more_impl3_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl3;.returnNum:()I")
            ->as_def();
    more_impl4_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl4;.returnNum:()I")
            ->as_def();
    more_impl5_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl5;.returnNum:()I")
            ->as_def();
    more_impl6_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Impl6;.returnNum:()I")
            ->as_def();
    less_impl1_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/LessThan5Impl1;.returnNum:()I")
            ->as_def();
    less_impl2_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/LessThan5Impl2;.returnNum:()I")
            ->as_def();
    less_impl3_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/LessThan5Impl3;.returnNum:()I")
            ->as_def();
    less_impl4_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/LessThan5Impl4;.returnNum:()I")
            ->as_def();
    extended_init =
        DexMethod::get_method("Lcom/facebook/redextest/Extended;.<init>:()V")
            ->as_def();
    less_impl3_init = DexMethod::get_method(
                          "Lcom/facebook/redextest/LessThan5Impl3;.<init>:()V")
                          ->as_def();
    more_impl1_init = DexMethod::get_method(
                          "Lcom/facebook/redextest/MoreThan5Impl1;.<init>:()V")
                          ->as_def();
    pure_ref_intf_return =
        DexMethod::get_method("Lcom/facebook/redextest/PureRef;.returnNum:()I")
            ->as_def();
    pure_ref_3_return =
        DexMethod::get_method(
            "Lcom/facebook/redextest/PureRefImpl3;.returnNum:()I")
            ->as_def();
    pure_ref_3_init = DexMethod::get_method(
                          "Lcom/facebook/redextest/PureRefImpl3;.<init>:()V")
                          ->as_def();

    more_than_5_class_extends_1_init = DexMethod::get_method(
                                           "Lcom/facebook/redextest/"
                                           "MoreThan5ClassExtends1;.<init>:()V")
                                           ->as_def();

    more_than_5_class_extends_1_return_super_num =
        DexMethod::get_method(
            "Lcom/facebook/redextest/"
            "MoreThan5ClassExtends1;.returnSuperNum:()I")
            ->as_def();

    more_than_5_class_return_num =
        DexMethod::get_method(
            "Lcom/facebook/redextest/MoreThan5Class;.returnNum:()I")
            ->as_def();
  }

  std::vector<const DexMethod*> get_callees(const call_graph::Graph& graph,
                                            const DexMethod* method) {
    return get_callees(graph.node(method));
  }

  std::vector<const DexMethod*> get_callees(const call_graph::NodeId& node) {
    auto successors = node->callees();
    std::vector<const DexMethod*> ret;
    ret.reserve(successors.size());
    for (const auto& succ : successors) {
      ret.emplace_back(succ->callee()->method());
    }
    return ret;
  }
};

TEST_F(CallGraphTest, test_resolve_static_callees) {
  IRCode* code = clinit->get_code();
  IRInstruction* invoke_insn = nullptr;
  for (const auto& mie : InstructionIterable(code)) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode()) &&
        insn->get_method()->str() == "foo") {
      invoke_insn = mie.insn;
    }
  }
  ASSERT_NE(invoke_insn, nullptr);
  const auto& callees =
      call_graph::resolve_callees_in_graph(*complete_graph, invoke_insn);
  EXPECT_THAT(unordered_unsafe_unwrap(callees),
              ::testing::UnorderedElementsAre(base_foo));
}

TEST_F(CallGraphTest, test_resolve_virtual_callees) {
  IRCode* code = calls_returns_int->get_code();
  IRInstruction* invoke_insn = nullptr;
  for (const auto& mie : InstructionIterable(code)) {
    if (opcode::is_an_invoke(mie.insn->opcode())) {
      invoke_insn = mie.insn;
    }
  }
  ASSERT_NE(invoke_insn, nullptr);
  const auto& callees =
      call_graph::resolve_callees_in_graph(*complete_graph, invoke_insn);
  EXPECT_THAT(unordered_unsafe_unwrap(callees),
              ::testing::UnorderedElementsAre(base_returns_int,
                                              extended_returns_int,
                                              extendedextended_returns_int));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_entry) {
  auto entry_callees = get_callees(multiple_graph->entry());
  EXPECT_THAT(entry_callees,
              ::testing::IsSupersetOf({extended_init, less_impl3_init,
                                       more_impl1_init, pure_ref_3_init}));
  std::erase_if(entry_callees,
                [](auto* m) { return method::is_argless_init(m); });
  EXPECT_THAT(entry_callees,
              ::testing::UnorderedElementsAre(clinit,
                                              more_impl1_return,
                                              more_impl2_return,
                                              more_impl3_return,
                                              more_impl4_return,
                                              more_impl5_return,
                                              more_impl6_return));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_clinit) {
  auto clinit_callees = get_callees(*multiple_graph, clinit);
  EXPECT_THAT(clinit_callees,
              ::testing::UnorderedElementsAre(
                  calls_returns_int,
                  base_foo,
                  extended_init,
                  less_impl3_init,
                  more_impl1_init,
                  more_impl1_init,
                  more_impl1_return,
                  less_impl1_return,
                  less_impl2_return,
                  less_impl3_return,
                  less_impl4_return,
                  more_than_5_class_extends_1_init,
                  more_than_5_class_extends_1_return_super_num));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_return4) {
  auto impl4_callees = get_callees(*multiple_graph, less_impl4_return);
  EXPECT_THAT(
      impl4_callees,
      ::testing::UnorderedElementsAre(pure_ref_3_init, pure_ref_3_return));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_calls_returns_int) {
  auto calls_returns_int_callees =
      get_callees(*multiple_graph, calls_returns_int);
  EXPECT_THAT(calls_returns_int_callees,
              ::testing::UnorderedElementsAre(base_returns_int,
                                              extended_returns_int,
                                              extendedextended_returns_int));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_extended_returns_int) {
  auto extendedextended_returns_int_callees =
      get_callees(*multiple_graph, extendedextended_returns_int);
  EXPECT_THAT(extendedextended_returns_int_callees,
              ::testing::UnorderedElementsAre(extended_returns_int));
}

TEST_F(CallGraphTest, test_multiple_callee_graph_invoke_super) {
  auto callees = get_callees(*multiple_graph,
                             more_than_5_class_extends_1_return_super_num);
  EXPECT_THAT(callees,
              ::testing::UnorderedElementsAre(more_than_5_class_return_num));
}

TEST_F(CallGraphTest, test_complete_callers_inherit_virtual_callers) {
  call_graph::CompleteCallers complete_callers(*method_override_graph, scope);
  // callsReturnsInt invokes Base.returnsInt virtually, so it may run every
  // override.
  auto callers = complete_callers.get_callers(extendedextended_returns_int);
  EXPECT_THAT(unordered_to_ordered(callers, compare_dexmethods),
              ::testing::Contains(calls_returns_int));
}

TEST_F(CallGraphTest, test_complete_callers_match_complete_call_graph) {
  call_graph::CompleteCallers complete_callers(*method_override_graph, scope);
  size_t methods_with_callers = 0;
  walk::methods(scope, [&](DexMethod* method) {
    const auto& graph_callers = complete_graph->get_callers(method);
    auto expected = unordered_to_ordered(graph_callers, compare_dexmethods);
    auto callers = complete_callers.get_callers(method);
    auto actual = unordered_to_ordered(callers, compare_dexmethods);
    EXPECT_EQ(expected, actual) << show(method);
    if (!expected.empty()) {
      ++methods_with_callers;
    }
  });
  EXPECT_GT(methods_with_callers, 0);
}
