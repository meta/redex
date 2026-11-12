/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>

#include <gtest/gtest.h>

#include "NeverInlineEligibility.h"

#include "ControlFlow.h"
#include "Creators.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "RedexTest.h"
#include "Show.h"

// Truth-table tests for the shape-eligibility decision itself. Callers test
// their own use of it.
namespace {

class NeverInlineEligibilityTest : public RedexTest {
 public:
  static DexMethod* make_method(const std::string& sig,
                                const std::string& code_str) {
    static std::atomic<size_t> counter{0};
    size_t c = counter.fetch_add(1);
    std::string name = std::string("LFoo") + std::to_string(c) + ";";
    ClassCreator cc{DexType::make_type(name)};
    cc.set_super(type::java_lang_Object());
    auto* m =
        DexMethod::make_method(name + ".bar:" + sig)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                            assembler::ircode_from_string(code_str), false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    cc.create();
    return m;
  }
};

} // namespace

TEST_F(NeverInlineEligibilityTest, EligibleOrdinaryMethod) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (add-int v0 v0 v1)
      (add-int v0 v0 v2)
      (return v0)
    ))");
  EXPECT_EQ(
      never_inline_analysis::never_inline_eligibility(
          m, /* max_callee_code_units */ 40, /* min_callee_instructions */ 4),
      never_inline_analysis::Ineligibility::kEligible);
}

TEST_F(NeverInlineEligibilityTest, AlwaysThrowsHasNoReturnBlock) {
  auto* m = make_method("(I)V", R"((
      (load-param v0)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v1)
      (throw v1)
    ))");
  EXPECT_EQ(
      never_inline_analysis::never_inline_eligibility(
          m, /* max_callee_code_units */ 40, /* min_callee_instructions */ 1),
      never_inline_analysis::Ineligibility::kAlwaysThrows);
}

TEST_F(NeverInlineEligibilityTest, TooLargeOverCodeUnitCeiling) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (add-int v0 v0 v1)
      (add-int v0 v0 v2)
      (return v0)
    ))");
  EXPECT_EQ(
      never_inline_analysis::never_inline_eligibility(
          m, /* max_callee_code_units */ 1, /* min_callee_instructions */ 1),
      never_inline_analysis::Ineligibility::kTooLarge);
}

TEST_F(NeverInlineEligibilityTest, TooSmallUnderInstructionFloor) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (const v1 1)
      (add-int v0 v0 v1)
      (return v0)
    ))");
  EXPECT_EQ(never_inline_analysis::never_inline_eligibility(
                m, /* max_callee_code_units */ 40,
                /* min_callee_instructions */ 100),
            never_inline_analysis::Ineligibility::kTooSmall);
}

TEST_F(NeverInlineEligibilityTest, SimpleForwarderIsIneligible) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (return v0)
    ))");
  EXPECT_EQ(
      never_inline_analysis::never_inline_eligibility(
          m, /* max_callee_code_units */ 40, /* min_callee_instructions */ 1),
      never_inline_analysis::Ineligibility::kSimple);
}

TEST_F(NeverInlineEligibilityTest, IsSimpleTrueForTrivialForwarder) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (return v0)
    ))");
  EXPECT_TRUE(never_inline_analysis::is_simple(m));
}

TEST_F(NeverInlineEligibilityTest, IsSimpleFalseForOrdinaryMethod) {
  auto* m = make_method("(I)I", R"((
      (load-param v0)
      (const v1 1)
      (const v2 2)
      (add-int v0 v0 v1)
      (add-int v0 v0 v2)
      (return v0)
    ))");
  EXPECT_FALSE(never_inline_analysis::is_simple(m));
}

TEST_F(NeverInlineEligibilityTest, IsSimplePopulatesInvokeInsnForForwarder) {
  static std::atomic<size_t> counter{0};
  size_t c = counter.fetch_add(1);
  std::string name = std::string("LBaz") + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(name + ".callee:()I")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                     assembler::ircode_from_string(R"((
                                        (const v0 1)
                                        (return v0)
                                      ))"),
                                     false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);
  auto* caller = DexMethod::make_method(name + ".caller:()I")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                     assembler::ircode_from_string(
                                         "(\n"
                                         "  (invoke-static () \"" +
                                         name +
                                         ".callee:()I\")\n"
                                         "  (move-result v0)\n"
                                         "  (return v0)\n"
                                         ")"),
                                     false);
  caller->set_deobfuscated_name(show(caller));
  caller->get_code()->build_cfg();
  cc.add_method(caller);
  cc.create();

  IRInstruction* invoke_insn = nullptr;
  EXPECT_TRUE(never_inline_analysis::is_simple(caller, &invoke_insn));
  ASSERT_NE(invoke_insn, nullptr);
  EXPECT_TRUE(opcode::is_an_invoke(invoke_insn->opcode()));
}

TEST_F(NeverInlineEligibilityTest, ExactCallSites) {
  ClassCreator cc{DexType::make_type("LCalls;")};
  cc.set_super(type::java_lang_Object());
  auto add = [&](const std::string& sig, DexAccessFlags access, bool is_virtual,
                 const std::string& code) {
    auto* m = DexMethod::make_method("LCalls;." + sig)
                  ->make_concrete(access, assembler::ircode_from_string(code),
                                  is_virtual);
    m->get_code()->build_cfg();
    cc.add_method(m);
    return m;
  };
  auto* callee =
      add("callee:()V", ACC_PUBLIC | ACC_STATIC, false, "((return-void))");
  auto* message =
      add("message:()Ljava/lang/String;", ACC_PUBLIC | ACC_STATIC, false,
          "((const-string \"m\") (move-result-pseudo-object v0) (return-object "
          "v0))");
  auto* virt = add("virt:()V", ACC_PUBLIC, true,
                   "((load-param-object v0) (return-void))");
  auto* caller = add("caller:(LCalls;Z)V", ACC_PUBLIC | ACC_STATIC, false, R"(
    (
      (load-param-object v0)
      (load-param v1)
      (invoke-static () "LCalls;.callee:()V")
      (invoke-static () "LSubCalls;.callee:()V")
      (invoke-static () "Ljava/lang/System;.gc:()V")
      (invoke-virtual (v0) "LCalls;.virt:()V")
      (if-eqz v1 :throw)
      (return-void)
      (:throw)
      (invoke-static () "LCalls;.message:()Ljava/lang/String;")
      (move-result-object v2)
      (new-instance "Ljava/lang/IllegalStateException;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v2) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
      (throw v3)
    )
  )");
  cc.create();
  ClassCreator sub_cc{DexType::make_type("LSubCalls;")};
  sub_cc.set_super(DexType::make_type("LCalls;"));
  sub_cc.create();

  auto visit_all = [&](const InsertOnlyConcurrentSet<DexMethod*>& exact) {
    std::vector<DexMethod*> visited;
    auto skips = never_inline_analysis::for_each_exact_call_site(
        caller, caller->get_code()->cfg(), exact,
        [&](cfg::Block*, IRInstruction*, DexMethod* m) {
          visited.push_back(m);
        });
    return std::make_pair(visited, skips);
  };

  // The message call is the first non-constructor invoke before the throw, so
  // it only builds the exception. A call naming `callee` through a subclass is
  // a call of `callee`.
  auto [visited, skips] = visit_all({});
  EXPECT_EQ(visited, (std::vector<DexMethod*>{callee, callee}));
  EXPECT_EQ(skips.throw_adjacent, 2);
  EXPECT_EQ(skips.unresolved + skips.external_or_no_code, 1);
  EXPECT_EQ(skips.ambiguous_virtual, 1);

  InsertOnlyConcurrentSet<DexMethod*> exact;
  exact.insert(virt);
  auto [visited_exact, skips_exact] = visit_all(exact);
  EXPECT_EQ(visited_exact, (std::vector<DexMethod*>{callee, callee, virt}));
  EXPECT_EQ(skips_exact.ambiguous_virtual, 0);
  (void)message;
}

TEST_F(NeverInlineEligibilityTest, ShapeTakesNoThreshold) {
  using never_inline_analysis::Shape;
  auto* throws = make_method("(I)V", R"((
      (load-param v0)
      (new-instance "Ljava/lang/Exception;")
      (move-result-pseudo-object v1)
      (throw v1)
    ))");
  EXPECT_EQ(never_inline_analysis::never_inline_shape(throws),
            Shape::kAlwaysThrows);
  auto* forwarder = make_method("(I)I", "((load-param v0) (return v0))");
  EXPECT_EQ(never_inline_analysis::never_inline_shape(forwarder),
            Shape::kSimple);
  auto* ordinary = make_method("(I)I", R"((
      (load-param v0)
      (const v1 1)
      (add-int v0 v0 v1)
      (add-int v0 v0 v1)
      (return v0)
    ))");
  EXPECT_EQ(never_inline_analysis::never_inline_shape(ordinary),
            Shape::kEligible);
}

TEST_F(NeverInlineEligibilityTest, CallerInlineBudget) {
  using never_inline_analysis::CallerBudget;
  EXPECT_EQ(never_inline_analysis::caller_inline_budget(10, 4, 10, 4),
            CallerBudget::kWithin);
  EXPECT_EQ(never_inline_analysis::caller_inline_budget(11, 40, 10, 4),
            CallerBudget::kTooManyInstructions);
  EXPECT_EQ(never_inline_analysis::caller_inline_budget(10, 5, 10, 4),
            CallerBudget::kTooManyRegisters);
  EXPECT_EQ(never_inline_analysis::caller_inline_instruction_budget(10, 10),
            CallerBudget::kWithin);
  EXPECT_EQ(never_inline_analysis::caller_inline_instruction_budget(11, 10),
            CallerBudget::kTooManyInstructions);
}

TEST_F(NeverInlineEligibilityTest, ExactVirtualsAreThoseNothingOverrides) {
  auto make_virtual = [](const std::string& cls) {
    auto* m = DexMethod::make_method(cls + ".run:()V")
                  ->make_concrete(ACC_PUBLIC,
                                  assembler::ircode_from_string(
                                      "((load-param-object v0) (return-void))"),
                                  /* is_virtual */ true);
    return m;
  };
  ClassCreator base_cc{DexType::make_type("LBase;")};
  base_cc.set_super(type::java_lang_Object());
  auto* base_run = make_virtual("LBase;");
  base_cc.add_method(base_run);
  auto* base = base_cc.create();
  ClassCreator leaf_cc{DexType::make_type("LLeaf;")};
  leaf_cc.set_super(DexType::make_type("LBase;"));
  auto* leaf_run = make_virtual("LLeaf;");
  leaf_cc.add_method(leaf_run);
  auto* leaf = leaf_cc.create();

  // `Leaf.run` overrides `Base.run` but has no overrider itself, so a call of
  // it is exact; a call of `Base.run` may reach `Leaf.run`.
  std::vector<DexClass*> scope{base, leaf};
  auto graph = method_override_graph::build_graph(scope);
  auto exact = never_inline_analysis::exact_virtuals(*graph, scope);
  EXPECT_EQ(exact.count(leaf_run), 1);
  EXPECT_EQ(exact.count(base_run), 0);
}

TEST_F(NeverInlineEligibilityTest, ThrowConstructingInvokes) {
  auto code = assembler::ircode_from_string(R"(
    (
      (invoke-static () "LCalls;.before:()V")
      (invoke-static () "LCalls;.message:()Ljava/lang/String;")
      (move-result-object v0)
      (new-instance "Ljava/lang/IllegalStateException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
      (throw v1)
    )
  )");
  code->build_cfg();
  auto* block = code->cfg().entry_block();
  auto invokes = never_inline_analysis::throw_constructing_invokes(block);
  std::vector<std::string> names;
  for (auto& mie : InstructionIterable(block)) {
    if (invokes.count(mie.insn) != 0u) {
      names.push_back(mie.insn->get_method()->get_name()->str_copy());
    }
  }
  // Up to and including the first invoke that is not a constructor call.
  EXPECT_EQ(names, (std::vector<std::string>{"message", "<init>"}));
}
