/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "CFGInliner.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "Show.h"

cfg::InstructionIterator get_invoke(cfg::ControlFlowGraph* cfg) {
  auto iterable = cfg::InstructionIterable(*cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (opcode::is_an_invoke(it->insn->opcode())) {
      return it;
    }
  }
  always_assert_log(false, "can't find invoke in %s", SHOW(*cfg));
}

void test_inliner(const std::string& caller_str,
                  const std::string& callee_str,
                  const std::string& expected_str,
                  DexType* needs_receiver_cast = nullptr,
                  DexType* needs_init_class = nullptr) {
  auto caller_code = assembler::ircode_from_string(caller_str);
  caller_code->build_cfg();
  auto& caller = caller_code->cfg();

  auto callee_code = assembler::ircode_from_string(callee_str);
  callee_code->build_cfg();
  auto& callee = callee_code->cfg();

  cfg::CFGInliner::inline_cfg(&caller,
                              get_invoke(&caller),
                              needs_receiver_cast,
                              needs_init_class,
                              callee,
                              caller.get_registers_size());

  auto expected_code = assembler::ircode_from_string(expected_str);

  const std::string& final_cfg = show(caller);
  caller_code->clear_cfg();
  EXPECT_EQ(assembler::to_string(expected_code.get()),
            assembler::to_string(caller_code.get()))
      << final_cfg;
}

class CFGInlinerTest : public RedexTest {};

// A position's `parent` must itself be a position present in this CFG --
// `ControlFlowGraph::no_dangling_dex_positions` asserts exactly that, and it
// runs on every `sanity_check`, so a parent that lives nowhere in the block
// list crashes any later pass that inlines this code.
//
// Inlining is where the invariant is easiest to break: every callee position
// without a parent is given one pointing at the callsite. Point it at a fresh
// copy instead of the callsite position itself and the copy is owned by
// nothing and reachable from nothing, which leaks it as well.
TEST_F(CFGInlinerTest, inlined_positions_parent_stays_in_the_cfg) {
  auto caller_code = assembler::ircode_from_string(R"(
    (
      (.pos:dbg_call "LFoo;.caller:()V" Foo.java 10)
      (const v0 0)
      (invoke-static () "LFoo;.callee:()V")
      (return-void)
    )
  )");
  caller_code->build_cfg();
  auto& caller = caller_code->cfg();

  auto callee_code = assembler::ircode_from_string(R"(
    (
      (.pos:dbg_leaf "LFoo;.callee:()V" Foo.java 20)
      (const v1 1)
      (return-void)
    )
  )");
  callee_code->build_cfg();
  auto& callee = callee_code->cfg();

  cfg::CFGInliner::inline_cfg(&caller, get_invoke(&caller), nullptr, nullptr,
                              callee, caller.get_registers_size());

  UnorderedSet<DexPosition*> present;
  for (auto* b : caller.blocks()) {
    for (auto& mie : *b) {
      if (mie.type == MFLOW_POSITION) {
        present.insert(mie.pos.get());
      }
    }
  }
  ASSERT_FALSE(present.empty()) << show(caller);

  size_t checked = 0;
  for (auto* b : caller.blocks()) {
    for (auto& mie : *b) {
      if (mie.type != MFLOW_POSITION || mie.pos->parent == nullptr) {
        continue;
      }
      checked++;
      EXPECT_EQ(present.count(mie.pos->parent), 1u)
          << "parent " << mie.pos->parent
          << " is not a position in this CFG: " << show(caller);
    }
  }
  // Without a parented position the loop above is vacuous, and the test would
  // pass against the very bug it exists for.
  EXPECT_GT(checked, 0u) << "no inlined position received a parent: "
                         << show(caller);
}

TEST_F(CFGInlinerTest, partial_inline_fallback_keeps_exact_callsite_position) {
  auto caller_code = assembler::ircode_from_string(R"(
    (
      (.pos:callsite "LFoo;.caller:()V" Foo.java 10)
      (invoke-static () "LFoo;.partial:()V")
      (return-void)
    )
  )");
  caller_code->build_cfg();
  auto& caller = caller_code->cfg();

  auto callee_code = assembler::ircode_from_string(R"(
    (
      (.pos:fallback "LFoo;.partial:()V" PartiallyInlinedSource 0)
      (invoke-static () "LFoo;.partial:()V")
      (return-void)
    )
  )");
  callee_code->build_cfg();

  cfg::CFGInliner::inline_cfg(&caller, get_invoke(&caller), nullptr, nullptr,
                              callee_code->cfg(), caller.get_registers_size());

  auto instructions = cfg::InstructionIterable(caller);
  size_t fallback_invokes = 0;
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    if (!opcode::is_an_invoke(it->insn->opcode())) {
      continue;
    }
    ++fallback_invokes;
    auto* position = caller.get_dbg_pos(it);
    ASSERT_NE(position, nullptr);
    EXPECT_EQ(position->file, DexString::make_string("Foo.java"));
    EXPECT_EQ(position->line, 10u);
    EXPECT_FALSE(position->is_synthetic());
    EXPECT_FALSE(position->is_unreliable());
  }
  EXPECT_EQ(fallback_invokes, 1u);
}

TEST_F(CFGInlinerTest, simple) {
  const auto* const caller_str = R"(
    (
      (invoke-static () "LCls;.foo:()V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, with_regs) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (invoke-static () "LCls;.foo:()V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (const v0 1)
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (const v1 1)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, with_args) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "LCls;.foo:(I)V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (move v1 v0)
      (const v2 1)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, with_returns) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (invoke-static () "LCls;.foo:()I")
      (move-result v1)
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (const v0 1)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (const v2 1)
      (move v1 v2)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, with_args_and_returns) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "LCls;.foo:(I)I")
      (move-result v0)
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (add-int v0 v0 v1)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (move v1 v0)
      (const v2 1)
      (add-int v1 v1 v2)
      (move v0 v1)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, multi_return) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (const v1 10)
      (invoke-static (v0 v1) "LCls;.max:(II)I")
      (move-result v2)
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      ; max
      (load-param v0)
      (load-param v1)
      (if-ge v0 v1 :true)

      (return v1)

      (:true)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (const v1 10)
      (move v3 v0)
      (move v4 v1)
      (if-ge v3 v4 :true)

      (move v2 v4)

      (:exit)
      (return-void)

      (:true)
      (move v2 v3)
      (goto :exit)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, multi_return_wide) {
  const auto* const caller_str = R"(
    (
      (const-wide v0 0)
      (const-wide v2 10)
      (invoke-static (v0 v2) "LCls;.max:(JJ)J")
      (move-result-wide v0)
      (return-wide v0)
    )
  )";
  const auto* const callee_str = R"(
    (
      ; max
      (load-param-wide v0)
      (load-param-wide v2)
      (cmp-long v4 v0 v2)
      (if-gtz v4 :true)

      (return-wide v2)

      (:true)
      (return-wide v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const-wide v0 0)
      (const-wide v2 10)

      (move-wide v4 v0)
      (move-wide v6 v2)
      (cmp-long v8 v4 v6)
      (if-gtz v8 :true)

      (move-wide v0 v6)

      (:exit)
      (return-wide v0)

      (:true)
      (move-wide v0 v4)
      (goto :exit)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, multi_return_object) {
  const auto* const caller_str = R"(
    (
      (invoke-static () "LCls;.randObj:()Ljava/lang/Object;")
      (move-result v0)
      (return-object v0)
    )
  )";
  const auto* const callee_str = R"(
    (
      (new-instance "Ljava/util/Random;")
      (move-result-pseudo v0)
      (invoke-virtual (v0) "Ljava/util/Random;.nextBoolean:()Z")
      (move-result-pseudo v0)
      (if-nez v0 :true)

      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (return-object v0)

      (:true)
      (new-instance "LBar;")
      (move-result-pseudo-object v0)
      (return-object v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (new-instance "Ljava/util/Random;")
      (move-result-pseudo v1)
      (invoke-virtual (v1) "Ljava/util/Random;.nextBoolean:()Z")
      (move-result-pseudo v1)
      (if-nez v1 :true)

      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (move-object v0 v1)

      (:exit)
      (return-object v0)

      (:true)
      (new-instance "LBar;")
      (move-result-pseudo-object v1)
      (move-object v0 v1)
      (goto :exit)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, both_multi_block) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (const v1 10)
      (if-nez v1 :true)
      (return-void)

      (:true)
      (invoke-static (v0 v1) "LCls;.max:(II)I")
      (move-result v2)
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      ; max
      (load-param v0)
      (load-param v1)
      (if-ge v0 v1 :true)

      (return v1)

      (:true)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (const v1 10)
      (if-nez v1 :outer_true)
      (return-void)

      (:outer_true)
      (move v3 v0)
      (move v4 v1)
      (if-ge v3 v4 :true)

      (move v2 v4)
      (goto :exit)

      (:true)
      (move v2 v3)

      (:exit)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, callee_diamond_caller_loop) {
  const auto* const caller_str = R"(
    (
      (const v0 10)

      (:loop)
      (if-eqz v0 :end)
      (invoke-static (v0) "LCls;.foo:(I)I")
      (move-result v1)
      (add-int v0 v0 v1)
      (goto :loop)

      (:end)
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (if-nez v0 :true)
      (const v0 0)
      (goto :end)

      (:true)
      (const v0 -1)

      (:end)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 10)

      (:loop)
      (if-eqz v0 :end)

      ; callee starts here
      (move v2 v0)
      (if-nez v2 :true)
      (const v2 0)

      (:inner_end)
      (move v1 v2)
      (add-int v0 v0 v1)
      (goto :loop)

      (:true)
      (const v2 -1)
      (goto :inner_end)

      (:end)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_simple) {
  const auto* const caller_str = R"(
    (
      (.try_start a)
      (iget v0 "LCls;.bar:I")
      (invoke-static () "LCls;.foo:()V")
      (return v0)
      (.try_end a)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (const v0 0)
      (throw v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (.try_start a)
      (iget v0 "LCls;.bar:I")
      (const v2 0)
      (throw v2)
      (.try_end a)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_with_return_reg) {
  const auto* const caller_str = R"(
    (
      (.try_start a)
      (iget v0 "LCls;.bar:I")
      (invoke-static () "LCls;.foo:()I")
      (.try_end a)
      (move-result v0)
      (return v0)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (const v0 0)
      (throw v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (.try_start a)
      (iget v0 "LCls;.bar:I")
      (const v2 0)
      (throw v2)
      (.try_end a)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_with_arg_and_return_regs) {
  const auto* const caller_str = R"(
    (
      (.try_start a)
      (invoke-static (v0) "LCls;.foo:(I)I")
      (move-result v0)
      (return v0)
      (.try_end a)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :thr)
      (return v0)

      (:thr)
      (throw v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (move v2 v0)
      (if-eqz v2 :thr)
      (move v0 v2)
      (return v0)

      (.try_start a)
      (:thr)
      (throw v2)

      (.try_end a)

      (.catch (a))
      (const v1 1)
      (return v1)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_caller_catch_chain) {
  const auto* const caller_str = R"(
    (
      (.try_start a)
      (invoke-static (v0) "LCls;.foo:(I)I")
      (move-result v0)
      (return v0)
      (.try_end a)

      (.catch (b))
      (return v0)

      (.catch (a b) "LExcept;")
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :thr)
      (return v0)

      (:thr)
      (throw v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (move v2 v0)
      (if-eqz v2 :thr)
      (move v0 v2)
      (return v0)

      (.try_start a)
      (:thr)
      (throw v2)

      (.try_end a)

      (.catch (b))
      (return v0)

      (.catch (a b) "LExcept;")
      (const v1 1)
      (return v1)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_with_may_throws) {
  const auto* const caller_str = R"(
    (
      (.try_start outer)
      (invoke-static () "LCls;.foo:()I")
      (move-result v0)
      (return v0)
      (.try_end outer)

      (.catch (all))
      (return v0)

      (.catch (outer all) "LOuterExcept;")
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (.try_start inner)

      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :thr)
      (return v0)

      (:thr)
      (throw v0)

      (.try_end inner)
      (.catch (inner) "LInnerExcept")
      (const v0 0)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (.try_start inner)
      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (if-eqz v2 :thr)
      (move v0 v2)
      (goto :exit)

      (:thr)
      (throw v2)
      (.try_end inner)


      (.catch (all))
      (return v0)

      (.catch (outer all) "LOuterExcept;")
      (const v1 1)
      (return v1)

      (.catch (inner outer) "LInnerExcept")
      (const v2 0)
      (move v0 v2)

      (:exit)
      (return v0)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_with_only_may_throws) {
  const auto* const caller_str = R"(
    (
      (.try_start outer)
      (invoke-static () "LCls;.foo:()I")
      (move-result v0)
      (return v0)
      (.try_end outer)

      (.catch (all))
      (return v0)

      (.catch (outer all) "LOuterExcept;")
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (.try_start outer)

      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (move v0 v2)

      (return v0)
      (.try_end outer)

      (.catch (all))
      (return v0)

      (.catch (outer all) "LOuterExcept;")
      (const v1 1)
      (return v1)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, try_catch_callee_has_chain) {
  const auto* const caller_str = R"(
    (
      (.try_start outer)
      (invoke-static () "LCls;.foo:()I")
      (move-result v0)
      (return v0)
      (.try_end outer)

      (.catch (outer))
      (const v1 1)
      (return v1)
    )
  )";
  const auto* const callee_str = R"(
    (
      (.try_start inner1)
      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (return v0)
      (.try_end inner1)

      (.catch (inner2) "LExcept2;")
      (const v0 1)
      (return v0)

      (.catch (inner1 inner2) "LExcept1;")
      (const v0 0)
      (return v0)
    )
  )";
  const auto* const expected_str = R"(
    (
      (.try_start inner1)
      (sget-object "LCls;.field:Ljava/lang/Object;")
      (move-result-pseudo-object v2)
      (move v0 v2)
      (goto :end_callee)
      (.try_end inner1)

      (.catch (outer))
      (const v1 1)
      (return v1)

      (.catch (inner2 outer) "LExcept2;")
      (const v2 1)
      (move v0 v2)
      (goto :end_callee)

      (.catch (inner1 inner2) "LExcept1;")
      (const v2 0)
      (move v0 v2)

      (:end_callee)
      (return v0)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, inf_loop) {
  const auto* const caller_str = R"(
    (
      (:lbl)
      (invoke-static () "LCls;.foo:()I")
      (goto :lbl)
    )
  )";
  const auto* const callee_str = R"(
    (
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (:lbl)
      (goto :lbl)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, cleanup_debug) {
  const auto* const caller_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "LCls;.foo:(I)V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)
      (.dbg DBG_START_LOCAL_EXTENDED 4 "will_not_be_removed" "Ljava/lang/Objects;" "sig")
      (.dbg DBG_START_LOCAL 5 "will_not_be_removed" "Ljava/lang/Objects;")
      (const v1 1)
      (.dbg DBG_END_LOCAL 3)
      (.dbg DBG_END_LOCAL 4)
      (.dbg DBG_RESTART_LOCAL 6)
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (const v0 0)
      (move v1 v0)
      (.dbg DBG_START_LOCAL_EXTENDED 4 "will_not_be_removed" "Ljava/lang/Objects;" "sig")
      (.dbg DBG_START_LOCAL 5 "will_not_be_removed" "Ljava/lang/Objects;")
      (const v2 1)
      (.dbg DBG_END_LOCAL 4)
      (return-void)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(CFGInlinerTest, needs_receiver_cast) {
  const auto* const caller_str = R"(
    (
      (invoke-static (v0) "LCls;.foo:(LCls;)V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (load-param-object v0)
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (move-object v0 v0)
      (check-cast v0 "LCls;")
      (move-result-pseudo-object v0)
      (return-void)
    )
  )";
  DexType* needs_receiver_cast = DexType::make_type("LCls;");
  test_inliner(caller_str, callee_str, expected_str, needs_receiver_cast);
}

TEST_F(CFGInlinerTest, needs_init_class) {
  const auto* const caller_str = R"(
    (
      (invoke-static () "LCls;.foo:()V")
      (return-void)
    )
  )";
  const auto* const callee_str = R"(
    (
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (init-class "LCls;")
      (return-void)
    )
  )";
  DexType* needs_receiver_cast = nullptr;
  DexType* needs_init_class = DexType::make_type("LCls;");
  test_inliner(caller_str,
               callee_str,
               expected_str,
               needs_receiver_cast,
               needs_init_class);
}
