/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Debug.h"
#include "DedupBlocks.h"
#include "DedupBlocksPass.h"
#include "InsertSourceBlocks.h"

#include <boost/regex.hpp>

#include <gtest/gtest.h>

#include "RedexContext.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Walkers.h"

class SourceBlocksDedupTest : public RedexIntegrationTest {
 public:
  SourceBlocksDedupTest() {
    // The loading code in integ-test does not insert deobfuscated names.
    walk::methods(*classes, [](auto* m) {
      always_assert(m->get_deobfuscated_name_or_null() == nullptr);
      m->set_deobfuscated_name(show(m));
    });
  }

  std::string remove_mies(const std::string& cfg_str) {
    boost::regex mie("\\[0x[0-9a-f]+\\] ");
    return boost::regex_replace(cfg_str, mie, "");
  }

 protected:
  void enable_pass(InsertSourceBlocksPass& isbp) { isbp.m_force_run = true; }
  void enable_always_inject(InsertSourceBlocksPass& isbp) {
    isbp.m_always_inject = true;
  }
  void set_insert_after_excs(InsertSourceBlocksPass& isbp, bool val) {
    isbp.m_insert_after_excs = val;
  }

  testing::AssertionResult prepare() {
    g_redex->instrument_mode = true;
    IRList::CONSECUTIVE_STYLE = IRList::ConsecutiveStyle::kChain;
    auto* type =
        DexType::get_type("Lcom/facebook/redextest/SourceBlocksDedupTest;");
    if (type == nullptr) {
      return testing::AssertionFailure() << "type not found";
    }
    auto* cls = type_class(type);
    if (cls == nullptr) {
      return testing::AssertionFailure() << "class not found";
    }

    // Check that no code has source blocks so far.
    {
      for (const auto* m : cls->get_all_methods()) {
        if (m->get_code() == nullptr) {
          continue;
        }
        for (const auto& mie : *m->get_code()) {
          if (mie.type == MFLOW_SOURCE_BLOCK) {
            return testing::AssertionFailure() << "source block found";
          }
        }
      }
    }

    InsertSourceBlocksPass isbp{};
    run_passes({&isbp, new DedupBlocksPass()}, nullptr, Json::nullValue,
               [&](const auto&) {
                 enable_pass(isbp);
                 enable_always_inject(isbp);
                 set_insert_after_excs(isbp, false);
               });

    return testing::AssertionSuccess();
  }
};

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_useSwitch) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* switch_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I")
          ->as_def()
          ->get_code();
  switch_method->build_cfg();
  std::string switch_method_cfg = remove_mies(SHOW(switch_method->cfg()));
  EXPECT_EQ(switch_method_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v4\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:20)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@0()\n\
   OPCODE: INVOKE_STATIC Ljava/lang/Math;.random:()D\n\
   OPCODE: MOVE_RESULT_WIDE v0\n\
   OPCODE: CONST_WIDE v2, 4621819117588971520\n\
   OPCODE: MUL_DOUBLE v0, v0, v2\n\
   OPCODE: DOUBLE_TO_INT v0, v0\n\
   OPCODE: SWITCH v0\n\
   succs: (branch 2 B3) (branch 1 B4) (branch 0 B5) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:31)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@1()\n\
   OPCODE: INVOKE_VIRTUAL v4, Lcom/facebook/redextest/SourceBlocksDedupTest;.otherFunc:()V\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B6)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:34)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@2()\n\
   OPCODE: CONST v0, 0\n\
   OPCODE: RETURN v0\n\
   succs:\n\
 Block B3:\n\
   preds: (branch 2 B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:28)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@5()\n\
   succs: (goto B6)\n\
 Block B4:\n\
   preds: (branch 1 B0)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@4()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:26)\n\
   succs: (goto B6)\n\
 Block B5:\n\
   preds: (branch 0 B0)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@3()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:23)\n\
   succs: (goto B6)\n\
 Block B6:\n\
   preds: (goto B3) (goto B4) (goto B5)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:23)\n\
   OPCODE: INVOKE_VIRTUAL v4, Lcom/facebook/redextest/SourceBlocksDedupTest;.someFunc:()V\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:29)\n\
   succs: (goto B2)\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_deepestIsNotTheBestCase) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* deepest_not_best =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I")
          ->as_def()
          ->get_code();
  deepest_not_best->build_cfg();
  std::string deepest_not_best_cfg = remove_mies(show(deepest_not_best->cfg()));
  EXPECT_EQ(deepest_not_best_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v3\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:38)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@0()\n\
   OPCODE: CONST v0, 0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:39)\n\
   DEBUG: DBG_START_LOCAL v0 x:I\n\
   OPCODE: CONST v1, 1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:40)\n\
   DEBUG: DBG_START_LOCAL v1 y:I\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B3) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:41)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@1()\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B14)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:41)\n\
   OPCODE: RETURN v0\n\
   succs:\n\
 Block B3:\n\
   preds: (branch B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:42)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@2()\n\
   OPCODE: CONST v2, 1\n\
   OPCODE: IF_NE v0, v2\n\
   succs: (branch B6) (goto B4)\n\
 Block B4:\n\
   preds: (goto B3)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:43)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@3()\n\
   OPCODE: CONST v2, 1\n\
   succs: (goto B5)\n\
 Block B5:\n\
   preds: (goto B4) (goto B7) (goto B9) (goto B11) (goto B13)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:44)\n\
   DEBUG: DBG_START_LOCAL v2 z:I\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:45)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:46)\n\
   OPCODE: RETURN v2\n\
   succs:\n\
 Block B6:\n\
   preds: (branch B3)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:47)\n\
   DEBUG: DBG_END_LOCAL v2\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@4()\n\
   OPCODE: CONST v2, 2\n\
   OPCODE: IF_NE v0, v2\n\
   succs: (branch B8) (goto B7)\n\
 Block B7:\n\
   preds: (goto B6)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:48)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@5()\n\
   OPCODE: CONST v2, 2\n\
   succs: (goto B5)\n\
 Block B8:\n\
   preds: (branch B6)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:52)\n\
   DEBUG: DBG_END_LOCAL v2\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@6()\n\
   OPCODE: CONST v2, 3\n\
   OPCODE: IF_NE v0, v2\n\
   succs: (branch B10) (goto B9)\n\
 Block B9:\n\
   preds: (goto B8)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:53)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@7()\n\
   OPCODE: CONST v2, 3\n\
   succs: (goto B5)\n\
 Block B10:\n\
   preds: (branch B8)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:57)\n\
   DEBUG: DBG_END_LOCAL v2\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@8()\n\
   OPCODE: CONST v2, 4\n\
   OPCODE: IF_NE v0, v2\n\
   succs: (branch B12) (goto B11)\n\
 Block B11:\n\
   preds: (goto B10)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:58)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@9()\n\
   OPCODE: CONST v2, 4\n\
   succs: (goto B5)\n\
 Block B12:\n\
   preds: (branch B10)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:62)\n\
   DEBUG: DBG_END_LOCAL v2\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@10()\n\
   OPCODE: CONST v2, 5\n\
   OPCODE: IF_NE v0, v2\n\
   succs: (branch B14) (goto B13)\n\
 Block B13:\n\
   preds: (goto B12)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I(SourceBlocksDedupTest.java:63)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@11()\n\
   OPCODE: CONST v2, 5\n\
   succs: (goto B5)\n\
 Block B14:\n\
   preds: (branch B12)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.deepestIsNotTheBestCase:()I@12()\n\
   succs: (goto B2)\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_dedupThrows) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* dedup_throws = DexMethod::get_method(
                           "Lcom/facebook/redextest/"
                           "SourceBlocksDedupTest;.dedupThrows:()V")
                           ->as_def()
                           ->get_code();
  dedup_throws->build_cfg();
  std::string dedup_throws_cfg = remove_mies(show(dedup_throws->cfg()));
  EXPECT_EQ(dedup_throws_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v3\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V(SourceBlocksDedupTest.java:73)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V@0()\n\
   OPCODE: CONST v0, 0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V(SourceBlocksDedupTest.java:74)\n\
   DEBUG: DBG_START_LOCAL v0 x:I\n\
   OPCODE: CONST_STRING \"throwing\"\n\
   OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT v1\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B3) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V(SourceBlocksDedupTest.java:75)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V@1()\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B3)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V(SourceBlocksDedupTest.java:75)\n\
   OPCODE: NEW_INSTANCE Ljava/lang/ArithmeticException;\n\
   OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT v2\n\
   OPCODE: INVOKE_DIRECT v2, v1, Ljava/lang/ArithmeticException;.<init>:(Ljava/lang/String;)V\n\
   OPCODE: THROW v2\n\
   succs:\n\
 Block B3:\n\
   preds: (branch B0)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.dedupThrows:()V@2()\n\
   succs: (goto B2)\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_simplestCase) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* simplest_case =
      DexMethod::get_method(
          "Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V")
          ->as_def()
          ->get_code();
  simplest_case->build_cfg();
  std::string simplest_case_cfg = remove_mies(show(simplest_case->cfg()));
  EXPECT_EQ(simplest_case_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:82)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@0()\n\
   OPCODE: CONST v0, 0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:83)\n\
   DEBUG: DBG_START_LOCAL v0 x:I\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:84)\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B3) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:85)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@1()\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B3)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:89)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:91)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@2()\n\
   OPCODE: RETURN_VOID \n\
   succs:\n\
 Block B3:\n\
   preds: (branch B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:88)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@3()\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   succs: (goto B2)\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_postfixDiscardingOne) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* postfix_discarding_one =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "SourceBlocksDedupTest;.postfixDiscardingOne:()V")
          ->as_def()
          ->get_code();
  postfix_discarding_one->build_cfg();
  std::string postfix_discarding_one_cfg =
      remove_mies(show(postfix_discarding_one->cfg()));
  EXPECT_EQ(postfix_discarding_one_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:95)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@0()\n\
   OPCODE: CONST v0, 0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:96)\n\
   DEBUG: DBG_START_LOCAL v0 x:I\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:97)\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B5) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:98)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@1()\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B4) (goto B2)\n\
 Block B2:\n\
   preds: (goto B1)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:99)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@2()\n\
   OPCODE: SUB_INT v0, v0, v0\n\
   succs: (goto B3)\n\
 Block B3:\n\
   preds: (goto B2) (goto B6)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:115)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@3()\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:116)\n\
   OPCODE: RETURN_VOID \n\
   succs:\n\
 Block B4:\n\
   preds: (branch B1)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:102)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@4()\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   succs: (goto B6)\n\
 Block B5:\n\
   preds: (branch B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:109)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@5()\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:110)\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   succs: (goto B6)\n\
 Block B6:\n\
   preds: (goto B4) (goto B5)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:103)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:104)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.postfixDiscardingOne:()V(SourceBlocksDedupTest.java:105)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   succs: (goto B3)\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_dedup_identicalSelfLoops) {
  auto res = prepare();
  ASSERT_TRUE(res);

  auto* self_loops = DexMethod::get_method(
                         "Lcom/facebook/redextest/"
                         "SourceBlocksDedupTest;.identicalSelfLoops:()V")
                         ->as_def()
                         ->get_code();
  self_loops->build_cfg();
  std::string self_loops_cfg = remove_mies(show(self_loops->cfg()));
  EXPECT_EQ(self_loops_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V(SourceBlocksDedupTest.java:120)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@0()\n\
   OPCODE: CONST v0, 1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V(SourceBlocksDedupTest.java:121)\n\
   DEBUG: DBG_START_LOCAL v0 i:Z\n\
   OPCODE: IF_EQZ v0\n\
   succs: (branch B3) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0) (goto B1)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@1() Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V(SourceBlocksDedupTest.java:122)\n\
   OPCODE: IF_EQZ v0\n\
   succs: (branch B5) (goto B1)\n\
 Block B3:\n\
   preds: (branch B0) (goto B3)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@3() Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V(SourceBlocksDedupTest.java:124)\n\
   OPCODE: IF_EQZ v0\n\
   succs: (branch B5) (goto B3)\n\
 Block B5:\n\
   preds: (branch B1) (branch B3)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V(SourceBlocksDedupTest.java:126)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.identicalSelfLoops:()V@2()\n\
   OPCODE: RETURN_VOID \n\
   succs:\n");
}

TEST_F(SourceBlocksDedupTest, source_blocks_chain) {
  g_redex->instrument_mode = true;
  IRList::CONSECUTIVE_STYLE = IRList::ConsecutiveStyle::kChain;
  auto* type =
      DexType::get_type("Lcom/facebook/redextest/SourceBlocksDedupTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
  });

  auto* switch_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I")
          ->as_def();
  auto* switch_code = switch_method->get_code();
  switch_code->build_cfg();
  auto& cfg = switch_code->cfg();

  for (int i = 3; i <= 5; i++) {
    auto* block = cfg.get_block(i);
    for (int j = 1; j < 4; j++) {
      auto new_sb = std::make_unique<SourceBlock>(
          *source_blocks::get_last_source_block(block));
      new_sb->id = 100;
      block->insert_before(block->get_first_insn(), std::move(new_sb));
    }
  }

  dedup_blocks_impl::Config empty_config;
  dedup_blocks_impl::DedupBlocks db(&empty_config, switch_method);
  db.run();

  switch_code->build_cfg();
  std::string switch_cfg = remove_mies(show(switch_code->cfg()));
  EXPECT_EQ(
      switch_cfg,
      "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v4\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:20)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@0()\n\
   OPCODE: INVOKE_STATIC Ljava/lang/Math;.random:()D\n\
   OPCODE: MOVE_RESULT_WIDE v0\n\
   OPCODE: CONST_WIDE v2, 4621819117588971520\n\
   OPCODE: MUL_DOUBLE v0, v0, v2\n\
   OPCODE: DOUBLE_TO_INT v0, v0\n\
   OPCODE: SWITCH v0\n\
   succs: (branch 2 B3) (branch 1 B4) (branch 0 B5) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:31)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@1()\n\
   OPCODE: INVOKE_VIRTUAL v4, Lcom/facebook/redextest/SourceBlocksDedupTest;.otherFunc:()V\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B6)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:34)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@2()\n\
   OPCODE: CONST v0, 0\n\
   OPCODE: RETURN v0\n\
   succs:\n\
 Block B3:\n\
   preds: (branch 2 B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:28)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@5()\n\
   succs: (goto B6)\n\
 Block B4:\n\
   preds: (branch 1 B0)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@4()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:26)\n\
   succs: (goto B6)\n\
 Block B5:\n\
   preds: (branch 0 B0)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@3()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:23)\n\
   succs: (goto B6)\n\
 Block B6:\n\
   preds: (goto B3) (goto B4) (goto B5)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@100() "
      "Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@100() Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I@100()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:23)\n\
   OPCODE: INVOKE_VIRTUAL v4, Lcom/facebook/redextest/SourceBlocksDedupTest;.someFunc:()V\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.useSwitch:()I(SourceBlocksDedupTest.java:29)\n\
   succs: (goto B2)\n");
}

TEST_F(SourceBlocksDedupTest, multiple_source_blocks_in_one_block) {
  g_redex->instrument_mode = true;
  IRList::CONSECUTIVE_STYLE = IRList::ConsecutiveStyle::kChain;
  auto* type =
      DexType::get_type("Lcom/facebook/redextest/SourceBlocksDedupTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
  });

  auto* simplest_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V")
          ->as_def();
  auto* simpliest_code = simplest_method->get_code();
  simpliest_code->build_cfg();
  auto& cfg = simpliest_code->cfg();

  auto* block = cfg.get_block(1);
  auto new_sb = std::make_unique<SourceBlock>(
      *source_blocks::get_last_source_block(block));
  new_sb->id = 100;
  block->insert_after(block->get_last_insn(), std::move(new_sb));

  block = cfg.get_block(3);
  new_sb = std::make_unique<SourceBlock>(
      *source_blocks::get_last_source_block(block));
  new_sb->id = 100;
  block->insert_after(block->get_last_insn(), std::move(new_sb));

  dedup_blocks_impl::Config empty_config;
  dedup_blocks_impl::DedupBlocks db(&empty_config, simplest_method);
  db.run();

  simpliest_code->build_cfg();
  std::string simplest_cfg = remove_mies(show(simpliest_code->cfg()));
  EXPECT_EQ(simplest_cfg,
            "CFG:\n\
 Block B0: entry\n\
   preds:\n\
   OPCODE: IOPCODE_LOAD_PARAM_OBJECT v1\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:82)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@0()\n\
   OPCODE: CONST v0, 0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:83)\n\
   DEBUG: DBG_START_LOCAL v0 x:I\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:84)\n\
   OPCODE: IF_NEZ v0\n\
   succs: (branch B3) (goto B1)\n\
 Block B1:\n\
   preds: (goto B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:85)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@1()\n\
   succs: (goto B2)\n\
 Block B2:\n\
   preds: (goto B1) (goto B3)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@4294967295()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:89)\n\
   OPCODE: ADD_INT v0, v0, v0\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@100() Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@2()\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:91)\n\
   OPCODE: RETURN_VOID \n\
   succs:\n\
 Block B3:\n\
   preds: (branch B0)\n\
   POSITION: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V(SourceBlocksDedupTest.java:88)\n\
   SOURCE-BLOCKS: Lcom/facebook/redextest/SourceBlocksDedupTest;.simplestCase:()V@3()\n\
   OPCODE: MUL_INT v0, v0, v0\n\
   succs: (goto B2)\n");
}
