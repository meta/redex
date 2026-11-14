/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "DexAsm.h"
#include "IRAssembler.h"
#include "RedexTest.h"

#include <functional>

using namespace cfg;
using namespace dex_asm;
using namespace opcode;

namespace {

/// Test that the mutation to the control flow graph representation of \p actual
/// results in the \p expected IR.
///
/// \p m A function that mutates the CFG given to it.
/// \p actual The actual state of the IR before the mutation has been applied,
///     as an s-expression.
/// \p expected The expected state of the IR after the mutation has been
///     applied, as an s-expression.
void EXPECT_MUTATION(const std::function<void(IRCode&, ControlFlowGraph&)>& m,
                     const char* actual,
                     const char* expected) {
  auto actual_ir = assembler::ircode_from_string(actual);
  const auto expected_ir = assembler::ircode_from_string(expected);

  actual_ir->build_cfg();

  // Run body of test (that performs the mutation).
  m(*actual_ir, actual_ir->cfg());

  // The mutation may introduce more register uses, so recompute them.
  actual_ir->cfg().recompute_registers_size();

  actual_ir->clear_cfg();
  EXPECT_CODE_EQ(expected_ir.get(), actual_ir.get());
}

class CFGMutationTest : public RedexTest {};

TEST_F(CFGMutationTest, RemoveAllButLastPositon) {
  EXPECT_MUTATION([](IRCode&, ControlFlowGraph& cfg) { cfg.simplify(); },
                  /* ACTUAL */ R"((
        (.pos:dbg_0 method_name RedexGenerated 0)
        (.pos:dbg_1 method_name RedexGenerated 0)
        (.pos:dbg_2 method_name RedexGenerated 0)
        (const v0 0)
        (return-void)
      ))",
                  /* EXPECTED */ R"((
        (.pos:dbg_0 method_name RedexGenerated 0)
        (const v0 0)
        (return-void)
      ))");
}

TEST_F(CFGMutationTest, SimplificationRemovesEmptyBlockWithPosition) {
  EXPECT_MUTATION([](IRCode&, ControlFlowGraph& cfg) { cfg.simplify(); },
                  /* ACTUAL */ R"((
        (.pos:dbg_parent method_name RedexGenerated 0)
        (goto :Loop)

        (:Loop)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))",
                  /* EXPECTED */ R"((
        (:Loop)
        (.pos:dbg_parent method_name RedexGenerated 0)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))");
}

TEST_F(CFGMutationTest, RetainParentWhenRemovingBlock) {
  EXPECT_MUTATION(
      [](IRCode&, ControlFlowGraph& cfg) {
        cfg.remove_block(cfg.blocks().at(0));
      },
      /* ACTUAL */ R"((
        (.pos:dbg_parent method_name RedexGenerated 0)
        (const v0 0)
        (goto :Loop)

        (:Loop)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))",
      /* EXPECTED */ R"((
        (:Loop)
        (.pos:dbg_parent method_name RedexGenerated 0)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))");
}

TEST_F(CFGMutationTest, RetainParentWhenReplacingBlock) {
  EXPECT_MUTATION(
      [](IRCode&, ControlFlowGraph& cfg) {
        cfg.replace_block(cfg.blocks().at(0), cfg.create_block());
      },
      /* ACTUAL */ R"((
        (.pos:dbg_parent method_name RedexGenerated 0)
        (const v0 0)
        (goto :Loop)

        (:Loop)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))",
      /* EXPECTED */ R"((
        (:Loop)
        (.pos:dbg_parent method_name RedexGenerated 0)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))");
}

TEST_F(CFGMutationTest, RetainParentsWhenRemovingBlock) {
  EXPECT_MUTATION(
      [](IRCode&, ControlFlowGraph& cfg) {
        cfg.remove_block(cfg.blocks().at(0));
      },
      /* ACTUAL */ R"((
        (.pos:dbg_parent_parent method_name RedexGenerated 0)
        (.pos:dbg_parent method_name RedexGenerated 0 dbg_parent_parent)
        (const v0 0)
        (goto :Loop)

        (:Loop)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))",
      /* EXPECTED */ R"((
        (:Loop)
        (.pos:dbg_parent_parent method_name RedexGenerated 0)
        (.pos:dbg_parent method_name RedexGenerated 0 dbg_parent_parent)
        (.pos:dbg_child method_name RedexGenerated 0 dbg_parent)
        (const v0 0)
        (.pos:dbg_child method_name RedexGenerated 1 dbg_parent)
        (goto :Loop)
      ))");
}

TEST_F(CFGMutationTest, RemoveDuplicatePositions) {
  EXPECT_MUTATION(
      [](IRCode& code, ControlFlowGraph&) {
        // rebuilder cfg
        code.build_cfg();
      },
      /* ACTUAL */ R"((
        (.pos:pos0 FooBar Foo.java 0)
        (const v0 0)
        (.pos:pos1 FooBar Foo.java 0)
        (.pos:pos2 FooBar Foo.java 0)
        (.pos:pos3 FooBar Foo.java 0)
        (return-void)
      ))",
      /* EXPECTED */ R"((
        (.pos:pos4 FooBar Foo.java 0)
        (const v0 0)
        (return-void)
      ))");
}

TEST_F(CFGMutationTest, RemoveRedundantPositions) {
  EXPECT_MUTATION(
      [](IRCode& code, ControlFlowGraph&) {
        // rebuilder cfg
        code.build_cfg();
      },
      /* ACTUAL */ R"((
        (.pos:pos0 FooBar Foo.java 0)
        (const v0 0)
        (.pos:pos1 FooBar Foo.java 1)
        (.pos:pos2 FooBar Foo.java 2)
        (.pos:pos3 FooBar Foo.java 3)
        (return-void)
      ))",
      /* EXPECTED */ R"((
        (.pos:pos0 FooBar Foo.java 0)
        (const v0 0)
        (.pos:pos3 FooBar Foo.java 3)
        (return-void)
      ))");
}

TEST_F(CFGMutationTest, RemoveRedundantPositionsButKeepParents) {
  EXPECT_MUTATION(
      [](IRCode& code, ControlFlowGraph&) {
        // rebuilder cfg
        code.build_cfg();
      },
      /* ACTUAL */ R"((
        (.pos:pos0parent FooBoo Foo.java 0)
        (.pos:pos0 FooBar Foo.java 100 pos0parent)
        (const v0 0)
        (.pos:pos1 FooBar Foo.java 101)
        (.pos:pos2 FooBar Foo.java 102)
        (.pos:pos3parent FooBoo Foo.java 0)
        (.pos:pos3 FooBar Foo.java 103 pos3parent)
        (return-void)
      ))",
      /* EXPECTED */ R"((
        (.pos:pos0parent FooBoo Foo.java 0)
        (.pos:pos0 FooBar Foo.java 100 pos0parent)
        (const v0 0)
        (.pos:pos3parent FooBoo Foo.java 0)
        (.pos:pos3 FooBar Foo.java 103 pos3parent)
        (return-void)
      ))");
}
TEST_F(CFGMutationTest, RemoveRedundantAndDuplicatePositions) {
  EXPECT_MUTATION(
      [](IRCode& code, ControlFlowGraph&) {
        // rebuilder cfg
        code.build_cfg();
      },
      /* ACTUAL */ R"((
        (.pos:pos0 FooBar Foo.java 0)
        (const v0 0)
        (.pos:pos1 FooBar Foo.java 1)
        (.pos:pos2 FooBar Foo.java 2)
        (.pos:pos3 FooBar Foo.java 0)
        (return-void)
      ))",
      /* EXPECTED */ R"((
        (.pos:pos0 FooBar Foo.java 0)
        (const v0 0)
        (return-void)
      ))");
}

TEST_F(CFGMutationTest, RedundantAndDuplicatePositionsWithParents) {
  // Unfortunately, the logic in remove_redundant_positions cannot yet collapse
  // this.
  EXPECT_MUTATION(
      [](IRCode& code, ControlFlowGraph&) {
        // rebuild cfg
        code.build_cfg();
      },
      /* ACTUAL */ R"((
        (.pos:pos0parent FooBoo Foo.java 0)
        (.pos:pos0 FooBar Foo.java 100 pos0parent)
        (const v0 0)
        (.pos:pos1parent FooBoo Foo.java 0)
        (.pos:pos1 FooBar Foo.java 100 pos1parent)
        (return-void)
      ))",
      /* EXPECTED */ R"((
        (.pos:pos0parent FooBoo Foo.java 0)
        (.pos:pos0 FooBar Foo.java 100 pos0parent)
        (const v0 0)
        (.pos:pos1parent FooBoo Foo.java 0)
        (.pos:pos1 FooBar Foo.java 100 pos1parent)
        (return-void)
      ))");
}

std::vector<DexPosition*> cfg_positions(ControlFlowGraph& cfg) {
  std::vector<DexPosition*> result;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION) {
        result.push_back(mie.pos.get());
      }
    }
  }
  return result;
}

std::vector<DexPosition*> linear_positions(IRCode& code) {
  std::vector<DexPosition*> result;
  for (auto it = code.begin(); it != code.end(); ++it) {
    if (it->type == MFLOW_POSITION) {
      result.push_back(it->pos.get());
    }
  }
  return result;
}

std::unique_ptr<IRCode> linearize_marked_positions(
    const char* source, const std::vector<size_t>& marked_indices) {
  auto code = assembler::ircode_from_string(source);
  code->build_cfg();
  auto positions = cfg_positions(code->cfg());
  for (auto index : marked_indices) {
    positions.at(index)->mark_unreliable();
  }
  code->clear_cfg();
  return code;
}

// A producer that marks a block-start copy is saying that the instructions
// after the copy were folded. The instructions before it, still governed by
// the original, were not.
TEST_F(CFGMutationTest, MarkedCopyStaysSeparateFromOriginal) {
  auto code = linearize_marked_positions(R"((
    (.pos:first FooBar Foo.java 1)
    (const v0 0)
    (.pos:second FooBar Foo.java 1)
    (return-void)
  ))",
                                         {1});
  auto positions = linear_positions(*code);
  ASSERT_EQ(positions.size(), 2u);
  EXPECT_FALSE(positions[0]->is_unreliable());
  EXPECT_TRUE(positions[1]->is_unreliable());
}

TEST_F(CFGMutationTest, UnmarkedCopyAfterMarkedOriginalStaysSeparate) {
  auto code = linearize_marked_positions(R"((
    (.pos:first FooBar Foo.java 1)
    (const v0 0)
    (.pos:second FooBar Foo.java 1)
    (return-void)
  ))",
                                         {0});
  auto positions = linear_positions(*code);
  ASSERT_EQ(positions.size(), 2u);
  EXPECT_TRUE(positions[0]->is_unreliable());
  EXPECT_FALSE(positions[1]->is_unreliable());
}

TEST_F(CFGMutationTest, DuplicatesWithEqualProvenanceCollapse) {
  for (const auto& marked : std::vector<std::vector<size_t>>{{}, {0, 1}}) {
    auto code = linearize_marked_positions(R"((
      (.pos:first FooBar Foo.java 1)
      (const v0 0)
      (.pos:second FooBar Foo.java 1)
      (return-void)
    ))",
                                           marked);
    auto positions = linear_positions(*code);
    ASSERT_EQ(positions.size(), 1u);
    EXPECT_EQ(positions[0]->is_unreliable(), !marked.empty());
  }
}

// Building a CFG copies the position in effect into every later block, and
// linearizing drops those copies again. Neither step folds code, so neither
// may change what a synthetic position, or a frame inlined under one, claims.
TEST_F(CFGMutationTest, SyntheticChainSurvivesCfgRoundTrip) {
  auto code = assembler::ircode_from_string(R"((
    (.pos:callsite FooBoo Parent.java 0)
    (.pos:leaf FooBar Foo.java 1 callsite)
    (const v0 0)
    (if-eqz v0 :b)
    (const v1 1)
    (:b)
    (return-void)
  ))");
  code->build_cfg();
  code->clear_cfg();
  code->build_cfg();
  code->clear_cfg();

  auto positions = linear_positions(*code);
  ASSERT_EQ(positions.size(), 2u);
  for (auto* position : positions) {
    EXPECT_FALSE(position->is_unreliable());
  }
  EXPECT_TRUE(positions[0]->is_synthetic());
  EXPECT_FALSE(positions[1]->is_synthetic());
  EXPECT_EQ(positions[1]->parent, positions[0]);
}

TEST_F(CFGMutationTest, DuplicateParentProvenanceIsPreserved) {
  auto code = assembler::ircode_from_string(R"((
    (.pos:first_parent FooBoo Parent.java 2)
    (.pos:second_parent FooBoo Parent.java 2)
    (goto :leaves)
    (:leaves)
    (.pos:first FooBar Foo.java 1 first_parent)
    (.pos:second FooBar Foo.java 1 second_parent)
    (return-void)
  ))");
  code->build_cfg();
  auto positions = cfg_positions(code->cfg());
  std::vector<DexPosition*> leaves;
  for (auto* position : positions) {
    if (position->method == DexString::make_string("FooBar")) {
      leaves.push_back(position);
    }
  }
  ASSERT_EQ(leaves.size(), 2u);
  ASSERT_NE(leaves[1]->parent, nullptr);
  leaves[1]->parent->mark_unreliable();

  code->clear_cfg();
  positions = linear_positions(*code);
  DexPosition* retained_leaf = nullptr;
  for (auto* position : positions) {
    if (position->method == DexString::make_string("FooBar")) {
      retained_leaf = position;
      break;
    }
  }
  ASSERT_NE(retained_leaf, nullptr);
  ASSERT_NE(retained_leaf->parent, nullptr);
  EXPECT_FALSE(retained_leaf->is_unreliable());
  EXPECT_TRUE(retained_leaf->parent->is_unreliable());
}

TEST_F(CFGMutationTest, AdjacentDifferentPositionsDoNotTransferProvenance) {
  auto code = linearize_marked_positions(R"((
    (.pos:first FooBar Foo.java 1)
    (.pos:second FooBar Foo.java 2)
    (return-void)
  ))",
                                         {0});
  auto positions = linear_positions(*code);
  ASSERT_EQ(positions.size(), 1u);
  EXPECT_EQ(positions[0]->line, 2u);
  EXPECT_FALSE(positions[0]->is_unreliable());
}

} // namespace
