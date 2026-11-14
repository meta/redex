/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <regex>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexAsm.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRTemplate.h"
#include "RedexTest.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace cfg {

std::ostream& operator<<(std::ostream& os, const Block* b) {
  return os << b->id();
}

} // namespace cfg

using namespace cfg;
using namespace dex_asm;

class ControlFlowTest : public RedexTest {
 public:
  InstructionEquality m_equal = std::equal_to<const IRInstruction&>();
};

TEST_F(ControlFlowTest, findExitBlocks) {
  {
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b0})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b0);
  }
  {
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b1})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b1);
  }
  {
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b0, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b0})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b0);
  }
  {
    //   +---------+
    //   v         |
    // +---+     +---+     +---+
    // | 0 | --> | 1 | --> | 2 |
    // +---+     +---+     +---+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b0, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b2})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b2);
  }
  {
    //             +---------+
    //             v         |
    // +---+     +---+     +---+
    // | 0 | --> | 1 | --> | 2 |
    // +---+     +---+     +---+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.add_edge(b2, b1, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b1})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b1);
  }
  {
    //             +---------+
    //             v         |
    // +---+     +---+     +---+
    // | 0 | --> | 1 | --> | 2 |
    // +---+     +---+     +---+
    //   |
    //   |
    //   v
    // +---+
    // | 3 |
    // +---+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    auto* b3 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.add_edge(b2, b1, EDGE_GOTO);
    cfg.add_edge(b0, b3, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_THAT(cfg.real_exit_blocks(/* include_infinite_loops */ true),
                ::testing::UnorderedElementsAre(b1, b3))
        << show(cfg);
    EXPECT_EQ(cfg.exit_block()->id(), 4);
  }
  {
    //             +---------+
    //             v         |
    // +---+     +---+     +---+     +---+
    // | 0 | --> | 1 | --> | 2 | --> | 3 |
    // +---+     +---+     +---+     +---+
    //   ^                             |
    //   +-----------------------------+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    auto* b3 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.add_edge(b2, b1, EDGE_GOTO);
    cfg.add_edge(b2, b3, EDGE_GOTO);
    cfg.add_edge(b3, b0, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b0})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b0);
  }
  {
    //                 +---------+
    //                 v         |
    //     +---+     +---+     +---+
    //  +- | 0 | --> | 1 | --> | 2 |
    //  |  +---+     +---+     +---+
    //  |
    //  |    +---------+
    //  |    v         |
    //  |  +---+     +---+
    //  +> | 3 | --> | 4 |
    //     +---+     +---+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    auto* b3 = cfg.create_block();
    auto* b4 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.add_edge(b2, b1, EDGE_GOTO);
    cfg.add_edge(b0, b3, EDGE_GOTO);
    cfg.add_edge(b3, b4, EDGE_GOTO);
    cfg.add_edge(b4, b3, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_THAT(cfg.real_exit_blocks(/* include_infinite_loops */ true),
                ::testing::UnorderedElementsAre(b1, b3))
        << show(cfg);
    EXPECT_EQ(cfg.exit_block()->id(), 5);
  }
  {
    //                 +---------+
    //                 v         |
    //     +---+     +---+     +---+     +---+
    //  +- | 0 | --> | 1 | --> | 2 | --> | 5 |
    //  |  +---+     +---+     +---+     +---+
    //  |                                  ^
    //  |    +---------+                   |
    //  |    v         |                   |
    //  |  +---+     +---+                 |
    //  +> | 3 | --> | 4 | ----------------+
    //     +---+     +---+
    ControlFlowGraph cfg;
    auto* b0 = cfg.create_block();
    auto* b1 = cfg.create_block();
    auto* b2 = cfg.create_block();
    auto* b3 = cfg.create_block();
    auto* b4 = cfg.create_block();
    auto* b5 = cfg.create_block();
    cfg.set_entry_block(b0);
    cfg.add_edge(b0, b1, EDGE_GOTO);
    cfg.add_edge(b1, b2, EDGE_GOTO);
    cfg.add_edge(b2, b1, EDGE_GOTO);
    cfg.add_edge(b0, b3, EDGE_GOTO);
    cfg.add_edge(b3, b4, EDGE_GOTO);
    cfg.add_edge(b4, b3, EDGE_GOTO);
    cfg.add_edge(b4, b5, EDGE_GOTO);
    cfg.add_edge(b2, b5, EDGE_GOTO);
    cfg.calculate_exit_block();
    EXPECT_EQ(cfg.real_exit_blocks(/* include_infinite_loops */ true),
              std::vector<Block*>{b5})
        << show(cfg);
    EXPECT_EQ(cfg.exit_block(), b5);
  }
}

TEST_F(ControlFlowTest, iterate1) {
  auto code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
  )");
  code->build_cfg();
  for (Block* b : code->cfg().blocks()) {
    EXPECT_NE(nullptr, b);
  }
  for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
    EXPECT_EQ(OPCODE_RETURN_VOID, mie.insn->opcode());
  }
}

TEST_F(ControlFlowTest, iterate2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :if-true-label)
     (goto :loop) ; this goto is removed

     (:if-true-label)
     (return-void)
    )
)");
  code->build_cfg();
  for (Block* b : code->cfg().blocks()) {
    EXPECT_NE(nullptr, b);
  }

  // iterate within a block in the correct order
  // but visit the blocks in any order
  std::unordered_map<IRInstruction*, size_t> times_encountered;
  auto iterable = cfg::InstructionIterable(code->cfg());
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    EXPECT_FALSE(it.is_end());
    auto* insn = it->insn;
    auto op = insn->opcode();
    if (op == OPCODE_CONST) {
      EXPECT_EQ(OPCODE_IF_GEZ, std::next(it)->insn->opcode());
    }
    times_encountered[insn] += 1;
  }
  EXPECT_TRUE(iterable.end().is_end());
  EXPECT_EQ(4, times_encountered.size());
  for (const auto& entry : times_encountered) {
    EXPECT_EQ(1, entry.second);
  }
  TRACE(CFG, 1, "%s", SHOW(code->cfg()));
}

TEST_F(ControlFlowTest, iterate3) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :if-true-label)
     (goto :loop) ; this goto is removed

     (:if-true-label)
     (return-void)
    )
)");
  code->build_cfg();
  // Check that ++ and -- agree
  auto iterable = cfg::InstructionIterable(code->cfg());
  std::stack<cfg::InstructionIterator> iterators;
  for (auto it = iterable.end(); it != iterable.begin(); --it) {
    iterators.push(it);
  }
  iterators.push(iterable.begin());
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    EXPECT_EQ(it, iterators.top());
    iterators.pop();
  }
  EXPECT_EQ(iterable.end(), iterators.top());
  iterators.pop();
  EXPECT_TRUE(iterators.empty());
}

// C++14 Null Forward Iterators
// Make sure the default constructed InstructionIterator compares equal
// to other default constructed InstructionIterator
//
// boost.org/doc/libs/1_58_0/doc/html/container/Cpp11_conformance.html
TEST_F(ControlFlowTest, nullForwardIterators) {
  auto code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  for (int i = 0; i < 100; i++) {
    auto* a = new cfg::InstructionIterable(cfg);
    EXPECT_TRUE(a->end() == cfg::InstructionIterable(cfg).end());
    delete a;
  }

  IRList::iterator a;
  IRList::iterator b;
  EXPECT_EQ(a, b);
  for (int i = 0; i < 100; i++) {
    auto* iterable = new cfg::InstructionIterable(cfg);
    EXPECT_EQ(a, iterable->end().unwrap());
    EXPECT_EQ(b, iterable->end().unwrap());
    delete iterable;
  }

  for (int i = 0; i < 100; i++) {
    auto* iterator = new ir_list::InstructionIterator();
    EXPECT_EQ(ir_list::InstructionIterator(), *iterator);
    delete iterator;
  }

  auto iterable = cfg::InstructionIterable(cfg);
  EXPECT_TRUE(iterable.end().is_end());
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    EXPECT_FALSE(it.is_end());
  }
}

TEST_F(ControlFlowTest, copyConstructibleIterator) {
  auto code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
  )");
  code->build_cfg();
  ControlFlowGraph& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  std::optional<cfg::InstructionIterator> opt;
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    opt = it;
  }
}

TEST_F(ControlFlowTest, buildAndLinearizeNoChange) {
  const auto* str = R"(
    (
      (const v0 0)
      (const v1 1)
      (move v3 v0)
      (return v3)
    )
  )";
  auto input_code = assembler::ircode_from_string(str);
  auto expected_code = assembler::ircode_from_string(str);

  input_code->build_cfg();
  input_code->clear_cfg();

  EXPECT_CODE_EQ(expected_code.get(), input_code.get());
}

TEST_F(ControlFlowTest, infinite) {
  const auto* str = R"(
    (
      (:lbl)
      (goto :lbl)
    )
  )";
  auto input_code = assembler::ircode_from_string(str);
  auto expected_code = assembler::ircode_from_string(str);

  TRACE(CFG, 1, "%s", SHOW(input_code));
  input_code->build_cfg();
  TRACE(CFG, 1, "%s", SHOW(input_code->cfg()));
  input_code->clear_cfg();

  EXPECT_CODE_EQ(expected_code.get(), input_code.get());
}

TEST_F(ControlFlowTest, infinite2) {
  const auto* str = R"(
    (
      (:lbl)
      (const v0 0)
      (goto :lbl)
    )
  )";
  auto input_code = assembler::ircode_from_string(str);
  auto expected_code = assembler::ircode_from_string(str);

  input_code->build_cfg();
  TRACE(CFG, 1, "%s", SHOW(input_code->cfg()));
  input_code->clear_cfg();

  EXPECT_CODE_EQ(expected_code.get(), input_code.get());
}

TEST_F(ControlFlowTest, unreachable) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:lbl)
      (return-void)

      (goto :lbl)
    )
  )");
  auto expected_code = assembler::ircode_from_string(R"(
    (
      ; cfg simplification removes the unreachable empty block
      (return-void)
    )
  )");

  input_code->build_cfg();
  TRACE(CFG, 1, "%s", SHOW(input_code->cfg()));
  input_code->clear_cfg();

  EXPECT_CODE_EQ(expected_code.get(), input_code.get());
}

TEST_F(ControlFlowTest, unreachable2) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:lbl)
      (return-void)

      (const v0 0)
      (goto :lbl)
    )
  )");
  auto expected_code = assembler::ircode_from_string(R"(
    (
      ; cfg simplification removes the unreachable block
      (return-void)
    )
  )");

  input_code->build_cfg();
  TRACE(CFG, 1, "%s", SHOW(input_code->cfg()));
  input_code->clear_cfg();

  EXPECT_CODE_EQ(expected_code.get(), input_code.get());
}

TEST_F(ControlFlowTest, remove_non_branch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const-wide v2 1)
      (move v1 v0)
      (return-void)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto iterable = cfg::InstructionIterable(cfg);
  std::vector<cfg::InstructionIterator> to_delete;
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST_WIDE) {
      to_delete.push_back(it);
    }
  }

  for (auto& it : to_delete) {
    cfg.remove_insn(it);
  }
  cfg.recompute_registers_size();

  code->clear_cfg();
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (move v1 v0)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

void delete_if(ControlFlowGraph& cfg,
               const std::function<bool(IROpcode)>& predicate) {
  auto iterable = cfg::InstructionIterable(cfg);
  std::vector<cfg::InstructionIterator> to_delete;
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (predicate(it->insn->opcode())) {
      to_delete.push_back(it);
    }
  }

  for (auto& it : to_delete) {
    cfg.remove_insn(it);
  }
  cfg.recompute_registers_size();
}

TEST_F(ControlFlowTest, remove_non_branch_with_loop) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     ; implicit goto (:loop)

     (:loop)
     (const v1 0)
     (if-gez v0 :if-true-label)
     (goto :loop)

     (:if-true-label)
     (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op == OPCODE_CONST; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     ; implicit goto :loop

     (:loop)
     (if-gez v0 :if-true-label)
     (goto :loop)

     (:if-true-label)
     (return-void)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_branch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :lbl)
      (const v1 1)

      (:lbl)
      (return-void)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op == OPCODE_IF_EQZ; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_branch_with_loop) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :loop)

     (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op == OPCODE_IF_GEZ; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (const v1 0)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_all_but_return) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :loop)

     (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op != OPCODE_RETURN_VOID; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:a :b))

      (:exit)
      (return-void)

      (:a 0)
      (const v0 0)
      (goto :exit)

      (:b 1)
      (const v1 1)
      (goto :exit)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op == OPCODE_SWITCH; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_switch2) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:a :b))
      (goto :exit)

      (:a 0)
      (const v0 0)
      (goto :exit)

      (:b 1)
      (const v1 1)
      (goto :exit)

      (:exit)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  delete_if(cfg, [](IROpcode op) { return op == OPCODE_SWITCH; });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_pred_edge_if) {
  auto code = assembler::ircode_from_string(R"(
    (
      (:a 0)
      (const v0 1)
      (if-eqz v0 :end)

      (switch v0 (:a :b))

      (:b 1)
      (const v0 2)
      (if-eqz v0 :end)

      (const v0 3)

      (:end)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.delete_pred_edge_if(cfg.entry_block(), [](const cfg::Edge* e) {
    return e->type() == EDGE_BRANCH;
  });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (if-eqz v0 :end)

      (switch v0 (:b))

      (:b 1)
      (const v0 2)
      (if-eqz v0 :end)

      (const v0 3)

      (:end)
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, cleanup_after_deleting_branch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (if-eqz v0 :true)

      (const v0 0)
      (goto :end)

      (:true)
      (const v1 1)

      (:end)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.delete_succ_edge_if(cfg.entry_block(), [](const cfg::Edge* e) {
    return e->type() == EDGE_BRANCH;
  });
  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, cleanup_after_deleting_goto) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (if-eqz v0 :true)

      (const v0 0)

      (:true)
      (const v1 1)
      (return-void)
    )
)");

  code->build_cfg();

  auto& cfg = code->cfg();
  cfg.delete_succ_edge_if(cfg.entry_block(), [](const cfg::Edge* e) {
    return e->type() == EDGE_GOTO;
  });

  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (const v1 1)
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, remove_sget) {

  auto code = assembler::ircode_from_string(R"(
    (
      (sget Lcom/Foo.bar:I)
      (move-result-pseudo v0)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  auto iterable = cfg::InstructionIterable(cfg);
  std::vector<cfg::InstructionIterator> to_delete;
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn->opcode() == OPCODE_SGET) {
      to_delete.push_back(it);
    }
  }

  for (auto& it : to_delete) {
    cfg.remove_insn(it);
  }
  cfg.recompute_registers_size();

  code->clear_cfg();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
)");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(ControlFlowTest, branchingness) {

  auto code = assembler::ircode_from_string(R"(
    (
      (const-string "one")
      (move-result-pseudo v0)
      (if-eqz v0 :a)

      (const-string "two")
      (move-result-pseudo v0)
      (goto :end)

      (:a)
      (const-string "three")
      (move-result-pseudo v0)

      (:end)
      (const-string "four")
      (move-result-pseudo v0)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  uint16_t blocks_checked = 0;
  for (Block* b : cfg.blocks()) {
    const auto str = b->get_first_insn()->insn->get_string()->str();
    if (str == "one") {
      EXPECT_EQ(opcode::BRANCH_IF, b->branchingness());
      ++blocks_checked;
    }
    if (str == "two" || str == "three") {
      EXPECT_EQ(opcode::BRANCH_GOTO, b->branchingness());
      ++blocks_checked;
    }
    if (str == "four") {
      EXPECT_EQ(opcode::BRANCH_RETURN, b->branchingness());
      ++blocks_checked;
    }
  }
  EXPECT_EQ(4, blocks_checked);
}

TEST_F(ControlFlowTest, empty_first_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (goto :exit)

      (add-int/lit v0 v0 1)

      (:exit)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();

  auto iterable = cfg::InstructionIterable(cfg);
  std::vector<cfg::InstructionIterator> to_delete;
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST) {
      // make the first block empty
      to_delete.push_back(it);
    }
  }
  for (const auto& it : to_delete) {
    cfg.remove_insn(it);
  }
  cfg.recompute_registers_size();

  for (const auto& mie : cfg::ConstInstructionIterable(code->cfg())) {
    std::cout << show(mie) << "\n";
  }
}

TEST_F(ControlFlowTest, exit_blocks) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :thr)
      (return-void)
      (:thr)
      (throw v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  EXPECT_EQ(2, cfg.real_exit_blocks().size());
  code->clear_cfg();
}

TEST_F(ControlFlowTest, exit_blocks_change) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :thr)
      (return-void)
      (:thr)
      (throw v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_EQ(2, cfg.real_exit_blocks().size());

  auto iterable = cfg::InstructionIterable(cfg);
  std::vector<cfg::Block*> to_delete;
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn->opcode() == OPCODE_THROW) {
      to_delete.push_back(it.block());
    }
  }
  cfg.remove_blocks(to_delete);
  cfg.recompute_registers_size();

  EXPECT_EQ(1, cfg.real_exit_blocks().size());
  code->clear_cfg();
}

TEST_F(ControlFlowTest, remove_ghost_exit_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :thr)
      (return-void)
      (:thr)
      (throw v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_EQ(cfg.num_blocks(), 3);
  EXPECT_EQ(cfg.exit_block(), nullptr);
  cfg.calculate_exit_block();
  EXPECT_EQ(cfg.num_blocks(), 4);
  EXPECT_NE(cfg.exit_block(), nullptr);
  cfg.remove_block(cfg.exit_block());
  EXPECT_EQ(cfg.num_blocks(), 3);
  EXPECT_EQ(cfg.exit_block(), nullptr);
  code->clear_cfg();
}

TEST_F(ControlFlowTest, remove_real_exit_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (goto :next)
      (:next)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_EQ(cfg.num_blocks(), 2);
  EXPECT_EQ(cfg.exit_block(), nullptr);
  cfg.calculate_exit_block();
  EXPECT_EQ(cfg.num_blocks(), 2);
  EXPECT_NE(cfg.exit_block(), nullptr);
  cfg.remove_block(cfg.exit_block());
  EXPECT_EQ(cfg.num_blocks(), 1);
  EXPECT_EQ(cfg.exit_block(), nullptr);
  code->clear_cfg();
}

TEST_F(ControlFlowTest, deep_copy1) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :thr)
      (return-void)
      (:thr)
      (throw v0)
    )
)");

  code->build_cfg();
  auto& orig = code->cfg();

  cfg::ControlFlowGraph copy;
  orig.deep_copy(&copy);
  EXPECT_TRUE(orig.structural_equals(copy));
  auto orig_list = orig.linearize();
  auto copy_list = copy.linearize();

  EXPECT_TRUE(orig_list->structural_equals(*copy_list, m_equal));
}

TEST_F(ControlFlowTest, structural_equals_switch_case_keys) {
  // The case keys live on the CFG edges, not on the switch instruction.
  constexpr const char* kSwitch = R"(
    (
      (load-param v0)
      (switch v0 (:a :b))
      (return-void)
      (:a $KEY_A)
      (const v1 10)
      (return-void)
      (:b $KEY_B)
      (const v1 20)
      (return-void)
    )
  )";
  auto make_code = [&](const std::string& key_a, const std::string& key_b) {
    return assembler::ircode_from_string(
        ir(kSwitch, {{"$KEY_A", key_a}, {"$KEY_B", key_b}}));
  };
  auto keys_0_1 = make_code("0", "1");
  auto keys_0_1_copy = make_code("0", "1");
  auto keys_1_2 = make_code("1", "2");
  EXPECT_FALSE(keys_0_1->structural_equals(*keys_1_2));

  keys_0_1->build_cfg();
  keys_0_1_copy->build_cfg();
  keys_1_2->build_cfg();
  EXPECT_TRUE(keys_0_1->cfg().structural_equals(keys_0_1_copy->cfg()));
  EXPECT_FALSE(keys_0_1->cfg().structural_equals(keys_1_2->cfg()));
}

TEST_F(ControlFlowTest, structural_equals_catch_types) {
  // The catch type lives on the CFG throw edge, not on any instruction. An
  // IllegalArgumentException thrown by bar() is caught by the RuntimeException
  // handler but not by the IllegalStateException one.
  constexpr const char* kCatch = R"(
    (
      (.try_start a)
      (invoke-static () "LFoo;.bar:()V")
      (.try_end a)
      (const v0 0)
      (return v0)
      (.catch (a) "$CATCH_TYPE")
      (const v0 1)
      (return v0)
    )
  )";
  auto make_code = [&](const std::string& catch_type) {
    return assembler::ircode_from_string(
        ir(kCatch, {{"$CATCH_TYPE", catch_type}}));
  };
  auto ise = make_code("Ljava/lang/IllegalStateException;");
  auto ise_copy = make_code("Ljava/lang/IllegalStateException;");
  auto rte = make_code("Ljava/lang/RuntimeException;");
  EXPECT_FALSE(ise->structural_equals(*rte));

  ise->build_cfg();
  ise_copy->build_cfg();
  rte->build_cfg();
  EXPECT_TRUE(ise->cfg().structural_equals(ise_copy->cfg()));
  EXPECT_FALSE(ise->cfg().structural_equals(rte->cfg()));
}

TEST_F(ControlFlowTest, deep_copy2) {

  auto code = assembler::ircode_from_string(R"(
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
)");

  code->build_cfg();
  auto& orig = code->cfg();

  cfg::ControlFlowGraph copy;
  orig.deep_copy(&copy);
  EXPECT_TRUE(orig.structural_equals(copy));
  auto orig_list = orig.linearize();
  auto copy_list = copy.linearize();

  EXPECT_TRUE(orig_list->structural_equals(*copy_list, m_equal));
}

TEST_F(ControlFlowTest, deep_copy3) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 10)

      (:loop)
      (if-eqz v0 :end)

      (move v2 v0)
      (if-nez v2 :true)
      (const v2 0)
      (goto :inner_end)

      (:true)
      (const v2 -1)

      (:inner_end)
      (move v1 v2)

      (add-int v0 v0 v1)
      (goto :loop)

      (:end)
      (return-void)
    )
)");

  code->build_cfg();
  auto& orig = code->cfg();

  cfg::ControlFlowGraph copy;
  orig.deep_copy(&copy);
  EXPECT_TRUE(orig.structural_equals(copy));
  auto orig_list = orig.linearize();
  auto copy_list = copy.linearize();

  EXPECT_TRUE(orig_list->structural_equals(*copy_list, m_equal));
}

TEST_F(ControlFlowTest, deep_copy_into_existing_cfg) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :thr)
      (return-void)
      (:thr)
      (throw v0)
    )
)");

  auto copy_code = assembler::ircode_from_string(R"(
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
)");

  code->build_cfg();
  auto& orig = code->cfg();

  copy_code->build_cfg();
  auto& copy = copy_code->cfg();

  orig.deep_copy(&copy);

  code->clear_cfg();
  copy_code->clear_cfg();

  EXPECT_CODE_EQ(code.get(), copy_code.get());
}

TEST_F(ControlFlowTest, line_numbers) {

  [[maybe_unused]] DexMethod* m =
      DexMethod::make_method("LFoo;.m:()V")
          ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (if-eqz v0 :true)

      (const v1 1)
      (goto :exit)

      (:true)
      (const v2 2)

      (:exit)
      (.pos "LFoo;.m:()V" "Foo.java" 2)
      (return-void)
    )
  )");

  code->build_cfg();
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (.pos "LFoo;.m:()V" "Foo.java" 2)
      (return-void)

      (:true)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (const v2 2)
      (goto :exit)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, simple_push_back) {
  ControlFlowGraph cfg{};
  Block* entry = cfg.create_block();
  cfg.set_entry_block(entry);
  entry->push_back(new IRInstruction(OPCODE_RETURN_VOID));
  cfg.sanity_check();
  for (Block* b : cfg.blocks()) {
    for (const auto& mie : ir_list::InstructionIterable(*b)) {
      always_assert(mie.insn->opcode() == OPCODE_RETURN_VOID);
    }
  }
}

TEST_F(ControlFlowTest, simple_push_back_it) {
  ControlFlowGraph cfg{};
  Block* entry = cfg.create_block();
  cfg.set_entry_block(entry);

  std::deque<IRInstruction*> to_insert;
  for (int i = 0; i < 5; i++) {
    auto* insn = new IRInstruction(OPCODE_CONST);
    insn->set_literal(i);
    insn->set_dest(cfg.allocate_temp());
    to_insert.push_back(insn);
  }
  entry->push_back(to_insert.begin(), to_insert.end());
  cfg.sanity_check();
  for (Block* b : cfg.blocks()) {
    for (const auto& mie : ir_list::InstructionIterable(*b)) {
      always_assert(mie.insn->opcode() == OPCODE_CONST);
    }
  }
}

TEST_F(ControlFlowTest, simple_push_front) {
  ControlFlowGraph cfg{};
  Block* entry = cfg.create_block();
  cfg.set_entry_block(entry);
  entry->push_front(new IRInstruction(OPCODE_RETURN_VOID));
  cfg.sanity_check();
  for (Block* b : cfg.blocks()) {
    for (const auto& mie : ir_list::InstructionIterable(*b)) {
      always_assert(mie.insn->opcode() == OPCODE_RETURN_VOID);
    }
  }
}

TEST_F(ControlFlowTest, simple_push_front_it) {
  ControlFlowGraph cfg{};
  Block* entry = cfg.create_block();
  cfg.set_entry_block(entry);

  std::deque<IRInstruction*> to_insert;
  for (int i = 0; i < 5; i++) {
    auto* insn = new IRInstruction(OPCODE_CONST);
    insn->set_literal(i);
    insn->set_dest(cfg.allocate_temp());
    to_insert.push_back(insn);
  }
  entry->push_front(to_insert.begin(), to_insert.end());
  cfg.sanity_check();
  for (Block* b : cfg.blocks()) {
    for (const auto& mie : ir_list::InstructionIterable(*b)) {
      always_assert(mie.insn->opcode() == OPCODE_CONST);
    }
  }
}

TEST_F(ControlFlowTest, insertion) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (goto :exit)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  IRInstruction add{OPCODE_ADD_INT_LIT};
  add.set_literal(1);
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_const(insn->opcode())) {
      auto* new_insn = new IRInstruction(add);
      new_insn->set_src(0, insn->dest());
      new_insn->set_dest(insn->dest());
      cfg.insert_after(it, new_insn);
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (add-int/lit v0 v0 1)
      (if-eqz v0 :true)

      (const v1 1)
      (add-int/lit v1 v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (add-int/lit v2 v2 1)
      (goto :exit)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, insertion_it) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (goto :exit)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  IRInstruction add{OPCODE_ADD_INT_LIT};
  add.set_literal(1);
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_const(insn->opcode())) {
      auto* new_insn = new IRInstruction(add);
      new_insn->set_src(0, insn->dest());
      new_insn->set_dest(insn->dest());

      std::vector<IRInstruction*> to_add{new IRInstruction(*new_insn),
                                         new IRInstruction(*new_insn)};

      cfg.insert_after(it, to_add.begin(), to_add.end());
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (add-int/lit v0 v0 1)
      (add-int/lit v0 v0 1)
      (if-eqz v0 :true)

      (const v1 1)
      (add-int/lit v1 v1 1)
      (add-int/lit v1 v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (add-int/lit v2 v2 1)
      (add-int/lit v2 v2 1)
      (goto :exit)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, insertion_it_var) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (goto :exit)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  IRInstruction add{OPCODE_ADD_INT_LIT};
  add.set_literal(1);
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_const(insn->opcode())) {
      auto* new_insn = new IRInstruction(add);
      new_insn->set_src(0, insn->dest());
      new_insn->set_dest(insn->dest());

      std::vector<cfg::ControlFlowGraph::InsertVariant> to_add;
      to_add.emplace_back(new IRInstruction(*new_insn));

      const auto* mref = DexString::make_string("LFoo;.bar:()V");
      to_add.emplace_back(std::make_unique<SourceBlock>(mref, 0));
      to_add.emplace_back(new IRInstruction(*new_insn));

      cfg.insert_after(it, to_add.begin(), to_add.end());
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (add-int/lit v0 v0 1)
      (.src_block "LFoo;.bar:()V" 0)
      (add-int/lit v0 v0 1)
      (if-eqz v0 :true)

      (const v1 1)
      (add-int/lit v1 v1 1)
      (.src_block "LFoo;.bar:()V" 0)
      (add-int/lit v1 v1 1)

      (:exit)
      (return-void)

      (:true)
      (const v2 2)
      (add-int/lit v2 v2 1)
      (.src_block "LFoo;.bar:()V" 0)
      (add-int/lit v2 v2 1)
      (goto :exit)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, insertion_after_may_throw) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)

      (.try_start foo)
      (aput-object v0 v1 v2)
      (return v1)
      (.try_end foo)

      (.catch (foo))
      (const v1 0)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_an_aput(insn->opcode())) {
      auto* new_insn = new IRInstruction(*insn);
      cfg.insert_after(it, new_insn);
      break;
    }
  }
  code->clear_cfg();
  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)

      (.try_start foo)
      (aput-object v0 v1 v2)
      (aput-object v0 v1 v2)
      (return v1)
      (.try_end foo)

      (.catch (foo))
      (const v1 0)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, insertion_after_may_throw_with_move_result) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)

      (.try_start foo)
      (aput-object v0 v1 v2)
      (return v1)
      (.try_end foo)

      (.catch (foo))
      (const v1 0)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_an_aput(insn->opcode())) {
      std::vector<IRInstruction*> new_insns;
      auto* new_insn = new IRInstruction(OPCODE_DIV_INT);
      new_insn->set_srcs_size(2);
      new_insn->set_src(0, 2);
      new_insn->set_src(1, 2);
      new_insns.push_back(new_insn);
      new_insn = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      new_insn->set_dest(2);
      new_insns.push_back(new_insn);
      cfg.insert_after(it, new_insns);
      break;
    }
  }
  code->clear_cfg();
  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)

      (.try_start foo)
      (aput-object v0 v1 v2)
      (div-int v2 v2)
      (move-result-pseudo v2)
      (return v1)
      (.try_end foo)

      (.catch (foo))
      (const v1 0)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, insertion_with_source_blocks) {
  auto code = assembler::ircode_from_string(R"(
    (
      (:main)
      (.src_block "LFoo;.bar:()V" 1 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (.try_start foo)
      (.src_block "LFoo;.bar:()V" 2 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (aput-object v0 v1 v2)
      (goto :return)
      (.try_end foo)

      (:return)
      (return v1)

      (:catch)
      (.catch (foo))
      (.src_block "LFoo;.bar:()V" 3 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (const v1 0)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_an_aput(insn->opcode())) {
      std::vector<IRInstruction*> new_insns;
      auto* new_insn = new IRInstruction(OPCODE_DIV_INT);
      new_insn->set_srcs_size(2);
      new_insn->set_src(0, 2);
      new_insn->set_src(1, 2);
      new_insns.push_back(new_insn);
      new_insn = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      new_insn->set_dest(2);
      new_insns.push_back(new_insn);
      cfg.insert_after(it, new_insns);
      break;
    }
  }
  code->clear_cfg();
  code->build_cfg();
  auto& cfg2 = code->cfg();
  for (auto* block : cfg2.blocks()) {
    always_assert(source_blocks::has_source_blocks(block));
  }
}

TEST_F(ControlFlowTest, insertion_with_source_blocks_middle) {
  auto code = assembler::ircode_from_string(R"(
    (
      (:main)
      (.src_block "LFoo;.bar:()V" 1 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (.try_start foo)
      (.src_block "LFoo;.bar:()V" 2 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (add-int v1 v1 v1)
      (aput-object v0 v1 v2)
      (goto :return)
      (.try_end foo)

      (:return)
      (.src_block "LFoo;.bar:()V" 4 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (return v1)

      (:catch)
      (.catch (foo))
      (.src_block "LFoo;.bar:()V" 3 (1.0 1.0) (1.0 1.0) (1.0 1.0))
      (const v1 0)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (insn->opcode() == OPCODE_ADD_INT) {
      std::vector<IRInstruction*> new_insns;
      auto* new_insn = new IRInstruction(OPCODE_DIV_INT);
      new_insn->set_srcs_size(2);
      new_insn->set_src(0, 2);
      new_insn->set_src(1, 2);
      new_insns.push_back(new_insn);
      new_insn = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      new_insn->set_dest(2);
      new_insns.push_back(new_insn);
      cfg.insert_after(it, new_insns);
      break;
    }
  }
  code->clear_cfg();
  code->build_cfg();
  auto& cfg2 = code->cfg();
  for (auto* block : cfg2.blocks()) {
    always_assert(source_blocks::has_source_blocks(block));
  }
}

TEST_F(ControlFlowTest, add_sget) {

  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (sput v1 "LFoo;.field:I")
      (return-void)

      (:true)
      (const v1 2)
      (goto :exit)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_conditional_branch(insn->opcode())) {
      IRInstruction* sget = new IRInstruction(OPCODE_SGET);
      sget->set_field(DexField::make_field("LFoo;.field:I"));
      IRInstruction* move_res = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      move_res->set_dest(insn->src(0));
      cfg.insert_before(it, {sget, move_res});
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (sget "LFoo;.field:I")
      (move-result-pseudo v0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (sput v1 "LFoo;.field:I")
      (return-void)

      (:true)
      (const v1 2)
      (goto :exit)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, add_return) {

  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (sput v1 "LFoo;.field:I")
      (return-void)

      (:true)
      (const v1 2)
      (goto :exit)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_conditional_branch(insn->opcode())) {
      auto* ret = new IRInstruction(OPCODE_RETURN_VOID);
      cfg.insert_before(it, ret);
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, add_throw) {

  auto code = assembler::ircode_from_string(R"(
    (
      (.try_start foo)
      (const v0 0)
      (sget "LFoo;.field:I")
      (move-result-pseudo v0)
      (if-eqz v0 :true)

      (const v1 1)

      (:exit)
      (return v1)

      (:true)
      (const v1 2)
      (return v1)

      (.try_end foo)

      (.catch (foo))
      (const v1 3)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_an_sget(insn->opcode())) {
      auto* thr = new IRInstruction(OPCODE_THROW);
      cfg.insert_before(it, thr);
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (.try_start foo)
      (const v0 0)
      (throw v0)
      (.try_end foo)

      (.catch (foo))
      (const v1 3)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, add_branch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto* entry_block = cfg.entry_block();
  auto load_param =
      entry_block->to_cfg_instruction_iterator(*entry_block->begin());
  cfg.split_block(load_param);
  IRInstruction ret(OPCODE_RETURN);
  ret.set_src(0, 0);
  auto* fls = cfg.create_block();
  {
    auto* load_zero = new IRInstruction(OPCODE_CONST);
    load_zero->set_dest(0);
    load_zero->set_literal(0);
    fls->push_back({load_zero, new IRInstruction(ret)});
  }
  auto* tru = cfg.create_block();
  {
    auto* load_one = new IRInstruction(OPCODE_CONST);
    load_one->set_dest(0);
    load_one->set_literal(1);
    tru->push_back({load_one, new IRInstruction(ret)});
  }
  auto* if_eqz = new IRInstruction(OPCODE_IF_EQZ);
  if_eqz->set_src(0, 0);
  cfg.create_branch(entry_block, if_eqz, fls, tru);
  cfg.recompute_registers_size();
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :tru)

      (const v0 0)
      (return v0)

      (:tru)
      (const v0 1)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

/**
 * Construct new code but keeping param loading instructions.
 */
TEST_F(ControlFlowTest, test_first_non_param_loading_insn) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 1)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto* entry_block = cfg.entry_block();

  auto it = entry_block->get_first_non_param_loading_insn();
  auto non_param = entry_block->to_cfg_instruction_iterator(it);
  entry_block->insert_before(non_param, dasm(OPCODE_RETURN, {0_v}));
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

Block* create_ret_const_block(ControlFlowGraph& cfg, uint64_t lit) {
  auto* b = cfg.create_block();
  auto* c = new IRInstruction(OPCODE_CONST);
  auto reg = cfg.allocate_temp();
  c->set_dest(reg);
  c->set_literal(lit);
  auto* r = new IRInstruction(OPCODE_RETURN);
  r->set_src(0, reg);
  b->push_back({c, r});
  return b;
}

TEST_F(ControlFlowTest, add_branch_null_goto_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :tru)

      (const v1 10)
      (goto :exit)

      (:tru)
      (const v1 20)

      (:exit)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto* new_block = create_ret_const_block(cfg, 30);

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST && it->insn->get_literal() == 10) {
      auto* br = new IRInstruction(OPCODE_IF_LEZ);
      br->set_src(0, 0);
      cfg.create_branch(it.block(), br, nullptr, new_block);
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :tru)

      (const v1 10)
      (if-lez v0 :new_exit)

      (:exit)
      (return v1)

      (:tru)
      (const v1 20)
      (goto :exit)

      (:new_exit)
      (const v2 30)
      (return v2)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, add_branch_redirect_goto_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :tru)

      (const v1 10)
      (goto :exit)

      (:tru)
      (const v1 20)

      (:exit)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto* thirty = create_ret_const_block(cfg, 30);
  auto* forty = create_ret_const_block(cfg, 40);

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST && it->insn->get_literal() == 10) {
      auto* br = new IRInstruction(OPCODE_IF_LEZ);
      br->set_src(0, 0);
      cfg.create_branch(it.block(), br, thirty, forty);
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :tru)

      (const v1 10)
      (if-lez v0 :forty)

      (const v2 30)
      (return v2)

      (:forty)
      (const v3 40)
      (return v3)

      (:tru)
      (const v1 20)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, add_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto* ten = create_ret_const_block(cfg, 10);
  auto* twenty = create_ret_const_block(cfg, 20);
  auto* thirty = create_ret_const_block(cfg, 30);
  auto* forty = create_ret_const_block(cfg, 40);

  auto* entry = cfg.entry_block();
  auto* exit_block =
      cfg.split_block(entry->to_cfg_instruction_iterator(*entry->begin()));
  auto* sw = new IRInstruction(OPCODE_SWITCH);
  sw->set_src(0, 0);
  cfg.create_branch(cfg.entry_block(),
                    sw,
                    exit_block,
                    {{0, ten}, {1, twenty}, {2, thirty}, {3, forty}});
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0 (:ten :twenty :thirty :forty))
      (return v0)

      (:forty 3)
      (const v4 40)
      (return v4)

      (:thirty 2)
      (const v3 30)
      (return v3)

      (:twenty 1)
      (const v2 20)
      (return v2)

      (:ten 0)
      (const v1 10)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_insn_basic) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v0 0)
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST) {
      auto* new_const = new IRInstruction(OPCODE_CONST);
      new_const->set_literal(1);
      new_const->set_dest(0);
      auto* new_const2 = new IRInstruction(OPCODE_CONST);
      new_const2->set_literal(2);
      new_const2->set_dest(0);
      cfg.replace_insns(it, {new_const, new_const2});
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v0 1)
      (const v0 2)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_insn_may_throw) {

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (const v0 0)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST) {
      auto* sget = new IRInstruction(OPCODE_SGET);
      sget->set_field(DexField::make_field("LFoo;.b:I"));
      auto* move_res = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      move_res->set_dest(0);
      cfg.replace_insns(it, {sget, move_res});
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (sget "LFoo;.b:I")
      (move-result-pseudo v0)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_insn_may_throw2) {

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (sput v0 "LFoo;.a:I")
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_SPUT) {
      auto* sget = new IRInstruction(OPCODE_SGET);
      sget->set_field(DexField::make_field("LFoo;.a:I"));
      auto* move_res = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      move_res->set_dest(0);
      cfg.replace_insns(it, {sget, move_res});
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_insn_may_throw3) {

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_SGET) {
      auto* sget = new IRInstruction(OPCODE_SGET);
      sget->set_field(DexField::make_field("LFoo;.b:I"));
      auto* move_res = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
      auto temp = cfg.allocate_temp();
      move_res->set_dest(temp);

      auto* sput = new IRInstruction(OPCODE_SPUT);
      sput->set_field(DexField::make_field("LFoo;.a:I"));
      sput->set_src(0, temp);
      cfg.replace_insns(it, {sget, move_res, sput});
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.try_start a)
      (sget "LFoo;.b:I")
      (move-result-pseudo v1)
      (sput v1 "LFoo;.a:I")
      (return v0)
      (.try_end a)

      (.catch (a))
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_insn_invoke) {

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (invoke-virtual (v0) "LFoo;.bar:()I")
      (move-result v0)
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      cfg.replace_insn(it, dasm(OPCODE_NOP));
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (nop)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, replace_if_with_return) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-gtz v0 :tru)

      (const v1 1)
      (return v1)

      (:tru)
      (const v2 2)
      (return v2)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (opcode::is_a_conditional_branch(it->insn->opcode())) {
      auto* ret = new IRInstruction(OPCODE_RETURN);
      ret->set_src(0, 0);
      cfg.replace_insn(it, ret);
      break;
    }
  }
  code->clear_cfg();

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(expected.get(), code.get());
}

TEST_F(ControlFlowTest, split_block) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)
      (return v1)

      (:true)
      (const v1 2)
      (add-int v1 v1 v1)
      (return v1)
    )
  )");
  code->build_cfg();

  auto& cfg = code->cfg();

  EXPECT_EQ(cfg.num_blocks(), 3);

  // Simple split
  Block* s_block = cfg.blocks().back();
  EXPECT_EQ(s_block->succs().size(), 0);

  cfg.split_block(s_block->to_cfg_instruction_iterator(*s_block->begin()));

  EXPECT_EQ(cfg.num_blocks(), 4);
  EXPECT_EQ(s_block->succs().size(), 1);
  EXPECT_EQ(s_block->preds().size(), 1);
  EXPECT_EQ(s_block->preds()[0]->src()->begin()->insn->opcode(), OPCODE_CONST);

  // Test split at the end
  s_block = cfg.blocks().back();
  cfg.split_block(
      s_block->to_cfg_instruction_iterator(*std::prev(s_block->end())));
  EXPECT_EQ(cfg.num_blocks(), 5);

  EXPECT_EQ(s_block->succs().size(), 1);
  EXPECT_EQ(s_block->begin()->insn->opcode(), OPCODE_ADD_INT);
  EXPECT_EQ(std::prev(s_block->end())->insn->opcode(), OPCODE_RETURN);

  // Test split_block() throws an instruction when splitting past the last
  // instruction
  EXPECT_THROW(
      cfg.split_block(s_block->to_cfg_instruction_iterator(*s_block->end())),
      RedexException);
}

TEST_F(ControlFlowTest, block_begins_with) {
  auto full_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)
      (const-string "one")
      (move-result-pseudo v0)
      (return v0)
    )
  )");

  auto partial_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)
      (const-string "one")
      (move-result-pseudo v0)
    )
  )");

  full_code->build_cfg();
  partial_code->build_cfg();

  auto& full_cfg = full_code->cfg();
  auto& partial_cfg = partial_code->cfg();

  EXPECT_TRUE(full_cfg.entry_block()->begins_with(partial_cfg.entry_block()));
  EXPECT_FALSE(partial_cfg.entry_block()->begins_with(full_cfg.entry_block()));
}

TEST_F(ControlFlowTest, get_param_instructions_basic) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const-string "one")
      (move-result-pseudo v0)
      (return v0)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();

  MethodItemEntry* param_insn = &*cfg.entry_block()->begin();
  auto param_insns_range = cfg.get_param_instructions();
  EXPECT_FALSE(param_insns_range.empty());
  EXPECT_EQ(&*param_insns_range.begin(), param_insn);
  EXPECT_EQ(&*param_insns_range.end(), &*std::next(cfg.entry_block()->begin()));
}

TEST_F(ControlFlowTest, get_param_instructions_empty) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.dbg DBG_SET_PROLOGUE_END)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();

  EXPECT_TRUE(cfg.get_param_instructions().empty());
}

TEST_F(ControlFlowTest, no_crash_on_remove_insn) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (invoke-virtual (v0) "LFoo;.bar:()V")
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  auto it = InstructionIterator{cfg, /*is_begin=*/true};
  for (; !it.is_end(); ++it) {
    if (it->insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      break;
    }
  }
  ASSERT_FALSE(it.is_end());

  cfg.remove_insn(it); // Should not crash.
}

TEST_F(ControlFlowTest, move_result_chain) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)

      (.try_start foo)
      (add-int v0 v0 v1)
      (invoke-static (v0) "LCls;.foo:(I)I")

      (move-result v1)
      (return v1)
      (.try_end foo)

      (.catch (foo))
      (const v1 0)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();

  // Find the add, break that block.
  {
    auto ii = cfg::InstructionIterable(cfg);
    auto add_it = std::find_if(ii.begin(), ii.end(), [](const auto& mie) {
      return mie.insn->opcode() == OPCODE_ADD_INT;
    });
    ASSERT_FALSE(add_it.is_end());

    cfg.split_block(add_it);
  }

  code->clear_cfg();

  // Ensure that the move-result is in the right location.
  auto invoke_it =
      std::find_if(code->begin(), code->end(), [](const auto& mie) {
        return mie.type == MFLOW_OPCODE &&
               mie.insn->opcode() == OPCODE_INVOKE_STATIC;
      });
  ASSERT_TRUE(invoke_it != code->end()) << show(code);
  auto next_it = std::next(invoke_it);
  ASSERT_TRUE(next_it != code->end()) << show(code);
  ASSERT_EQ(next_it->type, MFLOW_OPCODE) << show(code);
  EXPECT_EQ(next_it->insn->opcode(), OPCODE_MOVE_RESULT) << show(code);
}

namespace {

std::string sanitize(const std::string& s) {
  return std::regex_replace(
      std::regex_replace(std::regex_replace(s, std::regex("0x[0-9a-f]+"), ""),
                         std::regex(R"((^|\n)\[\] +)"),
                         "$1"),
      std::regex(R"( +($|\n))"), "$1");
}

} // namespace

// Chains are created in block order. Ensure that chains are created correctly
// when the entry block is not first block on destruction.
TEST_F(ControlFlowTest, entry_not_first_block_order_first) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->set_entry_block(cfg->blocks().at(2));
    cfg->simplify();
    EXPECT_EQ(cfg->order().at(0), cfg->entry_block()) << show(*cfg);
  }
}

TEST_F(ControlFlowTest, entry_not_first_block_order_first_linearization) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  EXPECT_EQ(sanitize(show(code.get())), R"(TARGET: SIMPLE
OPCODE: IF_EQZ v0
OPCODE: RETURN_VOID
TARGET: SIMPLE
OPCODE: ADD_INT_LIT v0, v0, 1
OPCODE: GOTO
)");
}

TEST_F(ControlFlowTest, empty_block_move_pos) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  EXPECT_EQ(sanitize(show(code.get())), R"(TARGET: SIMPLE
POSITION: LFoo;.m:()V(Foo.java:1)
OPCODE: IF_EQZ v0
OPCODE: RETURN_VOID
TARGET: SIMPLE
OPCODE: ADD_INT_LIT v0, v0, 1
OPCODE: GOTO
)");
}

TEST_F(ControlFlowTest, empty_block_do_not_move_into_block_with_pos) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (goto :next)

      (:next)
      (.pos "LFoo;.m:()V" "Foo.java" 2)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  EXPECT_EQ(sanitize(show(code.get())), R"(POSITION: LFoo;.m:()V(Foo.java:2)
OPCODE: RETURN_VOID
)");
}

TEST_F(ControlFlowTest, empty_block_do_not_move_into_block_with_pos_complex) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (.pos "LFoo;.m:()V" "Foo.java" 2)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  // TODO: This is really a weird case. It is not clear why this is shifted
  //       there.

  EXPECT_EQ(sanitize(show(code.get())), R"(TARGET: SIMPLE
POSITION: LFoo;.m:()V(Foo.java:2)
OPCODE: IF_EQZ v0
OPCODE: RETURN_VOID
TARGET: SIMPLE
POSITION: LFoo;.m:()V(Foo.java:1)
OPCODE: ADD_INT_LIT v0, v0, 1
OPCODE: GOTO
)");
}

TEST_F(ControlFlowTest, empty_block_not_move_source_blocks_complex) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.src_block "LFoo;.m:()V" 1)
      (const v0 0)
      (.src_block "LFoo;.m:()V" 2)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (.src_block "LFoo;.m:()V" 3)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  EXPECT_EQ(sanitize(show(code.get())), R"(TARGET: SIMPLE
SOURCE-BLOCKS: LFoo;.m:()V@3()
OPCODE: IF_EQZ v0
OPCODE: RETURN_VOID
TARGET: SIMPLE
OPCODE: ADD_INT_LIT v0, v0, 1
OPCODE: GOTO
)");
}

// Remarks follow the source-block policy in remove_empty_blocks: when the
// emptied block's successor is reached only via it, the remarks move onto the
// successor's head, preserving their original order.
TEST_F(ControlFlowTest, empty_block_moves_remark_to_single_pred_succ) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (.remark "P" "s" 1)
      (.remark "P" "s" 2)
      (goto :next)

      (:next)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  std::vector<int64_t> remarks;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_REMARK) {
      remarks.push_back(mie.remark->val_int);
    }
  }
  // Both remarks survive on the merged block, in original order (not reversed).
  EXPECT_EQ(remarks, (std::vector<int64_t>{1, 2}));
}

// The drop-guard mirror of empty_block_not_move_source_blocks_complex: the loop
// block has two predecessors, so the emptied entry block's remarks (1, 2) must
// be dropped rather than mis-attributed; only the loop block's own remark (3)
// remains.
TEST_F(ControlFlowTest, empty_block_does_not_move_remark_into_multi_pred_succ) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.remark "P" "s" 1)
      (const v0 0)
      (.remark "P" "s" 2)
      (goto :loop)

      (:true)
      (add-int/lit v0 v0 1)

      (:loop)
      (.remark "P" "s" 3)
      (if-eqz v0 :true)

      (:exit)
      (return-void)
    )
  )");

  {
    ScopedCFG cfg(code.get());
    cfg->entry_block()->remove_insn(cfg->entry_block()->get_first_insn());
  }

  std::vector<int64_t> remarks;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_REMARK) {
      remarks.push_back(mie.remark->val_int);
    }
  }
  EXPECT_EQ(remarks, (std::vector<int64_t>{3}));
}

TEST_F(ControlFlowTest, non_cfg_case_keys) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:a :b))

      (:exit)
      (return-void)

      (:a 0)
      (const v0 0)
      (goto :exit)

      (:b 1)
      (const v1 1)
      (goto :exit)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  std::vector<int32_t> case_keys;
  auto* switch_block = cfg.entry_block();
  auto switch_insn = switch_block->get_first_insn();
  EXPECT_NE(switch_insn, switch_block->end());
  EXPECT_EQ(switch_insn->insn->opcode(), OPCODE_SWITCH);
  for (auto* edge : switch_block->succs()) {
    if (edge->type() == cfg::EDGE_GOTO) {
      continue;
    }
    EXPECT_EQ((uint8_t)edge->type(), (uint8_t)cfg::EDGE_BRANCH);
    EXPECT_TRUE(edge->case_key());
    case_keys.push_back(*edge->case_key());
  }
  code->clear_cfg();
  EXPECT_EQ(case_keys.size(), 2);
  std::sort(case_keys.begin(), case_keys.end());
  EXPECT_EQ(case_keys.at(0), 0);
  EXPECT_EQ(case_keys.at(1), 1);
}

TEST_F(ControlFlowTest, insert_block_if) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :true)

      (const v1 1)
      (return v1)

      (:true)
      (const v1 2)
      (add-int v1 v1 v1)
      (return v1)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_EQ(cfg.num_blocks(), 3);

  auto* nb0 = cfg.create_block();
  auto* nb1 = cfg.create_block();

  // Now the cfg should be:
  // entry_block --(GOTO)--> goto_block
  //      |
  //      ----(BRANCH) --> branch_block
  auto* entry_block = cfg.entry_block();
  EXPECT_TRUE(entry_block->succs().size() == 2);
  auto* goto_block = entry_block->goes_to();
  EXPECT_TRUE(goto_block);
  auto* branch_edge = cfg.get_succ_edge_of_type(entry_block, cfg::EDGE_BRANCH);
  EXPECT_TRUE(branch_edge);
  auto* branch_block = branch_edge->target();

  cfg.insert_block(entry_block, goto_block, nb0);
  cfg.insert_block(entry_block, branch_block, nb1);

  // Now the cfg should be:
  // entry_block --(GOTO)--> nb0 --(GOTO)-->goto_block
  //      |
  //      ----(BRANCH) --> nb1 -- (GOTO) --> branch_block
  EXPECT_EQ(cfg.num_blocks(), 5);
  EXPECT_TRUE(entry_block->succs().size() == 2);
  EXPECT_TRUE(entry_block->goes_to() != nullptr &&
              entry_block->goes_to() == nb0);
  EXPECT_TRUE(nb0->goes_to() != nullptr && nb0->goes_to() == goto_block);

  auto* new_branch_edge =
      cfg.get_succ_edge_of_type(entry_block, cfg::EDGE_BRANCH);
  EXPECT_TRUE(new_branch_edge);
  EXPECT_TRUE(new_branch_edge->target() == nb1);
  EXPECT_TRUE(nb1->goes_to() != nullptr && nb1->goes_to() == branch_block);
}

TEST_F(ControlFlowTest, insert_block_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (switch v0 (:b :c :d))

     (const v1 100)
     (return v1)

     (:b 1)
     (:c 2)
     (:d 3)
     (const v1 300)
     (return v1)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_EQ(cfg.num_blocks(), 3);

  // Now the cfg should be:
  // switch_block --(GOTO)--> default_block
  //    |   |  |
  //    |   |   ----(BRANCH case_key 1) --> branch_block
  //    |   --------(BRANCH case_key 2) -------^  ^
  //    ------------(BRANCH case_key 3)-----------|
  auto* switch_block = cfg.entry_block();
  auto* goto_edge = cfg.get_succ_edge_of_type(switch_block, cfg::EDGE_GOTO);
  EXPECT_TRUE(goto_edge);
  auto branch_edges =
      cfg.get_succ_edges_of_type(switch_block, cfg::EDGE_BRANCH);
  EXPECT_EQ(branch_edges.size(), 3);
  auto* branch_block = branch_edges[0]->target();
  EXPECT_TRUE(branch_block);
  EXPECT_TRUE(branch_edges[1]->target() == branch_block &&
              branch_edges[2]->target() == branch_block);

  auto* nb0 = cfg.create_block();
  cfg.insert_block(switch_block, branch_block, nb0);

  // After insertion the cfg should be:
  // switch_block --(GOTO)--> default_block
  //    |   |  |
  //    |   |   ----(BRANCH case_key 1) -->       nb0 --(GOTO)-->branch_block
  //    |   --------(BRANCH case_key 2) -------^  ^
  //    ------------(BRANCH case_key 3)-----------|
  EXPECT_EQ(cfg.num_blocks(), 4);
  auto new_branch_edges =
      cfg.get_succ_edges_of_type(switch_block, cfg::EDGE_BRANCH);
  EXPECT_EQ(new_branch_edges.size(), 3);
  EXPECT_TRUE(branch_edges[0]->target() == nb0);
  EXPECT_TRUE(branch_edges[1]->target() == nb0);
  EXPECT_TRUE(branch_edges[2]->target() == nb0);
  EXPECT_TRUE(nb0->goes_to() != nullptr && nb0->goes_to() == branch_block);
}

TEST_F(ControlFlowTest, blockUnconditionallyThrowsDirectThrow) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/RuntimeException;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/RuntimeException;.<init>:()V")
      (throw v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_TRUE(cfg::block_eventually_throws(cfg.entry_block()))
      << "Entry block that directly throws should be flagged";
}

TEST_F(ControlFlowTest, blockUnconditionallyThrowsReturnNotFlagged) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (return v0)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_FALSE(cfg::block_eventually_throws(cfg.entry_block()))
      << "Entry block that returns should NOT be flagged";
}

TEST_F(ControlFlowTest, blockUnconditionallyThrowsConditionalNotFlagged) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-eqz v0 :throw)
      (const v1 1)
      (return v1)
      (:throw)
      (new-instance "Ljava/lang/RuntimeException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/RuntimeException;.<init>:()V")
      (throw v2)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_FALSE(cfg::block_eventually_throws(cfg.entry_block()))
      << "Entry block with conditional path should NOT be flagged";
}

TEST_F(ControlFlowTest, blockUnconditionallyThrowsInfiniteLoopNotFlagged) {
  auto code = assembler::ircode_from_string(R"(
    (
      (:loop)
      (goto :loop)
    )
  )");
  code->build_cfg();
  auto& cfg = code->cfg();
  EXPECT_FALSE(cfg::block_eventually_throws(cfg.entry_block()))
      << "Infinite loop should NOT be flagged as unconditionally throwing";
}
