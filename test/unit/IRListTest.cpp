/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <utility>
#include <vector>

#include "Debug.h"
#include "DexInstruction.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IRList.h"
#include "IROpcode.h"
#include "RedexTest.h"

class IRListTest : public RedexTest {};

TEST_F(IRListTest, method_item_entry_equality) {
  std::string s_insns = R"(
    (
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)

      (.try_start foo)
      (const v0 0)
      (if-gtz v0 :tru)
      (throw v0)
      (.try_end foo)

      (.catch (foo))
      (const v1 3)
      (return v1)

      (:tru)
      (const v2 2)
      (return v2)

      (return v0)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);
  auto code_clone = assembler::ircode_from_string(s_insns);

  IRList::iterator code_it = code->begin();
  IRList::iterator clone_it = code_clone->begin();

  while (code_it != code->end() && clone_it != code_clone->end()) {
    EXPECT_TRUE(*code_it == *clone_it);

    code_it++;
    clone_it++;
  }

  always_assert(code_it == code->end() && clone_it == code_clone->end());
}

TEST_F(IRListTest, remove_prologue) {
  const auto* const s_insns = R"(
    (
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)
      (const v1 1)
      (return-void)
    )
  )";
  const auto* const expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (return-void)
    )
  )";

  auto code = assembler::ircode_from_string(s_insns);
  auto expected_code = assembler::ircode_from_string(expected_str);

  code->cleanup_debug();

  EXPECT_EQ(assembler::to_string(expected_code.get()),
            assembler::to_string(code.get()));
}

TEST_F(IRListTest, remove_when_register_not_used) {
  const auto* const s_insns = R"(
    (
      (load-param v0)
      (const v1 1)
      (.dbg DBG_END_LOCAL 3)
      (.dbg DBG_RESTART_LOCAL 6)
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);

  const auto* const expected_str = R"(
    (
      (load-param v0)
      (const v1 1)
      (return-void)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);

  code->cleanup_debug();

  EXPECT_EQ(assembler::to_string(expected_code.get()),
            assembler::to_string(code.get()));
}

namespace {

struct Tally {
  uint32_t opcode_code_units{0};
  std::vector<const DexOpcodeData*> payloads;
};

Tally tally_opcodes(const IRCode& code) {
  Tally tally;
  for (const auto& mie : code) {
    if (mie.type != MFLOW_OPCODE) {
      continue;
    }
    tally.opcode_code_units += mie.insn->size();
    if (opcode::is_fill_array_data(mie.insn->opcode())) {
      tally.payloads.push_back(mie.insn->get_data());
    }
  }
  return tally;
}

uint32_t sum_payload_sizes(const Tally& tally) {
  uint32_t sum{0};
  for (const auto* payload : tally.payloads) {
    sum += payload->size();
  }
  return sum;
}

} // namespace

TEST_F(IRListTest, estimate_code_units_fill_array_data) {
  const auto* const s_insns = R"(
    (
      (const v0 3)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (fill-array-data v1 #4 (63 64 65))
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);

  auto tally = tally_opcodes(*code);
  ASSERT_EQ(tally.payloads.size(), 1);

  // 3 elements of 4 bytes = 6 code units of data, plus the 4 header code units
  // (ident, element_width, and the two size words) that DexOpcodeData::size()
  // already accounts for.
  EXPECT_EQ(tally.payloads.at(0)->size(), 10);
  EXPECT_EQ(code->estimate_code_units(),
            tally.opcode_code_units + sum_payload_sizes(tally));

  // Every in-pass caller goes through the CFG, which must agree.
  code->build_cfg();
  EXPECT_EQ(code->estimate_code_units(),
            tally.opcode_code_units + sum_payload_sizes(tally));
}

// The data words are `(bytes + 1) / 2`, so a payload whose elements do not fill
// a whole code unit rounds up.
TEST_F(IRListTest, estimate_code_units_fill_array_data_odd_byte_count) {
  const auto* const s_insns = R"(
    (
      (const v0 3)
      (new-array v0 "[B")
      (move-result-pseudo-object v1)
      (fill-array-data v1 #1 (1 2 3))
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);

  auto tally = tally_opcodes(*code);
  ASSERT_EQ(tally.payloads.size(), 1);

  // 3 elements of 1 byte round up to 2 code units of data, plus 4 header ones.
  EXPECT_EQ(tally.payloads.at(0)->size(), 6);
  EXPECT_EQ(code->estimate_code_units(),
            tally.opcode_code_units + sum_payload_sizes(tally));
}

// Each payload must be counted once and in full; a single-payload test cannot
// tell a per-payload contribution apart from a per-method one.
TEST_F(IRListTest, estimate_code_units_multiple_fill_array_data) {
  const auto* const s_insns = R"(
    (
      (const v0 3)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (fill-array-data v1 #4 (63 64 65))
      (const v2 5)
      (new-array v2 "[S")
      (move-result-pseudo-object v3)
      (fill-array-data v3 #2 (1 2 3 4 5))
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);

  auto tally = tally_opcodes(*code);
  ASSERT_EQ(tally.payloads.size(), 2);

  EXPECT_EQ(tally.payloads.at(0)->size(), 10); // 3 x 4 bytes -> 6 + 4
  EXPECT_EQ(tally.payloads.at(1)->size(), 9); // 5 x 2 bytes -> 5 + 4
  EXPECT_EQ(sum_payload_sizes(tally), 19);
  EXPECT_EQ(code->estimate_code_units(), tally.opcode_code_units + 19);

  code->build_cfg();
  EXPECT_EQ(code->estimate_code_units(), tally.opcode_code_units + 19);
}

TEST_F(IRListTest, keep_valid_regs) {
  const auto* const s_insns = R"(
    (
      (load-param v0)
      (.dbg DBG_START_LOCAL_EXTENDED 4 "will_not_be_removed" "Ljava/lang/Objects;" "sig")
      (const v1 1)
      (.dbg DBG_END_LOCAL 4)
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(s_insns);

  const auto* const expected_str = R"(
    (
      (load-param v0)
      (.dbg DBG_START_LOCAL_EXTENDED 4 "will_not_be_removed" "Ljava/lang/Objects;" "sig")
      (const v1 1)
      (.dbg DBG_END_LOCAL 4)
      (return-void)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);

  code->cleanup_debug();

  EXPECT_EQ(assembler::to_string(expected_code.get()),
            assembler::to_string(code.get()));
}

TEST_F(IRListTest, reversed_instruction_iterable) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.pos "LFoo;.m:()V" "Foo.java" 1)
      (load-param v0)
      (.dbg DBG_SET_PROLOGUE_END)
      (const v1 1)
      (return-void)
      (.pos "LFoo;.m:()V" "Foo.java" 2)
    )
  )");
  const std::vector<IROpcode> expected{OPCODE_RETURN_VOID, OPCODE_CONST,
                                       IOPCODE_LOAD_PARAM};

  std::vector<IROpcode> reversed;
  for (auto& mie : InstructionIterable(*code).reversed()) {
    reversed.push_back(mie.insn->opcode());
  }
  EXPECT_EQ(reversed, expected);

  std::vector<IROpcode> const_reversed;
  for (const auto& mie : InstructionIterable(std::as_const(*code)).reversed()) {
    const_reversed.push_back(mie.insn->opcode());
  }
  EXPECT_EQ(const_reversed, expected);

  IRList empty;
  EXPECT_TRUE(InstructionIterable(empty).reversed().empty());
}
