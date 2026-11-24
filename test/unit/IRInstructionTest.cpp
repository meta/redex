/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <set>

#include "DexAsm.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "InstructionLowering.h"
#include "OpcodeList.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Show.h"
#include "TypeUtil.h"

class IRInstructionTest : public RedexTest {};

// A method's outs_size must cover the argument words of every call it makes,
// method handle calls and call-site calls included, or ART rejects the method.
TEST_F(IRInstructionTest, DynamicInvokesCountTowardOutsSize) {
  auto* invoke_exact = DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)"
      "Ljava/lang/Object;");
  for (auto op : {DOPCODE_INVOKE_POLYMORPHIC, DOPCODE_INVOKE_POLYMORPHIC_RANGE,
                  DOPCODE_INVOKE_CUSTOM, DOPCODE_INVOKE_CUSTOM_RANGE}) {
    bool polymorphic = op == DOPCODE_INVOKE_POLYMORPHIC ||
                       op == DOPCODE_INVOKE_POLYMORPHIC_RANGE;
    bool range = dex_opcode::has_range(op);
    // The range forms pass three longs, the others an int and a long. A method
    // handle call also passes the handle.
    std::string args = range ? "JJJ" : "IJ";
    uint16_t words = (range ? 6 : 3) + (polymorphic ? 1 : 0);
    auto* method = DexMethod::make_method(
                       "LFoo;.call" + std::to_string(op) + ":(" +
                       (polymorphic ? "Ljava/lang/invoke/MethodHandle;" : "") +
                       args + ")V")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    std::string proto = "(" + args + ")V";
    DexInstruction* invoke;
    if (polymorphic) {
      invoke = new DexOpcodeSignaturePolymorphic(op, invoke_exact,
                                                 DexProto::make_proto(proto));
    } else {
      invoke = new DexOpcodeCallSite(op, redex::make_callsite("run", proto));
    }
    if (range) {
      invoke->set_range_base(0);
      invoke->set_range_size(words);
    } else {
      invoke->set_arg_word_count(words);
      for (uint16_t i = 0; i < words; ++i) {
        invoke->set_src(i, i);
      }
    }
    auto code = std::make_unique<DexCode>();
    code->set_registers_size(words);
    code->set_ins_size(words);
    code->set_outs_size(words);
    code->get_instructions().push_back(invoke);
    code->get_instructions().push_back(new DexInstruction(DOPCODE_RETURN_VOID));
    method->set_dex_code(std::move(code));
    method->balloon();
    instruction_lowering::lower(method);
    method->sync();
    EXPECT_EQ(method->get_dex_code()->get_outs_size(), words) << show(op);
  }
}

// for nicer gtest error messages
std::ostream& operator<<(std::ostream& os, const DexInstruction& to_show) {
  return os << show(&to_show);
}

bool is_move(DexOpcode op) {
  return op >= DOPCODE_MOVE && op <= DOPCODE_MOVE_OBJECT_16;
}

TEST_F(IRInstructionTest, RoundTrip) {
  using namespace instruction_lowering::impl;

  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);
  auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(
      ty, str, DexProto::make_proto(ty, DexTypeList::make_type_list({}))));
  method->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  for (auto op : all_dex_opcodes) {
    // XXX we currently aren't testing these opcodes because they change when
    // we do the round-trip conversion. For example, `const v0` gets converted
    // to `const/4 v0`. To prevent these changes from happening, we can set the
    // operands to the largest values that can be encoded for a given opcode.
    if (is_move(op) ||
        (op >= DOPCODE_CONST_4 && op <= DOPCODE_CONST_WIDE_HIGH16) ||
        op == DOPCODE_CONST_STRING_JUMBO) {
      continue;
    }
    // XXX we can test these opcodes if we create a corresponding data payload
    if (op == DOPCODE_FILL_ARRAY_DATA) {
      continue;
    }
    // XXX we eliminate NOPs, so no point testing them. As for opcodes with
    // offsets, they are tricky to test as sync() can change them depending on
    // the size of the offset.
    if (op == DOPCODE_NOP || dex_opcode::has_offset(op)) {
      continue;
    }

    auto* insn = DexInstruction::make_instruction(op);
    // populate the instruction args with non-zero values so we can check
    // if we have copied everything correctly
    if (insn->has_dest()) {
      insn->set_dest(0xf);
    }
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      insn->set_src(i, i + 1);
    }
    if (dex_opcode::has_literal(op)) {
      insn->set_literal(0xface);
    }
    if (dex_opcode::has_range(op)) {
      insn->set_range_base(0xf);
      insn->set_range_size(0xf);
    }
    if (dex_opcode::has_arg_word_count(op)) {
      insn->set_arg_word_count(5);
    }
    if (insn->has_string()) {
      dynamic_cast<DexOpcodeString*>(insn)->set_string(str);
    } else if (insn->has_type()) {
      dynamic_cast<DexOpcodeType*>(insn)->set_type(ty);
    } else if (insn->has_field()) {
      dynamic_cast<DexOpcodeField*>(insn)->set_field(field);
    } else if (insn->has_method() || insn->has_proto() ||
               insn->has_methodhandle() || insn->has_callsite()) {
      // TODO: We can / should test method-, proto-, methodhandle- and
      // callsite-bearing instructions -- just need to generate a method or
      // call site with a proto that matches the number of registers we are
      // passing in, or a proto/methodhandle
      continue;
    }

    method->set_dex_code(std::make_unique<DexCode>());
    method->get_dex_code()->get_instructions().push_back(insn);
    method->get_dex_code()->set_registers_size(0xff);

    // Create a copy of insn because balloon frees the DexInstructions
    auto* copy = insn->clone();
    insn = nullptr;

    method->balloon();
    instruction_lowering::lower(method);
    method->sync();
    EXPECT_EQ(*method->get_dex_code()->get_instructions().at(0), *copy)
        << "at " << show(op);

    delete copy;
  }
}

// An `invoke-custom` reads into IR and lowers back to the same instruction,
// its wide argument included.
TEST_F(IRInstructionTest, InvokeCustomRoundTrip) {
  auto* callsite = redex::make_callsite("run", "(IJ)V");
  auto* method = DexMethod::make_method("LFoo;.roundTrip:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  auto* insn = new DexOpcodeCallSite(DOPCODE_INVOKE_CUSTOM, callsite);
  insn->set_arg_word_count(3);
  insn->set_src(0, 1);
  insn->set_src(1, 2);
  insn->set_src(2, 3);
  method->set_dex_code(std::make_unique<DexCode>());
  method->get_dex_code()->get_instructions().push_back(insn);
  method->get_dex_code()->set_registers_size(0xff);
  std::unique_ptr<DexInstruction> copy(insn->clone());

  method->balloon();
  instruction_lowering::lower(method);
  method->sync();
  EXPECT_EQ(*method->get_dex_code()->get_instructions().at(0), *copy);
}

TEST_F(IRInstructionTest, NormalizeInvoke) {
  using namespace dex_asm;

  auto* method = DexMethod::make_method("LFoo;", "x", "V", {"J", "I", "J"});
  auto* insn =
      dasm(OPCODE_INVOKE_VIRTUAL, method, {1_v, 2_v, 3_v, 4_v, 5_v, 6_v});
  EXPECT_TRUE(needs_range_conversion(insn));

  auto* orig = new IRInstruction(*insn);

  auto norm_res = insn->normalize_registers();
  ASSERT_TRUE(norm_res);
  EXPECT_EQ(*insn, *dasm(OPCODE_INVOKE_VIRTUAL, method, {1_v, 2_v, 4_v, 5_v}));

  insn->denormalize_registers();
  EXPECT_EQ(
      *insn,
      *dasm(OPCODE_INVOKE_VIRTUAL, method, {1_v, 2_v, 3_v, 4_v, 5_v, 6_v}));

  EXPECT_EQ(*insn, *orig);

  delete insn;
  delete orig;
}

/*
 * Helper function to run select and then extract the resulting instruction
 * from the instruction list. The only reason it's a list is that const-cast
 * IRInstructions can expand into two instructions due to select. Everything
 * else is a simple one-to-one instruction mapping, and that's the case that
 * this makes easy to test.
 */
IRInstruction* select_instruction(IRInstruction* insn) {
  DexMethod* method =
      dynamic_cast<DexMethod*>(DexMethod::make_method("Lfoo;", "bar", "V", {}));
  method->make_concrete(ACC_STATIC, false);
  method->set_code(std::make_unique<IRCode>(method, 0));
  auto* code = method->get_code();
  code->push_back(insn);
  instruction_lowering::lower(method);
  return code->begin()->insn;
}

TEST_F(IRInstructionTest, TwoAddr) {
  using namespace dex_asm;

  auto* method =
      dynamic_cast<DexMethod*>(DexMethod::make_method("Lfoo;", "bar", "V", {}));
  method->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  auto do_test = [&](IRInstruction* insn, DexInstruction* expected) {
    method->set_code(std::make_unique<IRCode>(method, 0));
    method->get_code()->push_back(insn);
    instruction_lowering::lower(method);
    EXPECT_EQ(*method->get_code()->begin()->dex_insn, *expected);
  };

  // Check that we recognize IRInstructions that can be converted to 2addr form
  do_test(dasm(OPCODE_ADD_INT, {0_v, 0_v, 1_v}),
          (new DexInstruction(DOPCODE_ADD_INT_2ADDR))
              ->set_src(0, 0)
              ->set_src(1, 1));

  // IRInstructions that have registers beyond 4 bits can't benefit, however
  do_test(dasm(OPCODE_ADD_INT, {17_v, 17_v, 1_v}),
          (new DexInstruction(DOPCODE_ADD_INT))
              ->set_dest(17)
              ->set_src(0, 17)
              ->set_src(1, 1));

  do_test(dasm(OPCODE_ADD_INT, {0_v, 0_v, 17_v}),
          (new DexInstruction(DOPCODE_ADD_INT))
              ->set_dest(0)
              ->set_src(0, 0)
              ->set_src(1, 17));

  // Check that we take advantage of commutativity
  do_test(dasm(OPCODE_ADD_INT, {1_v, 0_v, 1_v}),
          (new DexInstruction(DOPCODE_ADD_INT_2ADDR))
              ->set_src(0, 1)
              ->set_src(1, 0));

  // Check that we don't abuse commutativity if the operators aren't
  // commutative
  do_test(dasm(OPCODE_SUB_INT, {1_v, 0_v, 1_v}),
          (new DexInstruction(DOPCODE_SUB_INT))
              ->set_dest(1)
              ->set_src(0, 0)
              ->set_src(1, 1));

  // check registers beyond 4 bits can't benefit
  do_test(dasm(OPCODE_ADD_INT, {17_v, 1_v, 17_v}),
          (new DexInstruction(DOPCODE_ADD_INT))
              ->set_dest(17)
              ->set_src(0, 1)
              ->set_src(1, 17));
}

TEST_F(IRInstructionTest, SelectCheckCast) {
  using namespace dex_asm;

  DexMethod* method =
      dynamic_cast<DexMethod*>(DexMethod::make_method("Lfoo;", "bar", "V", {}));
  method->make_concrete(ACC_STATIC, false);
  method->set_code(std::make_unique<IRCode>(method, 0));
  auto* code = method->get_code();
  code->push_back(dasm(OPCODE_CHECK_CAST, type::java_lang_Object(), {1_v}));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}));
  instruction_lowering::lower(method);

  // check that we inserted a move opcode before the check-cast
  auto it = code->begin();
  EXPECT_EQ(
      *it->dex_insn,
      *(new DexInstruction(DOPCODE_MOVE_OBJECT))->set_dest(0)->set_src(0, 1));
  ++it;
  EXPECT_EQ(*it->dex_insn,
            *(new DexOpcodeType(DOPCODE_CHECK_CAST, type::java_lang_Object()))
                 ->set_src(0, 0));
}

/*
 * check-cast's single register field is 8 bits wide, so a dest in v16-v255 is
 * encodable; the materializing move just widens to /from16 rather than needing
 * the dest to fit in 4 bits.
 */
TEST_F(IRInstructionTest, SelectCheckCastHighDest) {
  using namespace dex_asm;

  DexMethod* method = dynamic_cast<DexMethod*>(
      DexMethod::make_method("Lfoo;", "high_dest", "V", {}));
  method->make_concrete(ACC_STATIC, false);
  method->set_code(std::make_unique<IRCode>(method, 0));
  auto* code = method->get_code();
  code->push_back(dasm(OPCODE_CHECK_CAST, type::java_lang_Object(), {1_v}));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {200_v}));
  instruction_lowering::lower(method);

  auto it = code->begin();
  EXPECT_EQ(*it->dex_insn,
            *(new DexInstruction(DOPCODE_MOVE_OBJECT_FROM16))
                 ->set_dest(200)
                 ->set_src(0, 1));
  ++it;
  EXPECT_EQ(*it->dex_insn,
            *(new DexOpcodeType(DOPCODE_CHECK_CAST, type::java_lang_Object()))
                 ->set_src(0, 200));
}

TEST_F(IRInstructionTest, MakeCheckCast) {
  using namespace dex_asm;
  auto insns = make_check_cast(type::java_lang_String(), 3);
  ASSERT_EQ(insns.size(), 2);
  EXPECT_EQ(*insns[0],
            *dasm(OPCODE_CHECK_CAST, type::java_lang_String(), {3_v}));
  EXPECT_EQ(*insns[1], *dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {3_v}));
  for (auto* insn : insns) {
    delete insn;
  }
}

TEST_F(IRInstructionTest, SelectMove) {
  using namespace dex_asm;
  using namespace instruction_lowering::impl;

  EXPECT_EQ(DOPCODE_MOVE, select_move_opcode(dasm(OPCODE_MOVE, {0_v, 0_v})));
  EXPECT_EQ(DOPCODE_MOVE_FROM16,
            select_move_opcode(dasm(OPCODE_MOVE, {255_v, 65535_v})));
  EXPECT_EQ(DOPCODE_MOVE_16,
            select_move_opcode(dasm(OPCODE_MOVE, {65535_v, 65535_v})));
  EXPECT_EQ(DOPCODE_MOVE_OBJECT,
            select_move_opcode(dasm(OPCODE_MOVE_OBJECT, {0_v, 0_v})));
  EXPECT_EQ(DOPCODE_MOVE_OBJECT_FROM16,
            select_move_opcode(dasm(OPCODE_MOVE_OBJECT, {255_v, 65535_v})));
  EXPECT_EQ(DOPCODE_MOVE_OBJECT_16,
            select_move_opcode(dasm(OPCODE_MOVE_OBJECT, {65535_v, 65535_v})));
}

TEST_F(IRInstructionTest, SelectConst) {
  using namespace dex_asm;
  using namespace instruction_lowering::impl;

  auto* insn = dasm(OPCODE_CONST, {0_v});
  EXPECT_EQ(DOPCODE_CONST_4, select_const_opcode(insn));

  insn->set_literal(0xf);
  // This has to be const/16 and not const/4 because sign extension will cause
  // const/4 0xf to load the value 0xffffffff into the dest register
  EXPECT_EQ(DOPCODE_CONST_16, select_const_opcode(insn));

  insn->set_literal(static_cast<int64_t>(0xffffffffffffffff));
  // Conversely, this can use const/4 because of sign extension
  EXPECT_EQ(DOPCODE_CONST_4, select_const_opcode(insn));

  insn->set_literal(std::numeric_limits<int16_t>::max());
  EXPECT_EQ(DOPCODE_CONST_16, select_const_opcode(insn));
  insn->set_literal(std::numeric_limits<int16_t>::min());
  EXPECT_EQ(DOPCODE_CONST_16, select_const_opcode(insn));

  insn->set_literal(static_cast<int32_t>(0xffff0000));
  EXPECT_EQ(DOPCODE_CONST_HIGH16, select_const_opcode(insn));

  insn->set_literal(static_cast<int32_t>(0xffff0001));
  EXPECT_EQ(DOPCODE_CONST, select_const_opcode(insn));

  insn->set_literal(static_cast<int64_t>(0xf0ffffffffffffff));
  EXPECT_THROW(select_const_opcode(insn), RedexException);

  delete insn;

  auto* wide_insn = dasm(OPCODE_CONST_WIDE, {0_v});

  EXPECT_EQ(DOPCODE_CONST_WIDE_16, select_const_opcode(wide_insn));

  wide_insn->set_literal(static_cast<int32_t>(0xffff0001));
  EXPECT_EQ(DOPCODE_CONST_WIDE_32, select_const_opcode(wide_insn));

  wide_insn->set_literal(static_cast<int64_t>(0xffff000000000000));
  EXPECT_EQ(DOPCODE_CONST_WIDE_HIGH16, select_const_opcode(wide_insn));

  wide_insn->set_literal(static_cast<int64_t>(0xffff000000000001));
  EXPECT_EQ(DOPCODE_CONST_WIDE, select_const_opcode(wide_insn));

  delete wide_insn;
}

TEST_F(IRInstructionTest, SelectBinopLit) {
  using namespace dex_asm;
  using namespace instruction_lowering::impl;
  const IROpcode ops[] = {
      OPCODE_ADD_INT_LIT,  OPCODE_RSUB_INT_LIT, OPCODE_MUL_INT_LIT,
      OPCODE_DIV_INT_LIT,  OPCODE_REM_INT_LIT,  OPCODE_AND_INT_LIT,
      OPCODE_OR_INT_LIT,   OPCODE_XOR_INT_LIT,  OPCODE_ADD_INT_LIT,
      OPCODE_RSUB_INT_LIT, OPCODE_MUL_INT_LIT,  OPCODE_DIV_INT_LIT,
      OPCODE_REM_INT_LIT,  OPCODE_AND_INT_LIT,  OPCODE_OR_INT_LIT,
      OPCODE_XOR_INT_LIT,  OPCODE_SHL_INT_LIT,  OPCODE_SHR_INT_LIT,
      OPCODE_USHR_INT_LIT};

  const DexOpcode expected_fit8[] = {
      DOPCODE_ADD_INT_LIT8,  DOPCODE_RSUB_INT_LIT8, DOPCODE_MUL_INT_LIT8,
      DOPCODE_DIV_INT_LIT8,  DOPCODE_REM_INT_LIT8,  DOPCODE_AND_INT_LIT8,
      DOPCODE_OR_INT_LIT8,   DOPCODE_XOR_INT_LIT8,  DOPCODE_ADD_INT_LIT8,
      DOPCODE_RSUB_INT_LIT8, DOPCODE_MUL_INT_LIT8,  DOPCODE_DIV_INT_LIT8,
      DOPCODE_REM_INT_LIT8,  DOPCODE_AND_INT_LIT8,  DOPCODE_OR_INT_LIT8,
      DOPCODE_XOR_INT_LIT8,  DOPCODE_SHL_INT_LIT8,  DOPCODE_SHR_INT_LIT8,
      DOPCODE_USHR_INT_LIT8};

  const DexOpcode expected_fit16[] = {
      DOPCODE_ADD_INT_LIT16, DOPCODE_RSUB_INT,      DOPCODE_MUL_INT_LIT16,
      DOPCODE_DIV_INT_LIT16, DOPCODE_REM_INT_LIT16, DOPCODE_AND_INT_LIT16,
      DOPCODE_OR_INT_LIT16,  DOPCODE_XOR_INT_LIT16, DOPCODE_ADD_INT_LIT16,
      DOPCODE_RSUB_INT,      DOPCODE_MUL_INT_LIT16, DOPCODE_DIV_INT_LIT16,
      DOPCODE_REM_INT_LIT16, DOPCODE_AND_INT_LIT16, DOPCODE_OR_INT_LIT16,
      DOPCODE_XOR_INT_LIT16};

  size_t count_inst = sizeof(ops) / sizeof(ops[0]);
  for (int i = 0; i < count_inst; i++) {
    // literal set to default size (0)
    auto* insn = new IRInstruction(ops[i]);
    EXPECT_EQ(expected_fit8[i], select_binop_lit_opcode(insn))
        << "at " << show(ops[i]);

    // literal within 8 bits
    insn->set_literal(0x7f);
    EXPECT_EQ(expected_fit8[i], select_binop_lit_opcode(insn))
        << "at " << show(ops[i]);

    // literal within 16 bits
    insn->set_literal(0x7fff);
    if (ops[i] != OPCODE_SHL_INT_LIT && ops[i] != OPCODE_SHR_INT_LIT &&
        ops[i] != OPCODE_USHR_INT_LIT) {
      EXPECT_EQ(expected_fit16[i], select_binop_lit_opcode(insn))
          << "at " << show(ops[i]);
    }

    // literal > 16 bits
    insn->set_literal(0xffffff);
    EXPECT_THROW(select_binop_lit_opcode(insn), RedexException)
        << "at " << show(ops[i]);

    delete insn;
  }
}

TEST_F(IRInstructionTest, InvokeSourceIsWideBasic) {
  using namespace dex_asm;

  DexMethodRef* m = DexMethod::make_method("Lfoo;", "baz", "V", {"J"});
  IRInstruction* insn = new IRInstruction(OPCODE_INVOKE_STATIC);
  insn->set_srcs_size(1);
  insn->set_src(0, 0);
  insn->set_method(m);

  EXPECT_TRUE(insn->invoke_src_is_wide(0));

  delete insn;
}

TEST_F(IRInstructionTest, InvokeSourceIsWideComplex) {
  IRInstruction* insn = new IRInstruction(OPCODE_INVOKE_VIRTUAL);
  DexMethodRef* m =
      DexMethod::make_method("Lfoo;", "qux", "V", {"I", "J", "I"});
  insn->set_method(m);
  insn->set_srcs_size(4);
  insn->set_src(0, 1);
  insn->set_src(1, 0);
  insn->set_src(2, 2);
  insn->set_src(3, 3);

  EXPECT_FALSE(insn->invoke_src_is_wide(0));
  EXPECT_FALSE(insn->invoke_src_is_wide(1));
  EXPECT_TRUE(insn->invoke_src_is_wide(2));
  EXPECT_FALSE(insn->invoke_src_is_wide(3));

  delete insn;
}

TEST_F(IRInstructionTest, InvokeSourceIsWideComplex2) {
  IRInstruction* insn = new IRInstruction(OPCODE_INVOKE_VIRTUAL);
  DexMethodRef* m =
      DexMethod::make_method("Lfoo;", "qux", "V", {"I", "J", "I", "J"});
  insn->set_method(m);
  insn->set_srcs_size(5);
  insn->set_src(0, 0);
  insn->set_src(1, 1);
  insn->set_src(2, 2);
  insn->set_src(3, 3);
  insn->set_src(4, 4);

  EXPECT_FALSE(insn->invoke_src_is_wide(0));
  EXPECT_FALSE(insn->invoke_src_is_wide(1));
  EXPECT_TRUE(insn->invoke_src_is_wide(2));
  EXPECT_FALSE(insn->invoke_src_is_wide(3));
  EXPECT_TRUE(insn->invoke_src_is_wide(4));

  delete insn;
}

TEST_F(IRInstructionTest, CopyInstructionWithData) {
  IRInstruction* insn = new IRInstruction(OPCODE_FILL_ARRAY_DATA);
  insn->set_src(0, 0);
  std::vector<uint16_t> data(2);
  uint16_t* ptr = data.data();
  ptr[0] = FOPCODE_FILLED_ARRAY; // header
  ptr[1] = 0;
  insn->set_data(std::make_unique<DexOpcodeData>(data));

  auto* copy = new IRInstruction(*insn);

  EXPECT_NE(insn->get_data(), copy->get_data());
  EXPECT_EQ(insn->get_data()->data_size(), copy->get_data()->data_size());
  EXPECT_EQ(insn->get_data()->data_size(), 1);
  EXPECT_EQ(insn->get_data()->data()[0], insn->get_data()->data()[0]);

  delete insn;
  delete copy;
}

TEST_F(IRInstructionTest, ArrayOpcodeForType) {
  const std::vector<std::tuple<const DexType*, IROpcode, IROpcode, IROpcode>>
      cases = {
          {type::_boolean(), OPCODE_AGET_BOOLEAN, OPCODE_APUT_BOOLEAN,
           IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_byte(), OPCODE_AGET_BYTE, OPCODE_APUT_BYTE,
           IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_char(), OPCODE_AGET_CHAR, OPCODE_APUT_CHAR,
           IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_short(), OPCODE_AGET_SHORT, OPCODE_APUT_SHORT,
           IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_int(), OPCODE_AGET, OPCODE_APUT, IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_float(), OPCODE_AGET, OPCODE_APUT,
           IOPCODE_MOVE_RESULT_PSEUDO},
          {type::_long(), OPCODE_AGET_WIDE, OPCODE_APUT_WIDE,
           IOPCODE_MOVE_RESULT_PSEUDO_WIDE},
          {type::_double(), OPCODE_AGET_WIDE, OPCODE_APUT_WIDE,
           IOPCODE_MOVE_RESULT_PSEUDO_WIDE},
          {type::java_lang_Object(), OPCODE_AGET_OBJECT, OPCODE_APUT_OBJECT,
           IOPCODE_MOVE_RESULT_PSEUDO_OBJECT},
          {type::make_array_type(type::_int()), OPCODE_AGET_OBJECT,
           OPCODE_APUT_OBJECT, IOPCODE_MOVE_RESULT_PSEUDO_OBJECT},
      };
  for (const auto& [component, aget, aput, move_result] : cases) {
    EXPECT_EQ(opcode::aget_opcode_for_type(component), aget) << SHOW(component);
    EXPECT_EQ(opcode::aput_opcode_for_type(component), aput) << SHOW(component);
    EXPECT_EQ(opcode::move_result_pseudo_for(aget), move_result)
        << SHOW(component);
  }
}

TEST_F(IRInstructionTest, MoveResultPseudoFor) {
  const std::vector<std::pair<IROpcode, IROpcode>> cases = {
      {OPCODE_IGET, IOPCODE_MOVE_RESULT_PSEUDO},
      {OPCODE_IGET_WIDE, IOPCODE_MOVE_RESULT_PSEUDO_WIDE},
      {OPCODE_IGET_OBJECT, IOPCODE_MOVE_RESULT_PSEUDO_OBJECT},
      {OPCODE_SGET, IOPCODE_MOVE_RESULT_PSEUDO},
      {OPCODE_SGET_WIDE, IOPCODE_MOVE_RESULT_PSEUDO_WIDE},
      {OPCODE_SGET_OBJECT, IOPCODE_MOVE_RESULT_PSEUDO_OBJECT},
      {OPCODE_CHECK_CAST, IOPCODE_MOVE_RESULT_PSEUDO_OBJECT},
  };
  for (const auto& [op, move_result] : cases) {
    EXPECT_EQ(opcode::move_result_pseudo_for(op), move_result) << SHOW(op);
  }
  EXPECT_EQ(opcode::move_result_pseudo_for_iget(OPCODE_IGET_WIDE),
            IOPCODE_MOVE_RESULT_PSEUDO_WIDE);
  EXPECT_EQ(opcode::move_result_pseudo_for_sget(OPCODE_SGET_OBJECT),
            IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
}

TEST_F(IRInstructionTest, DynamicInvokesAreExactlyPolymorphicAndCustom) {
  for (auto op : all_opcodes) {
    EXPECT_EQ(opcode::is_a_dynamic_invoke(op),
              op == OPCODE_INVOKE_POLYMORPHIC || op == OPCODE_INVOKE_CUSTOM)
        << SHOW(op);
  }
}

// `invoke-polymorphic` and its range form are four code units long, and both
// keep the method, the registers and the call-site prototype through
// ballooning and lowering.
TEST_F(IRInstructionTest, InvokePolymorphicRoundTrip) {
  auto* callee = DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)"
      "Ljava/lang/Object;");
  auto* proto = DexProto::make_proto("(IIII)V");
  auto* method = DexMethod::make_method("LFoo;.bar:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  for (auto op :
       {DOPCODE_INVOKE_POLYMORPHIC, DOPCODE_INVOKE_POLYMORPHIC_RANGE}) {
    auto* insn = new DexOpcodeSignaturePolymorphic(op, callee, proto);
    if (op == DOPCODE_INVOKE_POLYMORPHIC) {
      insn->set_arg_word_count(5);
      for (size_t i = 0; i < 5; ++i) {
        insn->set_src(i, i + 1);
      }
    } else {
      insn->set_range_base(0xf);
      insn->set_range_size(5);
    }
    method->set_dex_code(std::make_unique<DexCode>());
    method->get_dex_code()->get_instructions().push_back(insn);
    method->get_dex_code()->set_registers_size(0xff);
    std::unique_ptr<DexInstruction> copy(insn->clone());

    method->balloon();
    for (const auto& mie : InstructionIterable(method->get_code())) {
      EXPECT_EQ(mie.insn->size(), 4) << show(op);
    }
    instruction_lowering::lower(method);
    method->sync();
    const auto* out = method->get_dex_code()->get_instructions().at(0);
    EXPECT_EQ(*out, *copy) << show(op);
    EXPECT_EQ(out->size(), 4u) << show(op);
  }
}

TEST_F(IRInstructionTest, InvokePolymorphicWithoutReferenceIsChecked) {
  IRInstruction insn(OPCODE_INVOKE_POLYMORPHIC);
  EXPECT_THROW(insn.get_method(), RedexException);
  EXPECT_THROW(insn.get_callsite_proto(), RedexException);
}

// `invoke-polymorphic` names `invokeExact`, but calls whatever its method
// handle refers to, so it is not one of the instructions that have a method.
// `gather_methods` still reports the method it names.
TEST_F(IRInstructionTest, InvokePolymorphicNamesButDoesNotCallItsMethod) {
  auto* invoke_exact = DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)"
      "Ljava/lang/Object;");
  IRInstruction insn(OPCODE_INVOKE_POLYMORPHIC);
  insn.set_signature_polymorphic(invoke_exact, DexProto::make_proto("(I)V"));
  EXPECT_FALSE(insn.has_method());
  EXPECT_EQ(insn.get_signature_polymorphic()->method(), invoke_exact);
  std::vector<DexMethodRef*> methods;
  insn.gather_methods(methods);
  EXPECT_EQ(methods, std::vector<DexMethodRef*>{invoke_exact});
}

// A wide argument of `invoke-polymorphic` or `invoke-custom` is a register
// pair in dex code and one register in IR, as for the other invokes. Their
// call-site prototypes say which arguments are wide.
TEST_F(IRInstructionTest, NormalizeDynamicInvokes) {
  // (long) handle.invokeExact(longValue, intValue)
  IRInstruction polymorphic(OPCODE_INVOKE_POLYMORPHIC);
  polymorphic.set_signature_polymorphic(
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
          "lang/Object;)Ljava/lang/Object;"),
      DexProto::make_proto("(JI)J"));
  polymorphic.set_srcs({1, 2, 3, 4});
  ASSERT_TRUE(polymorphic.normalize_registers());
  EXPECT_EQ(polymorphic.srcs_copy(), (std::vector<reg_t>{1, 2, 4}));
  EXPECT_FALSE(polymorphic.src_is_wide(0));
  EXPECT_TRUE(polymorphic.src_is_wide(1));
  EXPECT_FALSE(polymorphic.src_is_wide(2));
  polymorphic.denormalize_registers();
  EXPECT_EQ(polymorphic.srcs_copy(), (std::vector<reg_t>{1, 2, 3, 4}));

  // A call site of type (JI)V has no receiver.
  IRInstruction custom(OPCODE_INVOKE_CUSTOM);
  custom.set_callsite(redex::make_callsite("run", "(JI)V"));
  custom.set_srcs({2, 3, 4});
  ASSERT_TRUE(custom.normalize_registers());
  EXPECT_EQ(custom.srcs_copy(), (std::vector<reg_t>{2, 4}));
  EXPECT_TRUE(custom.src_is_wide(0));
  EXPECT_FALSE(custom.src_is_wide(1));
  custom.denormalize_registers();
  EXPECT_EQ(custom.srcs_copy(), (std::vector<reg_t>{2, 3, 4}));
}

// A normalized invoke has one source for its receiver, if any, and one for each
// argument of its call-site prototype.
TEST_F(IRInstructionTest, InvokeSrcsSize) {
  IRInstruction polymorphic(OPCODE_INVOKE_POLYMORPHIC);
  polymorphic.set_signature_polymorphic(
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
          "lang/Object;)Ljava/lang/Object;"),
      DexProto::make_proto("(JI)J"));
  EXPECT_EQ(polymorphic.invoke_srcs_size(), 3u);

  IRInstruction custom(OPCODE_INVOKE_CUSTOM);
  custom.set_callsite(redex::make_callsite("run", "(JI)V"));
  EXPECT_EQ(custom.invoke_srcs_size(), 2u);
}

TEST_F(IRInstructionTest, CallsiteProtoWithoutReferenceIsChecked) {
  for (auto op : {OPCODE_INVOKE_CUSTOM, OPCODE_INVOKE_STATIC}) {
    IRInstruction insn(op);
    EXPECT_THROW(insn.get_callsite_proto(), RedexException) << show(op);
  }
  IRInstruction polymorphic(OPCODE_INVOKE_POLYMORPHIC);
  polymorphic.set_signature_polymorphic(
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
          "lang/Object;)Ljava/lang/Object;"),
      DexProto::make_proto("()V"));
  polymorphic.set_srcs_size(2);
  EXPECT_THROW(polymorphic.src_is_wide(1), RedexException);
}

// Besides its callee, a method handle call names the types of its call-site
// prototype. A method type, a method handle and a call site name types too:
// those of the method type and the bootstrap arguments, and those of the
// methods and fields that the method handles refer to.
TEST_F(IRInstructionTest, GatherTypesOfMethodTypesMethodHandlesAndCallSites) {
  auto types_of = [](const IRInstruction& insn) {
    std::vector<const DexType*> types;
    insn.gather_types(types);
    std::set<std::string> names;
    for (const auto* type : types) {
      names.insert(show(type));
    }
    return names;
  };

  IRInstruction polymorphic(OPCODE_INVOKE_POLYMORPHIC);
  polymorphic.set_signature_polymorphic(
      DexMethod::make_method("Ljava/lang/invoke/MethodHandle;.invokeExact:([L"
                             "java/lang/Object;)Ljava/lang/Object;"),
      DexProto::make_proto("(LK;)LL;"));
  EXPECT_EQ(types_of(polymorphic),
            (std::set<std::string>{"Ljava/lang/invoke/MethodHandle;",
                                   "[Ljava/lang/Object;", "Ljava/lang/Object;",
                                   "LK;", "LL;"}));

  IRInstruction method_type(OPCODE_CONST_METHOD_TYPE);
  method_type.set_proto(DexProto::make_proto("(LA;)LB;"));
  EXPECT_EQ(types_of(method_type), (std::set<std::string>{"LA;", "LB;"}));

  IRInstruction method_handle(OPCODE_CONST_METHOD_HANDLE);
  method_handle.set_methodhandle(redex::make_method_handle(
      METHOD_HANDLE_TYPE_INVOKE_STATIC, "LC;.m:(LD;)V"));
  EXPECT_EQ(types_of(method_handle),
            (std::set<std::string>{"LC;", "LD;", "V"}));

  IRInstruction field_handle(OPCODE_CONST_METHOD_HANDLE);
  field_handle.set_methodhandle(
      redex::make_method_handle(METHOD_HANDLE_TYPE_INSTANCE_GET, "LE;.f:LF;"));
  EXPECT_EQ(types_of(field_handle), (std::set<std::string>{"LE;", "LF;"}));

  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.emplace_back(new DexEncodedValueMethodHandle(redex::make_method_handle(
      METHOD_HANDLE_TYPE_INVOKE_STATIC, "LI;.m:()V")));
  args.emplace_back(
      new DexEncodedValueMethodType(DexProto::make_proto("(LJ;)V")));
  IRInstruction custom(OPCODE_INVOKE_CUSTOM);
  custom.set_callsite(redex::make_callsite("run", "(LG;)LH;", std::move(args)));
  EXPECT_EQ(
      types_of(custom),
      (std::set<std::string>{
          "LG;", "LH;", "LBoot;", "Ljava/lang/invoke/MethodHandles$Lookup;",
          "Ljava/lang/String;", "Ljava/lang/invoke/MethodType;",
          "Ljava/lang/invoke/MethodHandle;", "Ljava/lang/invoke/CallSite;",
          "LI;", "V", "LJ;"}));
}

// Both dynamic invokes write the result register, which a following
// move-result reads.
TEST_F(IRInstructionTest, DynamicInvokesHaveMoveResult) {
  for (auto op : {OPCODE_INVOKE_POLYMORPHIC, OPCODE_INVOKE_CUSTOM}) {
    EXPECT_TRUE(opcode::writes_result_register(op)) << show(op);
    EXPECT_TRUE(IRInstruction(op).has_move_result()) << show(op);
  }
}
