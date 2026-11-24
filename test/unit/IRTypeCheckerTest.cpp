/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Debug.h"
#include "gtest/gtest.h"
#include <algorithm>
#include <gmock/gmock.h>
#include <regex>
#include <sstream>
#include <string>

#include "Creators.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IROpcode.h"
#include "IRTypeChecker.h"
#include "RedexTest.h"
#include "Show.h"

using namespace testing;

/**
 * This enum is used in the iput/iget test
 * helper functions to check the suffix of the
 * IR operand. e.g iget-boolean vs iget-wide.
 * SHORT includes boolean, byte, char, short.
 */
enum OperandType { WIDE, SHORT, REF };

/**
 * This struct is used to describe the type of
 * the value in the iput/iget IR. It is used as
 * the argument for test helper functions.
 *
 * param value_type:         the DexType of this type;
 * param value_super_type:   super type;
 * param ctor_str:           string to create ctor for type;
 * param field_str:          string to create field for type;
 */
struct TestValueType {
  TestValueType(DexType* value_type,
                DexType* value_super_type,
                const std::string& ctor_str,
                const std::string& field_str) {
    this->value_type = value_type;
    this->value_super_type = value_super_type;
    this->ctor =
        DexMethod::make_method(ctor_str)->make_concrete(ACC_PUBLIC, false);
    this->field = DexField::make_field(field_str)->make_concrete(ACC_PUBLIC);
    // create class
    ClassCreator cls_creator(value_type);
    cls_creator.set_super(value_super_type);
    cls_creator.add_method(ctor);
    cls_creator.add_field(field);
    cls_creator.create();
  }

  DexType* value_type = nullptr;
  DexType* value_super_type = nullptr;
  DexMethod* ctor = nullptr;
  DexField* field = nullptr;
};

/**
 * Helper function for input-* / iget-* IR
 * Used for the failed tests
 *
 * param a_type:          struct instance to describe type a;
 * param b_type:          struct instance to describe type b;
 * param exp_fail_str:    the expected output for failed tests;
 * param opcode_to_test:  specify the instruction to test;
 * param is_put:          flag to tell whether it's a put IR
 * param ir_suffix:       suffix of the iget/iput IR
 *                        options: WIDE, REF, SHORT
                                 SHORT (byte, boolean, short, char)
 * param method:          pointer to DexMethod from IRTypeChecker;
 *
 * skeleton:
 * (const v3, 1) / (const-wide v3, 1)
 * (new-instance "LA;")
 * (move-result-pseudo-object v1)
 * (new-instance "LB;")
 * (move-result-pseudo-object v2)
 * (invoke-direct (v1) a_ctor)
 * (invoke-direct (v2) b_ctor)
 * (iput/iget [v0] v1 b_f)
 * [For iget] (move-result-pseudo v0) / (move-result-pseudo-wide v0)
 * (return-void)
 */
::testing::AssertionResult field_incompatible_fail_helper(
    const TestValueType& a_type,
    const TestValueType& b_type,
    const std::string& exp_fail_str,
    IROpcode opcode_to_test,
    bool is_put,
    OperandType ir_suffix,
    DexMethod* method) {

  using namespace dex_asm;
  // these instructions differ from each IR
  // const initialize
  IRInstruction* init_literal = nullptr;
  // invoke type a
  IRInstruction* a_invoke_insn = nullptr;
  // target IR to test
  IRInstruction* ir_to_test = nullptr;
  // move result pseudo for iget-*
  IRInstruction* extra_insn = nullptr;

  if (is_put) {
    // put-* IR
    a_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, a_type.ctor, {1_v});

    switch (ir_suffix) {
    case SHORT: {
      // short, byte, boolean, char
      init_literal = dasm(OPCODE_CONST, {3_v, 1_L});
      break;
    }
    case WIDE: {
      init_literal = dasm(OPCODE_CONST_WIDE, {3_v, 1_L});
      break;
    }
    case REF:
      not_reached();
    }

    ir_to_test = dasm(opcode_to_test, b_type.field, {3_v, 1_v});

  } else {
    // get-* IR
    a_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, a_type.ctor, {1_v, 3_v});

    switch (ir_suffix) {
    case SHORT: {
      // short, byte, boolean, char
      init_literal = dasm(OPCODE_CONST, {3_v, 1_L});
      extra_insn = dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v});
      break;
    }
    case WIDE: {
      init_literal = dasm(OPCODE_CONST_WIDE, {3_v, 1_L});
      extra_insn = dasm(IOPCODE_MOVE_RESULT_PSEUDO_WIDE, {5_v});
      break;
    }
    case REF:
      not_reached();
    }

    ir_to_test = dasm(opcode_to_test, b_type.field, {1_v});
  }

  // alternative to add_code
  // to avoid using function pointer
  // to a member of an abstract class
  IRCode* code = method->get_code();

  code->push_back(init_literal);
  // type a
  code->push_back(dasm(OPCODE_NEW_INSTANCE, a_type.value_type));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}));
  code->push_back(a_invoke_insn);
  // type b
  code->push_back(dasm(OPCODE_NEW_INSTANCE, b_type.value_type));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}));
  code->push_back(dasm(OPCODE_INVOKE_DIRECT, b_type.ctor, {2_v}));
  // test ir
  code->push_back(ir_to_test);
  // MOVE_RESULT_PSEUDO
  if (extra_insn != nullptr) {
    code->push_back(extra_insn);
  }
  // return
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(method);
  checker.run();

  if (!checker.fail()) {
    return ::testing::AssertionFailure() << "Checked did not fail";
  }

  auto matcher = (Matcher<std::string>)MatchesRegex(exp_fail_str.c_str());
  if (matcher.MatchAndExplain(checker.what(), nullptr)) {
    return ::testing::AssertionSuccess();
  }

  std::ostringstream oss;
  oss << checker.what() << " ";
  matcher.DescribeNegationTo(&oss);
  return ::testing::AssertionFailure() << oss.str();
}

/**
 * Helper function for input-* / iget-* IR
 * Used for the success tests
 *
 * param a_type:          struct instance to describe type a;
 * param b_type:          struct instance to describe type b;
 * param opcode_to_test:  specify the instruction to run;
 * param is_put:          flag to tell whether it's a put IR
 * param ir_suffix:       suffix of the iget/iput IR
 *                        options: WIDE, REF, SHORT
 * param method:          pointer to DexMethod from IRTypeChecker;
 *
 * skeleton:
 * (const v0, 1) / (const-wide v0, 1)
 * (new-instance "LA;")
 * (move-result-pseudo-object v1)
 * (new-instance "LAsub;")
 * (move-result-pseudo-object v2)
 * (invoke-direct (v1) a_ctor)
 * (invoke-direct (v2) sub_ctor)
 * (iput/iget [v0] v1 a_f)
 * [For iget] (move-result-pseudo v0) / (move-result-pseudo-wide v5)
 * (return-void)
 */
void field_compatible_success_helper(const TestValueType& a_type,
                                     const TestValueType& b_type,
                                     IROpcode opcode_to_test,
                                     bool is_put,
                                     OperandType ir_suffix,
                                     DexMethod* method) {

  using namespace dex_asm;
  // these instructions differ from each IR
  // const initialize
  IRInstruction* init_literal = nullptr;
  // invoke type a
  IRInstruction* a_invoke_insn = nullptr;
  // invoke type sub a
  IRInstruction* asub_invoke_insn = nullptr;
  // target IR to test
  IRInstruction* ir_to_test = nullptr;
  // move result pseudo for iget-*
  IRInstruction* extra_insn = nullptr;

  if (is_put) {
    // put-* IR
    a_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, a_type.ctor, {1_v});
    asub_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, b_type.ctor, {2_v});

    switch (ir_suffix) {
    case SHORT: {
      // short, byte, boolean, char
      init_literal = dasm(OPCODE_CONST, {3_v, 1_L});
      break;
    }
    case WIDE: {
      init_literal = dasm(OPCODE_CONST_WIDE, {3_v, 1_L});
      break;
    }
    case REF:
      not_reached();
    }

    ir_to_test = dasm(opcode_to_test, a_type.field, {3_v, 2_v});

  } else {
    // get-* IR
    a_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, a_type.ctor, {1_v, 3_v});
    asub_invoke_insn = dasm(OPCODE_INVOKE_DIRECT, b_type.ctor, {2_v, 3_v});

    switch (ir_suffix) {
    case SHORT: {
      // short, byte, boolean, char
      init_literal = dasm(OPCODE_CONST, {3_v, 1_L});
      extra_insn = dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v});
      break;
    }
    case WIDE: {
      init_literal = dasm(OPCODE_CONST_WIDE, {3_v, 1_L});
      extra_insn = dasm(IOPCODE_MOVE_RESULT_PSEUDO_WIDE, {5_v});
      break;
    }
    case REF:
      not_reached();
    }

    ir_to_test = dasm(opcode_to_test, a_type.field, {2_v});
  }

  IRCode* code = method->get_code();
  code->push_back(init_literal);
  // type a
  code->push_back(dasm(OPCODE_NEW_INSTANCE, a_type.value_type));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}));
  code->push_back(a_invoke_insn);
  // type asub
  code->push_back(dasm(OPCODE_NEW_INSTANCE, b_type.value_type));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}));
  code->push_back(asub_invoke_insn);
  // test ir
  code->push_back(ir_to_test);
  // MOVE_RESULT_PSEUDO
  if (extra_insn != nullptr) {
    code->push_back(extra_insn);
  }
  // return
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good());
}

class IRTypeCheckerTest : public RedexTest {
 public:
  ~IRTypeCheckerTest() {}

  IRTypeCheckerTest() {
    auto* args = DexTypeList::make_type_list({
        DexType::make_type("I"), // v5
        DexType::make_type("B"), // v6
        DexType::make_type("J"), // v7/v8
        DexType::make_type("Z"), // v9
        DexType::make_type("D"), // v10/v11
        DexType::make_type("S"), // v12
        DexType::make_type("F"), // v13
        type::java_lang_Object() // v14
    });
    ClassCreator cc(type::java_lang_Object());
    cc.set_access(ACC_PUBLIC);
    cc.set_external();
    [[maybe_unused]] auto* object_class = cc.create();

    auto* proto = DexProto::make_proto(type::_boolean(), args);
    m_method =
        DexMethod::make_method(DexType::make_type("Lbar;"),
                               DexString::make_string("testMethod"),
                               proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
    m_method->set_deobfuscated_name("testMethod");
    m_method->set_code(std::make_unique<IRCode>(m_method, /* temp_regs */ 5));

    proto = DexProto::make_proto(type::java_lang_Object(), args);
    m_method_ret_obj =
        DexMethod::make_method(DexType::make_type("Lbar;"),
                               DexString::make_string("testMethodRetObj"),
                               proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
    m_method_ret_obj->set_deobfuscated_name("testMethodRetObj");
    m_method_ret_obj->set_code(
        std::make_unique<IRCode>(m_method_ret_obj, /* temp_regs */ 5));

    m_virtual_method =
        DexMethod::make_method(DexType::make_type("Lbar;"),
                               DexString::make_string("testVirtualMethod"),
                               proto)
            ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    m_virtual_method->set_deobfuscated_name("testVirtualMethod");
    m_virtual_method->set_code(
        std::make_unique<IRCode>(m_virtual_method, /* temp_regs */ 5));
  }

  void add_code(const std::vector<IRInstruction*>& insns) {
    add_code(m_method, insns);
  }

  void add_code(std::unique_ptr<IRCode> insns) {
    add_code(m_method, std::move(insns));
  }

  void add_code_ret_obj(const std::vector<IRInstruction*>& insns) {
    add_code(m_method_ret_obj, insns);
  }

  void add_code_ret_obj(std::unique_ptr<IRCode> insns) {
    add_code(m_method_ret_obj, std::move(insns));
  }

  void add_code(DexMethod* m, const std::vector<IRInstruction*>& insns) {
    IRCode* code = m->get_code();
    for (const auto& insn : insns) {
      code->push_back(insn);
    }
  }

  void add_code(DexMethod* m, std::unique_ptr<IRCode> insns) {
    IRCode* code = m->get_code();
    for (const auto& insn : *insns) {
      code->push_back(insn);
    }
    insns->set_insn_ownership(false);
  }

 protected:
  DexMethod* m_method;
  DexMethod* m_method_ret_obj;
  DexMethod* m_virtual_method;
};

TEST_F(IRTypeCheckerTest, load_param) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_ADD_INT, {5_v, 5_v, 6_v}),
      dasm(IOPCODE_LOAD_PARAM, {5_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Encountered [0x[0-9a-f]+] OPCODE: "
                           "IOPCODE_LOAD_PARAM v5 not at the start "
                           "of the method$"));
}

TEST_F(IRTypeCheckerTest, move_result) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_FILLED_NEW_ARRAY, DexType::make_type("I"))
          ->set_srcs_size(1)
          ->set_src(0, 5),
      dasm(OPCODE_ADD_INT, {5_v, 5_v, 5_v}),
      dasm(OPCODE_MOVE_RESULT, {0_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Encountered [0x[0-9a-f]+] OPCODE: MOVE_RESULT v0 "
                           "without appropriate prefix instruction. Expected "
                           "invoke or filled-new-array, got "
                           "ADD_INT v5, v5, v5$"));
}

// A void call leaves no result, even right after a call that does.
TEST_F(IRTypeCheckerTest, move_result_after_void_invoke) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()I"
     (
      (invoke-static () "LFoo;.getInt:()I")
      (invoke-static () "LFoo;.run:()V")
      (move-result v0)
      (return v0)
     )
    )
  )");
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, move_result_after_void_method_handle_call) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)I"
     (
      (load-param-object v0)
      (invoke-static () "LFoo;.getInt:()I")
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (move-result v1)
      (return v1)
     )
    )
  )");
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, move_result_at_start) {
  using namespace dex_asm;
  // Construct a new method because we don't want any load-param opcodes in
  // this one
  auto* args = DexTypeList::make_type_list({});
  auto* proto = DexProto::make_proto(type::_boolean(), args);
  auto* method =
      DexMethod::make_method(DexType::make_type("Lbar;"),
                             DexString::make_string("testMethod2"),
                             proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_deobfuscated_name("testMethod2");
  method->set_code(std::make_unique<IRCode>(method, 0));

  IRCode* code = method->get_code();
  code->push_back(dasm(OPCODE_MOVE_RESULT, {0_v}));
  code->push_back(dasm(OPCODE_ADD_INT, {5_v, 5_v, 5_v}));

  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Encountered [0x[0-9a-f]+] OPCODE: MOVE_RESULT v0 "
                           "at start of the method$"));
}

TEST_F(IRTypeCheckerTest, move_result_pseudo_no_prefix) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),
      dasm(OPCODE_ADD_INT, {5_v, 5_v, 5_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Encountered [0x[0-9a-f]+] OPCODE: IOPCODE_MOVE_RESULT_PSEUDO v0 "
          "without appropriate prefix instruction$"));
}

TEST_F(IRTypeCheckerTest, move_result_pseudo_no_suffix) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CHECK_CAST, type::java_lang_Object(), {14_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              ContainsRegex("^Did not find move-result-pseudo after "
                            "[0x[0-9a-f]+] OPCODE: CHECK_CAST v14, "
                            "Ljava/lang/Object;"));
}

TEST_F(IRTypeCheckerTest, arrayRead) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CHECK_CAST, DexType::make_type("[I"), {14_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_AGET, {0_v, 5_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {1_v}),
      dasm(OPCODE_ADD_INT, {2_v, 1_v, 5_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(IRType::SCALAR, checker.get_type(insns[4], 1));
  EXPECT_EQ(IRType::INT, checker.get_type(insns[5], 1));
}

TEST_F(IRTypeCheckerTest, arrayReadWide) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CHECK_CAST, DexType::make_type("[D"), {14_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_AGET_WIDE, {0_v, 5_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_WIDE, {1_v}),
      dasm(OPCODE_ADD_DOUBLE, {3_v, 1_v, 10_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ(IRType::SCALAR1, checker.get_type(insns[4], 1));
  EXPECT_EQ(IRType::SCALAR2, checker.get_type(insns[4], 2));
  EXPECT_EQ(IRType::DOUBLE1, checker.get_type(insns[5], 3));
  EXPECT_EQ(IRType::DOUBLE2, checker.get_type(insns[5], 4));
}

TEST_F(IRTypeCheckerTest, multipleDefinitions) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CHECK_CAST, DexType::make_type("[I"), {14_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_AGET, {0_v, 5_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),
      dasm(OPCODE_INT_TO_FLOAT, {0_v, 0_v}),
      dasm(OPCODE_NEG_FLOAT, {0_v, 0_v}),
      dasm(OPCODE_MOVE_OBJECT, {0_v, 14_v}),
      dasm(OPCODE_CHECK_CAST, DexType::make_type("Lfoo;"), {0_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL,
           DexMethod::make_method("LFoo;", "bar", "J", {"S"}),
           {0_v, 12_v}),
      dasm(OPCODE_MOVE_RESULT_WIDE, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[2], 0));
  EXPECT_EQ(IRType::SCALAR, checker.get_type(insns[4], 0));
  EXPECT_EQ(IRType::FLOAT, checker.get_type(insns[5], 0));
  EXPECT_EQ(IRType::FLOAT, checker.get_type(insns[6], 0));
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[7], 0));
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[9], 0));
  EXPECT_EQ(IRType::LONG1, checker.get_type(insns[11], 0));
  EXPECT_EQ(IRType::LONG2, checker.get_type(insns[11], 1));
}

TEST_F(IRTypeCheckerTest, referenceFromInteger) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_MOVE, {0_v, 5_v}),
      dasm(OPCODE_AGET, {0_v, 5_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'AGET v0, v5' "
          "@ 0x[0-9a-f]+ for register v0: expected type REF, but found "
          "INT instead"));
}

TEST_F(IRTypeCheckerTest, misalignedLong) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_MOVE_WIDE, {0_v, 7_v}),
      dasm(OPCODE_NEG_LONG, {1_v, 1_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'NEG_LONG v1, v1' "
          "@ 0x[0-9a-f]+ for register v1: expected type \\(LONG1, LONG2\\), "
          "but found \\(LONG2, TOP\\) instead"));
}

TEST_F(IRTypeCheckerTest, uninitializedRegister) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_INVOKE_VIRTUAL,
           DexMethod::make_method("Lbar;", "foo", "V", {}),
           {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'INVOKE_VIRTUAL v0, "
          "Lbar;\\.foo:\\(\\)V' @ 0x[0-9a-f]+ for register v0: expected "
          "type REF, but found TOP instead"));
}

TEST_F(IRTypeCheckerTest, undefinedRegister) {
  using namespace dex_asm;
  auto* if_mie = new MethodItemEntry(dasm(OPCODE_IF_EQZ, {9_v}));
  auto* goto_mie = new MethodItemEntry(dasm(OPCODE_GOTO, {}));
  auto* target1 = new BranchTarget(if_mie);
  auto* target2 = new BranchTarget(goto_mie);
  IRCode* code = m_method->get_code();
  code->push_back(*if_mie); // branch to target1
  code->push_back(dasm(OPCODE_MOVE_OBJECT, {0_v, 14_v}));
  code->push_back(dasm(OPCODE_CHECK_CAST, DexType::make_type("Lbar;"), {0_v}));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}));
  code->push_back(*goto_mie); // branch to target2
  code->push_back(target1);
  code->push_back(dasm(OPCODE_MOVE, {0_v, 12_v}));
  code->push_back(target2);
  // Coming out of one branch, v0 is a reference and coming out of the other,
  // it's an integer.
  code->push_back(dasm(OPCODE_INVOKE_VIRTUAL,
                       DexMethod::make_method("Lbar;", "foo", "V", {}),
                       {0_v}));
  code->push_back(dasm(OPCODE_RETURN, {9_v}));
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'INVOKE_VIRTUAL v0, "
          "Lbar;\\.foo:\\(\\)V' @ 0x[0-9a-f]+ for register v0: expected "
          "type REF, but found TOP instead"));
}

TEST_F(IRTypeCheckerTest, signatureMismatch) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CHECK_CAST, DexType::make_type("Lbar;"), {14_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL,
           DexMethod::make_method("Lbar;", "foo", "V", {"I", "J", "Z"}),
           {0_v, 5_v, 7_v, 13_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'INVOKE_VIRTUAL v0, "
          "v5, v7, v13, Lbar;\\.foo:\\(IJZ\\)V' @ 0x[0-9a-f]+ for register "
          "v13: expected type INT, but found FLOAT instead"));
}

TEST_F(IRTypeCheckerTest, longInvoke) {
  using namespace dex_asm;
  IRInstruction* invoke = new IRInstruction(OPCODE_INVOKE_STATIC);
  invoke->set_srcs_size(7);
  invoke->set_method(DexMethod::make_method(
      "Lbar;", "foo", "V", {"I", "B", "J", "Z", "D", "S", "F"}));
  invoke->set_src(0, 5);
  invoke->set_src(1, 6);
  invoke->set_src(2, 7);
  invoke->set_src(3, 9);
  invoke->set_src(4, 10);
  invoke->set_src(5, 12);
  invoke->set_src(6, 13);
  std::vector<IRInstruction*> insns = {invoke, dasm(OPCODE_RETURN, {9_v})};
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

TEST_F(IRTypeCheckerTest, longSignatureMismatch) {
  using namespace dex_asm;
  IRInstruction* invoke = new IRInstruction(OPCODE_INVOKE_STATIC);
  invoke->set_srcs_size(7);
  invoke->set_method(DexMethod::make_method(
      "Lbar;", "foo", "V", {"I", "B", "J", "Z", "S", "D", "F"}));
  invoke->set_src(0, 5);
  invoke->set_src(1, 6);
  invoke->set_src(2, 7);
  invoke->set_src(3, 9);
  invoke->set_src(4, 10);
  invoke->set_src(5, 11);
  invoke->set_src(6, 13);
  std::vector<IRInstruction*> insns = {invoke, dasm(OPCODE_RETURN, {9_v})};
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'INVOKE_STATIC "
          "v5, v6, v7, v9, v10, v11, v13, Lbar;\\.foo:\\(IBJZSDF\\)V' "
          "@ 0x[0-9a-f]+ for register v10: expected type INT, but found "
          "DOUBLE1 "
          "instead"));
}

TEST_F(IRTypeCheckerTest, comparisonOperation) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_MOVE_WIDE, {0_v, 10_v}),
      dasm(OPCODE_CMP_LONG, {0_v, 7_v, 0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction 'CMP_LONG v0, v7, "
          "v0' @ 0x[0-9a-f]+ for register v0: expected type \\(LONG1, "
          "LONG2\\), but found \\(DOUBLE1, DOUBLE2\\) instead"));
}

TEST_F(IRTypeCheckerTest, verifyMoves) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_MOVE_OBJECT, {1_v, 0_v}),
      dasm(OPCODE_MOVE, {1_v, 9_v}),
      dasm(OPCODE_RETURN, {1_v}),
  };
  add_code(insns);
  IRTypeChecker lax_checker(m_method);
  lax_checker.run();
  EXPECT_TRUE(lax_checker.good()) << lax_checker.what();
  IRTypeChecker strict_checker(m_method);
  strict_checker.verify_moves();
  strict_checker.run();
  EXPECT_TRUE(strict_checker.fail());
  EXPECT_THAT(
      strict_checker.what(),
      MatchesRegex(
          "^Type error in method testMethod at instruction "
          "'MOVE_OBJECT v1, v0' @ 0x[0-9a-f]+ for register v0: expected type "
          "REF, but found TOP instead"));
}

TEST_F(IRTypeCheckerTest, exceptionHandler) {
  using namespace dex_asm;
  auto* exception_type = DexType::make_type("Ljava/lang/Exception;");
  auto* catch_start = new MethodItemEntry(exception_type);
  IRCode* code = m_method->get_code();
  IRInstruction* noexc_return = dasm(OPCODE_RETURN, {1_v});
  IRInstruction* exc_return = dasm(OPCODE_RETURN, {0_v});
  code->push_back(dasm(OPCODE_MOVE, {0_v, 9_v}));
  code->push_back(dasm(OPCODE_CONST, {1_v, 0_L}));
  code->push_back(dasm(OPCODE_CONST, {2_v, 12_L}));
  code->push_back(TRY_START, catch_start);
  code->push_back(dasm(OPCODE_DIV_INT, {5_v, 5_v})); // Can throw
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO, {2_v}));
  code->push_back(dasm(OPCODE_CONST, {1_v, 1_L}));
  code->push_back(dasm(OPCODE_MOVE, {3_v, 1_v}));
  code->push_back(TRY_END, catch_start);
  code->push_back(noexc_return);
  code->push_back(*catch_start);
  code->push_back(exc_return);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ(IRType::INT, checker.get_type(noexc_return, 0));
  EXPECT_EQ(IRType::CONST, checker.get_type(noexc_return, 1));
  EXPECT_EQ(IRType::INT, checker.get_type(noexc_return, 2));
  EXPECT_EQ(IRType::CONST, checker.get_type(noexc_return, 3));
  // The exception is thrown by DIV_INT before v2 is modified.
  EXPECT_EQ(IRType::INT, checker.get_type(exc_return, 0));
  EXPECT_EQ(IRType::ZERO, checker.get_type(exc_return, 1));
  EXPECT_EQ(IRType::CONST, checker.get_type(exc_return, 2));
  EXPECT_EQ(IRType::TOP, checker.get_type(exc_return, 3));
  EXPECT_EQ(IRType::INT, checker.get_type(exc_return, 5));
  // The rest of the type environment, like method parameters, should be
  // left unchanged in the exception handler.
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(exc_return, 14));
}

TEST_F(IRTypeCheckerTest, overlappingMoveWide) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_MOVE_WIDE, {1_v, 7_v}),  dasm(OPCODE_MOVE_WIDE, {0_v, 1_v}),
      dasm(OPCODE_MOVE_WIDE, {0_v, 10_v}), dasm(OPCODE_MOVE_WIDE, {1_v, 0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };
  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(IRType::LONG1, checker.get_type(insns[1], 1));
  EXPECT_EQ(IRType::LONG2, checker.get_type(insns[1], 2));
  EXPECT_EQ(IRType::LONG1, checker.get_type(insns[2], 0));
  EXPECT_EQ(IRType::LONG2, checker.get_type(insns[2], 1));
  EXPECT_EQ(IRType::DOUBLE1, checker.get_type(insns[3], 0));
  EXPECT_EQ(IRType::DOUBLE2, checker.get_type(insns[3], 1));
  EXPECT_EQ(IRType::DOUBLE1, checker.get_type(insns[4], 1));
  EXPECT_EQ(IRType::DOUBLE2, checker.get_type(insns[4], 2));
}

TEST_F(IRTypeCheckerTest, filledNewArray) {
  auto insns = assembler::ircode_from_string(R"(
    (
      (const-string "S1")
      (move-result-pseudo-object v1)
      (const-string "S2")
      (move-result-pseudo-object v2)
      (const-string "S3")
      (move-result-pseudo-object v3)
      (filled-new-array (v1 v2 v3) "[Ljava/lang/String;")
      (move-result-object v0)
      (return v9)
    )
  )");
  add_code(std::move(insns));
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
}

TEST_F(IRTypeCheckerTest, zeroOrReference) {
  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      dasm(OPCODE_CONST_CLASS, DexType::make_type("Lbar;")),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_MONITOR_ENTER, {0_v}),
      dasm(OPCODE_CONST, {1_v, 0_L}),
      dasm(OPCODE_MONITOR_EXIT, {0_v}),
      dasm(OPCODE_RETURN_OBJECT, {0_v}),
      dasm(OPCODE_MOVE_EXCEPTION, {1_v}),
      dasm(OPCODE_MONITOR_EXIT, {0_v}),
      dasm(OPCODE_THROW, {1_v}),
  };
  add_code_ret_obj(insns);
  IRTypeChecker checker(m_method_ret_obj);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[2], 0));
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[3], 0));
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[4], 0));
  EXPECT_EQ(IRType::ZERO, checker.get_type(insns[4], 1));
  EXPECT_EQ(IRType::REFERENCE, checker.get_type(insns[5], 0));
  EXPECT_EQ(IRType::ZERO, checker.get_type(insns[5], 1));
  EXPECT_EQ(IRType::BOTTOM, checker.get_type(insns[6], 0));
  EXPECT_EQ(IRType::BOTTOM, checker.get_type(insns[6], 1));
  EXPECT_EQ(IRType::BOTTOM, checker.get_type(insns[7], 1));
  EXPECT_EQ(IRType::BOTTOM, checker.get_type(insns[8], 1));
}

/**
 * The bytecode stream of the following Java code.
 * A simple branch join scenario on a reference type.
 *
 * Base base = null;
 * if (condition) {
 *   base = new A();
 *   base.foo();
 * } else {
 *   base = new B();
 *   base.foo();
 * }
 * base.foo();
 */
TEST_F(IRTypeCheckerTest, joinDexTypesSharingCommonBaseSimple) {
  // Construct type hierarchy.
  auto* const type_base = DexType::make_type("LBase;");
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  ClassCreator cls_base_creator(type_base);
  cls_base_creator.set_super(type::java_lang_Object());
  auto* base_foo =
      DexMethod::make_method("LBase;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_base_creator.add_method(base_foo);
  cls_base_creator.create();

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type_base);
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_foo =
      DexMethod::make_method("LA;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_a_creator.add_method(a_foo);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type_base);
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_foo =
      DexMethod::make_method("LB;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_b_creator.add_method(b_foo);
  cls_b_creator.create();

  // Construct code that references the above hierarchy.
  using namespace dex_asm;
  auto* if_mie = new MethodItemEntry(dasm(OPCODE_IF_EQZ, {5_v}));
  auto* goto_mie = new MethodItemEntry(dasm(OPCODE_GOTO, {}));
  auto* target1 = new BranchTarget(if_mie);
  auto* target2 = new BranchTarget(goto_mie);

  std::vector<IRInstruction*> insns = {
      // B0
      // *if_mie, // branch to target1
      // B1
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, a_foo, {0_v}),
      // *goto_mie, // branch to target2
      // B2
      // target1,
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, b_foo, {0_v}),
      // target2,
      // B3
      // Coming out of one branch, v0 is a reference and coming out of the
      // other,
      // it's an integer.
      dasm(OPCODE_INVOKE_VIRTUAL, base_foo, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };

  IRCode* code = m_method->get_code();
  code->push_back(*if_mie);
  code->push_back(insns[0]);
  code->push_back(insns[1]);
  code->push_back(insns[2]);
  code->push_back(insns[3]);
  code->push_back(*goto_mie);
  code->push_back(target1);
  code->push_back(insns[4]);
  code->push_back(insns[5]);
  code->push_back(insns[6]);
  code->push_back(insns[7]);
  code->push_back(target2);
  code->push_back(insns[8]);
  code->push_back(insns[9]);

  IRTypeChecker checker(m_method);
  checker.run();
  // Checks
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[2], 0));
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[3], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[6], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[7], 0));
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[8], 0));
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[9], 0));
}

/**
 * The bytecode stream of the following Java code.
 * A simple branch join scenario on a reference type.
 *
 * Base base = null;
 * if (condition) {
 *   base = new A();
 *   base.foo();
 * } else {
 *   base = new B();
 *   base.foo();
 * }
 * base.foo();
 */
TEST_F(IRTypeCheckerTest, joinCommonBaseWithConflictingInterface) {
  // Construct type hierarchy.
  auto* const type_base = DexType::make_type("LBase;");
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");
  auto* const type_i = DexType::make_type("LI;");

  ClassCreator cls_base_creator(type_base);
  cls_base_creator.set_super(type::java_lang_Object());
  auto* base_foo =
      DexMethod::make_method("LBase;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_base_creator.add_method(base_foo);
  cls_base_creator.create();

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type_base);
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_foo =
      DexMethod::make_method("LA;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_a_creator.add_method(a_foo);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type_base);
  cls_b_creator.add_interface(type_i);

  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_foo =
      DexMethod::make_method("LB;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_b_creator.add_method(b_foo);
  cls_b_creator.create();

  // Construct code that references the above hierarchy.
  using namespace dex_asm;
  auto* if_mie = new MethodItemEntry(dasm(OPCODE_IF_EQZ, {5_v}));
  auto* goto_mie = new MethodItemEntry(dasm(OPCODE_GOTO, {}));
  auto* target1 = new BranchTarget(if_mie);
  auto* target2 = new BranchTarget(goto_mie);

  std::vector<IRInstruction*> insns = {
      // B0
      // *if_mie, // branch to target1
      // B1
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, a_foo, {0_v}),
      // *goto_mie, // branch to target2
      // B2
      // target1,
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, b_foo, {0_v}),
      // target2,
      // B3
      // Coming out of one branch, v0 is a reference and coming out of the
      // other,
      // it's an integer.
      dasm(OPCODE_INVOKE_VIRTUAL, base_foo, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };

  IRCode* code = m_method->get_code();
  code->push_back(*if_mie);
  code->push_back(insns[0]);
  code->push_back(insns[1]);
  code->push_back(insns[2]);
  code->push_back(insns[3]);
  code->push_back(*goto_mie);
  code->push_back(target1);
  code->push_back(insns[4]);
  code->push_back(insns[5]);
  code->push_back(insns[6]);
  code->push_back(insns[7]);
  code->push_back(target2);
  code->push_back(insns[8]);
  code->push_back(insns[9]);

  IRTypeChecker checker(m_method);
  checker.run();
  // Checks
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[2], 0));
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[3], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[6], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[7], 0));
  // B's interface I cannot survive a merge with A, but that is no reason to
  // lose the common base class as well.
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[8], 0));
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[9], 0));
}

/**
 * The bytecode stream of the following Java code.
 * A simple branch join scenario on a reference type.
 *
 * Base base = null;
 * if (condition) {
 *   base = new A();
 *   base.foo();
 * } else {
 *   base = new B();
 *   base.foo();
 * }
 * base.foo();
 */
TEST_F(IRTypeCheckerTest, joinCommonBaseWithMergableInterface) {
  // Construct type hierarchy.
  auto* const type_base = DexType::make_type("LBase;");
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");
  auto* const type_i = DexType::make_type("LI;");

  ClassCreator cls_base_creator(type_base);
  cls_base_creator.set_super(type::java_lang_Object());
  cls_base_creator.add_interface(type_i);
  auto* base_foo =
      DexMethod::make_method("LBase;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_base_creator.add_method(base_foo);
  cls_base_creator.create();

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type_base);
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_foo =
      DexMethod::make_method("LA;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_a_creator.add_method(a_foo);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type_base);
  cls_b_creator.add_interface(type_i);

  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_foo =
      DexMethod::make_method("LB;.foo:()I")->make_concrete(ACC_PUBLIC, true);
  cls_b_creator.add_method(b_foo);
  cls_b_creator.create();

  // Construct code that references the above hierarchy.
  using namespace dex_asm;
  auto* if_mie = new MethodItemEntry(dasm(OPCODE_IF_EQZ, {5_v}));
  auto* goto_mie = new MethodItemEntry(dasm(OPCODE_GOTO, {}));
  auto* target1 = new BranchTarget(if_mie);
  auto* target2 = new BranchTarget(goto_mie);

  std::vector<IRInstruction*> insns = {
      // B0
      // *if_mie, // branch to target1
      // B1
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, a_foo, {0_v}),
      // *goto_mie, // branch to target2
      // B2
      // target1,
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      dasm(OPCODE_INVOKE_VIRTUAL, b_foo, {0_v}),
      // target2,
      // B3
      // Coming out of one branch, v0 is a reference and coming out of the
      // other,
      // it's an integer.
      dasm(OPCODE_INVOKE_VIRTUAL, base_foo, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };

  IRCode* code = m_method->get_code();
  code->push_back(*if_mie);
  code->push_back(insns[0]);
  code->push_back(insns[1]);
  code->push_back(insns[2]);
  code->push_back(insns[3]);
  code->push_back(*goto_mie);
  code->push_back(target1);
  code->push_back(insns[4]);
  code->push_back(insns[5]);
  code->push_back(insns[6]);
  code->push_back(insns[7]);
  code->push_back(target2);
  code->push_back(insns[8]);
  code->push_back(insns[9]);

  IRTypeChecker checker(m_method);
  checker.run();
  // Checks
  EXPECT_TRUE(checker.good()) << checker.what();
  EXPECT_EQ("OK", checker.what());
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[2], 0));
  EXPECT_EQ(type_a, *checker.get_dex_type(insns[3], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[6], 0));
  EXPECT_EQ(type_b, *checker.get_dex_type(insns[7], 0));
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[8], 0));
  EXPECT_EQ(type_base, *checker.get_dex_type(insns[9], 0));
}

namespace {

// First instruction with the given opcode, or null. Used to name the
// instruction a type error is expected to be attributed to.
IRInstruction* find_insn(DexMethod* method, IROpcode opcode) {
  for (const auto& mie : InstructionIterable(method->get_code())) {
    if (mie.insn->opcode() == opcode) {
      return mie.insn;
    }
  }
  return nullptr;
}

} // namespace

/**
 * Two unrelated classes merge, one of them declaring an interface. Their least
 * upper bound genuinely is Ljava/lang/Object;, and storing that into a field of
 * a more derived type is what the Android verifier rejects.
 *
 * The join used to report Top for this instead, because the merge point could
 * not carry LStoredIntf; -- and assume_assignable does nothing when there is no
 * type, so the store went unchecked. That is the shape that shipped in S697124.
 */
TEST_F(IRTypeCheckerTest, iputObjectOfUnrelatedJoinIsRejected) {
  auto* const type_intf = DexType::make_type("LStoredIntf;");
  ClassCreator intf_creator(type_intf);
  intf_creator.set_super(type::java_lang_Object());
  intf_creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
  intf_creator.create();

  // Declares an interface, so the merge point cannot preserve its full
  // identity. That is not a reason to give up on the class part.
  auto* const type_stored = DexType::make_type("LStored;");
  ClassCreator stored_creator(type_stored);
  stored_creator.set_super(type::java_lang_Object());
  stored_creator.add_interface(type_intf);
  stored_creator.add_method(DexMethod::make_method("LStored;.<init>:()V")
                                ->make_concrete(ACC_PUBLIC, false));
  stored_creator.create();

  // Shares nothing with LStored; but Object.
  auto* const type_other = DexType::make_type("LOther;");
  ClassCreator other_creator(type_other);
  other_creator.set_super(type::java_lang_Object());
  other_creator.add_method(DexMethod::make_method("LOther;.<init>:()V")
                               ->make_concrete(ACC_PUBLIC, false));
  other_creator.create();

  auto* const type_holder = DexType::make_type("LHolder;");
  ClassCreator holder_creator(type_holder);
  holder_creator.set_super(type::java_lang_Object());
  holder_creator.add_method(DexMethod::make_method("LHolder;.<init>:()V")
                                ->make_concrete(ACC_PUBLIC, false));
  holder_creator.add_field(
      DexField::make_field("LHolder;.f:LStored;")->make_concrete(ACC_PUBLIC));
  holder_creator.create();

  auto* method = DexMethod::make_method("LHolder;.store:(I)V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v2)

      (if-eqz v2 :other)
      (new-instance "LStored;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LStored;.<init>:()V")
      (goto :join)

      (:other)
      (new-instance "LOther;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LOther;.<init>:()V")

      (:join)
      (new-instance "LHolder;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LHolder;.<init>:()V")
      (iput-object v0 v1 "LHolder;.f:LStored;")
      (return-void)
    )
  )"));

  auto* iput_insn = find_insn(method, OPCODE_IPUT_OBJECT);
  ASSERT_NE(nullptr, iput_insn);

  IRTypeChecker checker(method);
  checker.run();

  // Pin what the join produced, not just that something was rejected.
  EXPECT_EQ(type::java_lang_Object(), *checker.get_dex_type(iput_insn, 0));
  EXPECT_FALSE(checker.good());
  EXPECT_THAT(checker.what(),
              HasSubstr("Ljava/lang/Object; is not assignable to LStored;"));
  EXPECT_EQ(iput_insn, checker.error_insn());
}

/**
 * The same bad store, but reached around a loop back edge rather than through
 * a branch. This is the shape S697124 actually shipped: a value live across a
 * loop is clobbered on one path through the body, so from the second iteration
 * on the store sees the wrong type.
 *
 * Worth knowing if this ever starts failing: the join is only half the story
 * here. `DexTypeValue::widen_with` drops straight to Top for any two distinct
 * types, and Sparta widens at a loop head from its second iteration on, so a
 * merge that needs more rounds than this one to settle would be unchecked
 * regardless of what `find_common_type` returns.
 */
TEST_F(IRTypeCheckerTest, iputObjectOfLoopCarriedUnrelatedJoinIsRejected) {
  auto* const type_intf = DexType::make_type("LLoopIntf;");
  ClassCreator intf_creator(type_intf);
  intf_creator.set_super(type::java_lang_Object());
  intf_creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
  intf_creator.create();

  auto* const type_stored = DexType::make_type("LLoopStored;");
  ClassCreator stored_creator(type_stored);
  stored_creator.set_super(type::java_lang_Object());
  stored_creator.add_interface(type_intf);
  stored_creator.add_method(DexMethod::make_method("LLoopStored;.<init>:()V")
                                ->make_concrete(ACC_PUBLIC, false));
  stored_creator.create();

  auto* const type_other = DexType::make_type("LLoopOther;");
  ClassCreator other_creator(type_other);
  other_creator.set_super(type::java_lang_Object());
  other_creator.add_method(DexMethod::make_method("LLoopOther;.<init>:()V")
                               ->make_concrete(ACC_PUBLIC, false));
  other_creator.create();

  auto* const type_holder = DexType::make_type("LLoopHolder;");
  ClassCreator holder_creator(type_holder);
  holder_creator.set_super(type::java_lang_Object());
  holder_creator.add_method(DexMethod::make_method("LLoopHolder;.<init>:()V")
                                ->make_concrete(ACC_PUBLIC, false));
  holder_creator.add_field(DexField::make_field("LLoopHolder;.f:LLoopStored;")
                               ->make_concrete(ACC_PUBLIC));
  holder_creator.create();

  auto* method = DexMethod::make_method("LLoopHolder;.storeInLoop:(I)V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v2)

      ; v0 starts out as the type the field expects
      (new-instance "LLoopStored;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LLoopStored;.<init>:()V")

      (:loop)
      (if-eqz v2 :store)

      ; the other path through the body reuses v0 as scratch space, so
      ; `stored` does not survive the iteration
      (new-instance "LLoopOther;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LLoopOther;.<init>:()V")
      (goto :latch)

      (:store)
      (new-instance "LLoopHolder;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LLoopHolder;.<init>:()V")
      (iput-object v0 v1 "LLoopHolder;.f:LLoopStored;")

      (:latch)
      (if-eqz v2 :loop)
      (return-void)
    )
  )"));

  auto* iput_insn = find_insn(method, OPCODE_IPUT_OBJECT);
  ASSERT_NE(nullptr, iput_insn);

  IRTypeChecker checker(method);
  checker.run();

  EXPECT_EQ(type::java_lang_Object(), *checker.get_dex_type(iput_insn, 0));
  EXPECT_FALSE(checker.good());
  EXPECT_THAT(
      checker.what(),
      HasSubstr("Ljava/lang/Object; is not assignable to LLoopStored;"));
  EXPECT_EQ(iput_insn, checker.error_insn());
}

/**
 * The bytecode stream of the following Java code.
 *
 * Base base;
 * if (condition) {
 *   base = null;
 * } else {
 *   base = new Object();
 * }
 * base.foo();
 */
TEST_F(IRTypeCheckerTest, invokeInvalidObjectType) {
  // Construct type hierarchy.
  auto* const type_base = DexType::make_type("LBase;");

  ClassCreator cls_base_creator(type_base);
  cls_base_creator.set_super(type::java_lang_Object());
  auto* base_foobar = DexMethod::make_method("LBase;.foobar:()I")
                          ->make_concrete(ACC_PUBLIC, true);
  cls_base_creator.add_method(base_foobar);
  cls_base_creator.create();

  auto* object_ctor = DexMethod::make_method("Ljava/lang/Object;.<init>:()V");
  EXPECT_TRUE(object_ctor != nullptr);

  // Construct code that references the above hierarchy.
  using namespace dex_asm;
  auto* if_mie = new MethodItemEntry(dasm(OPCODE_IF_EQZ, {5_v}));
  auto* goto_mie = new MethodItemEntry(dasm(OPCODE_GOTO, {}));
  auto* target1 = new BranchTarget(if_mie);
  auto* target2 = new BranchTarget(goto_mie);

  std::vector<IRInstruction*> insns = {
      // B0
      // *if_mie, // branch to target1
      // B1
      dasm(OPCODE_CONST, {0_v, 0_L}),
      // *goto_mie, // branch to target2
      // B2
      // target1,
      dasm(OPCODE_NEW_INSTANCE, type::java_lang_Object()),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, object_ctor, {0_v}),
      // target2,
      // B3
      // Coming out of one branch, v0 is null and coming out of the
      // other, it's an Object, but not (necessarily) a Base
      dasm(OPCODE_INVOKE_VIRTUAL, base_foobar, {0_v}),
      dasm(OPCODE_RETURN, {9_v}),
  };

  IRCode* code = m_method->get_code();
  code->push_back(*if_mie);
  code->push_back(insns[0]);
  code->push_back(*goto_mie);
  code->push_back(target1);
  code->push_back(insns[1]);
  code->push_back(insns[2]);
  code->push_back(insns[3]);
  code->push_back(target2);
  code->push_back(insns[4]);
  code->push_back(insns[5]);

  IRTypeChecker checker(m_method);
  checker.run();

  // This should NOT type check successfully due to invoking Base.foobar against
  // an Object
  EXPECT_FALSE(checker.good()) << checker.what();
  EXPECT_NE("OK", checker.what());
}

TEST_F(IRTypeCheckerTest, invokeInitAfterNewInstance) {
  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LFoo;.<init>:()V")
      )
    )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
  }
  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
      )
    )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (move-object v1 v0)
        (return-object v1)
      )
    )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.good());
    EXPECT_THAT(checker.what(),
                MatchesRegex("^Use of uninitialized variable.*"));
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (move-object v1 v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (return-object v1)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (move-object v1 v0)
      (return-object v1)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.good());
    EXPECT_THAT(checker.what(),
                MatchesRegex("^Use of uninitialized variable.*"));
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (new-instance "LFoo;")
        (move-result-pseudo-object v5)
        (invoke-direct (v5) "LFoo;.<init>:()V")
        (return-object v5)
        (return-object v0)
      )
    )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
  }
}

TEST_F(IRTypeCheckerTest, invokeInitOfSuperTypeAfterNewInstanceDefault) {
  auto* const type_super = DexType::make_type("LSuper;");
  auto* const type_sub = DexType::make_type("LSub;");

  ClassCreator cls_super_creator(type_super);
  cls_super_creator.set_super(type::java_lang_Object());
  auto* super_ctor = DexMethod::make_method("LSuper;.<init>:()V")
                         ->make_concrete(ACC_PUBLIC, false);
  cls_super_creator.add_method(super_ctor);
  cls_super_creator.create();

  ClassCreator cls_sub_creator(type_sub);
  cls_sub_creator.set_super(type_super);
  cls_sub_creator.create();

  auto* method =
      DexMethod::make_method("LFoo;.bar:()LSub;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
      (
        (new-instance "LSub;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LSuper;.<init>:()V")
        (return-object v0)
      )
    )"));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_FALSE(checker.good()) << checker.what(); // should fail
}

TEST_F(IRTypeCheckerTest, invokeInitOfSuperTypeAfterNewInstanceRelaxed) {
  auto* const type_super = DexType::make_type("LSuper;");
  auto* const type_sub = DexType::make_type("LSub;");

  ClassCreator cls_super_creator(type_super);
  cls_super_creator.set_super(type::java_lang_Object());
  auto* super_ctor = DexMethod::make_method("LSuper;.<init>:()V")
                         ->make_concrete(ACC_PUBLIC, false);
  cls_super_creator.add_method(super_ctor);
  cls_super_creator.create();

  ClassCreator cls_sub_creator(type_sub);
  cls_sub_creator.set_super(type_super);
  cls_sub_creator.create();

  auto* method =
      DexMethod::make_method("LFoo;.bar:()LSub;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
      (
        (new-instance "LSub;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LSuper;.<init>:()V")
        (return-object v0)
      )
    )"));
  IRTypeChecker checker(method);
  checker.relaxed_init_check(); // enabling the relaxed init-check
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what(); // should succeed
}

TEST_F(IRTypeCheckerTest, checkNoOverwriteThis) {
  // Good
  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v1 0)
        (return-object v0)
      )
    )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
  }
  // Bad: virtual method
  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v0 0) ; overwrites `this` register
        (return-object v0)
      )
    )"));
    IRTypeChecker checker(method);
    checker.check_no_overwrite_this();
    checker.run();
    EXPECT_FALSE(checker.good());
    EXPECT_EQ(checker.what(),
              "Encountered overwrite of `this` register by CONST v0, 0");
  }
  // Bad: non-static (private) direct method
  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LBar;)LFoo;")
                       ->make_concrete(ACC_PRIVATE, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v0 0) ; overwrites `this` register
        (return-object v0)
      )
    )"));
    IRTypeChecker checker(method);
    checker.check_no_overwrite_this();
    checker.run();
    EXPECT_FALSE(checker.good());
    EXPECT_EQ(checker.what(),
              "Encountered overwrite of `this` register by CONST v0, 0");
  }
}

TEST_F(IRTypeCheckerTest, loadParamVirtualFail) {
  m_virtual_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param v0)
        (const v1 0)
        (return-object v1)
      )
    )"));
  IRTypeChecker checker(m_virtual_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^First parameter must be loaded with "
                           "load-param-object: IOPCODE_LOAD_PARAM v0$"));
}

TEST_F(IRTypeCheckerTest, loadParamVirtualSuccess) {
  m_virtual_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param v1)
        (load-param v2)
        (load-param-wide v3)
        (load-param v4)
        (load-param-wide v5)
        (load-param v6)
        (load-param v7)
        (load-param-object v8)
        (return-object v8)
      )
    )"));
  IRTypeChecker checker(m_virtual_method);
  checker.run();
  EXPECT_FALSE(checker.fail());
}

TEST_F(IRTypeCheckerTest, loadParamStaticCountSuccess) {
  m_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param v0)
        (load-param v1)
        (load-param-wide v2)
        (load-param v3)
        (load-param-wide v4)
        (load-param v5)
        (load-param v6)
        (load-param-object v7)
        (const v7 0)
        (return-object v7)
      )
    )"));
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_FALSE(checker.fail());
}

TEST_F(IRTypeCheckerTest, loadParamStaticCountLessFail) {
  m_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param v0)
        (load-param v1)
        (load-param-wide v2)
        (const v3 0)
        (return-object v3)
      )
    )"));
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_EQ(checker.what(),
            "Number of existing load-param instructions (3) is lower than "
            "expected (8)");
}

TEST_F(IRTypeCheckerTest, loadParamInstanceCountLessFail) {
  m_virtual_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (const v3 0)
        (return-object v3)
      )
    )"));
  IRTypeChecker checker(m_virtual_method);
  checker.run();
  EXPECT_EQ(checker.what(),
            "Number of existing load-param instructions (1) is lower than "
            "expected (9)");
}

TEST_F(IRTypeCheckerTest, loadParamInstanceCountMoreFail) {
  m_virtual_method->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param v1)
        (load-param v2)
        (load-param-wide v3)
        (load-param v4)
        (load-param-wide v5)
        (load-param v6)
        (load-param v7)
        (load-param-object v8)
        (load-param v9)
        (const v7 0)
        (return-object v7)
      )
    )"));
  IRTypeChecker checker(m_virtual_method);
  checker.run();
  EXPECT_EQ(checker.what(),
            "Not enough argument types for IOPCODE_LOAD_PARAM v9");
}

TEST_F(IRTypeCheckerTest, loadParamStaticCountMoreFail) {
  m_method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (load-param v1)
      (load-param-wide v2)
      (load-param v3)
      (load-param-wide v4)
      (load-param v5)
      (load-param v6)
      (load-param-object v7)
      (load-param v8)
      (return-object v7)
    )
    )"));
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_EQ(checker.what(),
            "Not enough argument types for IOPCODE_LOAD_PARAM v8");
}

/**
 * v0 not compatible with field type
 *
 * class A { B f; } -> v1
 * class B {}
 * class C {}       -> v0
 *
 * iput-object C (v0), A (v1), "LA;.f:LB;"
 *
 */
TEST_F(IRTypeCheckerTest, putObjectFieldIncompatibleTypeFail) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");
  auto* const type_c = DexType::make_type("LC;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  cls_b_creator.create();

  ClassCreator cls_c_creator(type_c);
  cls_c_creator.set_super(type::java_lang_Object());
  auto* c_ctor = DexMethod::make_method("LC;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_c_creator.add_method(c_ctor);
  cls_c_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // type c
      dasm(OPCODE_NEW_INSTANCE, type_c),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, c_ctor, {0_v}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {2_v}),

      dasm(OPCODE_IPUT_OBJECT, a_f, {0_v, 1_v}),
      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Type error in method testMethod at instruction "
                           "'IPUT_OBJECT v0, v1, LA;.f:LB;' "
                           "@ 0x[0-9a-f]+ for : LC; is not assignable to "
                           "LB;\nC\n-> java.lang.Object\n"));
}

/**
 * v1 not compatible with field class
 *
 * class A { B f; } -> v1
 * class B {}       -> v0
 * class C { B f; }
 *
 * iput-object B (v0), A (v1), "LC;.f:LB;"
 *
 */
TEST_F(IRTypeCheckerTest, putObjectFieldIncompatibleClassFail) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");
  auto* const type_c = DexType::make_type("LC;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  cls_b_creator.create();

  ClassCreator cls_c_creator(type_c);
  cls_c_creator.set_super(type::java_lang_Object());
  auto* c_ctor = DexMethod::make_method("LC;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  auto* c_f = DexField::make_field("LC;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_c_creator.add_field(c_f);
  cls_c_creator.add_method(c_ctor);
  cls_c_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),
      // type c
      dasm(OPCODE_NEW_INSTANCE, type_c),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, c_ctor, {2_v}),

      dasm(OPCODE_IPUT_OBJECT, c_f, {0_v, 1_v}),
      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Type error in method testMethod at instruction "
                           "'IPUT_OBJECT v0, v1, LC;.f:LB;' "
                           "@ 0x[0-9a-f]+ for : LA; is not assignable to "
                           "LC;\nA\n-> java.lang.Object\n"));
}

/**
 * iput-object success
 *
 * class A { B f; } -> v1
 * class B {}       -> v0
 *
 * iput-object B (v0), A (v1), "LA;.f:LB;"
 *
 */
TEST_F(IRTypeCheckerTest, putObjectSuccess) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  cls_b_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),

      dasm(OPCODE_IPUT_OBJECT, a_f, {0_v, 1_v}),
      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good());
}

/**
 * v1 not compatible with field class
 *
 * class A { B f; } -> v1
 * class B {}       -> v0
 * class C { B f; }
 *
 * iget-object B (v0), A (v1), "LC;.f:LB;"
 *
 */
TEST_F(IRTypeCheckerTest, getObjectFieldIncompatibleClassFail) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");
  auto* const type_c = DexType::make_type("LC;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  cls_b_creator.create();

  ClassCreator cls_c_creator(type_c);
  cls_c_creator.set_super(type::java_lang_Object());
  auto* c_ctor = DexMethod::make_method("LC;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  auto* c_f = DexField::make_field("LC;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_c_creator.add_field(c_f);
  cls_c_creator.add_method(c_ctor);
  cls_c_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),
      // type c
      dasm(OPCODE_NEW_INSTANCE, type_c),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, c_ctor, {2_v}),

      dasm(OPCODE_IGET_OBJECT, c_f, {1_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Type error in method testMethod at instruction "
                           "'IGET_OBJECT v1, LC;.f:LB;' "
                           "@ 0x[0-9a-f]+ for : LA; is not assignable to "
                           "LC;\nA\n-> java.lang.Object\n"));
}

/**
 * iget-object success
 *
 * class A { B f; } -> v1
 * class B {}       -> v0
 *
 * iget-object B (v0), A (v1), "LA;.f:LB;
 *
 */
TEST_F(IRTypeCheckerTest, getObjectSuccess) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:LB;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  cls_b_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {0_v}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),

      dasm(OPCODE_IGET_OBJECT, a_f, {1_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good());
}

/**
 * v1 not compatible with field class
 *
 * class A { int f; } -> v1
 * int   2            -> v0
 * class B { int f; }
 *
 * iput 2 (v0), A (v1), "LB;.f:I;"
 *
 */
TEST_F(IRTypeCheckerTest, putInstanceFieldIncompatibleClassFail) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_f = DexField::make_field("LB;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_b_creator.add_field(b_f);
  cls_b_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // literal 2
      dasm(OPCODE_CONST, {0_v, 2_L}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {2_v}),

      dasm(OPCODE_IPUT, b_f, {0_v, 1_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Type error in method testMethod at instruction "
                           "'IPUT v0, v1, LB;.f:I;' "
                           "@ 0x[0-9a-f]+ for : LA; is not assignable to "
                           "LB;\nA\n-> java.lang.Object\n"));
}

/**
 * iput success
 *
 * class A { int f; } -> v1
 * int   2            -> v0
 *
 * iput 2 (v0), A (v1), "LA;.f:I;"
 *
 */
TEST_F(IRTypeCheckerTest, putInstanceSuccess) {
  auto* const type_a = DexType::make_type("LA;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // literal 2
      dasm(OPCODE_CONST, {0_v, 2_L}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v}),

      dasm(OPCODE_IPUT, a_f, {0_v, 1_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good());
}

/**
 * v1 not compatible with field class
 *
 * class A { int f = 2; } -> v1
 *
 * class B { int f; }
 *
 * iget v0, A (v1), "LB;.f:I;"
 *
 */
TEST_F(IRTypeCheckerTest, getInstanceFieldIncompatibleClassFail) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:(I)V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_f = DexField::make_field("LB;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_b_creator.add_field(b_f);
  cls_b_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // literal 2
      dasm(OPCODE_CONST, {3_v, 2_L}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v, 3_v}),
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {2_v}),

      dasm(OPCODE_IGET, b_f, {1_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(),
              MatchesRegex("^Type error in method testMethod at instruction "
                           "'IGET v1, LB;.f:I;' "
                           "@ 0x[0-9a-f]+ for : LA; is not assignable to "
                           "LB;\nA\n-> java.lang.Object\n"));
}

/**
 * Same as above, but with deeper hierarchy.
 *
 */
TEST_F(IRTypeCheckerTest, deepClassFailPrinting) {
  auto* const type_a = DexType::make_type("LA;");
  auto* const type_b = DexType::make_type("LB;");

  constexpr size_t kClasses = 5;

  std::vector<DexType*> types;
  types.reserve(kClasses);
  for (size_t i = 0; i != kClasses; ++i) {
    types.push_back(DexType::make_type("LX" + std::to_string(i) + ";"));
  }
  std::vector<DexType*> intfs;
  intfs.reserve(kClasses);
  for (size_t i = 0; i != kClasses; ++i) {
    intfs.push_back(DexType::make_type("LI" + std::to_string(i) + ";"));
  }
  auto* const type_y = DexType::make_type("LY;"); // Type without class.

  for (size_t i = 0; i != kClasses; ++i) {
    ClassCreator cls_x_creator(types[i]);
    cls_x_creator.set_super(i == 0 ? type_y : types[i - 1]);
    cls_x_creator.add_interface(intfs[i]);
    auto* x_ctor = DexMethod::make_method(show(types[i]) + ".<init>:(I)V")
                       ->make_concrete(ACC_PUBLIC, false);
    cls_x_creator.add_method(x_ctor);
    auto* x_f = DexField::make_field(show(types[i]) + ".f:I;")
                    ->make_concrete(ACC_PUBLIC);
    cls_x_creator.add_field(x_f);
    cls_x_creator.create();
  }

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(types[kClasses - 1]);
  auto* a_ctor = DexMethod::make_method("LA;.<init>:(I)V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  ClassCreator cls_b_creator(type_b);
  cls_b_creator.set_super(type::java_lang_Object());
  auto* b_ctor = DexMethod::make_method("LB;.<init>:()V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_b_creator.add_method(b_ctor);
  auto* b_f = DexField::make_field("LB;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_b_creator.add_field(b_f);
  cls_b_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // literal 2
      dasm(OPCODE_CONST, {3_v, 2_L}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v, 3_v}),
      // type b
      dasm(OPCODE_NEW_INSTANCE, type_b),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
      dasm(OPCODE_INVOKE_DIRECT, b_ctor, {2_v}),

      dasm(OPCODE_IGET, b_f, {1_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(
      checker.what(),
      MatchesRegex("^Type error in method testMethod at instruction 'IGET v1, "
                   "LB;.f:I;' @ 0x[0-9a-f]+ for : LA; is not assignable to "
                   "LB;\nA\n-> X4 \\(implements I4\\)\n---> X3 \\(implements "
                   "I3\\)\n-----> X2 \\(implements I2\\)\n-------> X1 "
                   "\\(implements I1\\)\n---------> X0 \\(implements "
                   "I0\\)\n-----------> Y \\(no class\\)\n"));
  // Should look like this:
  // Type error in method ...
  // A
  // -> X4 (implements I4)
  // ---> X3 (implements I3)
  // -----> X2 (implements I2)
  // -------> X1 (implements I1)
  // ---------> X0 (implements I0)
  // -----------> Y (no class)
}

/**
 * iget success
 *
 * class A { int f = 2; } -> v1
 *
 * iget v0, A (v1), "LA;.f:I;"
 *
 */
TEST_F(IRTypeCheckerTest, getInstanceSuccess) {
  auto* const type_a = DexType::make_type("LA;");

  ClassCreator cls_a_creator(type_a);
  cls_a_creator.set_super(type::java_lang_Object());
  auto* a_ctor = DexMethod::make_method("LA;.<init>:(I)V")
                     ->make_concrete(ACC_PUBLIC, false);
  cls_a_creator.add_method(a_ctor);
  auto* a_f = DexField::make_field("LA;.f:I;")->make_concrete(ACC_PUBLIC);
  cls_a_creator.add_field(a_f);
  cls_a_creator.create();

  using namespace dex_asm;
  std::vector<IRInstruction*> insns = {
      // literal 2
      dasm(OPCODE_CONST, {3_v, 2_L}),
      // type a
      dasm(OPCODE_NEW_INSTANCE, type_a),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
      dasm(OPCODE_INVOKE_DIRECT, a_ctor, {1_v, 3_v}),

      dasm(OPCODE_IGET, a_f, {1_v}),
      dasm(IOPCODE_MOVE_RESULT_PSEUDO, {0_v}),

      dasm(OPCODE_RETURN_VOID),
  };

  add_code(insns);
  IRTypeChecker checker(m_method);
  checker.run();
  EXPECT_TRUE(checker.good());
}

/**
 * v1 not compatible with field class
 *
 * class A { short f; } -> v1
 * short 1              -> v3
 * class B { short f; }
 *
 * iput-short 1 (v3), A (v1), "LB;.f:S;"
 *
 */
TEST_F(IRTypeCheckerTest, putShortFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IPUT_SHORT v3, v1, LB;.f:S;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IPUT_SHORT;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:S;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:S;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             true, SHORT, m_method));
}

/**
 * iput-short success
 *
 * class A { short f; } -> v1
 * short 1              -> v3
 *
 * iput-short 1 (v3), A (v1), "LA;.f:S;"
 *
 */
TEST_F(IRTypeCheckerTest, putShortSuccess) {

  IROpcode op = OPCODE_IPUT_SHORT;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:S;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:()V",
                         "LAsub;.f:S;");

  field_compatible_success_helper(a_type, sub_type, op, true, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { short f = 1; } -> v1
 *
 * class B { short f; }
 *
 * iget-short v3, A (v1), "LB;.f:S;"
 *
 */
TEST_F(IRTypeCheckerTest, getShortFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IGET_SHORT v1, LB;.f:S;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";
  IROpcode op = OPCODE_IGET_SHORT;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(S)V",
                       "LA;.f:S;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:S;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             false, SHORT, m_method));
}

/**
 * iget-short success
 *
 * class A { short f = 1; } -> v1
 *
 * iget-short v3, A (v1), "LA;.f:S;"
 *
 */
TEST_F(IRTypeCheckerTest, getShortSuccess) {

  IROpcode op = OPCODE_IGET_SHORT;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(S)V",
                       "LA;.f:S;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:(S)V",
                         "LAsub;.f:S;");

  field_compatible_success_helper(a_type, sub_type, op, false, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { boolean f; }    -> v1
 * boolean true              -> v3
 * class B { boolean f; }
 *
 * iput-boolean true (v3), A (v1), "LB;.f:Z;"
 *
 */
TEST_F(IRTypeCheckerTest, putBoolFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IPUT_BOOLEAN v3, v1, LB;.f:Z;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IPUT_BOOLEAN;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:Z;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:Z;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             true, SHORT, m_method));
}

/**
 * iput-boolean success
 *
 * class A { boolean f; }    -> v1
 * boolean true              -> v3
 * class Asub extends A {};  -> v2
 *
 * iput-boolean true (v3), Asub (v2), "LA;.f:Z;"
 *
 */
TEST_F(IRTypeCheckerTest, putBoolSuccess) {

  IROpcode op = OPCODE_IPUT_BOOLEAN;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:Z;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:()V",
                         "LAsub;.f:Z;");

  field_compatible_success_helper(a_type, sub_type, op, true, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { boolean f = true; } -> v1
 *
 * class B { boolean f; }
 *
 * iget-boolean v0, A (v1), "LB;.f:Z;"
 *
 */
TEST_F(IRTypeCheckerTest, getBoolFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IGET_BOOLEAN v1, LB;.f:Z;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IGET_BOOLEAN;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(Z)V",
                       "LA;.f:Z;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:Z;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             false, SHORT, m_method));
}

/**
 * iget-boolean success
 *
 * class A {boolean f = true}                 -> v1
 *
 * class Asub extends A {boolean f = true;};  -> v2
 *
 * iget-boolean v0, Asub (v2), "LA;.f:Z;"
 *
 */
TEST_F(IRTypeCheckerTest, getBoolSuccess) {

  IROpcode op = OPCODE_IGET_BOOLEAN;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(Z)V",
                       "LA;.f:Z;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:(Z)V",
                         "LAsub;.f:Z;");

  field_compatible_success_helper(a_type, sub_type, op, false, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { long f; }    -> v1
 * long 1L                -> v3
 * class B { long f; }    -> v2
 *
 * iput-wide 1L (v3), A (v1), "LB;.f:J;"
 *
 */
TEST_F(IRTypeCheckerTest, putWideFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IPUT_WIDE v3, v1, LB;.f:J;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IPUT_WIDE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:J;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:J;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             true, WIDE, m_method));
}

/**
 * iput-wide success
 *
 * class A { long f; }      -> v1
 * long 1L                  -> v3
 * class Asub extends A {}; -> v2
 *
 * iput-wide 1L (v3), Asub (v2), "LA;.f:J;"
 *
 */
TEST_F(IRTypeCheckerTest, putWideSuccess) {

  IROpcode op = OPCODE_IPUT_WIDE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:J;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:()V",
                         "LAsub;.f:J;");

  field_compatible_success_helper(a_type, sub_type, op, true, WIDE, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { long f = 1L; } -> v1
 *
 * class B { long f; }
 *
 * iget-wide v5, A (v1), "LB;.f:J;"
 *
 */
TEST_F(IRTypeCheckerTest, getWideFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IGET_WIDE v1, LB;.f:J;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IGET_WIDE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(J)V",
                       "LA;.f:J;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:J;");
  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             false, WIDE, m_method));
}

/**
 * iget-wide success
 *
 * class A {long f = 1L}                 -> v1
 *
 * class Asub extends A {long f = 1L;};  -> v2
 *
 * iget-wide v5, Asub (v2), "LA;.f:J;"
 *
 */
TEST_F(IRTypeCheckerTest, getWideSuccess) {

  IROpcode op = OPCODE_IGET_WIDE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(J)V",
                       "LA;.f:J;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:(J)V",
                         "LAsub;.f:J;");
  field_compatible_success_helper(a_type, sub_type, op, false, WIDE, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { byte f; }    -> v1
 * byte 1                 -> v3
 * class B { byte f; }    -> v2
 *
 * iput-byte 1 (v3), A (v1), "LB;.f:B;"
 *
 */
TEST_F(IRTypeCheckerTest, putByteFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IPUT_BYTE v3, v1, LB;.f:B;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IPUT_BYTE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:B;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:B;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             true, SHORT, m_method));
}

/**
 * iput-byte success
 *
 * class A { byte f; }       -> v1
 * byte 1                    -> v3
 * class Asub extends A {};  -> v2
 *
 * iput-byte 1 (v3), Asub (v2), "LA;.f:B;"
 *
 */
TEST_F(IRTypeCheckerTest, putByteSuccess) {

  IROpcode op = OPCODE_IPUT_BYTE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:B;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:()V",
                         "LAsub;.f:B;");

  field_compatible_success_helper(a_type, sub_type, op, true, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { byte f = 1; } -> v1
 *
 * class B { byte f; }
 *
 * iget-byte v0, A (v1), "LB;.f:B;"
 *
 */
TEST_F(IRTypeCheckerTest, getByteFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IGET_BYTE v1, LB;.f:B;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IGET_BYTE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(B)V",
                       "LA;.f:B;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:B;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             false, SHORT, m_method));
}

/**
 * iget-byte success
 *
 * class A {byte f = 1}                 -> v1
 *
 * class Asub extends A {byte f = 1;};  -> v2
 *
 * iget-byte v0, Asub (v2), "LA;.f:B;"
 *
 */
TEST_F(IRTypeCheckerTest, getByteSuccess) {

  IROpcode op = OPCODE_IGET_BYTE;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(B)V",
                       "LA;.f:B;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:(B)V",
                         "LAsub;.f:B;");

  field_compatible_success_helper(a_type, sub_type, op, false, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { char f; }    -> v1
 * char  1                -> v3
 * class B { char f; }    -> v2
 *
 * iput-char 1 (v3), A (v1), "LB;.f:C;"
 *
 */
TEST_F(IRTypeCheckerTest, putCharFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IPUT_CHAR v3, v1, LB;.f:C;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IPUT_CHAR;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:C;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:C;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             true, SHORT, m_method));
}

/**
 * iput-char success
 *
 * class A { char f; }       -> v1
 * char 1                    -> v3
 * class Asub extends A {};  -> v2
 *
 * iput-char 1 (v3), Asub (v2), "LA;.f:C;"
 *
 */
TEST_F(IRTypeCheckerTest, putCharSuccess) {

  IROpcode op = OPCODE_IPUT_CHAR;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:()V",
                       "LA;.f:C;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:()V",
                         "LAsub;.f:C;");

  field_compatible_success_helper(a_type, sub_type, op, true, SHORT, m_method);
}

/**
 * v1 not compatible with field class
 *
 * class A { char f = 1; } -> v1
 *
 * class B { char f; }
 *
 * iget-char v0, A (v1), "LB;.f:C;"
 *
 */
TEST_F(IRTypeCheckerTest, getCharFieldIncompatibleClassFail) {

  const std::string exp_fail_str =
      "^Type error in method testMethod at instruction "
      "'IGET_CHAR v1, LB;.f:C;' "
      "@ 0x[0-9a-f]+ for : LA; is not assignable to LB;\nA\n-> "
      "java.lang.Object\n";

  IROpcode op = OPCODE_IGET_CHAR;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_b = DexType::make_type("LB;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(C)V",
                       "LA;.f:C;");
  TestValueType b_type(dex_type_b, type::java_lang_Object(), "LB;.<init>:()V",
                       "LB;.f:C;");

  EXPECT_TRUE(field_incompatible_fail_helper(a_type, b_type, exp_fail_str, op,
                                             false, SHORT, m_method));
}

/**
 * iget-char success
 *
 * class A {char f = 1}                 -> v1
 *
 * class Asub extends A {char f = 1};   -> v2
 *
 * iget-char v0, Asub (v2), "LA;.f:C;"
 *
 */
TEST_F(IRTypeCheckerTest, getCharSuccess) {

  IROpcode op = OPCODE_IGET_CHAR;
  auto* const dex_type_a = DexType::make_type("LA;");
  auto* const dex_type_asub = DexType::make_type("LAsub;");

  TestValueType a_type(dex_type_a, type::java_lang_Object(), "LA;.<init>:(C)V",
                       "LA;.f:C;");
  TestValueType sub_type(dex_type_asub, dex_type_a, "LAsub;.<init>:(C)V",
                         "LAsub;.f:C;");

  field_compatible_success_helper(a_type, sub_type, op, false, SHORT, m_method);
}

template <bool kVirtual>
class LoadParamMutationTest : public IRTypeCheckerTest {
 public:
  void run() {
    IRCode* code = (kVirtual ? m_virtual_method : m_method)->get_code();
    recurse(code, code->begin());
  }

  void recurse(IRCode* code, IRList::iterator it) {
    if (it == code->end()) {
      return;
    }

    if (it->type == MFLOW_OPCODE &&
        opcode::is_a_load_param(it->insn->opcode())) {
      auto real_op = it->insn->opcode();
      for (auto op = IOPCODE_LOAD_PARAM; op <= IOPCODE_LOAD_PARAM_WIDE;
           op = static_cast<IROpcode>(static_cast<uint16_t>(op) + 1)) {
        if (op == real_op) {
          continue;
        }
        it->insn->set_opcode(op);
        check_fail();
      }
      it->insn->set_opcode(real_op);
    }

    ++it;
    recurse(code, it);
  }

  void check_fail() {
    IRTypeChecker checker(kVirtual ? m_virtual_method : m_method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }
};

using LoadParamMutationStaticTest = LoadParamMutationTest<false>;
using LoadParamMutationVirtualTest = LoadParamMutationTest<true>;

TEST_F(LoadParamMutationStaticTest, mutate) { run(); }
TEST_F(LoadParamMutationVirtualTest, mutate) { run(); }

TEST_F(IRTypeCheckerTest, invokeSuperInterfaceMethod) {
  // Construct type hierarchy.
  auto* const interface_type = DexType::make_type("LI;");
  ClassCreator interface_type_creator(interface_type);
  interface_type_creator.set_super(type::java_lang_Object());
  interface_type_creator.set_access(ACC_INTERFACE);
  auto* foo_method =
      DexMethod::make_method("LI;.foo:()V")->make_concrete(ACC_PUBLIC, true);
  interface_type_creator.add_method(foo_method);
  interface_type_creator.create();

  // Construct code that references the above hierarchy.
  using namespace dex_asm;
  IRCode* code = m_method->get_code();
  code->push_back(dasm(OPCODE_CONST, {0_v, 0_L}));
  code->push_back(dasm(OPCODE_INVOKE_SUPER, foo_method, {0_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(m_method);
  checker.run();
  // Checks
  EXPECT_FALSE(checker.good());
  EXPECT_THAT(checker.what(),
              MatchesRegex(".*\nillegal invoke-super to interface method.*"));
}

TEST_F(IRTypeCheckerTest, synchronizedThrowOutsideCatchAllInTry) {
  auto* method = DexMethod::make_method("LFoo;.bar:()V;")
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (monitor-enter v0)

      (.try_start a)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (.try_end a)

      (.catch (a) "LMyThrowable;")
      (monitor-exit v0)

      (return-void)
    )
  )"));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokePolymorphic) {
  // Mimic java.lang.invoke.MethodHandle as closely as possible.
  auto* const type_method_handle =
      DexType::make_type("Ljava/lang/invoke/MethodHandle;");
  ClassCreator method_handle_creator(type_method_handle);
  auto* invoke_method =
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/"
          "lang/Object;)Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_FINAL | ACC_VARARGS,
                          /* is_virtual */ false);
  method_handle_creator.add_method(invoke_method);
  method_handle_creator.set_super(type::java_lang_Object());
  method_handle_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  method_handle_creator.create();

  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method =
      DexMethod::make_method("LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const-string "S1")
      (move-result-pseudo-object v1)
      (const-string "S2")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/String;)V")
      (invoke-polymorphic (v0 v1 v2) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/String;Ljava/lang/String;)V")
      (return-void)
  ))"));
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();

  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

TEST_F(IRTypeCheckerTest, invokePolymorphicOnUnexpectedExternalMethod) {
  // Mimic java.lang.invoke.MethodHandle.invoke as closely as possible except
  // name.
  auto* const type_method_handle =
      DexType::make_type("Ljava/lang/invoke/MethodHandle;");
  ClassCreator method_handle_creator(type_method_handle);
  auto* not_invoke_method =
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.notInvoke:([Ljava/"
          "lang/Object;)Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_FINAL | ACC_VARARGS,
                          /* is_virtual */ false);
  method_handle_creator.add_method(not_invoke_method);
  method_handle_creator.set_super(type::java_lang_Object());
  method_handle_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  method_handle_creator.create();

  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method =
      DexMethod::make_method("LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const-string "S1")
      (move-result-pseudo-object v1)
      (const-string "S2")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v0 v1 v2) "Ljava/lang/invoke/MethodHandle;.notInvoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/String;Ljava/lang/String;)V")
      (return-void)
  ))"));
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();

  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(checker.what(),
              HasSubstr("invoke-polymorphic: Callee must be either "
                        "MethodHandle.invoke or MethodHandle.invokeExact"));
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokePolymorphicOnWrongArgMethod) {
  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method = DexMethod::make_method("LFoo;.bar:()V;")
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-polymorphic (v0) "LFoo;.bar:()V" "()V")
      (return-void)
  ))"));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(
      checker.what(),
      ContainsRegex("invoke-polymorphic.*Arg count.*is expected to be 1"));
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokePolymorphicOnFixedArgMethod) {
  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method = DexMethod::make_method("LFoo;.bar:(Ljava/lang/Object;)V;")
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-polymorphic (v0 v1) "LFoo;.bar:(Ljava/lang/Object;)V" "(Ljava/lang/Object;)V")
      (return-void)
  ))"));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(checker.what(),
              ContainsRegex("invoke-polymorphic.*is expected to be an array"));
  EXPECT_TRUE(checker.fail());
}

// A move-result reads the result of a method handle call.
TEST_F(IRTypeCheckerTest, moveResultAfterInvokePolymorphic) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "()Ljava/lang/Object;")
      (move-result-object v1)
      (return-void)
     )
    )
  )");
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

// A static initializer that calls a method handle:
//
//   static final long START = (long) NOW.invokeExact();
TEST_F(IRTypeCheckerTest, invokePolymorphicWideResult) {
  auto* method = assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
     (
      (sget-object "LFoo;.NOW:Ljava/lang/invoke/MethodHandle;")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()J")
      (move-result-wide v1)
      (sput-wide v1 "LFoo;.START:J")
      (return-void)
     )
    )
  )");
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

TEST_F(IRTypeCheckerTest, invokePolymorphicResultMismatchIsAnError) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()J")
      (move-result-object v1)
      (return-void)
     )
    )
  )");
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokeOnClassInitializer) {
  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (invoke-static () "LFoo;.<clinit>:()V")
      (return-void)
  ))"));
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(checker.what(), HasSubstr("invoking a class initializer"));
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokeDirectOnConstructor) {
  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (invoke-static () "LFoo;.<init>:()V")
      (return-void)
  ))"));
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  // Set to public to eliminate potential failure due to access check.
  cls_foo_creator.set_access(ACC_PUBLIC);
  cls_foo_creator.create();
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(checker.what(),
              HasSubstr("invoking a constructor with an unexpected opcode"));
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, checkVirtualPrivateMethod) {
  auto* const type_foo = DexType::make_type("LFoo;");
  ClassCreator cls_foo_creator(type_foo);
  auto* method = DexMethod::make_method("LFoo;.bar:()V")
                     ->make_concrete(ACC_PRIVATE, /* is_virtual */ true);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (return-void)
  ))"));
  cls_foo_creator.add_method(method);
  cls_foo_creator.set_super(type::java_lang_Object());
  cls_foo_creator.create();
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_THAT(checker.what(),
              HasSubstr("A method cannot be both private and virtual"));
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, invokeVirtualOnInterfaceMethod) {
  auto* const interface_type = DexType::make_type("LI;");
  ClassCreator interface_type_creator(interface_type);
  interface_type_creator.set_super(type::java_lang_Object());
  interface_type_creator.set_access(ACC_INTERFACE);
  auto* foo_method =
      DexMethod::make_method("LI;.foo:()V")->make_concrete(ACC_PUBLIC, true);
  interface_type_creator.add_method(foo_method);
  interface_type_creator.create();

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LI;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-virtual (v1) "LI;.foo:()V")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LI;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-interface (v1) "LI;.foo:()V")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail());
  }
}

TEST_F(IRTypeCheckerTest, sputObjectPass) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.add_field(DexField::make_field("LA;.f:LA;")
                                ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    cls_a_creator.create();
  }

  auto* const type_b = DexType::make_type("LB;");
  {
    ClassCreator cls_b_creator(type_b);
    cls_b_creator.set_super(type_a);
    cls_b_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:LA;")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail());
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(LB;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:LA;")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail());
  }
}

TEST_F(IRTypeCheckerTest, sputObjectFail) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.add_field(DexField::make_field("LA;.f:LA;")
                                ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    cls_a_creator.create();
  }

  auto* const type_b = DexType::make_type("LB;");
  {
    ClassCreator cls_b_creator(type_b);
    cls_b_creator.set_super(type::java_lang_Object());
    cls_b_creator.create();
  }

  auto* method = DexMethod::make_method("LFoo;.bar:(LB;)V;")
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:LA;")
      (return-void)
    )
  )"));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}

TEST_F(IRTypeCheckerTest, sputObjectArrayFail) {
  auto* const type_a = DexType::make_type("LA;");
  [[maybe_unused]] auto* const type_a_arr = type::make_array_type(type_a);

  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.add_field(DexField::make_field("LA;.f:[LA;")
                                ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    cls_a_creator.create();
  }

  auto* const type_b = DexType::make_type("LB;");
  {
    ClassCreator cls_b_creator(type_b);
    cls_b_creator.set_super(type::java_lang_Object());
    cls_b_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:([LA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:[LA;")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail());
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:([[LA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:[LA;")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:([LB;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (sput-object v1 "LA;.f:[LA;")
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }
}

TEST_F(IRTypeCheckerTest, agetArrayTypePass) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(I[LA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (aget-object v2 v1)
      (move-result-pseudo-object v3)
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail()) << checker.what();
  }
}

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aget_opcodes_and_descriptors() {
  return {
      {"aget", {"I", ""}}, // Does not test float. Oh well.
      {"aget-wide", {"J", "-wide"}}, // Does not test double. Oh well.
      {"aget-boolean", {"Z", ""}},
      {"aget-byte", {"B", ""}},
      {"aget-char", {"C", ""}},
      {"aget-short", {"S", ""}},
      {"aget-object", {"LA;", "-object"}},
  };
}

using AgetPairType =
    typename decltype(get_aget_opcodes_and_descriptors())::value_type;

std::string format_param(const AgetPairType& data) {
  std::string name = data.first;
  name.append("_");
  name.append(data.second.first);
  name.append("_");
  name.append(data.second.second);
  std::replace_if(
      name.begin(), name.end(), [](char c) { return std::isalnum(c) == 0; },
      '_');
  return name;
}

} // namespace

class IRTypeCheckerAgetPassTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AgetPairType> {};

TEST_P(IRTypeCheckerAgetPassTest, test) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  const auto& [opcode, type_and_pseudo] = GetParam();
  const auto& [type, pseudo] = type_and_pseudo;
  std::string method_descr =
      std::regex_replace("LFoo;.bar:(I[TYPE)V;", std::regex("TYPE"), type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (OPCODE v2 v1)
      (move-result-pseudoPSEUDO v3)
      (return-void)
    )
    )";
  method->set_code(assembler::ircode_from_string(std::regex_replace(
      std::regex_replace(body_template, std::regex("OPCODE"), opcode),
      std::regex("PSEUDO"), pseudo)));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_FALSE(checker.fail()) << checker.what();
}
INSTANTIATE_TEST_SUITE_P(
    AGetMatching,
    IRTypeCheckerAgetPassTest,
    ::testing::ValuesIn(get_aget_opcodes_and_descriptors()),
    [](const testing::TestParamInfo<IRTypeCheckerAgetPassTest::ParamType>&
           info) { return format_param(info.param); });

TEST_F(IRTypeCheckerTest, agetArrayTypeFail) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(ILA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (aget-object v2 v1)
      (move-result-pseudo-object v3)
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }
}

namespace {

std::vector<std::pair<AgetPairType, AgetPairType>> get_aget_mismatches() {
  std::vector<std::pair<AgetPairType, AgetPairType>> tmp;
  for (auto& lhs : get_aget_opcodes_and_descriptors()) {
    for (auto& rhs : get_aget_opcodes_and_descriptors()) {
      if (lhs.first == rhs.first) {
        continue;
      }
      tmp.emplace_back(lhs, rhs);
    }
  }
  return tmp;
}

using AgetFailType = typename decltype(get_aget_mismatches())::value_type;

} // namespace

class IRTypeCheckerAgetFailTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AgetFailType> {};

TEST_P(IRTypeCheckerAgetFailTest, failArrayType) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  const auto& [lhs, rhs] = GetParam();

  const auto& [opcode1, type_and_pseudo1] = lhs;
  const auto& [type1, pseudo1] = type_and_pseudo1;
  const auto& [opcode2, type_and_pseudo2] = rhs;
  const auto& [type2, pseudo2] = type_and_pseudo2;

  std::string method_descr =
      std::regex_replace("LFoo;.bar:(I[TYPE1)V;", std::regex("TYPE1"), type1);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (OPCODE2 v2 v1)
      (move-result-pseudoPSEUDO2 v3)
      (return-void)
    )
    )";
  method->set_code(assembler::ircode_from_string(std::regex_replace(
      std::regex_replace(body_template, std::regex("OPCODE2"), opcode2),
      std::regex("PSEUDO2"), pseudo2)));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail());
}
INSTANTIATE_TEST_SUITE_P(AGetNotMatching,
                         IRTypeCheckerAgetFailTest,
                         ::testing::ValuesIn(get_aget_mismatches()),
                         [](const testing::TestParamInfo<
                             IRTypeCheckerAgetFailTest::ParamType>& info) {
                           std::string name = format_param(info.param.first);
                           name.append("_");
                           name.append(format_param(info.param.second));
                           return name;
                         });

TEST_F(IRTypeCheckerTest, aputArrayTypePass) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(ILA;[LA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (load-param-object v3)
      (aput-object v2 v3 v1)
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_FALSE(checker.fail());
  }
}

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aput_opcodes_and_descriptors() {
  return {
      {"aput", {"I", ""}}, // Does not test float. Oh well.
      {"aput-wide", {"J", "-wide"}}, // Does not test double. Oh well.
      {"aput-boolean", {"Z", ""}},
      {"aput-byte", {"B", ""}},
      {"aput-char", {"C", ""}},
      {"aput-short", {"S", ""}},
      {"aput-object", {"LA;", "-object"}},
  };
}

using AputPairType =
    typename decltype(get_aput_opcodes_and_descriptors())::value_type;

} // namespace

class IRTypeCheckerAputPassTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputPairType> {};

TEST_P(IRTypeCheckerAputPassTest, test) {
  const auto& [opcode, type_and_loadp] = GetParam();
  const auto& [type, loadp] = type_and_loadp;
  std::string method_descr =
      std::regex_replace("LFoo;.bar:(ITYPE[TYPE)V;", std::regex("TYPE"), type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-paramLOADP v2)
      (load-param-object v4)
      (OPCODE v2 v4 v1)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(std::regex_replace(
      std::regex_replace(body_template, std::regex("LOADP"), loadp),
      std::regex("OPCODE"), opcode)));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_FALSE(checker.fail()) << checker.what();
}
INSTANTIATE_TEST_SUITE_P(
    APutMatching,
    IRTypeCheckerAputPassTest,
    ::testing::ValuesIn(get_aput_opcodes_and_descriptors()),
    [](const testing::TestParamInfo<IRTypeCheckerAputPassTest::ParamType>&
           info) { return format_param(info.param); });

TEST_F(IRTypeCheckerTest, aputArrayTypeFail) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  {
    auto* method = DexMethod::make_method("LFoo;.bar:(ILA;)V;")
                       ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
    method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (aput-object v2 v2 v1)
      (return-void)
    )
  )"));
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.fail());
  }
}

namespace {

std::vector<std::pair<AputPairType, AputPairType>> get_aput_mismatches() {
  std::vector<std::pair<AputPairType, AputPairType>> tmp;
  for (auto& lhs : get_aput_opcodes_and_descriptors()) {
    for (auto& rhs : get_aput_opcodes_and_descriptors()) {
      if (lhs.first == rhs.first) {
        continue;
      }
      tmp.emplace_back(lhs, rhs);
    }
  }
  return tmp;
}

using AputFailType = typename decltype(get_aput_mismatches())::value_type;

} // namespace

class IRTypeCheckerAputFailTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputFailType> {};

TEST_P(IRTypeCheckerAputFailTest, failArrayType) {
  auto* const type_a = DexType::make_type("LA;");
  {
    ClassCreator cls_a_creator(type_a);
    cls_a_creator.set_super(type::java_lang_Object());
    cls_a_creator.create();
  }

  const auto& [lhs, rhs] = GetParam();

  const auto& [opcode1, type_and_loadp1] = lhs;
  const auto& [type1, loadp1] = type_and_loadp1;
  const auto& [opcode2, type_and_loadp2] = rhs;
  const auto& [type2, loadp2] = type_and_loadp2;

  std::string method_descr =
      std::regex_replace(std::regex_replace("LFoo;.bar:(I[TYPE1TYPE2)V;",
                                            std::regex("TYPE1"), type1),
                         std::regex("TYPE2"), type2);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (load-param-object v2)
      (load-paramLOADP2 v3)
      (OPCODE2 v3 v2 v1)
      (return-void)
    )
    )";
  auto body = std::regex_replace(
      std::regex_replace(body_template, std::regex("OPCODE2"), opcode2),
      std::regex("LOADP2"), loadp2);

  method->set_code(assembler::ircode_from_string(body));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail()) << body;
}
INSTANTIATE_TEST_SUITE_P(APutNotMatching,
                         IRTypeCheckerAputFailTest,
                         ::testing::ValuesIn(get_aput_mismatches()),
                         [](const testing::TestParamInfo<
                             IRTypeCheckerAputFailTest::ParamType>& info) {
                           std::string name = format_param(info.param.first);
                           name.append("_");
                           name.append(format_param(info.param.second));
                           return name;
                         });

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aput_intfloat_pass_descriptors() {
  return {
      {"int-int", {"[I", "I"}},     {"int-short", {"[I", "S"}},
      {"int-char", {"[I", "C"}},    {"int-byte", {"[I", "B"}},
      {"int-boolean", {"[I", "Z"}}, {"float-float", {"[F", "F"}},
  };
}

using AputIntFloatPairType =
    typename decltype(get_aput_intfloat_pass_descriptors())::value_type;

} // namespace

class IRTypeCheckerAputIntFloatPassTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputIntFloatPairType> {};

TEST_P(IRTypeCheckerAputIntFloatPassTest, test) {
  const auto& [name, array_type_val_type] = GetParam();
  const auto& [array_type, val_type] = array_type_val_type;
  std::string method_descr =
      std::regex_replace(std::regex_replace("LFoo;.bar:(ATYPEVTYPE)V;",
                                            std::regex("ATYPE"), array_type),
                         std::regex("VTYPE"), val_type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (const v3 0)
      (aput v2 v1 v3)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(body_template));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_FALSE(checker.fail()) << checker.what();
}
INSTANTIATE_TEST_SUITE_P(
    APutIntFloatMatching,
    IRTypeCheckerAputIntFloatPassTest,
    ::testing::ValuesIn(get_aput_intfloat_pass_descriptors()),
    [](const testing::TestParamInfo<
        IRTypeCheckerAputIntFloatPassTest::ParamType>& info) {
      return format_param(info.param);
    });

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aput_intfloat_mismatch_descriptors() {
  return {
      {"float-int", {"[F", "I"}},     {"float-short", {"[F", "S"}},
      {"float-char", {"[F", "C"}},    {"float-byte", {"[F", "B"}},
      {"float-boolean", {"[F", "Z"}}, {"int-float", {"[I", "F"}},
  };
}

using AputIntFloatMissPairType =
    typename decltype(get_aput_intfloat_mismatch_descriptors())::value_type;

} // namespace

class IRTypeCheckerAputIntFloatMismatchTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputIntFloatMissPairType> {};

TEST_P(IRTypeCheckerAputIntFloatMismatchTest, test) {
  const auto& [name, array_type_val_type] = GetParam();
  const auto& [array_type, val_type] = array_type_val_type;
  std::string method_descr =
      std::regex_replace(std::regex_replace("LFoo;.bar:(ATYPEVTYPE)V;",
                                            std::regex("ATYPE"), array_type),
                         std::regex("VTYPE"), val_type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (const v3 0)
      (aput v2 v1 v3)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(body_template));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail()) << method_descr << body_template;
}
INSTANTIATE_TEST_SUITE_P(
    APutIntFloatMismatching,
    IRTypeCheckerAputIntFloatMismatchTest,
    ::testing::ValuesIn(get_aput_intfloat_mismatch_descriptors()),
    [](const testing::TestParamInfo<
        IRTypeCheckerAputIntFloatMismatchTest::ParamType>& info) {
      return format_param(info.param);
    });

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aput_wide_pass_descriptors() {
  return {
      {"long-long", {"[J", "J"}},
      {"double-double", {"[D", "D"}},
  };
}

using AputWidePairType =
    typename decltype(get_aput_wide_pass_descriptors())::value_type;

} // namespace

class IRTypeCheckerAputWidePassTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputWidePairType> {};

TEST_P(IRTypeCheckerAputWidePassTest, test) {
  const auto& [name, array_type_val_type] = GetParam();
  const auto& [array_type, val_type] = array_type_val_type;
  std::string method_descr =
      std::regex_replace(std::regex_replace("LFoo;.bar:(ATYPEVTYPE)V;",
                                            std::regex("ATYPE"), array_type),
                         std::regex("VTYPE"), val_type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param-wide v2)
      (const v4 0)
      (aput-wide v2 v1 v4)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(body_template));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_FALSE(checker.fail()) << checker.what();
}
INSTANTIATE_TEST_SUITE_P(
    APutWideMatching,
    IRTypeCheckerAputWidePassTest,
    ::testing::ValuesIn(get_aput_wide_pass_descriptors()),
    [](const testing::TestParamInfo<IRTypeCheckerAputWidePassTest::ParamType>&
           info) { return format_param(info.param); });

namespace {

std::unordered_map<std::string, std::pair<std::string, std::string>>
get_aput_wide_mismatch_descriptors() {
  return {
      {"long-double", {"[J", "D"}},
      {"double-long", {"[D", "J"}},
  };
}

using AputWideMissPairType =
    typename decltype(get_aput_wide_mismatch_descriptors())::value_type;

} // namespace

class IRTypeCheckerAputWideMismatchTest
    : public IRTypeCheckerTest,
      public ::testing::WithParamInterface<AputWideMissPairType> {};

TEST_P(IRTypeCheckerAputWideMismatchTest, test) {
  const auto& [name, array_type_val_type] = GetParam();
  const auto& [array_type, val_type] = array_type_val_type;
  std::string method_descr =
      std::regex_replace(std::regex_replace("LFoo;.bar:(ATYPEVTYPE)V;",
                                            std::regex("ATYPE"), array_type),
                         std::regex("VTYPE"), val_type);
  auto* method = DexMethod::make_method(method_descr)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);

  const auto* body_template = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param-wide v2)
      (const v4 0)
      (aput-wide v2 v1 v4)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(body_template));
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.fail()) << method_descr << body_template;
}
INSTANTIATE_TEST_SUITE_P(
    APutWideMismatching,
    IRTypeCheckerAputWideMismatchTest,
    ::testing::ValuesIn(get_aput_wide_mismatch_descriptors()),
    [](const testing::TestParamInfo<
        IRTypeCheckerAputWideMismatchTest::ParamType>& info) {
      return format_param(info.param);
    });

class IRTypeCheckerFinalFieldTest : public RedexTest {};

// IPUT to a final field in the correct <init> method should pass.
TEST_F(IRTypeCheckerFinalFieldTest, iput_final_field_in_own_init) {
  using namespace dex_asm;

  auto* owner_type = DexType::make_type("LFinalFieldOwner;");
  auto* field = DexField::make_field("LFinalFieldOwner;.val:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);

  auto* init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* init_method =
      DexMethod::make_method(owner_type, DexString::make_string("<init>"),
                             init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);
  init_method->set_deobfuscated_name("LFinalFieldOwner;.<init>:()V");
  init_method->set_code(
      std::make_unique<IRCode>(init_method, /* temp_regs */ 2));

  ClassCreator cc(owner_type);
  cc.set_super(type::java_lang_Object());
  cc.add_method(init_method);
  cc.add_field(field);
  cc.create();

  // temp_regs=2 means: v0, v1 are temps; v2 is 'this'
  IRCode* code = init_method->get_code();
  code->push_back(dasm(OPCODE_CONST, {0_v, 42_L}));
  code->push_back(dasm(OPCODE_IPUT, field, {0_v, 2_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(init_method);
  checker.validate_access();
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

// IPUT to a final field in a non-constructor method should fail.
TEST_F(IRTypeCheckerFinalFieldTest, iput_final_field_in_non_init) {
  using namespace dex_asm;

  auto* owner_type = DexType::make_type("LFinalFieldOwner2;");
  auto* field = DexField::make_field("LFinalFieldOwner2;.val:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);

  auto* init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* init_method =
      DexMethod::make_method(owner_type, DexString::make_string("<init>"),
                             init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);

  auto* regular_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* regular_method =
      DexMethod::make_method(owner_type, DexString::make_string("setVal"),
                             regular_proto)
          ->make_concrete(ACC_PUBLIC, false);
  regular_method->set_deobfuscated_name("LFinalFieldOwner2;.setVal:()V");
  regular_method->set_code(
      std::make_unique<IRCode>(regular_method, /* temp_regs */ 2));

  ClassCreator cc(owner_type);
  cc.set_super(type::java_lang_Object());
  cc.add_method(init_method);
  cc.add_method(regular_method);
  cc.add_field(field);
  cc.create();

  // temp_regs=2 means: v0, v1 are temps; v2 is 'this'
  IRCode* code = regular_method->get_code();
  code->push_back(dasm(OPCODE_CONST, {0_v, 42_L}));
  code->push_back(dasm(OPCODE_IPUT, field, {0_v, 2_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(regular_method);
  checker.validate_access();
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(), HasSubstr("final instance field"));
}

// IPUT to a final field in a constructor of a different class should fail.
TEST_F(IRTypeCheckerFinalFieldTest, iput_final_field_in_other_class_init) {
  using namespace dex_asm;

  auto* owner_type = DexType::make_type("LFinalFieldOwner3;");
  auto* field = DexField::make_field("LFinalFieldOwner3;.val:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);

  auto* owner_init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* owner_init =
      DexMethod::make_method(owner_type, DexString::make_string("<init>"),
                             owner_init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);

  ClassCreator cc_owner(owner_type);
  cc_owner.set_super(type::java_lang_Object());
  cc_owner.add_method(owner_init);
  cc_owner.add_field(field);
  cc_owner.create();

  auto* other_type = DexType::make_type("LOtherClass3;");
  auto* other_init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* other_init =
      DexMethod::make_method(other_type, DexString::make_string("<init>"),
                             other_init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);
  other_init->set_deobfuscated_name("LOtherClass3;.<init>:()V");
  other_init->set_code(std::make_unique<IRCode>(other_init, /* temp_regs */ 2));

  ClassCreator cc_other(other_type);
  cc_other.set_super(type::java_lang_Object());
  cc_other.add_method(other_init);
  cc_other.create();

  // temp_regs=2 means: v0, v1 are temps; v2 is 'this'
  IRCode* code = other_init->get_code();
  // Create an instance of the owner class and write to its final field
  code->push_back(dasm(OPCODE_NEW_INSTANCE, owner_type));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}));
  code->push_back(dasm(OPCODE_INVOKE_DIRECT, owner_init, {0_v}));
  code->push_back(dasm(OPCODE_CONST, {1_v, 42_L}));
  code->push_back(dasm(OPCODE_IPUT, field, {1_v, 0_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(other_init);
  checker.validate_access();
  checker.run();
  EXPECT_TRUE(checker.fail());
  EXPECT_THAT(checker.what(), HasSubstr("final instance field"));
}

// IPUT to a non-final field in a regular method should pass (regression test).
TEST_F(IRTypeCheckerFinalFieldTest, iput_non_final_field_in_regular_method) {
  using namespace dex_asm;

  auto* owner_type = DexType::make_type("LNonFinalFieldOwner;");
  auto* field = DexField::make_field("LNonFinalFieldOwner;.val:I")
                    ->make_concrete(ACC_PUBLIC);

  auto* init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* init_method =
      DexMethod::make_method(owner_type, DexString::make_string("<init>"),
                             init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);

  auto* regular_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* regular_method =
      DexMethod::make_method(owner_type, DexString::make_string("setVal"),
                             regular_proto)
          ->make_concrete(ACC_PUBLIC, false);
  regular_method->set_deobfuscated_name("LNonFinalFieldOwner;.setVal:()V");
  regular_method->set_code(
      std::make_unique<IRCode>(regular_method, /* temp_regs */ 2));

  ClassCreator cc(owner_type);
  cc.set_super(type::java_lang_Object());
  cc.add_method(init_method);
  cc.add_method(regular_method);
  cc.add_field(field);
  cc.create();

  // temp_regs=2 means: v0, v1 are temps; v2 is 'this'
  IRCode* code = regular_method->get_code();
  code->push_back(dasm(OPCODE_CONST, {0_v, 42_L}));
  code->push_back(dasm(OPCODE_IPUT, field, {0_v, 2_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(regular_method);
  checker.validate_access();
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

// IPUT to an unresolvable (external) final field should pass gracefully.
TEST_F(IRTypeCheckerFinalFieldTest, iput_unresolvable_final_field) {
  using namespace dex_asm;

  auto* owner_type = DexType::make_type("LExternalFinalField;");
  // Create a field ref that won't resolve (no concrete class)
  auto* field_ref = DexField::make_field("LExternalFinalField;.val:I");

  auto* caller_type = DexType::make_type("LCallerOfExternal;");
  auto* init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* init_method =
      DexMethod::make_method(caller_type, DexString::make_string("<init>"),
                             init_proto)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);

  auto* regular_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* regular_method =
      DexMethod::make_method(caller_type, DexString::make_string("doStuff"),
                             regular_proto)
          ->make_concrete(ACC_PUBLIC, false);
  regular_method->set_deobfuscated_name("LCallerOfExternal;.doStuff:()V");
  regular_method->set_code(
      std::make_unique<IRCode>(regular_method, /* temp_regs */ 2));

  ClassCreator cc(caller_type);
  cc.set_super(type::java_lang_Object());
  cc.add_method(init_method);
  cc.add_method(regular_method);
  cc.create();

  // Note: we don't create a class for LExternalFinalField, so resolve_field
  // will return nullptr, and the check should be skipped.
  // temp_regs=2 means: v0, v1 are temps; v2 is 'this'
  IRCode* code = regular_method->get_code();
  code->push_back(dasm(OPCODE_CHECK_CAST, owner_type, {2_v}));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}));
  code->push_back(dasm(OPCODE_CONST, {1_v, 42_L}));
  code->push_back(dasm(OPCODE_IPUT, field_ref, {1_v, 0_v}));
  code->push_back(dasm(OPCODE_RETURN_VOID));

  IRTypeChecker checker(regular_method);
  checker.validate_access();
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}
