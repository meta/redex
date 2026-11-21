/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IRAssembler.h"

#include <cstdint>
#include <gtest/gtest.h>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexDebugInstruction.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "DexPosition.h"
#include "IRCode.h"
#include "IRList.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypeUtil.h"

struct IRAssemblerTest : public RedexTest {};

namespace {

SourceBlock* first_source_block(IRCode* code) {
  for (auto& mie : *code) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      return mie.src_block.get();
    }
  }
  return nullptr;
}

// Renders only the vals of a source block, so that a failure reports the
// values that differ instead of just a size.
std::string show_vals(const SourceBlock* sb) {
  std::ostringstream oss;
  sb->foreach_val([&oss](const auto& val) {
    if (val) {
      oss << "(" << val->val << " " << val->appear100 << ")";
    } else {
      oss << "()";
    }
  });
  return oss.str();
}

// Serializes `code`, parses the result back and checks that the source block
// came through unchanged. ASSERT_* only returns from the function it appears
// in, so keeping this out of the test body lets a caller check several cases.
void check_source_block_round_trips(IRCode* code) {
  const auto* sb = first_source_block(code);
  ASSERT_NE(sb, nullptr);

  auto serialized = assembler::to_string(code);
  SCOPED_TRACE(serialized);

  std::unique_ptr<IRCode> reparsed;
  ASSERT_NO_THROW(reparsed = assembler::ircode_from_string(serialized));

  const auto* reparsed_sb = first_source_block(reparsed.get());
  ASSERT_NE(reparsed_sb, nullptr);
  EXPECT_EQ(reparsed_sb->vals_size, sb->vals_size);
  EXPECT_EQ(show_vals(reparsed_sb), show_vals(sb));
  EXPECT_EQ(assembler::to_string(reparsed.get()), serialized);
}

} // namespace

TEST_F(IRAssemblerTest, disassembleCode) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (:foo-label)
     (if-eqz v0 :foo-label)
     (invoke-virtual (v0 v1) "LFoo;.bar:(II)V")
     (sget-object "LFoo;.qux:LBar;")
     (move-result-pseudo-object v0)
     (return-void)
    )
)");
  EXPECT_EQ(code->get_registers_size(), 2);

  std::cout << show(code) << "\n";
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((const v0 0) "
            "(:L0) "
            "(if-eqz v0 :L0) "
            "(invoke-virtual (v0 v1) \"LFoo;.bar:(II)V\") "
            "(sget-object \"LFoo;.qux:LBar;\") "
            "(move-result-pseudo-object v0) "
            "(return-void))");
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, methodConstantsRoundTrip) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const-method-type "(CSJ)Z")
     (move-result-pseudo-object v0)
     (const-method-handle invoke-instance "Ljava/lang/Object;.hashCode:()I")
     (move-result-pseudo-object v1)
     (const-method-handle static-get "LFoo;.bar:I")
     (move-result-pseudo-object v2)
     (return-void)
    )
)");
  auto it = InstructionIterable(code.get()).begin();
  EXPECT_EQ(it->insn->get_proto(), DexProto::make_proto("(CSJ)Z"));
  ++it;
  ++it;
  const auto* handle = it->insn->get_methodhandle();
  EXPECT_EQ(handle->type(), METHOD_HANDLE_TYPE_INVOKE_INSTANCE);
  EXPECT_EQ(handle->methodref(),
            DexMethod::get_method("Ljava/lang/Object;.hashCode:()I"));
  ++it;
  ++it;
  handle = it->insn->get_methodhandle();
  EXPECT_EQ(handle->type(), METHOD_HANDLE_TYPE_STATIC_GET);
  EXPECT_EQ(handle->fieldref(), DexField::get_field("LFoo;.bar:I"));

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((const-method-type \"(CSJ)Z\") "
            "(move-result-pseudo-object v0) "
            "(const-method-handle invoke-instance "
            "\"Ljava/lang/Object;.hashCode:()I\") "
            "(move-result-pseudo-object v1) "
            "(const-method-handle static-get \"LFoo;.bar:I\") "
            "(move-result-pseudo-object v2) "
            "(return-void))");
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, unknownMethodHandleKindIsRejected) {
  EXPECT_THROW(assembler::ircode_from_string(R"(
    (
      (const-method-handle invoke-everything "LFoo;.bar:()V")
      (move-result-pseudo-object v0)
    )
  )"),
               RedexException);
}

TEST_F(IRAssemblerTest, empty) {
  auto code = assembler::ircode_from_string(R"((
    (return-void)
  ))");
  EXPECT_EQ(code->get_registers_size(), 0);
}

// The assembler preserves the authored source-block id verbatim: it does not
// renumber (DFS renumbering only happens in insert_source_blocks). Cover a
// mid-range id, 0, and the reserved kSyntheticId (UINT32_MAX).
// A register index that is missing, non-numeric, only partially numeric, or
// out of range must be rejected rather than assembled against an arbitrary
// register. All of these tokens lex as a single s-expression symbol, so they
// do reach the register parser rather than failing earlier.
TEST_F(IRAssemblerTest, rejectsMalformedRegister) {
  for (const auto* reg : {"v", "vx", "v0x1", "v-1", /* 2^32 */ "v4294967296"}) {
    auto s = std::string("((load-param ") + reg + "))";
    EXPECT_THROW(assembler::ircode_from_string(s), RedexException) << s;
  }
}

TEST_F(IRAssemblerTest, findOpcodeMapsANameToItsOpcode) {
  EXPECT_EQ(assembler::find_opcode("const-string"), OPCODE_CONST_STRING);
}

TEST_F(IRAssemblerTest, findOpcodeRejectsAnUnknownName) {
  EXPECT_EQ(assembler::find_opcode("frobnicate"), std::nullopt);
}

TEST_F(IRAssemblerTest, getOpcodeNameReturnsTheAssemblerSpelling) {
  EXPECT_EQ(assembler::get_opcode_name(OPCODE_CONST_STRING), "const-string");
}

TEST_F(IRAssemblerTest, sourceBlockIdRoundTrips) {
  for (uint32_t want_id : {0u, 7u, SourceBlock::kSyntheticId}) {
    auto s = std::string("((.src_block \"LFoo;.bar:()V\" ") +
             std::to_string(want_id) + " (1.0 1.0)) (return-void))";
    auto code = assembler::ircode_from_string(s);

    SourceBlock* sb = nullptr;
    for (auto& mie : *code) {
      if (mie.type == MFLOW_SOURCE_BLOCK) {
        sb = mie.src_block.get();
        break;
      }
    }
    ASSERT_NE(sb, nullptr);
    EXPECT_EQ(sb->id, want_id);

    // The id also survives a serialize -> parse -> serialize round trip.
    EXPECT_EQ(assembler::to_string(code.get()),
              assembler::to_string(assembler::ircode_from_string(s).get()));
  }
}

// A genuine round trip -- parse(to_string(x)) -- over 0, 1 and 3 vals. The
// serializer's own output has to be something the parser accepts, and the vals
// have to come back unchanged. sourceBlockIdRoundTrips cannot check this
// because both of its sides are to_string(parse(s)).
TEST_F(IRAssemblerTest, sourceBlockValsSurviveSerializeThenParse) {
  for (const auto* vals : {"", "(1.0 1.0)", "(1.0 1.0) (0.5 0.4) (0.0 0.0)"}) {
    auto s = std::string("((.src_block \"LFoo;.bar:()V\" 0 ") + vals +
             ") (return-void))";
    check_source_block_round_trips(assembler::ircode_from_string(s).get());
  }
}

// The vals must be emitted as flat siblings -- the shape the parser accepts and
// that every .src_block test input in the tree uses -- and not wrapped in one
// extra list.
TEST_F(IRAssemblerTest, sourceBlockValsSerializeAsFlatSiblings) {
  auto one_val = assembler::ircode_from_string(
      R"(((.src_block "LFoo;.bar:()V" 0 (1.0 1.0)) (return-void)))");
  EXPECT_EQ(assembler::to_string(one_val.get()),
            "((.src_block \"LFoo;.bar:()V\" 0 (1.000000 1.000000)) "
            "(return-void))");

  auto multi_val = assembler::ircode_from_string(
      R"(((.src_block "LFoo;.bar:()V" 0 (1.0 1.0) (0.5 0.4) (0.0 0.0))
          (return-void)))");
  EXPECT_EQ(assembler::to_string(multi_val.get()),
            "((.src_block \"LFoo;.bar:()V\" 0 (1.000000 1.000000) "
            "(0.500000 0.400000) (0.000000 0.000000)) (return-void))");
}

// Val::none() is a third state distinct from a 0.0 val, serialized as "()".
// The vals are built in C++ rather than parsed from a fixture string so that
// the none is ground truth: a text fixture would take its meaning from the very
// parser this test is checking.
TEST_F(IRAssemblerTest, sourceBlockNoneValSurvivesSerializeThenParse) {
  auto code = assembler::ircode_from_string(
      R"(((.src_block "LFoo;.bar:()V" 0 (0.0 0.0)) (return-void)))");
  const std::vector<SourceBlock::Val> vals{SourceBlock::Val(1.0f, 1.0f),
                                           SourceBlock::Val::none(),
                                           SourceBlock::Val(0.5f, 0.4f)};
  for (auto& mie : *code) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      mie.src_block = std::make_unique<SourceBlock>(
          DexString::make_string("LFoo;.bar:()V"), 0, vals);
    }
  }
  EXPECT_EQ(assembler::to_string(code.get()),
            "((.src_block \"LFoo;.bar:()V\" 0 (1.000000 1.000000) () "
            "(0.500000 0.400000)) (return-void))");
  check_source_block_round_trips(code.get());
}

TEST_F(IRAssemblerTest, assembleMethod) {
  auto* method = assembler::method_from_string(R"(
    (method (private) "LFoo;.bar:(I)V"
     (
      (return-void)
     )
    )
)");
  EXPECT_EQ(method->get_access(), ACC_PRIVATE);
  EXPECT_STREQ(method->get_name()->c_str(), "bar");
  EXPECT_STREQ(method->get_class()->get_name()->c_str(), "LFoo;");
  EXPECT_EQ(assembler::to_string(method->get_code()), "((return-void))");

  auto* static_method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.baz:(I)V"
     (
      (return-void)
     )
    )
)");
  EXPECT_EQ(static_method->get_access(), ACC_PUBLIC | ACC_STATIC);
  EXPECT_STREQ(static_method->get_name()->c_str(), "baz");
  EXPECT_STREQ(static_method->get_class()->get_name()->c_str(), "LFoo;");
}

TEST_F(IRAssemblerTest, assembleClassWithMethod) {
  auto* method = assembler::class_with_method("LFoo;",
                                              R"(
      (method (private) "LFoo;.bar:(I)V"
       (
        (return-void)
       )
      )
    )");
  EXPECT_EQ(method->get_access(), ACC_PRIVATE);
  EXPECT_STREQ(method->get_name()->c_str(), "bar");
  EXPECT_STREQ(method->get_class()->get_name()->c_str(), "LFoo;");
  EXPECT_EQ(assembler::to_string(method->get_code()), "((return-void))");
}

TEST_F(IRAssemblerTest, assembleClassWithMethods) {
  const std::vector<DexMethod*>& methods = {
      assembler::method_from_string(R"(
        (method (private) "LFoo;.bar0:(I)V"
          (
            (return-void)
          )
        )
      )"),
      assembler::method_from_string(R"(
        (method (public) "LFoo;.bar1:(V)V"
          (
            (return-void)
          )
        )
      )"),
  };

  auto* clazz = assembler::class_with_methods("LFoo;", methods);

  DexMethod* method0 = clazz->get_dmethods().at(0);
  EXPECT_EQ(method0->get_access(), ACC_PRIVATE);
  EXPECT_STREQ(method0->get_name()->c_str(), "bar0");
  EXPECT_STREQ(method0->get_class()->get_name()->c_str(), "LFoo;");
  EXPECT_EQ(assembler::to_string(method0->get_code()), "((return-void))");

  DexMethod* method1 = clazz->get_vmethods().at(0);
  EXPECT_EQ(method1->get_access(), ACC_PUBLIC);
  EXPECT_STREQ(method1->get_name()->c_str(), "bar1");
  EXPECT_STREQ(method1->get_class()->get_name()->c_str(), "LFoo;");
  EXPECT_EQ(assembler::to_string(method1->get_code()), "((return-void))");
}

TEST_F(IRAssemblerTest, use_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:a :b :c))
      (return-void)

      (:a 0)
      (const v0 0)

      (:b 1)
      (const v1 1)

      (:c 2)
      (const v2 2)
    )
  )");

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((switch v0 (:L0 :L1 :L2)) "
            "(return-void) "
            "(:L0 0) "
            "(const v0 0) "
            "(:L1 1) "
            "(const v1 1) "
            "(:L2 2) "
            "(const v2 2))");
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, use_switch_and_branch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:a :b :c))
      (:default)
      (return-void)

      (:a 0)
      (const v0 0)
      (if-eqz v0 :lbl)
      (goto :default)

      (:b 1)
      (const v1 1)
      (goto :default)

      (:c 2)
      (const v2 2)
      (goto :default)

      (const v3 3)
      (goto :default)

      (:lbl)
      (const v4 4)
    )
  )");

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((switch v0 (:L1 :L2 :L3)) "
            "(:L0) "
            "(return-void) "

            "(:L1 0) "
            "(const v0 0) "
            "(if-eqz v0 :L4) "
            "(goto :L0) "

            "(:L2 1) "
            "(const v1 1) "
            "(goto :L0) "

            "(:L3 2) "
            "(const v2 2) "
            "(goto :L0) "

            "(const v3 3) "
            "(goto :L0) "

            "(:L4) "
            "(const v4 4))");
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, diabolical_double_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v1 (:a :b))
      (switch v0 (:a :b))

      (:a 0)
      (const v0 0)

      (:b 1)
      (const v1 1)
    )
  )");

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((switch v1 (:L0 :L1)) "
            "(switch v0 (:L0 :L1)) "

            "(:L0 0) "
            "(const v0 0) "

            "(:L1 1) "
            "(const v1 1))");

  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, diabolical_bad_order_switch) {
  auto code = assembler::ircode_from_string(R"(
    (
      (switch v0 (:b :a))

      (:a 0)
      (const v0 0)

      (:b 1)
      (const v1 1)
    )
  )");

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s,
            "((switch v0 (:L0 :L1)) "

            "(:L0 0) "
            "(const v0 0) "

            "(:L1 1) "
            "(const v1 1))");

  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, try_catch_simplest) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.try_start a)
      (const v0 0)
      (.try_end a)

      (.catch (a))
      (const v2 2)
      (return-void)
    )
  )");
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, try_catch_with_next) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.try_start a)
      (const v0 0)
      (.try_end a)

      (.catch (a b) "LFoo;")
      (const v1 1)
      (return-void)

      (.catch (b) "LBar;")
      (const v2 2)
      (return-void)
    )
  )");
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

TEST_F(IRAssemblerTest, try_catch_exception_name) {
  auto code1 = assembler::ircode_from_string(R"(
    (
      (.try_start a)
      (const v0 0)
      (.try_end a)

      (.catch (a) "LFoo;")
      (const v1 1)
      (return-void)
    )
  )");
  auto code2 = assembler::ircode_from_string(R"(
    (
      (.try_start a)
      (const v0 0)
      (.try_end a)

      (.catch (a) "LBar;")
      (const v1 1)
      (return-void)
    )
  )");

  EXPECT_NE(assembler::to_string(code1.get()),
            assembler::to_string(code2.get()));
}

TEST_F(IRAssemblerTest, try_catch_with_two_tries) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.try_start a)
      (const v0 0)
      (.try_end a)

      (.try_start a)
      (const v1 1)
      (.try_end a)

      (.catch (a))
      (const v2 2)
      (return-void)
    )
  )");
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));
}

std::vector<DexPosition*> get_positions(const std::unique_ptr<IRCode>& code) {
  std::vector<DexPosition*> positions;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_POSITION) {
      positions.push_back(mie.pos.get());
    }
  }
  return positions;
}

TEST_F(IRAssemblerTest, pos) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos "LFoo;.bar:()V" "Foo.java" "420")
     (const v0 420)
    )
  )");

  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  EXPECT_EQ(code->count_opcodes(), 1);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 1);
  auto* pos = positions[0];
  EXPECT_EQ(show(pos->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos->line, 420);
  EXPECT_EQ(pos->parent, nullptr);
}

TEST_F(IRAssemblerTest, posWithParent_DbgLabel) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method2 =
      DexMethod::make_method("LFoo;.baz:()I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "LFoo;.bar:()V" "Foo.java" 420)
     (.pos:dbg_1 "LFoo;.baz:()I" "Foo.java" 440 dbg_0)
     (const v0 420)
     (return v0)
    )
  )");

  // Ensure serialize + deserialize works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialize actually works
  EXPECT_EQ(code->count_opcodes(), 2);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 2);

  auto* pos0 = positions[0];
  EXPECT_EQ(show(pos0->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos0->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos0->line, 420);
  EXPECT_EQ(pos0->parent, nullptr);

  auto* pos1 = positions[1];
  EXPECT_EQ(show(pos1->method), std::string("LFoo;.baz:()I"));
  EXPECT_EQ(pos1->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos1->line, 440);
  EXPECT_EQ(*pos1->parent, *pos0);
}

TEST_F(IRAssemblerTest, posWithParent_UserLabel) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method2 =
      DexMethod::make_method("LFoo;.baz:()I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos:DarthVader "LFoo;.bar:()V" "Foo.java" 420)
     (.pos:LukeSkywalker "LFoo;.baz:()I" "Foo.java" 440 DarthVader)
     (const v0 420)
     (return v0)
    )
  )");

  // Ensure serialize + deserialize works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialize actually works
  EXPECT_EQ(code->count_opcodes(), 2);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 2);

  auto* pos0 = positions[0];
  EXPECT_EQ(show(pos0->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos0->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos0->line, 420);
  EXPECT_EQ(pos0->parent, nullptr);

  auto* pos1 = positions[1];
  EXPECT_EQ(show(pos1->method), std::string("LFoo;.baz:()I"));
  EXPECT_EQ(pos1->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos1->line, 440);
  EXPECT_EQ(*pos1->parent, *pos0);
}

TEST_F(IRAssemblerTest, posWithParent_BadParent) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method2 =
      DexMethod::make_method("LFoo;.baz:()I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos:Bob "LFoo;.bar:()V" "Foo.java" 420)
     (.pos:John "LFoo;.baz:()I" "Foo.java" 440 BadParent)
     (const v0 420)
     (return v0)
    )
  )");

  // Ensure serialize + deserialize works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialize actually works
  EXPECT_EQ(code->count_opcodes(), 2);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 2);

  auto* pos0 = positions[0];
  EXPECT_EQ(show(pos0->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos0->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos0->line, 420);
  EXPECT_EQ(pos0->parent, nullptr);

  auto* pos1 = positions[1];
  EXPECT_EQ(show(pos1->method), std::string("LFoo;.baz:()I"));
  EXPECT_EQ(pos1->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos1->line, 440);
  EXPECT_EQ(pos1->parent, nullptr);
}

TEST_F(IRAssemblerTest, posWithGrandparent) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method2 =
      DexMethod::make_method("LFoo;.baz:()I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method3 =
      DexMethod::make_method("LFoo;.baz:()Z")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "LFoo;.bar:()V" "Foo.java" 420)
     (.pos:dbg_1 "LFoo;.baz:()I" "Foo.java" 440 dbg_0)
     (.pos:dbg_2 "LFoo;.baz:()Z" "Foo.java" 441 dbg_1)
     (const v0 420)
     (return v0)
    )
  )");

  // Ensure serialize + deserialize works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialize actually works
  EXPECT_EQ(code->count_opcodes(), 2);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 3);

  auto* pos0 = positions[0];
  EXPECT_EQ(show(pos0->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos0->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos0->line, 420);
  EXPECT_EQ(pos0->parent, nullptr);

  auto* pos2 = positions[2];
  EXPECT_EQ(show(pos2->method), std::string("LFoo;.baz:()Z"));
  EXPECT_EQ(pos2->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos2->line, 441);
  EXPECT_EQ(*pos2->parent->parent, *pos0);
}

TEST_F(IRAssemblerTest, posWithGreatGrandparent) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method2 =
      DexMethod::make_method("LFoo;.baz:()I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  [[maybe_unused]] auto* method3 =
      DexMethod::make_method("LFoo;.baz:()Z")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "LFoo;.bar:()V" "Foo.java" 420)
     (.pos:dbg_1 "LFoo;.baz:()I" "Foo.java" 440 dbg_0)
     (.pos:dbg_2 "LFoo;.baz:()Z" "Foo.java" 441 dbg_1)
     (.pos:dbg_3 "LFoo;.baz:()Z" "Foo.java" 442 dbg_2)
     (const v0 420)
     (return v0)
    )
  )");

  // Ensure serialize + deserialize works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialize actually works
  EXPECT_EQ(code->count_opcodes(), 2);
  auto positions = get_positions(code);
  ASSERT_EQ(positions.size(), 4);

  auto* pos0 = positions[0];
  EXPECT_EQ(show(pos0->method), std::string("LFoo;.bar:()V"));
  EXPECT_EQ(pos0->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos0->line, 420);
  EXPECT_EQ(pos0->parent, nullptr);

  auto* pos3 = positions[3];
  EXPECT_EQ(show(pos3->method), std::string("LFoo;.baz:()Z"));
  EXPECT_EQ(pos3->file->c_str(), std::string("Foo.java"));
  EXPECT_EQ(pos3->line, 442);
  EXPECT_EQ(*pos3->parent->parent->parent, *pos0);
}

std::vector<DexDebugInstruction*> get_debug_info(
    const std::unique_ptr<IRCode>& code) {
  std::vector<DexDebugInstruction*> debug_info;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_DEBUG) {
      debug_info.push_back(mie.dbgop.get());
    }
  }
  return debug_info;
}

TEST_F(IRAssemblerTest, dexDebugInstruction) {
  [[maybe_unused]] auto* method =
      DexMethod::make_method("LFoo;.bar:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto code = assembler::ircode_from_string(R"(
    (
      (.dbg DBG_SET_FILE "foo.java")
      (.dbg DBG_SET_EPILOGUE_BEGIN)
      (.dbg DBG_SET_PROLOGUE_END)
      (.dbg DBG_RESTART_LOCAL 1)
      (.dbg DBG_END_LOCAL 2)
      (.dbg DBG_START_LOCAL_EXTENDED 3 "name" "Ljava/lang/Objects;" "sig")
      (.dbg DBG_START_LOCAL 4 "name" "Ljava/lang/Objects;")
      (.dbg DBG_ADVANCE_LINE 5)
      (.dbg DBG_ADVANCE_PC 6)
      (.dbg DBG_END_SEQUENCE)
      (.dbg EMIT 10)
      (const v0 42)
      (return v0)
    )
  )");

  // Ensure serialization works as expected
  auto s = assembler::to_string(code.get());
  EXPECT_EQ(s, assembler::to_string(assembler::ircode_from_string(s).get()));

  // Ensure deserialization works as expected
  EXPECT_EQ(code->count_opcodes(), 2);
  auto debug_info = get_debug_info(code);
  EXPECT_EQ(debug_info.size(), 11);

  auto* dbg0 = debug_info[0];
  EXPECT_EQ(dbg0->opcode(), DBG_SET_FILE);
  auto* dbg0_ = dynamic_cast<DexDebugOpcodeSetFile*>(dbg0);
  EXPECT_NE(dbg0_, nullptr);
  EXPECT_EQ(dbg0_->file()->str(), "foo.java");

  auto* dbg1 = debug_info[1];
  EXPECT_EQ(dbg1->opcode(), DBG_SET_EPILOGUE_BEGIN);
  EXPECT_EQ(dbg1->uvalue(), DEX_NO_INDEX);

  auto* dbg2 = debug_info[2];
  EXPECT_EQ(dbg2->opcode(), DBG_SET_PROLOGUE_END);
  EXPECT_EQ(dbg2->uvalue(), DEX_NO_INDEX);

  auto* dbg3 = debug_info[3];
  EXPECT_EQ(dbg3->opcode(), DBG_RESTART_LOCAL);
  EXPECT_EQ(dbg3->uvalue(), 1);

  auto* dbg4 = debug_info[4];
  EXPECT_EQ(dbg4->opcode(), DBG_END_LOCAL);
  EXPECT_EQ(dbg4->uvalue(), 2);

  auto* dbg5 = debug_info[5];
  EXPECT_EQ(dbg5->opcode(), DBG_START_LOCAL_EXTENDED);
  auto* dbg5_ = dynamic_cast<DexDebugOpcodeStartLocal*>(dbg5);
  EXPECT_NE(dbg5_, nullptr);
  EXPECT_EQ(dbg5_->name()->str(), "name");
  EXPECT_EQ(dbg5_->type()->str(), "Ljava/lang/Objects;");
  EXPECT_EQ(dbg5_->sig()->str(), "sig");

  auto* dbg6 = debug_info[6];
  EXPECT_EQ(dbg6->opcode(), DBG_START_LOCAL);
  auto* dbg6_ = dynamic_cast<DexDebugOpcodeStartLocal*>(dbg6);
  EXPECT_NE(dbg6_, nullptr);
  EXPECT_EQ(dbg6_->name()->str(), "name");
  EXPECT_EQ(dbg6_->type()->str(), "Ljava/lang/Objects;");
  EXPECT_EQ(dbg6_->sig(), nullptr);

  auto* dbg7 = debug_info[7];
  EXPECT_EQ(dbg7->opcode(), DBG_ADVANCE_LINE);
  EXPECT_EQ(dbg7->value(), 5);

  auto* dbg8 = debug_info[8];
  EXPECT_EQ(dbg8->opcode(), DBG_ADVANCE_PC);
  EXPECT_EQ(dbg8->uvalue(), 6);

  auto* dbg9 = debug_info[9];
  EXPECT_EQ(dbg9->opcode(), DBG_END_SEQUENCE);
  EXPECT_EQ(dbg9->uvalue(), DEX_NO_INDEX);

  auto* dbg10 = debug_info[10];
  EXPECT_EQ(dbg10->opcode(), DBG_FIRST_SPECIAL);
  EXPECT_EQ(dbg10->uvalue(), DEX_NO_INDEX);
}

TEST_F(IRAssemblerTest, assembleField) {
  auto* field =
      assembler::field_from_string("(field (private) \"LFoo;.bar:I\")");
  EXPECT_EQ(field->get_access(), ACC_PRIVATE);
  EXPECT_EQ(field->get_name()->str(), "bar");
  EXPECT_EQ(field->get_class()->get_name()->str(), "LFoo;");

  auto* static_field =
      assembler::field_from_string("(field (public static) \"LFoo;.baz:I\")");
  EXPECT_EQ(static_field->get_access(), ACC_PUBLIC | ACC_STATIC);
  EXPECT_EQ(static_field->get_name()->str(), "baz");
  EXPECT_EQ(static_field->get_class()->get_name()->str(), "LFoo;");
}

TEST_F(IRAssemblerTest, assembleClassFromString) {
  auto* cls = assembler::class_from_string(R"(
    (class (public final) "LFoo;"
      (field (public) "LFoo;.bar:I")
      (field (public static) "LFoo;.barStatic:I")
      (field (public static) "LFoo;.bazStatic:I" #123)
      (method (private) "LFoo;.baz:(I)V"
        (
          (return-void)
        )
      )
      (method (public) "LFoo;.bazPublic:(I)V"
        (
          (return-void)
        )
      )
    )
  )");

  EXPECT_EQ(cls->get_access(), ACC_PUBLIC | ACC_FINAL);
  EXPECT_EQ(cls->get_name()->str(), "LFoo;");
  EXPECT_EQ(cls->get_super_class(), type::java_lang_Object());

  EXPECT_EQ(cls->get_ifields().size(), 1);
  ASSERT_GE(cls->get_ifields().size(), 1);
  auto* i_field = cls->get_ifields()[0];
  EXPECT_EQ(i_field->get_class(), cls->get_type());
  EXPECT_EQ(i_field->get_name()->str(), "bar");
  EXPECT_EQ(i_field->get_static_value(), nullptr);

  EXPECT_EQ(cls->get_sfields().size(), 2);
  ASSERT_GE(cls->get_sfields().size(), 2);
  {
    auto* s_field = cls->get_sfields()[0];
    EXPECT_EQ(s_field->get_class(), cls->get_type());
    EXPECT_EQ(s_field->get_name()->str(), "barStatic");
  }
  {
    auto* s_field = cls->get_sfields()[1];
    EXPECT_EQ(s_field->get_class(), cls->get_type());
    EXPECT_EQ(s_field->get_name()->str(), "bazStatic");
    EXPECT_NE(s_field->get_static_value(), nullptr);
    EXPECT_EQ(s_field->get_static_value()->as_value(), 123);
  }

  EXPECT_EQ(cls->get_dmethods().size(), 1);
  ASSERT_GE(cls->get_dmethods().size(), 1);
  auto* d_method = cls->get_dmethods()[0];
  EXPECT_EQ(d_method->get_class(), cls->get_type());
  EXPECT_EQ(d_method->get_name()->str(), "baz");

  EXPECT_EQ(cls->get_vmethods().size(), 1);
  ASSERT_GE(cls->get_vmethods().size(), 1);
  auto* v_method = cls->get_vmethods()[0];
  EXPECT_EQ(v_method->get_class(), cls->get_type());
  EXPECT_EQ(v_method->get_name()->str(), "bazPublic");

  auto* sub = assembler::class_from_string(R"(
    (class (public final) "LSub;" extends "LFoo;"
      (method (public) "LSub;.bazPublic:(I)V"
        (
          (return-void)
        )
      )
    )
  )");
  EXPECT_EQ(sub->get_super_class(), cls->get_type());
}

TEST_F(IRAssemblerTest, assembleInterfaceFromString) {
  {
    // Non public interface
    auto* iface = assembler::class_from_string(R"(
      (interface () "LIfaceNotPub;")
    )");
    EXPECT_TRUE(is_interface(iface));
    EXPECT_FALSE(is_public(iface));
  }
  auto* iface = assembler::class_from_string(R"(
    (interface (public) "LIface;"
      (method "LIface;.one:(I)V")
      (method "LIface;.two:(Ljava/lang/String;)I")
      (field "LIface;.three:I")
      (field "LIface;.four:Ljava/lang/String;")
      (field "LIface;.five:I" #5)
      (field "LIface;.six:I" #123)
      (field "LIface;.seven:Ljava/lang/String;" hello)
      (field "LIface;.eight:Z" true)
      (field "LIface;.nine:Z" false)
      (field "LIface;.ten:I" a)
      (field "LIface;.eleven:I" b)
      (field "LIface;.twelve:I" ab)
    )
  )");
  EXPECT_TRUE(is_interface(iface));
  EXPECT_TRUE(is_public(iface));

  const auto& methods = iface->get_all_methods();
  EXPECT_EQ(methods.size(), 2);
  for (const auto& m : methods) {
    EXPECT_TRUE(m->is_virtual());
    EXPECT_TRUE(m->is_concrete());
    EXPECT_EQ(m->get_access(),
              DexAccessFlags::ACC_PUBLIC | DexAccessFlags::ACC_ABSTRACT);
    auto name = m->str();
    EXPECT_TRUE(name == "one" || name == "two")
        << "Got unexpected method: " << name;
    EXPECT_EQ(m->get_code(), nullptr);
  }

  EXPECT_TRUE(iface->get_ifields().empty());
  const auto& fields = iface->get_sfields();
  EXPECT_EQ(fields.size(), 10);
  for (const auto& f : fields) {
    EXPECT_EQ(f->get_access(),
              DexAccessFlags::ACC_PUBLIC | DexAccessFlags::ACC_STATIC |
                  DexAccessFlags::ACC_FINAL);
    auto name = f->str();
    EXPECT_TRUE(name == "three" || name == "four" || name == "five" ||
                name == "six" || name == "seven" || name == "eight" ||
                name == "nine" || name == "ten" || name == "eleven" ||
                name == "twelve")
        << "Got unexpected field: " << name;
    if (name == "three") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 0);
      EXPECT_EQ(static_value->evtype(), DEVT_INT);
    } else if (name == "four") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), false);
      EXPECT_EQ(static_value->evtype(), DEVT_NULL);
    } else if (name == "five") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 5);
      EXPECT_EQ(static_value->evtype(), DEVT_INT);
    } else if (name == "six") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 123);
      EXPECT_EQ(static_value->evtype(), DEVT_INT);
    } else if (name == "seven") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->evtype(), DEVT_STRING);
      EXPECT_EQ(static_value->show(), "hello");
    } else if (name == "eight") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 1);
    } else if (name == "nine") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 0);
    } else if (name == "ten") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 10);
    } else if (name == "eleven") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 11);
    } else if (name == "twelve") {
      auto* static_value = f->get_static_value();
      EXPECT_EQ(static_value->value(), 171);
    }
  }

  // Interfaces that extend other interfaces
  auto* a = assembler::class_from_string(R"(
    (interface (public) "LA;"
      (method "LA;.one:(I)V")
    )
  )");
  EXPECT_EQ(a->get_interfaces()->size(), 0);
  auto* b = assembler::class_from_string(R"(
    (interface (public) "LB;"
      (method "LB;.two:(Ljava/lang/String;)I")
    )
  )");
  EXPECT_EQ(b->get_interfaces()->size(), 0);
  auto* c = assembler::class_from_string(R"(
    (interface (public) "LC;" extends "LA;")
  )");
  {
    const auto& ifaces = c->get_interfaces();
    EXPECT_EQ(ifaces->size(), 1);
    EXPECT_EQ(ifaces->at(0)->str(), "LA;");
  }
  auto* d = assembler::class_from_string(R"(
    (interface (public) "LD;" extends ("LA;" "LB;")
    (method "LD;.x:(II)V")
    )
  )");
  {
    const auto& ifaces = d->get_interfaces();
    EXPECT_EQ(ifaces->size(), 2);
    EXPECT_EQ(ifaces->at(0)->str(), "LA;");
    EXPECT_EQ(ifaces->at(1)->str(), "LB;");
  }
  // Make sure the rest of the expression is parsed
  EXPECT_EQ(d->get_all_methods().size(), 1);
  auto* d_x = *d->get_all_methods().begin();
  EXPECT_EQ(d_x->str(), "x");

  // Classes can implement interfaces
  auto* foo = assembler::class_from_string(R"(
    (class (public) "LFoo;" implements "LA;"
      (method (public) "LFoo;.one:(I)V"
        (
          (return-void)
        )
      )
    )
  )");
  EXPECT_EQ(foo->get_super_class(), type::java_lang_Object());
  EXPECT_EQ(foo->get_interfaces()->size(), 1);
  EXPECT_EQ(foo->get_interfaces()->at(0), a->get_type());
  EXPECT_EQ(foo->get_vmethods().size(), 1);
  auto* foo_one = *foo->get_vmethods().begin();
  EXPECT_EQ(foo_one->str(), "one");

  auto* bar = assembler::class_from_string(R"(
    (class (public) "LBar;" extends "LFoo;" implements ("Ljava/io/Serializable;" "LB;")
      (method (public) "LBar;.two:(Ljava/lang/String;)I"
        (
          (const v0 42)
          (return v0)
        )
      )
    )
  )");
  EXPECT_EQ(bar->get_super_class(), foo->get_type());
  EXPECT_EQ(bar->get_interfaces()->size(), 2);
  EXPECT_EQ(bar->get_interfaces()->at(0)->str(), "Ljava/io/Serializable;");
  EXPECT_EQ(bar->get_interfaces()->at(1), b->get_type());
  EXPECT_EQ(bar->get_vmethods().size(), 1);
  auto* bar_two = *bar->get_vmethods().begin();
  EXPECT_EQ(bar_two->str(), "two");
}

TEST_F(IRAssemblerTest, assembleInterfaceWithClinit) {
  auto* iface = assembler::class_from_string(R"(
    (interface (public) "LIface;"
      (field "LIface;.one:I")
      (field "LIface;.two:Ljava/lang/Class;")
      (method "LIface;.<clinit>:()V"
        (
          (const v0 42)
          (sput v0 "LIface;.one:I")
          (const-class "Ljava/lang/String;")
          (move-result-pseudo-object v0)
          (sput-object v0 "LIface;.two:Ljava/lang/Class;")
          (return-void)
        )
      )
    )
  )");
  EXPECT_TRUE(is_interface(iface));
  EXPECT_TRUE(is_public(iface));
  const auto& methods = iface->get_all_methods();
  EXPECT_EQ(methods.size(), 1);
  auto* clinit = methods.at(0);
  EXPECT_EQ(clinit, iface->get_clinit());
  EXPECT_EQ(clinit->get_access(),
            DexAccessFlags::ACC_STATIC | DexAccessFlags::ACC_CONSTRUCTOR);
  EXPECT_EQ(
      assembler::to_string(clinit->get_code()),
      R"(((const v0 42) (sput v0 "LIface;.one:I") (const-class "Ljava/lang/String;") (move-result-pseudo-object v0) (sput-object v0 "LIface;.two:Ljava/lang/Class;") (return-void)))");
}

std::vector<IRInstruction*> get_fill_array_data_insns(
    const std::unique_ptr<IRCode>& code) {
  std::vector<IRInstruction*> result;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_OPCODE &&
        mie.insn->opcode() == OPCODE_FILL_ARRAY_DATA) {
      result.push_back(mie.insn);
    }
  }
  return result;
}

TEST_F(IRAssemblerTest, fillArrayPayloads) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 3)

     (new-array v0 "[Z") ; create an array of length 3
     (move-result-pseudo-object v1)
     (fill-array-data v1 #1 (0 0 1))

     (new-array v0 "[C") ; create an array of length 3
     (move-result-pseudo-object v2)
     (fill-array-data v2 #2 (61 62 63))

     (new-array v0 "[I") ; create an array of length 3
     (move-result-pseudo-object v3)
     (fill-array-data v3 #4 (3e7 2 40000000))

     (new-array v0 "[J") ; create an array of length 3
     (move-result-pseudo-object v4)
     (fill-array-data v4 #8 (3b9aca00 b2d05e00 b2d05e01))

     (return-void)
    )
)");
  auto insns = get_fill_array_data_insns(code);
  EXPECT_EQ(insns.size(), 4);

  {
    auto* data = insns.at(0)->get_data();
    auto values = get_fill_array_data_payload<uint8_t>(data);
    EXPECT_EQ(values.size(), 3);
    EXPECT_EQ(values.at(0), 0x0);
    EXPECT_EQ(values.at(1), 0x0);
    EXPECT_EQ(values.at(2), 0x1);
  }
  {
    auto* data = insns.at(1)->get_data();
    auto values = get_fill_array_data_payload<uint16_t>(data);
    EXPECT_EQ(values.size(), 3);
    EXPECT_EQ(values.at(0), 0x61);
    EXPECT_EQ(values.at(1), 0x62);
    EXPECT_EQ(values.at(2), 0x63);
  }
  {
    auto* data = insns.at(2)->get_data();
    auto values = get_fill_array_data_payload<uint32_t>(data);
    EXPECT_EQ(values.size(), 3);
    EXPECT_EQ(values.at(0), 0x3e7);
    EXPECT_EQ(values.at(1), 0x2);
    EXPECT_EQ(values.at(2), 0x40000000);
  }
  {
    auto* data = insns.at(3)->get_data();
    auto values = get_fill_array_data_payload<uint64_t>(data);
    EXPECT_EQ(values.size(), 3);
    EXPECT_EQ(values.at(0), 0x3b9aca00);
    EXPECT_EQ(values.at(1), 0xb2d05e00);
    EXPECT_EQ(values.at(2), 0xb2d05e01);
  }
}

TEST_F(IRAssemblerTest, arrayDataRoundTrip) {
  {
    std::vector<std::string> elements{"3e7", "a"};
    auto op_data =
        encode_fill_array_data_payload_from_string<uint16_t>(elements);
    // SHOW and s-expr will use slightly different format, so that the latter
    // will be idiomatic. Just verify the elements are encoded the right way.
    EXPECT_STREQ(SHOW(&*op_data),
                 "fill-array-data-payload { [2 x 2] { 3e7, a } }");
  }
  {
    std::vector<std::string> elements{"3e7", "2", "40000000"};
    auto op_data =
        encode_fill_array_data_payload_from_string<uint32_t>(elements);
    EXPECT_STREQ(SHOW(&*op_data),
                 "fill-array-data-payload { [3 x 4] { 3e7, 2, 40000000 } }");
  }
  std::string expr(R"(
    (
     (const v0 3)
     (new-array v0 "[I") ; create an array of length 3
     (move-result-pseudo-object v1)
     (fill-array-data v1 #4 (63 64 65))
     (return-void)
    )
)");
  auto code = assembler::ircode_from_string(expr);
  std::string expected(
      "((const v0 3) (new-array v0 \"[I\") (move-result-pseudo-object v1) "
      "(fill-array-data v1 #4 (63 64 65)) (return-void))");
  EXPECT_EQ(expected, assembler::to_string(code.get()));
}
