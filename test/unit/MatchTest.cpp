/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <unordered_set>

#include "IRInstruction.h"
#include "Match.h"
#include "RedexTest.h"

class MatchTest : public RedexTest {};

TEST_F(MatchTest, Equality) {
  auto m = m::equals(42);

  int x = 43;
  auto n = m::equals(x);
  auto o = m::equals(&x);

  EXPECT_TRUE(m.matches(42));
  EXPECT_FALSE(m.matches(43));

  EXPECT_TRUE(n.matches(43));
  EXPECT_FALSE(n.matches(42));

  EXPECT_TRUE(o.matches(&x));
  EXPECT_FALSE(o.matches(nullptr));
}

TEST_F(MatchTest, In) {
  auto n = m::in<int>(std::unordered_set<int>{43});

  std::unordered_set<int> xs{42};
  auto m = m::in<int>(xs);

  EXPECT_TRUE(m.matches(42));
  EXPECT_FALSE(m.matches(43));

  EXPECT_TRUE(n.matches(43));
  EXPECT_FALSE(n.matches(42));
}

TEST_F(MatchTest, IputBasic) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);

  auto iput = std::make_unique<IRInstruction>(OPCODE_IPUT);
  iput->set_src(0, 0);
  iput->set_src(1, 1);
  iput->set_field(field);

  std::vector<MethodItemEntry> input{MethodItemEntry(iput.get())};
  auto match = m::find_insn_match(input, m::an_iput());

  ASSERT_EQ(match.size(), 1);
  EXPECT_EQ(match[0], iput.get());
}

TEST_F(MatchTest, IgetBasic) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);

  auto iget = std::make_unique<IRInstruction>(OPCODE_IGET);
  iget->set_src(0, 0);
  iget->set_field(field);

  std::vector<MethodItemEntry> input{MethodItemEntry(iget.get())};
  auto match = m::find_insn_match(input, m::an_iget());

  ASSERT_EQ(match.size(), 1);
  EXPECT_EQ(match[0], iget.get());
}

TEST_F(MatchTest, InvokeBasic) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexProto* proto = DexProto::make_proto(ty, DexTypeList::make_type_list({}));
  DexMethodRef* method = DexMethod::make_method(ty, str, proto);

  auto invoke = std::make_unique<IRInstruction>(OPCODE_INVOKE_VIRTUAL);
  invoke->set_method(method);

  std::vector<MethodItemEntry> input{MethodItemEntry(invoke.get())};
  auto match = m::find_insn_match(input, m::a_method_invoke());

  ASSERT_EQ(match.size(), 1);
  EXPECT_EQ(match[0], invoke.get());
}

TEST_F(MatchTest, opcode_string) {
  const auto* str = DexString::make_string("foo");

  IRInstruction* load_str = new IRInstruction(OPCODE_CONST_STRING);
  load_str->set_string(str);

  std::vector<MethodItemEntry> input{MethodItemEntry(load_str)};
  auto match = m::find_insn_match(input, m::has_string(m::equals(str)));

  EXPECT_EQ(match[0], load_str);
  delete load_str;
}

TEST_F(MatchTest, has_literal) {
  auto const_str = std::make_unique<IRInstruction>(OPCODE_CONST_STRING);
  const_str->set_string(DexString::make_string("foo"));

  auto const_int = std::make_unique<IRInstruction>(OPCODE_CONST);
  const_int->set_literal(42);

  auto p = m::has_literal();
  auto q = m::has_literal(m::equals<int64_t>(43));
  auto r = m::has_literal(m::equals<int64_t>(42));

  EXPECT_FALSE(p.matches(const_str.get()));
  EXPECT_FALSE(q.matches(const_int.get()));
  EXPECT_TRUE(r.matches(const_int.get()));
}

TEST_F(MatchTest, NotAllMatch) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);

  auto iput = std::make_unique<IRInstruction>(OPCODE_IPUT);
  iput->set_src(0, 0);
  iput->set_src(1, 1);
  iput->set_field(field);

  auto iget = std::make_unique<IRInstruction>(OPCODE_IGET);
  iget->set_src(0, 0);
  iget->set_field(field);

  DexProto* proto = DexProto::make_proto(ty, DexTypeList::make_type_list({}));
  DexMethodRef* method = DexMethod::make_method(ty, str, proto);

  auto invoke = std::make_unique<IRInstruction>(OPCODE_INVOKE_VIRTUAL);
  invoke->set_method(method);

  std::vector<MethodItemEntry> input{
      MethodItemEntry(iget.get()),
      MethodItemEntry(iput.get()),
      MethodItemEntry(invoke.get()),
  };
  auto match = m::find_insn_match(input, m::an_iput());

  ASSERT_EQ(match.size(), 1);
  EXPECT_EQ(match[0], iput.get());
}

TEST_F(MatchTest, SameFieldMatch) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);

  auto iput = std::make_unique<IRInstruction>(OPCODE_IPUT);
  iput->set_src(0, 0);
  iput->set_src(1, 1);
  iput->set_field(field);

  auto iget = std::make_unique<IRInstruction>(OPCODE_IGET);
  iget->set_src(0, 0);
  iget->set_field(field);

  DexProto* proto = DexProto::make_proto(ty, DexTypeList::make_type_list({}));
  DexMethodRef* method = DexMethod::make_method(ty, str, proto);

  auto invoke = std::make_unique<IRInstruction>(OPCODE_INVOKE_VIRTUAL);
  invoke->set_method(method);

  std::vector<MethodItemEntry> input{
      MethodItemEntry(iget.get()),
      MethodItemEntry(iput.get()),
      MethodItemEntry(invoke.get()),
  };
  auto match = m::find_insn_match(
      input, m::has_field(m::member_of<DexFieldRef>(m::equals(ty))));
  EXPECT_EQ(match.size(), 2);
}

TEST_F(MatchTest, SameMethodMatch) {
  DexType* ty = DexType::make_type("Lfoo;");
  const auto* str = DexString::make_string("foo");
  DexFieldRef* field = DexField::make_field(ty, str, ty);

  auto iput = std::make_unique<IRInstruction>(OPCODE_IPUT);
  iput->set_src(0, 0);
  iput->set_src(1, 1);
  iput->set_field(field);

  auto iget = std::make_unique<IRInstruction>(OPCODE_IGET);
  iget->set_src(0, 0);
  iget->set_field(field);

  DexProto* proto = DexProto::make_proto(ty, DexTypeList::make_type_list({}));
  DexMethodRef* method = DexMethod::make_method(ty, str, proto);

  auto invoke = std::make_unique<IRInstruction>(OPCODE_INVOKE_VIRTUAL);
  invoke->set_method(method);

  std::vector<MethodItemEntry> input{
      MethodItemEntry(iget.get()),
      MethodItemEntry(iput.get()),
      MethodItemEntry(invoke.get()),
  };
  auto match = m::find_insn_match(
      input, m::has_method(m::member_of<DexMethodRef>(m::equals(ty))));

  EXPECT_EQ(match.size(), 1);
}
