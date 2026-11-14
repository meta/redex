/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <map>
#include <string>

#include "DexClass.h"
#include "IROpcode.h"
#include "IRTypeChecker.h"
#include "NormalizeConstructor.h"
#include "RedexTest.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Walkers.h"

class ConstructorDedupTest : public RedexIntegrationTest {};

namespace {

void expect_throwing_positions_unreliable(DexMethod* method) {
  cfg::ScopedCFG cfg(method->get_code());
  auto instructions = cfg::InstructionIterable(*cfg);
  size_t throwing_instructions = 0;
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    if (!opcode::can_throw(it->insn->opcode())) {
      continue;
    }
    ++throwing_instructions;
    auto* position = cfg->get_dbg_pos(it);
    ASSERT_NE(position, nullptr);
    EXPECT_TRUE(position->is_unreliable());
  }
  EXPECT_GT(throwing_instructions, 0u);
}

// The positions governing the super constructor call and each field write of
// `ctor`, keyed by the member they refer to.
struct CtorPositions {
  DexPosition* super_call{nullptr};
  std::map<std::string, DexPosition*> field_writes;
};

CtorPositions ctor_positions(cfg::ControlFlowGraph& cfg) {
  CtorPositions result;
  auto instructions = cfg::InstructionIterable(cfg);
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_invoke_direct(insn->opcode())) {
      result.super_call = cfg.get_dbg_pos(it);
    } else if (opcode::is_an_iput(insn->opcode())) {
      result.field_writes[insn->get_field()->get_name()->str_copy()] =
          cfg.get_dbg_pos(it);
    }
  }
  return result;
}

} // namespace

TEST_F(ConstructorDedupTest, dedup) {
  auto* type =
      DexType::get_type("Lcom/facebook/redextest/ConstructorDedupTest;");
  auto* cls = type_class(type);
  EXPECT_NE(cls, nullptr);
  std::vector<DexClass*> scope({cls});
  auto ctors = cls->get_ctors();
  positions::JoinStats join_stats;
  auto dedupped = method_dedup::dedup_constructors(scope, scope, &join_stats);
  EXPECT_EQ(dedupped, 6);
  EXPECT_GT(join_stats.marked_unreliable, 0u);
  EXPECT_EQ(join_stats.not_recorded, 0u);
  walk::parallel::methods(scope, [&](DexMethod* method) {
    IRTypeChecker checker(method);
    checker.run();
    if (checker.fail()) {
      std::string msg = checker.what();
      fprintf(stderr, "ABORT! Inconsistency found in Dex code for %s.\n %s\n",
              SHOW(method), msg.c_str());
      fprintf(stderr, "Code:\n%s\n", SHOW(method->get_code()->cfg()));
      exit(EXIT_FAILURE);
    }
    auto method_name = method->str();
    if (method_name.find("dedup_") == std::string::npos) {
      return;
    }
    DexMethod* ctor{nullptr};
    if (method_name == "dedup_0") {
      // All the constructor invocations are calling ctors[0].
      ctor = ctors[0];
    } else if (method_name == "dedup_1") {
      // All the constructor invocations are calling ctors[1] - the proto also
      // contains additional integer parameters to address collisions
      ctor = ctors[1];
    } else {
      // All the constructor invocations are calling ctors[2].
      ctor = ctors[2];
    }

    for (auto& mie : InstructionIterable(method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee = insn->get_method();
        if (callee->get_class() == type && method::is_init(callee)) {
          // Only one constructor is used.
          EXPECT_EQ(callee, ctor);
        }
      }
    }
  });

  expect_throwing_positions_unreliable(ctors[0]);
  expect_throwing_positions_unreliable(ctors[1]);
  expect_throwing_positions_unreliable(ctors[2]);
}

// The constructors `dedup_0` calls store the same values into f0, f1 and f2 in
// different orders, and normalize to one representative. Their throwing
// instructions are paired by the member they refer to, not by position in the
// body: the super constructor calls, given one shared line here, agree and stay
// reliable, while each field write differs from the replaced constructors'
// writes of the same field and is marked.
TEST_F(ConstructorDedupTest, representative_joins_victims_by_member) {
  auto* type =
      DexType::get_type("Lcom/facebook/redextest/ConstructorDedupTest;");
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);
  // Every constructor's super call gets one shared line, so whichever
  // constructors end up replaced by the representative agree there.
  const auto* shared_method = DexString::make_string(
      "Lcom/facebook/redextest/ConstructorDedupTest;.<init>:()V");
  std::map<DexMethod*, std::map<std::string, uint32_t>, dexmethods_comparator>
      field_lines;
  for (auto* ctor : cls->get_ctors()) {
    cfg::ScopedCFG cfg(ctor->get_code());
    auto positions = ctor_positions(*cfg);
    ASSERT_NE(positions.super_call, nullptr) << SHOW(ctor);
    positions.super_call->method = shared_method;
    positions.super_call->line = 1;
    for (const auto& [field, position] : positions.field_writes) {
      ASSERT_NE(position, nullptr);
      ASSERT_NE(position, positions.super_call);
      field_lines[ctor][field] = position->line;
    }
  }

  std::vector<DexClass*> scope({cls});
  positions::JoinStats join_stats;
  method_dedup::dedup_constructors(scope, scope, &join_stats);
  EXPECT_EQ(join_stats.not_recorded, 0u);
  EXPECT_EQ(join_stats.merged_without_correspondence, 0u);

  DexMethod* representative = nullptr;
  auto* dedup_0 =
      DexMethod::get_method(
          "Lcom/facebook/redextest/ConstructorDedupTest;.dedup_0:()V")
          ->as_def();
  ASSERT_NE(dedup_0, nullptr);
  for (auto& mie : InstructionIterable(dedup_0->get_code())) {
    if (mie.insn->has_method() && method::is_init(mie.insn->get_method())) {
      representative = mie.insn->get_method()->as_def();
    }
  }
  ASSERT_NE(representative, nullptr);
  ASSERT_TRUE(field_lines.count(representative));

  cfg::ScopedCFG cfg(representative->get_code());
  auto positions = ctor_positions(*cfg);
  ASSERT_NE(positions.super_call, nullptr);
  EXPECT_FALSE(positions.super_call->is_unreliable());
  for (const auto& [field, position] : positions.field_writes) {
    ASSERT_NE(position, nullptr);
    EXPECT_TRUE(position->is_unreliable()) << field;
  }
}
