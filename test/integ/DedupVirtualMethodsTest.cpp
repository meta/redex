/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupVirtualMethods.h"
#include "AnnoUtils.h"
#include "DexStore.h"
#include "IROpcode.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"
#include <gtest/gtest.h>

class DedupVirtualMethodsTest : public RedexIntegrationTest {};

struct VMethodsStats {
  uint32_t total{0};
  uint32_t annotated{0};
};

VMethodsStats count_methods(const Scope& scope, DexType* annotation) {
  VMethodsStats stats;
  for (auto* cls : scope) {
    for (auto* method : cls->get_vmethods()) {
      stats.total++;
      stats.annotated +=
          (((get_annotation(method, annotation) == nullptr)) ? 0 : 1);
    }
  }
  return stats;
}

std::vector<DexMethod*> annotated_by_publicized(const Scope& scope) {
  auto* publicized_annotation =
      DexType::get_type("Lcom/facebook/redextest/Publicized;");
  std::vector<DexMethod*> result;
  for (auto* cls : scope) {
    for (auto* method : cls->get_vmethods()) {
      if (get_annotation(method, publicized_annotation) != nullptr) {
        result.push_back(method);
      }
    }
  }
  return result;
}

void check_public(const std::vector<DexMethod*>& methods,
                  bool should_be_public) {
  for (auto* method : methods) {
    if (!method->is_def()) {
      continue;
    }
    EXPECT_EQ(is_public(method), should_be_public)
        << show(method)
        << (should_be_public ? " should be public" : " should not be public");
  }
}

TEST_F(DedupVirtualMethodsTest, dedup) {
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto* annotation = DexType::get_type("Lcom/facebook/redextest/Duplication;");

  auto methods_annotated_by_pub = annotated_by_publicized(scope);
  check_public(methods_annotated_by_pub, false);

  auto* invoke_super_a = DexMethod::get_method(
      "Lcom/facebook/redextest/InvokeSuperA;.throwing_method:()Ljava/lang/"
      "Object;");
  auto* invoke_super_b = DexMethod::get_method(
      "Lcom/facebook/redextest/InvokeSuperB;.throwing_method:()Ljava/lang/"
      "Object;");
  auto* invoke_super_c = DexMethod::get_method(
      "Lcom/facebook/redextest/InvokeSuperC;.throwing_method:()Ljava/lang/"
      "Object;");
  auto* caller = DexMethod::get_method(
      "Lcom/facebook/redextest/InvokeSuperCaller;.call:(Lcom/facebook/"
      "redextest/InvokeSuperC;)Ljava/lang/Object;");
  ASSERT_NE(invoke_super_a, nullptr);
  ASSERT_NE(invoke_super_b, nullptr);
  ASSERT_NE(invoke_super_c, nullptr);
  ASSERT_NE(caller, nullptr);

  auto before_stats = count_methods(scope, annotation);
  positions::JoinStats join_stats;
  auto deduplicated_vmethods =
      dedup_vmethods::dedup(stores, /* method_profiles */ nullptr, &join_stats);
  auto after_stats = count_methods(scope, annotation);

  EXPECT_EQ(after_stats.annotated, 0);
  EXPECT_EQ(deduplicated_vmethods, before_stats.annotated);
  EXPECT_EQ(before_stats.total - before_stats.annotated, after_stats.total);
  EXPECT_EQ(join_stats.marked_unreliable, 3u);
  EXPECT_EQ(join_stats.not_recorded, 0u);
  // Every removed override still held its code when its line was compared
  // against the surviving one.
  EXPECT_EQ(join_stats.merged_without_correspondence, 0u);

  auto expect_unreliable = [](const char* descriptor, bool expected,
                              size_t expected_candidates) {
    auto* method_ref = DexMethod::get_method(descriptor);
    ASSERT_NE(method_ref, nullptr);
    auto* method = method_ref->as_def();
    ASSERT_NE(method, nullptr);
    auto& cfg = method->get_code()->cfg();
    auto instructions = cfg::InstructionIterable(cfg);
    size_t throwing_instructions = 0;
    for (auto it = instructions.begin(); it != instructions.end(); ++it) {
      if (!opcode::can_throw(it->insn->opcode())) {
        continue;
      }
      ++throwing_instructions;
      auto* position = cfg.get_dbg_pos(it);
      ASSERT_NE(position, nullptr);
      EXPECT_EQ(position->is_unreliable(), expected);
      if (expected_candidates == 0) {
        EXPECT_EQ(position->alt_id(), 0u);
      } else {
        ASSERT_NE(position->alt_id(), 0u);
        auto candidates =
            g_redex->get_position_pattern_switch_manager()->get_alt_set(
                position->alt_id());
        EXPECT_EQ(candidates.total_candidates(), expected_candidates);
      }
    }
    EXPECT_GT(throwing_instructions, 0u);
  };
  expect_unreliable(
      "Lcom/facebook/redextest/P;.throwing_method:()Ljava/lang/Object;", true,
      1);
  expect_unreliable(
      "Lcom/facebook/redextest/InvokeSuperA;.throwing_method:()Ljava/lang/"
      "Object;",
      false, 0);
  expect_unreliable(
      "Lcom/facebook/redextest/InvokeSuperB;.throwing_method:()Ljava/lang/"
      "Object;",
      true, 1);

  ASSERT_NE(invoke_super_a->as_def(), nullptr);
  ASSERT_NE(invoke_super_b->as_def(), nullptr);
  EXPECT_EQ(invoke_super_c->as_def(), nullptr);
  EXPECT_TRUE(is_public(invoke_super_a->as_def()));
  EXPECT_TRUE(is_public(invoke_super_b->as_def()));

  ASSERT_NE(caller->as_def(), nullptr);
  bool found_rewritten_call = false;
  for (const auto& mie :
       cfg::InstructionIterable(caller->as_def()->get_code()->cfg())) {
    if (opcode::is_invoke_virtual(mie.insn->opcode())) {
      EXPECT_EQ(mie.insn->get_method(), invoke_super_a);
      found_rewritten_call = true;
    }
  }
  EXPECT_TRUE(found_rewritten_call);
  check_public(methods_annotated_by_pub, true);
}

TEST_F(DedupVirtualMethodsTest, marksOnlyFinalSurvivor) {
  auto* class_a =
      type_class(DexType::get_type("Lcom/facebook/redextest/OutOfOrderA;"));
  auto* class_b =
      type_class(DexType::get_type("Lcom/facebook/redextest/OutOfOrderB;"));
  auto* class_c =
      type_class(DexType::get_type("Lcom/facebook/redextest/OutOfOrderC;"));
  ASSERT_NE(class_a, nullptr);
  ASSERT_NE(class_b, nullptr);
  ASSERT_NE(class_c, nullptr);

  DexStore store("classes");
  store.add_classes({class_b, class_a, class_c});
  DexStoresVector reordered_stores;
  reordered_stores.emplace_back(std::move(store));
  auto scope = build_class_scope(reordered_stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });

  auto* method_a = DexMethod::get_method(
      "Lcom/facebook/redextest/OutOfOrderA;.throwing_method:()Ljava/lang/"
      "Object;");
  auto* method_b = DexMethod::get_method(
      "Lcom/facebook/redextest/OutOfOrderB;.throwing_method:()Ljava/lang/"
      "Object;");
  auto* method_c = DexMethod::get_method(
      "Lcom/facebook/redextest/OutOfOrderC;.throwing_method:()Ljava/lang/"
      "Object;");
  ASSERT_NE(method_a, nullptr);
  ASSERT_NE(method_b, nullptr);
  ASSERT_NE(method_c, nullptr);

  positions::JoinStats join_stats;
  EXPECT_EQ(dedup_vmethods::dedup(reordered_stores,
                                  /* method_profiles */ nullptr, &join_stats),
            2u);
  EXPECT_EQ(join_stats.marked_unreliable, 1u);
  EXPECT_EQ(join_stats.not_recorded, 0u);
  // OutOfOrderC folds into OutOfOrderB, which then folds into OutOfOrderA.
  // Both lines reach the final survivor while they still exist.
  EXPECT_EQ(join_stats.merged_without_correspondence, 0u);

  ASSERT_NE(method_a->as_def(), nullptr);
  EXPECT_EQ(method_b->as_def(), nullptr);
  EXPECT_EQ(method_c->as_def(), nullptr);

  bool found_throwing_position = false;
  auto& cfg = method_a->as_def()->get_code()->cfg();
  auto instructions = cfg::InstructionIterable(cfg);
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    if (!opcode::can_throw(it->insn->opcode())) {
      continue;
    }
    auto* position = cfg.get_dbg_pos(it);
    ASSERT_NE(position, nullptr);
    EXPECT_TRUE(position->is_unreliable());
    ASSERT_NE(position->alt_id(), 0u);
    auto candidates =
        g_redex->get_position_pattern_switch_manager()->get_alt_set(
            position->alt_id());
    EXPECT_EQ(candidates.total_candidates(), 2u);
    found_throwing_position = true;
  }
  EXPECT_TRUE(found_throwing_position);
}

TEST_F(DedupVirtualMethodsTest, dedup_with_call) {
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto* annotation = DexType::get_type("Lcom/facebook/redextest/Duplication;");

  auto methods_annotated_by_pub = annotated_by_publicized(scope);
  check_public(methods_annotated_by_pub, false);

  [[maybe_unused]] auto before_stats = count_methods(scope, annotation);
  [[maybe_unused]] auto deduplicated_vmethods = dedup_vmethods::dedup(stores);
  auto after_stats = count_methods(scope, annotation);

  EXPECT_EQ(after_stats.annotated, 0);
}

namespace {

DexMethodRef* get_method(const char* cls) {
  return DexMethod::get_method(std::string("Lcom/facebook/redextest/") + cls +
                               ";.method:()I");
}

} // namespace

TEST_F(DedupVirtualMethodsTest, keeps_no_optimizations_copy) {
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  auto* c11 = get_method("C11")->as_def();
  c11->rstate.set_no_optimizations();
  dedup_vmethods::dedup(stores);
  EXPECT_EQ(get_method("C11"), c11);
  EXPECT_TRUE(c11->is_def());
  EXPECT_EQ(get_method("C2"), nullptr);
}

TEST_F(DedupVirtualMethodsTest, keeps_copies_of_no_optimizations_method) {
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
  get_method("P")->as_def()->rstate.set_no_optimizations();
  dedup_vmethods::dedup(stores);
  // P's code at runtime may differ from the identical code Redex sees.
  EXPECT_NE(get_method("C11"), nullptr);
  EXPECT_NE(get_method("C2"), nullptr);
}
