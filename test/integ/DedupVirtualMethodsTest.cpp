/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupVirtualMethods.h"
#include "AnnoUtils.h"
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

  auto before_stats = count_methods(scope, annotation);
  auto deduplicated_vmethods = dedup_vmethods::dedup(stores);
  auto after_stats = count_methods(scope, annotation);

  EXPECT_EQ(after_stats.annotated, 0);
  EXPECT_EQ(deduplicated_vmethods, before_stats.annotated);
  EXPECT_EQ(before_stats.total - before_stats.annotated, after_stats.total);
  check_public(methods_annotated_by_pub, true);
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
