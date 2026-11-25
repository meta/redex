/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ClassMergingTestFixture.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"

using namespace class_merging_test;

namespace {

// Relaxed init inlining turns `new A()`, with `A() { super(); }`, into
//
//   new-instance A
//   invoke-direct Base.<init>()V
//
// and deletes A's constructor once no caller is left. These tests check how
// class merging handles such sites.
class ClassMergingRelaxedInitTest : public ClassMergingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redex/test/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
    m_use = make_class("Lcom/redex/test/Use;", type::java_lang_Object());
  }

  // Adds `static make<n>()` to `owner` (by default Use), which instantiates
  // `cls` with the given constructor and calls run() on it, preceded by a
  // source block with the given value.
  DexMethod* add_site(const DexClass* cls,
                      const std::string& init,
                      float value = 1.0,
                      DexClass* owner = nullptr) {
    if (owner == nullptr) {
      owner = m_use;
    }
    auto name = "make" + std::to_string(m_num_sites++);
    auto method_name = owner->get_type()->str_copy() + "." + name + ":()V";
    std::string args = init.find("(I)") != std::string::npos ? " v1" : "";
    return add_method(owner,
                      ir(R"(
      (method (public static) "$METHOD"
       (
        (.src_block "$METHOD" 0 ($VALUE 1.0))
        (const v1 0)
        (new-instance "$CLS")
        (move-result-pseudo-object v0)
        (invoke-direct (v0$ARGS) "$INIT")
        (invoke-virtual (v0) "$CLS.run:()V")
        (return-void)
       )
      )
    )",
                         {{"$METHOD", method_name},
                          {"$VALUE", std::to_string(value)},
                          {"$CLS", cls->get_type()->str_copy()},
                          {"$ARGS", args},
                          {"$INIT", init}}));
  }

  std::string base_init() const {
    return m_base->get_type()->str_copy() + ".<init>:()V";
  }

  Json::Value model(const char* type_tag_config = "generate") {
    Json::Value model;
    model["enabled"] = true;
    model["name"] = "Relaxed";
    model["class_name_prefix"] = "Relaxed";
    model["roots"].append(m_base->get_type()->str_copy());
    model["interdex_grouping"] = "disabled";
    model["include_primary_dex"] = true;
    model["type_tag_config"] = type_tag_config;
    return model;
  }

  static int64_t metric(const UnorderedMap<std::string, int64_t>& metrics,
                        const std::string& name) {
    auto it = metrics.find("Relaxed_" + name);
    return it == metrics.end() ? -1 : it->second;
  }

  bool in_scope(const DexClass* cls) const {
    return std::find(m_scope.begin(), m_scope.end(), cls) != m_scope.end();
  }

  DexClass* m_use{nullptr};
  size_t m_num_sites{0};
};

// Class merging models treat their classes as generated code by default, and
// skip most bytecode checks in their methods. A relaxed init there bypasses the
// constructor that stores the type tag, so its class must stay unmerged.
TEST_F(ClassMergingRelaxedInitTest, RelaxedInitInGeneratedCodeExcludes) {
  auto* a = make_mergeable("Lcom/redex/test/A;");
  auto* b = make_mergeable("Lcom/redex/test/B;");
  make_mergeable("Lcom/redex/test/C;");
  add_site(a, base_init(), 1.0, /* owner */ b);

  auto metrics = run_merging({model()});

  EXPECT_TRUE(in_scope(a));
  EXPECT_EQ(metric(metrics, "class_merged"), 2);
}

} // namespace
