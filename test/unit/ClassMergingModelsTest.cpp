/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ClassMergingTestFixture.h"
#include "DexClass.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"

using namespace class_merging_test;

namespace {

class ClassMergingModelsTest : public ClassMergingTest {
 protected:
  void SetUp() override { m_scope = create_empty_scope(); }

  static Json::Value model(const DexClass* root, const char* prefix) {
    Json::Value model;
    model["name"] = prefix;
    model["class_name_prefix"] = prefix;
    model["roots"].append(root->get_type()->str_copy());
    model["include_primary_dex"] = true;
    return model;
  }

  DexClass* make_hierarchy(const char* root,
                           DexType* super,
                           const std::vector<const char*>& subclasses) {
    auto* cls = make_class(root, super);
    add_ctor(cls);
    for (const auto* name : subclasses) {
      add_ctor(make_class(name, cls->get_type()));
    }
    return cls;
  }

  void expect_overlap(const std::vector<Json::Value>& models,
                      const char* type) {
    try {
      run_merging(models);
      ADD_FAILURE() << "overlapping models were accepted";
    } catch (const RedexException& e) {
      const std::string what = e.what();
      for (const auto* part : {"Wrong specification: models ", "Inner", "Outer",
                               type, "put their classes into one model"}) {
        EXPECT_NE(what.find(part), std::string::npos) << what;
      }
    }
  }
};

} // namespace

TEST_F(ClassMergingModelsTest, ModelsMergingTheSameClassesAreRejected) {
  auto* base = make_hierarchy("Lcom/y/Base;", type::java_lang_Object(),
                              {"Lcom/y/Other1;", "Lcom/y/Other2;"});
  auto* mid = make_hierarchy("Lcom/y/Mid;", base->get_type(),
                             {"Lcom/y/Leaf1;", "Lcom/y/Leaf2;"});

  expect_overlap({model(mid, "Inner"), model(base, "Outer")}, "Lcom/y/Leaf");
}

TEST_F(ClassMergingModelsTest, ModelRootMergedByAnotherModelIsRejected) {
  auto* base = make_hierarchy("Lcom/z/Base;", type::java_lang_Object(),
                              {"Lcom/z/Other1;", "Lcom/z/Other2;"});
  auto* mid = make_hierarchy("Lcom/z/Mid;", base->get_type(), {});

  expect_overlap({model(base, "Outer"), model(mid, "Inner")}, "Lcom/z/Mid;");
}

TEST_F(ClassMergingModelsTest, DisjointModelsMerge) {
  auto* left = make_hierarchy("Lcom/x/Left;", type::java_lang_Object(),
                              {"Lcom/x/Left1;", "Lcom/x/Left2;"});
  auto* right = make_hierarchy("Lcom/x/Right;", type::java_lang_Object(),
                               {"Lcom/x/Right1;", "Lcom/x/Right2;"});

  auto metrics = run_merging({model(left, "Left"), model(right, "Right")});

  EXPECT_EQ(metrics.at(" total_class_merged"), 4);
}
