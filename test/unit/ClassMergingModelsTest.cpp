/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <gtest/gtest.h>
#include <memory>
#include <optional>

#include "ClassMergingTestFixture.h"
#include "ControlFlow.h"
#include "DexAnnotation.h"
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

  static constexpr const char* kMarker =
      "Lcom/facebook/kotlin/compilerplugins/dataclassgenerate/annotation/"
      "DcgMergeCandidate;";

  DexClass* object_root() {
    auto* root = type_class(type::java_lang_Object());
    auto* ctor = dynamic_cast<DexMethod*>(
        DexMethod::make_method("Ljava/lang/Object;.<init>:()V"));
    ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
    ctor->set_virtual(false);
    ctor->set_external();
    root->add_method(ctor);
    return root;
  }

  void define_marker() {
    auto* marker = make_class(kMarker, type::java_lang_Object());
    marker->set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT |
                       ACC_ANNOTATION);
  }

  DexClass* make_candidate(const char* name, DexType* super, bool marked) {
    auto* cls = make_class(name, super);
    add_ctor(cls);
    if (marked) {
      auto annotations = std::make_unique<DexAnnotationSet>();
      annotations->add_annotation(std::make_unique<DexAnnotation>(
          DexType::get_type(kMarker), DAV_RUNTIME));
      EXPECT_TRUE(cls->attach_annotation_set(std::move(annotations)));
    }
    return cls;
  }

  Json::Value marker_model() {
    auto config = model(object_root(), "Marked");
    config["target_annotations"].append(kMarker);
    return config;
  }

  bool contains_class(const DexClass* cls) const {
    return std::find(m_scope.begin(), m_scope.end(), cls) != m_scope.end();
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

TEST_F(ClassMergingModelsTest,
       AnnotationSelectorMergesOnlyMarkedDirectChildren) {
  define_marker();
  auto config = marker_model();
  auto* first = make_candidate("Lmarked/A;", type::java_lang_Object(), true);
  auto* second = make_candidate("Lmarked/B;", type::java_lang_Object(), true);
  auto* unmarked =
      make_candidate("Lmarked/C;", type::java_lang_Object(), false);
  auto* base = make_hierarchy("Lmarked/Base;", type::java_lang_Object(), {});
  auto* wrong_base = make_candidate("Lmarked/D;", base->get_type(), true);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  EXPECT_FALSE(contains_class(first));
  EXPECT_FALSE(contains_class(second));
  EXPECT_TRUE(contains_class(unmarked));
  EXPECT_TRUE(contains_class(base));
  EXPECT_TRUE(contains_class(wrong_base));
}

TEST_F(ClassMergingModelsTest, EmptyAnnotationSelectorDoesNotFallBackToRoots) {
  auto config = model(object_root(), "Empty");
  config["target_annotations"] = Json::Value(Json::arrayValue);
  auto* first = make_candidate("Lempty/A;", type::java_lang_Object(), false);
  auto* second = make_candidate("Lempty/B;", type::java_lang_Object(), false);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_TRUE(contains_class(first));
  EXPECT_TRUE(contains_class(second));
}

TEST_F(ClassMergingModelsTest,
       MissingAnnotationDefinitionDoesNotFallBackToRoots) {
  auto config = marker_model();
  DexType::make_type(kMarker);
  auto* first = make_candidate("Lmissing/A;", type::java_lang_Object(), true);
  auto* second = make_candidate("Lmissing/B;", type::java_lang_Object(), true);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_TRUE(contains_class(first));
  EXPECT_TRUE(contains_class(second));
}

TEST_F(ClassMergingModelsTest, UnusedAnnotationDoesNotFallBackToRoots) {
  define_marker();
  auto config = marker_model();
  auto* first = make_candidate("Lunused/A;", type::java_lang_Object(), false);
  auto* second = make_candidate("Lunused/B;", type::java_lang_Object(), false);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_TRUE(contains_class(first));
  EXPECT_TRUE(contains_class(second));
}

TEST_F(ClassMergingModelsTest, AnnotationSelectorPreservesMultipleInterfaces) {
  define_marker();
  auto config = marker_model();
  auto* first_interface =
      make_class("Linterfaces/First;", type::java_lang_Object());
  auto* second_interface =
      make_class("Linterfaces/Second;", type::java_lang_Object());
  first_interface->set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  second_interface->set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* interfaces = DexTypeList::make_type_list(
      {first_interface->get_type(), second_interface->get_type()});
  auto* first =
      make_candidate("Linterfaces/A;", type::java_lang_Object(), true);
  auto* second =
      make_candidate("Linterfaces/B;", type::java_lang_Object(), true);
  first->set_interfaces(interfaces);
  second->set_interfaces(interfaces);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  size_t mergers_with_interfaces = 0;
  for (const auto* cls : m_scope) {
    if (cls->rstate.is_generated() && cls->get_interfaces() == interfaces) {
      ++mergers_with_interfaces;
    }
  }
  EXPECT_EQ(mergers_with_interfaces, 1u);
}

TEST_F(ClassMergingModelsTest,
       MarkedParentsWithUnselectedChildrenAreNotMerged) {
  define_marker();
  auto config = marker_model();
  make_candidate("Lparents/A;", type::java_lang_Object(), true);
  make_candidate("Lparents/B;", type::java_lang_Object(), true);
  auto* parent =
      make_candidate("Lparents/Parent;", type::java_lang_Object(), true);
  auto* child = make_candidate("Lparents/Child;", parent->get_type(), false);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  EXPECT_TRUE(contains_class(parent));
  EXPECT_TRUE(contains_class(child));
}

TEST_F(ClassMergingModelsTest, AnnotationSelectorKeepsDistinctInstanceOfTags) {
  define_marker();
  auto config = marker_model();
  make_candidate("Ltags/A;", type::java_lang_Object(), true);
  make_candidate("Ltags/B;", type::java_lang_Object(), true);
  auto* probe = make_class("Ltags/Probe;", type::java_lang_Object());
  auto make_probe = [&](const char* name, const char* target) {
    return add_method(probe, ir(R"(
      (method (public static) "Ltags/Probe;.$NAME:(Ljava/lang/Object;)Z"
        ((load-param-object v0)
         (instance-of v0 "$TYPE")
         (move-result-pseudo v1)
         (return v1)))
    )",
                                {{"$NAME", name}, {"$TYPE", target}}));
  };
  auto* is_a = make_probe("isA", "Ltags/A;");
  auto* is_b = make_probe("isB", "Ltags/B;");

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 2);
  auto read_tagged_call = [](DexMethod* method) {
    DexMethodRef* call = nullptr;
    std::optional<int64_t> tag;
    method->get_code()->build_cfg();
    for (const auto& mie :
         cfg::InstructionIterable(method->get_code()->cfg())) {
      auto* insn = mie.insn;
      EXPECT_NE(insn->opcode(), OPCODE_INSTANCE_OF);
      if (insn->opcode() == OPCODE_CONST) {
        tag = insn->get_literal();
      } else if (insn->opcode() == OPCODE_INVOKE_STATIC) {
        EXPECT_EQ(insn->srcs_size(), 2u);
        call = insn->get_method();
      }
    }
    return std::make_pair(call, tag);
  };
  auto [a_call, a_tag] = read_tagged_call(is_a);
  auto [b_call, b_tag] = read_tagged_call(is_b);
  ASSERT_NE(a_call, nullptr);
  EXPECT_EQ(a_call, b_call);
  ASSERT_TRUE(a_tag.has_value());
  ASSERT_TRUE(b_tag.has_value());
  EXPECT_NE(*a_tag, *b_tag);
}

TEST_F(ClassMergingModelsTest, AnnotationSelectorChecksMarkedClassBodies) {
  define_marker();
  auto config = marker_model();
  auto* first = make_candidate("Lbodies/A;", type::java_lang_Object(), true);
  auto* reflected =
      make_candidate("Lbodies/B;", type::java_lang_Object(), true);
  add_method(first, R"(
    (method (public) "Lbodies/A;.classOfB:()Ljava/lang/Class;"
      ((load-param-object v0)
       (const-class "Lbodies/B;")
       (move-result-pseudo-object v1)
       (return-object v1)))
  )");

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_TRUE(contains_class(reflected));
}

TEST_F(ClassMergingModelsTest, UnresolvedAnnotationNameSelectsNothing) {
  define_marker();
  auto config = marker_model();
  config["target_annotations"].append("Lmissing/Typo;");
  auto* first = make_candidate("Ltypo/A;", type::java_lang_Object(), true);
  auto* second = make_candidate("Ltypo/B;", type::java_lang_Object(), true);

  auto metrics = run_merging({config});

  EXPECT_EQ(metrics.at(" total_class_merged"), 0);
  EXPECT_TRUE(contains_class(first));
  EXPECT_TRUE(contains_class(second));
}

TEST_F(ClassMergingModelsTest, HierarchyModelKeepsMarkedClassesItSelects) {
  define_marker();
  auto config = marker_model();
  config["name"] = "Outer";
  auto* root = make_class("Loverlap/Interface;", type::java_lang_Object());
  root->set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* interfaces = DexTypeList::make_type_list({root->get_type()});
  auto* first = make_candidate("Loverlap/A;", type::java_lang_Object(), true);
  auto* second = make_candidate("Loverlap/B;", type::java_lang_Object(), true);
  first->set_interfaces(interfaces);
  second->set_interfaces(interfaces);
  make_candidate("Loverlap/C;", type::java_lang_Object(), true);
  make_candidate("Loverlap/D;", type::java_lang_Object(), true);

  auto metrics = run_merging({config, model(root, "Inner")});

  EXPECT_EQ(metrics.at(" total_class_merged"), 4);
  size_t mergers_with_interface = 0;
  size_t mergers_without_interface = 0;
  for (const auto* cls : m_scope) {
    if (!cls->rstate.is_generated()) {
      continue;
    }
    if (cls->get_interfaces() == interfaces) {
      ++mergers_with_interface;
    } else if (cls->get_interfaces()->empty()) {
      ++mergers_without_interface;
    }
  }
  EXPECT_EQ(mergers_with_interface, 1u);
  EXPECT_EQ(mergers_without_interface, 1u);
}

TEST_F(ClassMergingModelsTest, MalformedAnnotationSelectorIsRejected) {
  auto config = model(object_root(), "Malformed");
  config["target_annotations"] = "not an array";

  EXPECT_THROW(run_merging({config}), RedexException);
}

TEST_F(ClassMergingModelsTest, NonStringAnnotationSelectorElementIsRejected) {
  auto config = model(object_root(), "NonString");
  config["target_annotations"].append(42);

  EXPECT_THROW(run_merging({config}), RedexException);
}

TEST_F(ClassMergingModelsTest, AnnotationSelectorRejectsInterfaceRoots) {
  define_marker();
  auto* root = make_class("Lroot/Interface;", type::java_lang_Object());
  root->set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto config = model(root, "InterfaceRoot");
  config["target_annotations"].append(kMarker);

  EXPECT_THROW(run_merging({config}), RedexException);
}
