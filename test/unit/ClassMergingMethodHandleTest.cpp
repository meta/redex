/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <functional>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "ClassMergingTestFixture.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "RedexTestUtils.h"
#include "Resolver.h"
#include "ScopeHelper.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace class_merging_test;

namespace {

// `Lcom/redextest/Base;` has the mergeable subclasses `Lcom/redextest/A;` and
// `Lcom/redextest/B;`.
class ClassMergingMethodHandleTest : public ClassMergingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redextest/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
    m_a = make_mergeable("Lcom/redextest/A;");
    m_b = make_mergeable("Lcom/redextest/B;");
  }

  // Runs one model for the subclasses of `Base`, which `edit_model` may
  // change, and returns whether `A` was merged away.
  bool run_merging(const std::function<void(Json::Value&)>& edit_model = {}) {
    Json::Value model;
    model["name"] = "Handles";
    model["class_name_prefix"] = "Handles";
    model["roots"].append("Lcom/redextest/Base;");
    model["include_primary_dex"] = true;
    if (edit_model) {
      edit_model(model);
    }
    ClassMergingTest::run_merging({model});
    return std::none_of(m_scope.begin(), m_scope.end(), [](DexClass* cls) {
      return cls->get_type() == DexType::get_type("Lcom/redextest/A;");
    });
  }

  // The method handles that the code in the scope holds.
  std::vector<DexMethodHandle*> held_method_handles() {
    std::vector<DexMethodHandle*> method_handles;
    walk::opcodes(m_scope, [&](DexMethod*, IRInstruction* insn) {
      for_each_method_handle(insn, [&](const DexMethodHandle* handle) {
        method_handles.push_back(const_cast<DexMethodHandle*>(handle));
      });
    });
    return method_handles;
  }

  DexClass* m_a{nullptr};
  DexClass* m_b{nullptr};
};

} // namespace

// Merging would make the private method `A.p` public and virtual, and move the
// code that holds its invoke-direct handle, so `A` stays apart.
TEST_F(ClassMergingMethodHandleTest,
       invokeDirectHandleOfPrivateMethodKeepsClass) {
  add_method(m_a, R"(
    (method (private) "Lcom/redextest/A;.p:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "Lcom/redextest/A;.p:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// A handle in another class that names `A.run` keeps `A`, whose `run` merging
// would replace with a dispatch in the merger.
TEST_F(ClassMergingMethodHandleTest, handleOfMethodKeepsItsClass) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-instance "Lcom/redextest/A;.run:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// A handle that names `Base.other` through `A` names `A`, which must go on
// existing for the handle to resolve.
TEST_F(ClassMergingMethodHandleTest, handleOfInheritedMethodKeepsNamedClass) {
  add_virtual(m_base, "other");
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-instance "Lcom/redextest/A;.other:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// What an invoke-direct handle of a method that is not private runs depends on
// the class of the code that holds it: from `A`, which inherits `Base.other`,
// every ART version runs `Base.other`, but from the merger, which overrides
// `other` for `B`, Android 9 would run that override. So `A` stays apart.
TEST_F(ClassMergingMethodHandleTest,
       invokeDirectHandleOfInheritedMethodKeepsHolder) {
  add_virtual(m_base, "other");
  add_virtual(m_b, "other");
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "Lcom/redextest/Base;.other:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// Without method handles, `A` and `B` merge.
TEST_F(ClassMergingMethodHandleTest, classesWithoutHandlesMerge) {
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_TRUE(run_merging());
}

// The merger has the superclass of `A` and `B`, so an invoke-super in their
// code calls the same method from the merger, and they merge.
TEST_F(ClassMergingMethodHandleTest, invokeSuperWithoutHandlesMerges) {
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (invoke-super (v0) "Lcom/redextest/Base;.run:()V")
      (return-void)
     )
    )
  )");

  EXPECT_TRUE(run_merging());
}

// Merging `A` and `B` makes the constructors `User(A)` and `User(B)` collide,
// which a type reference update resolves by adding a parameter to one of
// them. A method handle cannot pass it.
TEST_F(ClassMergingMethodHandleTest,
       constructorHandleKeepsTheTypesOfItsParameters) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  for (const auto* param : {"Lcom/redextest/A;", "Lcom/redextest/B;"}) {
    add_method(user, std::string(R"(
      (method (public constructor) "Lcom/redextest/User;.<init>:()") +
                         param + R"()V"
       (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
       )
      )
    )");
  }
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-constructor "Lcom/redextest/User;.<init>:(Lcom/redextest/A;)V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
  auto method_handles = held_method_handles();
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(show(method_handles[0]->methodref()),
            "Lcom/redextest/User;.<init>:(Lcom/redextest/A;)V");
}

namespace {

// A call site in the static method `User.use` whose only bootstrap argument is
// the Class of `type`.
DexCallSite* add_call_site_with_class_argument(DexClass* user,
                                               const char* type) {
  auto* use = assembler::method_from_string(R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (invoke-static () "Lcom/redextest/User;.placeholder:()V")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueType>(DexType::make_type(type)));
  auto* callsite =
      redex::make_invoke_custom(use->get_code(), "run", "()V", std::move(args));
  use->get_code()->build_cfg();
  user->add_method(use);
  return callsite;
}

// The Class that `callsite` passes to its bootstrap method.
std::string class_argument_of(const DexCallSite* callsite) {
  return show(
      redex::encoded_value_as<DexEncodedValueType>(callsite->args().at(0).get())
          ->type());
}

// The Class that the call site of `User.use` passes to its bootstrap method.
std::string class_argument() {
  std::string type;
  Scope scope{type_class(DexType::get_type("Lcom/redextest/User;"))};
  walk::opcodes(scope, [&](DexMethod*, IRInstruction* insn) {
    if (insn->has_callsite()) {
      type = class_argument_of(insn->get_callsite());
    }
  });
  return type;
}

} // namespace

// Without type tags, merging makes a const-class of `A` name the merged class;
// a Class of `A` among the bootstrap arguments of a call site must too.
TEST_F(ClassMergingMethodHandleTest,
       classArgumentNamesTheMergedClassWithoutTypeTags) {
  // Classes with true virtual methods are not merged without type tags.
  for (auto* cls : {m_a, m_b}) {
    cls->remove_method(cls->get_vmethods().front());
  }
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  auto* callsite =
      add_call_site_with_class_argument(user, "[Lcom/redextest/A;");

  EXPECT_TRUE(run_merging([](Json::Value& model) {
    model["type_tag_config"] = "none";
    model["interdex_grouping"] = "disabled";
  }));
  EXPECT_EQ(class_argument().rfind("[Lcom/redextest/HandlesBaseShape", 0), 0)
      << class_argument();
  EXPECT_EQ(class_argument_of(callsite), "[Lcom/redextest/A;");
}

// ART links each call site once, so instructions that share a call site must
// share its replacement.
TEST_F(ClassMergingMethodHandleTest,
       sharedCallSiteWithClassArgumentStaysShared) {
  for (auto* cls : {m_a, m_b}) {
    cls->remove_method(cls->get_vmethods().front());
  }
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  auto* use = assembler::method_from_string(R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (invoke-static () "Lcom/redextest/User;.placeholder:()V")
      (invoke-static () "Lcom/redextest/User;.placeholder:()V")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueType>(
      DexType::make_type("Lcom/redextest/A;")));
  auto* callsite =
      redex::make_invoke_custom(use->get_code(), "run", "()V", std::move(args));
  use->get_code()->build_cfg();
  user->add_method(use);

  EXPECT_TRUE(run_merging([](Json::Value& model) {
    model["type_tag_config"] = "none";
    model["interdex_grouping"] = "disabled";
  }));
  std::vector<DexCallSite*> callsites;
  walk::opcodes(Scope{user}, [&](DexMethod*, IRInstruction* insn) {
    if (insn->has_callsite()) {
      callsites.push_back(insn->get_callsite());
    }
  });
  ASSERT_EQ(callsites.size(), 2);
  EXPECT_NE(callsites[0], callsite);
  EXPECT_EQ(callsites[0], callsites[1]);
}

// With type tags, a const-class of `A` must only reach methods of classes in
// `const_class_safe_types`, since the merged class stands for `B` too. A Class
// of `A` among the bootstrap arguments of a call site reaches the bootstrap
// method.
TEST_F(ClassMergingMethodHandleTest, classArgumentKeepsItsClassWithTypeTags) {
  make_class("LBoot;", type::java_lang_Object());
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_call_site_with_class_argument(user, "Lcom/redextest/A;");

  EXPECT_FALSE(run_merging());
  EXPECT_EQ(class_argument(), "Lcom/redextest/A;");
}

// As for a const-class passed to such a method, a bootstrap method of a class
// in `const_class_safe_types` may receive the Class of the merged class.
TEST_F(ClassMergingMethodHandleTest,
       classArgumentToConstClassSafeBootstrapNamesTheMergedClass) {
  make_class("LBoot;", type::java_lang_Object());
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_call_site_with_class_argument(user, "Lcom/redextest/A;");

  EXPECT_TRUE(run_merging([](Json::Value& model) {
    model["const_class_safe_types"].append("LBoot;");
  }));
  EXPECT_EQ(class_argument().rfind("Lcom/redextest/HandlesBaseShape", 0), 0)
      << class_argument();
}

namespace {

// Gives `A` and `B` the instance field `f` of type `type`.
void add_instance_fields(const std::vector<DexClass*>& classes,
                         const std::string& type) {
  for (auto* cls : classes) {
    cls->add_field(
        DexField::make_field(cls->get_type()->str_copy() + ".f:" + type)
            ->make_concrete(ACC_PUBLIC));
  }
}

// Gives `cls` a static field whose value is a method handle of kind `type` for
// `ref`, and returns the field.
DexField* add_method_handle_value(DexClass* cls,
                                  MethodHandleType type,
                                  const std::string& ref) {
  auto* field =
      DexField::make_field(cls->get_type()->str_copy() + ".HANDLE" +
                           std::to_string(cls->get_sfields().size()) +
                           ":Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::make_unique<DexEncodedValueMethodHandle>(
                              redex::make_method_handle(type, ref)));
  cls->add_field(field);
  return field;
}

DexMethodHandle* method_handle_value(const DexField* field) {
  return redex::encoded_value_as<DexEncodedValueMethodHandle>(
             field->get_static_value())
      ->methodhandle();
}

// Gives `cls` an annotation whose only element is `value`.
void annotate(DexClass* cls, std::unique_ptr<DexEncodedValue> value) {
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("Lcom/redextest/Anno;"), DAV_RUNTIME);
  annotation->add_element("value", std::move(value));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(cls->attach_annotation_set(std::move(annotation_set)));
}

} // namespace

// A method handle that a static field value holds keeps a class from being
// merged as one that code holds does.
TEST_F(ClassMergingMethodHandleTest, staticFieldValueFieldHandleKeepsItsClass) {
  add_instance_fields({m_a, m_b}, "B");
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  auto* getter = add_method_handle_value(user, METHOD_HANDLE_TYPE_INSTANCE_GET,
                                         "Lcom/redextest/A;.f:B");

  EXPECT_FALSE(run_merging());
  EXPECT_EQ(show(method_handle_value(getter)->fieldref()),
            "Lcom/redextest/A;.f:B");
}

TEST_F(ClassMergingMethodHandleTest,
       staticFieldValueConstructorHandleKeepsItsClass) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  auto* constructor =
      add_method_handle_value(user, METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR,
                              "Lcom/redextest/A;.<init>:()V");

  EXPECT_FALSE(run_merging());
  EXPECT_EQ(show(method_handle_value(constructor)->methodref()),
            "Lcom/redextest/A;.<init>:()V");
}

// An annotation keeps the classes that its method handles and method types
// name from being merged, like those that its method and field values name.
TEST_F(ClassMergingMethodHandleTest, annotationConstructorHandleKeepsItsClass) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  annotate(user,
           std::make_unique<DexEncodedValueMethodHandle>(
               redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR,
                                         "Lcom/redextest/A;.<init>:()V")));

  EXPECT_FALSE(run_merging());
}

TEST_F(ClassMergingMethodHandleTest, annotationFieldHandleKeepsItsClass) {
  add_instance_fields({m_a, m_b}, "I");
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  annotate(
      user,
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INSTANCE_GET, "Lcom/redextest/A;.f:I")));

  EXPECT_FALSE(run_merging());
}

TEST_F(ClassMergingMethodHandleTest, annotationMethodTypeKeepsItsClasses) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  annotate(user,
           std::make_unique<DexEncodedValueMethodType>(
               DexProto::make_proto("([Lcom/redextest/A;)V")));

  EXPECT_FALSE(run_merging());
}
