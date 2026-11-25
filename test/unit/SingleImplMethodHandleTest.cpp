/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "SingleImpl.h"

namespace {

// The interface `LI;` with the method `m` has the only implementation
// `LImpl;`. `LUser;.use` holds what each test names `LI;` in.
class SingleImplMethodHandleTest : public RedexTest {
 protected:
  void SetUp() override {
    // As in an app, `java.lang.Object` resolves to an external class.
    create_object_class();
    type_class(type::java_lang_Object())->set_external();
    ClassCreator intf(DexType::make_type("LI;"));
    intf.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    intf.set_super(type::java_lang_Object());
    intf.add_method(DexMethod::make_method("LI;.m:()V")
                        ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                                        /* is_virtual */ true));
    m_intf = intf.create();

    ClassCreator impl(DexType::make_type("LImpl;"));
    impl.set_access(ACC_PUBLIC);
    impl.set_super(type::java_lang_Object());
    impl.add_interface(m_intf->get_type());
    impl.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LImpl;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (return-void))))"));
    impl.add_method(assembler::method_from_string(R"(
      (method (public) "LImpl;.m:()V"
        ((load-param-object v0) (return-void))))"));
    m_impl = impl.create();
  }

  IRCode* make_user(const std::string& code) {
    ClassCreator user(DexType::make_type("LUser;"));
    user.set_access(ACC_PUBLIC);
    user.set_super(type::java_lang_Object());
    user.add_method(assembler::method_from_string(R"(
      (method (public static) "LUser;.take:(LI;)V"
        ((load-param-object v0) (return-void))))"));
    auto* use = assembler::method_from_string(
        "(method (public static) \"LUser;.use:()V\" " + code + ")");
    user.add_method(use);
    m_user = user.create();
    return use->get_code();
  }

  // Runs the pass and returns whether `LI;` remains.
  bool run_pass_and_find_interface() {
    DexStore store("classes");
    store.add_classes({m_intf, m_impl, m_user});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    SingleImplPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    manager.run_passes(stores, config);
    const auto& classes = stores[0].get_dexen()[0];
    return std::find(classes.begin(), classes.end(), m_intf) != classes.end();
  }

  DexClass* m_intf{nullptr};
  DexClass* m_impl{nullptr};
  DexClass* m_user{nullptr};
};

// The body of `LUser;.use` in which every reference to `LI;` is one that the
// pass rewrites.
constexpr const char* kRewritableUses = R"((
  (new-instance "LImpl;")
  (move-result-pseudo-object v0)
  (invoke-direct (v0) "LImpl;.<init>:()V")
  (invoke-interface (v0) "LI;.m:()V")
  (invoke-static (v0) "LUser;.take:(LI;)V")
  (return-void)
))";

std::unique_ptr<DexAnnotationSet> make_annotation_set(
    std::unique_ptr<DexEncodedValue> value) {
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element("value", std::move(value));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  return annotation_set;
}

} // namespace

// Without anything that the pass cannot rewrite, it removes `LI;`.
TEST_F(SingleImplMethodHandleTest, removesInterfaceThatOnlyCodeNames) {
  make_user(kRewritableUses);
  EXPECT_FALSE(run_pass_and_find_interface());
}

// The handle would name the method of a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceWhoseMethodHandleCalls) {
  make_user(R"((
    (const-method-handle invoke-interface "LI;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The pass changes `take` to take `LImpl;`, so the method type of the handle,
// on which `invokeExact` callers depend, would change.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInPrototypeOfHandledMethod) {
  make_user(R"((
    (const-method-handle invoke-static "LUser;.take:(LI;)V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The call-site prototype would name a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInCallSitePrototype) {
  make_user(R"((
    (const v0 0)
    (new-instance "LImpl;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LImpl;.<init>:()V")
    (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LI;)V")
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The method type of the call site would name a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInCallSiteMethodType) {
  auto* code = make_user(R"((
    (invoke-static () "LUser;.placeholder:()LI;")
    (move-result-object v0)
    (return-void)
  ))");
  redex::make_invoke_custom(code, "make", "()LI;");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The method type of an annotation of a class would name a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInAnnotationMethodType) {
  make_user(kRewritableUses);
  ASSERT_TRUE(m_user->attach_annotation_set(make_annotation_set(
      std::make_unique<DexEncodedValueMethodType>(DexProto::make_proto(
          type::_void(), DexTypeList::make_type_list({m_intf->get_type()}))))));
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The pass changes `take` to take `LImpl;`. The handle that a static field
// value holds names the same method, so its type would change with it. This is
// defensive: an exact call of the handle names `LI;` in its call-site
// prototype, which keeps `LI;` by itself, and ART rejects a method handle as
// the initial value of a static field.
TEST_F(SingleImplMethodHandleTest,
       keepsInterfaceInPrototypeOfStaticValueHandle) {
  make_user(kRewritableUses);
  m_user->add_field(
      DexField::make_field("LUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "LUser;.take:(LI;)V"))));
  EXPECT_TRUE(run_pass_and_find_interface());
}

// A handle in a parameter annotation would name the method of a removed
// interface.
TEST_F(SingleImplMethodHandleTest,
       keepsInterfaceWhoseMethodParameterAnnotationHandleCalls) {
  make_user(kRewritableUses);
  auto* annotated = assembler::method_from_string(R"(
    (method (public static synthetic) "LUser;.annotated:(I)V"
      ((load-param v0) (return-void))))");
  annotated->attach_param_annotation_set(
      0,
      make_annotation_set(std::make_unique<DexEncodedValueMethodHandle>(
          redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_INTERFACE,
                                    "LI;.m:()V"))));
  m_user->add_method(annotated);
  EXPECT_TRUE(run_pass_and_find_interface());
}

// A method type inside an array inside a nested annotation counts too, and an
// array of the interface names the interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInNestedAnnotationMethodType) {
  make_user(kRewritableUses);
  auto* elements = new DexEncodedValueArray::Storage();
  elements->push_back(
      std::make_unique<DexEncodedValueMethodType>(DexProto::make_proto(
          DexType::make_type("[LI;"), DexTypeList::make_type_list({}))));
  EncodedAnnotations nested;
  nested.emplace_back(DexString::make_string("types"),
                      std::make_unique<DexEncodedValueArray>(elements));
  ASSERT_TRUE(m_user->attach_annotation_set(
      make_annotation_set(std::make_unique<DexEncodedValueAnnotation>(
          DexType::make_type("LNested;"), std::move(nested)))));
  EXPECT_TRUE(run_pass_and_find_interface());
}
