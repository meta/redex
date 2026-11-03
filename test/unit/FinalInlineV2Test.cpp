/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAccess.h"
#include "FinalInlineV2.h"
#include "IFieldAnalysisUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "Walkers.h"

struct FinalInlineTest : public RedexTest {
 public:
  void SetUp() override {
    m_cc = std::make_unique<ClassCreator>(DexType::make_type("LFoo;"));
    m_cc->set_super(type::java_lang_Object());
  }

 protected:
  DexField* create_field_with_zero_value(const char* name,
                                         ClassCreator* class_creator,
                                         DexAccessFlags access = ACC_PUBLIC |
                                                                 ACC_STATIC) {
    auto* field = dynamic_cast<DexField*>(DexField::make_field(name));
    field->make_concrete(access,
                         DexEncodedValue::zero_for_type(field->get_type()));
    class_creator->add_field(field);
    return field;
  }

  static void run(const Scope& scope,
                  const XStoreRefs* xstores,
                  bool create_init_class_insns = false) {
    ConfigFiles conf = ConfigFiles(Json::nullValue);
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, create_init_class_insns);
    walk::code(scope, [&](DexMethod*, IRCode& code) { code.build_cfg(); });
    int min_sdk = 0;
    constant_propagation::NullCheckMethods state;
    FinalInlinePassV2::run(scope, conf, min_sdk, init_classes_with_side_effects,
                           xstores, state);

    auto eligible_ifields =
        constant_propagation::gather_safely_inferable_ifield_candidates(scope,
                                                                        {});
    FinalInlinePassV2::run_inline_ifields(scope, conf, min_sdk,
                                          init_classes_with_side_effects,
                                          xstores, eligible_ifields, state);
    walk::code(scope, [&](DexMethod*, IRCode& code) { code.clear_cfg(); });
  }

  std::unique_ptr<ClassCreator> m_cc;
};

TEST_F(FinalInlineTest, encodeValues) {
  auto* field = create_field_with_zero_value("LFoo;.bar:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (const v0 1)
      (sput v0 "LFoo;.bar:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  run({cls}, /* xstores */ nullptr);

  EXPECT_EQ(cls->get_clinit(), nullptr);
  EXPECT_EQ(field->get_static_value()->value(), 1);
}

TEST_F(FinalInlineTest, constructorUpdatesStaticFieldInClinit) {
  create_field_with_zero_value("LFoo;.sNextId:I", m_cc.get(),
                               ACC_PRIVATE | ACC_STATIC);
  create_field_with_zero_value("LFoo;.DEFAULT:LFoo;", m_cc.get(),
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  create_field_with_zero_value("LFoo;.NUM_TYPES:I", m_cc.get(),
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  auto* clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
      (
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LFoo;.<init>:()V")
        (sput-object v0 "LFoo;.DEFAULT:LFoo;")
        (sget "LFoo;.sNextId:I")
        (move-result-pseudo v1)
        (sput v1 "LFoo;.NUM_TYPES:I")
        (return-void)
      )
    )
  )");
  m_cc->add_method(clinit);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (sget "LFoo;.sNextId:I")
        (move-result-pseudo v1)
        (add-int/lit v1 v1 1)
        (sput v1 "LFoo;.sNextId:I")
        (return-void)
      )
    )
  )"));
  auto* num_types = assembler::method_from_string(R"(
    (method (public static) "LFoo;.numTypes:()I"
      (
        (sget "LFoo;.NUM_TYPES:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");
  m_cc->add_method(num_types);
  auto* cls = m_cc->create();
  const auto original_clinit = assembler::to_s_expr(clinit->get_code());
  const auto original_reader = assembler::to_s_expr(num_types->get_code());

  run({cls}, /* xstores */ nullptr);

  ASSERT_EQ(cls->get_clinit(), clinit);
  EXPECT_EQ(assembler::to_s_expr(clinit->get_code()), original_clinit);
  EXPECT_EQ(assembler::to_s_expr(num_types->get_code()), original_reader);
}

TEST_F(FinalInlineTest, encodeTypeValues) {
  ClassCreator cc2(DexType::make_type("LBar;"));
  cc2.set_super(type::java_lang_Object());
  auto* cls2 = cc2.create();

  auto* field =
      create_field_with_zero_value("LFoo;.bar:Ljava/lang/Class;", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (sput v0 "LFoo;.bar:Ljava/lang/Class;")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto store = DexStore("store");
  store.add_classes({cls, cls2});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_EQ(cls->get_clinit(), nullptr);
  EXPECT_EQ(field->get_static_value()->evtype(), DEVT_TYPE);
  EXPECT_EQ(
      dynamic_cast<DexEncodedValueType*>(field->get_static_value())->type(),
      cls2->get_type());
}

TEST_F(FinalInlineTest, encodeTypeValuesXStore) {
  ClassCreator cc2(DexType::make_type("LBar;"));
  cc2.set_super(type::java_lang_Object());
  auto* cls2 = cc2.create();

  auto* field =
      create_field_with_zero_value("LFoo;.bar:Ljava/lang/Class;", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (sput v0 "LFoo;.bar:Ljava/lang/Class;")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto store1 = DexStore("classes");
  store1.add_classes({cls});
  auto store2 = DexStore("other_store");
  store2.add_classes({cls2});
  DexStoresVector stores{store1, store2};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_NE(cls->get_clinit(), nullptr);
  EXPECT_EQ(field->get_static_value()->evtype(), DEVT_NULL);
}

TEST_F(FinalInlineTest, fieldSetInLoop) {
  auto* field_bar = create_field_with_zero_value("LFoo;.bar:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (:loop)
      (sget "LFoo;.bar:I")
      (move-result-pseudo v0)
      (add-int/lit v0 v0 1)
      (sput v0 "LFoo;.bar:I")
      (const v1 10)
      (if-ne v0 v1 :loop)
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto original = assembler::to_s_expr(cls->get_clinit()->get_code());
  run({cls}, /* xstores */ nullptr);
  EXPECT_EQ(assembler::to_s_expr(cls->get_clinit()->get_code()), original);
  EXPECT_EQ(field_bar->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, fieldConditionallySet) {
  auto* field_bar = create_field_with_zero_value("LFoo;.bar:I", m_cc.get());
  auto* field_baz = create_field_with_zero_value("LFoo;.baz:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (sget "LUnknown;.field:I")
      (move-result-pseudo v0)
      (if-eqz v0 :true)
      (const v1 1)
      (sput v1 "LFoo;.bar:I")
      (:true)
      ; bar may be 0 or 1 here
      (sget "LFoo;.bar:I")
      (move-result-pseudo v0)
      (sput v0 "LFoo;.baz:I")
      (sput v1 "LFoo;.bar:I")
      ; bar is always 1 on exit
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto original = assembler::to_s_expr(cls->get_clinit()->get_code());
  run({cls}, /* xstores */ nullptr);
  EXPECT_EQ(assembler::to_s_expr(cls->get_clinit()->get_code()), original);
  EXPECT_EQ(field_bar->get_static_value()->value(), 0);
  EXPECT_EQ(field_baz->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, dominatedSget) {
  auto* field_bar = create_field_with_zero_value("LFoo;.bar:I", m_cc.get());
  auto* field_baz = create_field_with_zero_value("LFoo;.baz:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (const v0 1)
      (sput v0 "LFoo;.bar:I")
      (sget "LFoo;.bar:I")
      (move-result-pseudo v0)
      (sput v0 "LFoo;.baz:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  // This could be further optimized to remove the sput to the field bar. This
  // test illustrates that we are being overly conservative if a field is
  // ever read in its <clinit>. In practice though this rarely occurs.
  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (sput v0 "LFoo;.bar:I")
      (return-void)
    )
  )");

  auto original = assembler::to_s_expr(cls->get_clinit()->get_code());
  run({cls}, /* xstores */ nullptr);
  EXPECT_CODE_EQ(cls->get_clinit()->get_code(), expected.get());
  EXPECT_EQ(field_bar->get_static_value()->value(), 0);
  EXPECT_EQ(field_baz->get_static_value()->value(), 1);
}

TEST_F(FinalInlineTest, ReplaceSgetAddInitClass) {
  ClassCreator cc2(DexType::make_type("LBar;"));
  cc2.set_super(type::java_lang_Object());
  cc2.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.<clinit>:()V"
     (
      (invoke-static () "Lunknown;.unknown:()V")
      (return-void)
     )
    )
  )"));
  auto* field = create_field_with_zero_value(
      "LBar;.bar:I", &cc2, ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  auto* cls2 = cc2.create();

  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.getbar:()I"
     (
      (sget "LBar;.bar:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto store = DexStore("store");
  store.add_classes({cls, cls2});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores, /* create_init_class_insns */ true);

  auto expected = assembler::ircode_from_string(R"(
    (
      (init-class "LBar;")
      (const v0 0)
      (return v0)
    )
  )");
  EXPECT_EQ(cls->get_all_methods().size(), 1);
  EXPECT_CODE_EQ(cls->get_all_methods()[0]->get_code(), expected.get());
  EXPECT_EQ(field->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, ReplaceSgetNoInitClass) {
  ClassCreator cc2(DexType::make_type("LBar;"));
  cc2.set_super(type::java_lang_Object());
  cc2.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.<clinit>:()V"
     (
      (return-void)
     )
    )
  )"));
  auto* field = create_field_with_zero_value(
      "LBar;.bar:I", &cc2, ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  auto* cls2 = cc2.create();

  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.getbar:()I"
     (
      (sget "LBar;.bar:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto store = DexStore("store");
  store.add_classes({cls, cls2});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores, /* create_init_class_insns */ true);

  auto expected = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (return v0)
    )
  )");
  EXPECT_EQ(cls->get_all_methods().size(), 1);
  EXPECT_CODE_EQ(cls->get_all_methods()[0]->get_code(), expected.get());
  EXPECT_EQ(field->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, dominatedSgetRConst) {
  auto* field_bar = create_field_with_zero_value("LFoo;.bar:I", m_cc.get());
  auto* field_baz = create_field_with_zero_value("LFoo;.baz:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (r-const v0 2131230721)
      (sput v0 "LFoo;.bar:I")
      (sget "LFoo;.bar:I")
      (move-result-pseudo v0)
      (sput v0 "LFoo;.baz:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  // Unlike with regular const instructions, we can't remove the sput to these
  // fields since they would lose their resource ID properties
  auto expected = assembler::ircode_from_string(R"(
    (
      (r-const v0 2131230721)
      (sput v0 "LFoo;.bar:I")
      (r-const v0 2131230721)
      (sput v0 "LFoo;.baz:I")
      (return-void)
    )
  )");

  run({cls}, /* xstores */ nullptr);
  EXPECT_CODE_EQ(cls->get_clinit()->get_code(), expected.get());
  EXPECT_EQ(field_bar->get_static_value()->value(), 0);
  EXPECT_EQ(field_baz->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, encodeRConst) {
  ClassCreator cc2(DexType::make_type("LBar;"));
  cc2.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.go:()I"
     (
      (sget "LFoo;.app_name:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )"));
  cc2.set_super(type::java_lang_Object());
  auto* bar = cc2.create();

  create_field_with_zero_value("LFoo;.app_name:I", m_cc.get(),
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (r-const v0 2131230721)
      (sput v0 "LFoo;.app_name:I")
      (return-void)
     )
    )
  )"));
  auto* foo = m_cc->create();

  auto store = DexStore("store");
  store.add_classes({foo, bar});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  auto expected = assembler::ircode_from_string(R"(
    (
      (r-const v0 2131230721)
      (return v0)
    )
  )");
  EXPECT_EQ(bar->get_all_methods().size(), 1);
  EXPECT_CODE_EQ(bar->get_all_methods()[0]->get_code(), expected.get());
}

TEST_F(FinalInlineTest, rConstInstanceFieldInlining) {
  // Create a class with a final instance field
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.resId:I"));
  field->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(field);

  // Constructor stores an r-const value into the instance field
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (r-const v1 2131230721)
      (iput v1 v0 "LFoo;.resId:I")
      (return-void)
     )
    )
  )"));

  // Reader method that gets the field
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getResId:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.resId:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto* cls = m_cc->create();

  auto store = DexStore("store");
  store.add_classes({cls});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  // The iget should be replaced with r-const
  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (r-const v0 2131230721)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}
