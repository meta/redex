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
#include "RedexTestUtils.h"
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
        constant_propagation::gather_safely_inferable_ifield_candidates(
            scope,
            constant_propagation::gather_constructor_only_ifields(
                scope, local_pointers::analyze_constructors(scope, {})),
            {});
    FinalInlinePassV2::run_inline_ifields(scope, conf, min_sdk,
                                          init_classes_with_side_effects,
                                          xstores, eligible_ifields, state);
    walk::code(scope, [&](DexMethod*, IRCode& code) { code.clear_cfg(); });
  }

  std::unique_ptr<ClassCreator> m_cc;
};

TEST_F(FinalInlineTest, finalFieldOfMultiConstructorClassIsEligible) {
  auto* count = DexField::make_field("LFoo;.count:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(count);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (const v1 7) (iput v1 v0 "LFoo;.count:I") (return-void)))
  )"));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(I)V"
      ((load-param-object v0) (load-param v1)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (iput v1 v0 "LFoo;.count:I") (return-void)))
  )"));
  auto* cls = m_cc->create();
  const Scope scope{cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  // Both constructors store `count` only through `this`.
  auto eligible =
      constant_propagation::gather_safely_inferable_ifield_candidates(
          scope,
          constant_propagation::gather_constructor_only_ifields(
              scope, local_pointers::analyze_constructors(scope, {})),
          {});
  EXPECT_EQ(eligible.count(count), 1u);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(FinalInlineTest, storeOfExcludedConstructorIsNotConstructorOnly) {
  auto* count = DexField::make_field("LFoo;.count:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(count);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (const v1 7) (iput v1 v0 "LFoo;.count:I") (return-void)))
  )");
  m_cc->add_method(ctor);
  auto* cls = m_cc->create();
  const Scope scope{cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  const auto analyzed = local_pointers::analyze_constructors(scope, {});
  EXPECT_EQ(
      constant_propagation::gather_constructor_only_ifields(scope, analyzed)
          .count(count),
      1u);
  // The constructor's code may differ at runtime.
  ctor->rstate.set_no_optimizations();
  EXPECT_EQ(
      constant_propagation::gather_constructor_only_ifields(scope, analyzed)
          .count(count),
      0u);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(FinalInlineTest, constructorWritesOtherInstance) {
  auto* count =
      DexField::make_field("LFoo;.count:I")->make_concrete(ACC_PUBLIC);
  m_cc->add_field(count);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-static () "LRegistry;.current:()LFoo;")
      (move-result-object v2)
      (const v3 7)
      (iput v3 v2 "LFoo;.count:I")
      (return-void)
     )
    )
  )"));
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getCount:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.count:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto original = assembler::to_s_expr(reader->get_code());

  run({m_cc->create()}, /* xstores */ nullptr);

  EXPECT_EQ(assembler::to_s_expr(reader->get_code()), original);
}

TEST_F(FinalInlineTest, constructorMixedReceiverWriteIsNotInitialization) {
  m_cc->add_field(DexField::make_field("LFoo;.count:I")
                      ->make_concrete(ACC_PUBLIC | ACC_FINAL));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(Ljava/lang/Object;Z)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (if-eqz v2 :other_path)
      (move-object v3 v0)
      (goto :join)
      (:other_path)
      (check-cast v1 "LFoo;")
      (move-result-pseudo-object v3)
      (:join)
      (const v4 7)
      (iput v4 v3 "LFoo;.count:I")
      (const v4 1)
      (iput v4 v0 "LFoo;.count:I")
      (return-void)
     )
    )
  )"));
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getCount:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.count:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto original = assembler::to_s_expr(reader->get_code());

  run({m_cc->create()}, /* xstores */ nullptr);

  EXPECT_EQ(assembler::to_s_expr(reader->get_code()), original);
}

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

// A <clinit> call whose target is unknown may run code that reads a field
// before the <clinit> writes it, so the field keeps its <clinit>. The missing
// LibListener may declare onEvent(), so the target is unknown:
//   interface Known { default void onEvent() {} }
//   interface Listener extends LibListener, Known {}
//   class Impl implements Listener { void onEvent() { Bar.seen = Foo.y; } }
//   class Foo { static int y; static { new Impl().onEvent(); y = 5; } }
TEST_F(FinalInlineTest, unknownCalleeReadsFieldMissingSuperinterface) {
  ClassCreator listener_cc(DexType::make_type("LListener;"));
  listener_cc.set_super(type::java_lang_Object());
  listener_cc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  listener_cc.add_interface(DexType::make_type("LLibListener;"));
  listener_cc.add_interface(DexType::make_type("LKnown;"));
  ClassCreator known_cc(DexType::make_type("LKnown;"));
  known_cc.set_super(type::java_lang_Object());
  known_cc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  known_cc.add_method(assembler::method_from_string(R"(
    (method (public) "LKnown;.onEvent:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  ClassCreator impl_cc(DexType::make_type("LImpl;"));
  impl_cc.set_super(type::java_lang_Object());
  impl_cc.add_interface(DexType::make_type("LListener;"));
  impl_cc.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LImpl;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
     )
    )
  )"));
  impl_cc.add_method(assembler::method_from_string(R"(
    (method (public) "LImpl;.onEvent:()V"
     (
      (load-param-object v0)
      (sget "LFoo;.y:I")
      (move-result-pseudo v1)
      (sput v1 "LBar;.seen:I")
      (return-void)
     )
    )
  )"));
  ClassCreator bar_cc(DexType::make_type("LBar;"));
  bar_cc.set_super(type::java_lang_Object());
  create_field_with_zero_value("LBar;.seen:I", &bar_cc);
  auto* field_y = create_field_with_zero_value("LFoo;.y:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
     (
      (new-instance "LImpl;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LImpl;.<init>:()V")
      (invoke-interface (v0) "LListener;.onEvent:()V")
      (const v1 5)
      (sput v1 "LFoo;.y:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto original = assembler::to_s_expr(cls->get_clinit()->get_code());
  run({known_cc.create(), listener_cc.create(), impl_cc.create(),
       bar_cc.create(), cls},
      /* xstores */ nullptr);
  ASSERT_NE(cls->get_clinit(), nullptr);
  EXPECT_EQ(assembler::to_s_expr(cls->get_clinit()->get_code()), original);
  EXPECT_EQ(field_y->get_static_value()->value(), 0);
}

// As above, through a missing superclass that may declare m():
//   interface Known { default void m() {} }
//   class D extends LibBase implements Known {}
//   class Impl extends D { void m() { Bar.seen = Foo.y; } }
//   class Foo { static int y; static { D d = new Impl(); d.m(); y = 5; } }
TEST_F(FinalInlineTest, unknownCalleeReadsFieldMissingSuperclass) {
  ClassCreator known_cc(DexType::make_type("LKnown;"));
  known_cc.set_super(type::java_lang_Object());
  known_cc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  known_cc.add_method(assembler::method_from_string(R"(
    (method (public) "LKnown;.m:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  ClassCreator d_cc(DexType::make_type("LD;"));
  d_cc.set_super(DexType::make_type("LLibBase;"));
  d_cc.add_interface(DexType::make_type("LKnown;"));
  d_cc.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LD;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LLibBase;.<init>:()V")
      (return-void)
     )
    )
  )"));
  ClassCreator impl_cc(DexType::make_type("LImpl;"));
  impl_cc.set_super(DexType::make_type("LD;"));
  impl_cc.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LImpl;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LD;.<init>:()V")
      (return-void)
     )
    )
  )"));
  impl_cc.add_method(assembler::method_from_string(R"(
    (method (public) "LImpl;.m:()V"
     (
      (load-param-object v0)
      (sget "LFoo;.y:I")
      (move-result-pseudo v1)
      (sput v1 "LBar;.seen:I")
      (return-void)
     )
    )
  )"));
  ClassCreator bar_cc(DexType::make_type("LBar;"));
  bar_cc.set_super(type::java_lang_Object());
  create_field_with_zero_value("LBar;.seen:I", &bar_cc);
  auto* field_y = create_field_with_zero_value("LFoo;.y:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
     (
      (new-instance "LImpl;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LImpl;.<init>:()V")
      (invoke-virtual (v0) "LD;.m:()V")
      (const v1 5)
      (sput v1 "LFoo;.y:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  auto original = assembler::to_s_expr(cls->get_clinit()->get_code());
  run({known_cc.create(), d_cc.create(), impl_cc.create(), bar_cc.create(),
       cls},
      /* xstores */ nullptr);
  ASSERT_NE(cls->get_clinit(), nullptr);
  EXPECT_EQ(assembler::to_s_expr(cls->get_clinit()->get_code()), original);
  EXPECT_EQ(field_y->get_static_value()->value(), 0);
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

// `LFoo;.<clinit>` calls a method on null, so it never completes normally and
// `X` never holds a value. `LBar;.<clinit>` sets `y` to 1, or reads `X` in a
// try block whose handler sets `y` to 2. The read throws, so `y` can be 2, and
// reads of it must not fold to 1.
TEST_F(FinalInlineTest,
       handlerOfReadOfFieldThatNeverHoldsAValueStaysReachable) {
  create_field_with_zero_value("LFoo;.X:I", m_cc.get(),
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
      (
        (const v0 0)
        (invoke-virtual (v0) "Ljava/lang/Object;.hashCode:()I")
        (return-void)
      )
    )
  )"));
  auto* foo = m_cc->create();

  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  create_field_with_zero_value("LBar;.y:I", &bar_creator,
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  bar_creator.add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LBar;.<clinit>:()V"
      (
        (sget "LUnknown;.field:I")
        (move-result-pseudo v0)
        (if-eqz v0 :read)
        (const v1 1)
        (sput v1 "LBar;.y:I")
        (return-void)
        (:read)
        (.try_start a)
        (sget "LFoo;.X:I")
        (move-result-pseudo v0)
        (.try_end a)
        (sput v0 "LBar;.y:I")
        (return-void)
        (.catch (a))
        (const v1 2)
        (sput v1 "LBar;.y:I")
        (return-void)
      )
    )
  )"));
  auto* read = assembler::method_from_string(R"(
    (method (public static) "LBar;.read:()I"
      (
        (sget "LBar;.y:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");
  bar_creator.add_method(read);
  auto* bar = bar_creator.create();
  const auto original_read = assembler::to_s_expr(read->get_code());

  run({foo, bar}, /* xstores */ nullptr);

  EXPECT_EQ(assembler::to_s_expr(read->get_code()), original_read);
}

TEST_F(FinalInlineTest, writeToOwnFieldOfOtherObjectBlocksInference) {
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  // Java: Foo(Holder h) { h.foo.x = 1; }
  // The store goes to another Foo, so a new Foo's x stays 0.
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget-object v1 "LHolder;.foo:LFoo;")
      (move-result-pseudo-object v2)
      (const v3 1)
      (iput v3 v2 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getX:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(reader->get_code()));

  run({cls}, nullptr);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, writeThroughRegisterThatMayBeThisBlocksInference) {
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  // Java: Foo(Holder h, boolean b) { Foo f = b ? this : h.foo; f.x = 1; }
  // With b false this.x stays 0, so getX() must not be folded to 1.
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;Z)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (move-object v3 v0)
      (if-nez v2 :join)
      (iget-object v1 "LHolder;.foo:LFoo;")
      (move-result-pseudo-object v3)
      (:join)
      (const v4 1)
      (iput v4 v3 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getX:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(reader->get_code()));

  run({cls}, nullptr);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

// A method handle call that receives the object under construction can read
// its fields before the constructor sets them, so they keep their stores.
TEST_F(FinalInlineTest, instanceFieldReadThroughMethodHandleInConstructor) {
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.x:I"));
  field->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(field);
  create_field_with_zero_value("LFoo;.LOG:Ljava/lang/invoke/MethodHandle;",
                               m_cc.get());

  // Foo() throws Throwable { LOG.invokeExact(this); x = 5; }
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (sget-object "LFoo;.LOG:Ljava/lang/invoke/MethodHandle;")
      (move-result-pseudo-object v1)
      (invoke-polymorphic (v1 v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LFoo;)V")
      (const v2 5)
      (iput v2 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));

  // A read of x, as in what LOG calls.
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getX:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto* cls = m_cc->create();
  auto expected = std::make_unique<IRCode>(*reader->get_code());

  auto store = DexStore("store");
  store.add_classes({cls});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

// The same holds for a call site, here reached from a method the constructor
// calls on the object.
TEST_F(FinalInlineTest, instanceFieldReadThroughCallSiteInCallee) {
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.x:I"));
  field->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(field);

  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-direct (v0) "LFoo;.log:()V")
      (const v1 5)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));

  // Tool-generated: log() passes `this` to an invoke-custom.
  auto* log = assembler::method_from_string(R"(
    (method (private) "LFoo;.log:()V"
     (
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.placeholder:(LFoo;)V")
      (return-void)
     )
    )
  )");
  redex::make_invoke_custom(log->get_code(), "log", "(LFoo;)V");
  m_cc->add_method(log);

  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getX:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )");
  m_cc->add_method(reader);
  auto* cls = m_cc->create();
  auto expected = std::make_unique<IRCode>(*reader->get_code());

  auto store = DexStore("store");
  store.add_classes({cls});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}
