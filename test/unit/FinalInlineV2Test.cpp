/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <sstream>

#include "Creators.h"
#include "DexAccess.h"
#include "EditableCfgAdapter.h"
#include "FinalInlineV2.h"
#include "IFieldAnalysisUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Show.h"
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

  void add_instance_field(const char* name) {
    m_cc->add_field(DexField::make_field(name)->make_concrete(ACC_PRIVATE));
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

    const auto constructor_only_ifields =
        constant_propagation::gather_constructor_only_ifields(
            scope, local_pointers::analyze_constructors(scope, {}));
    auto eligible_ifields =
        constant_propagation::gather_safely_inferable_ifield_candidates(
            scope, constructor_only_ifields, {});
    FinalInlinePassV2::run_inline_ifields(
        scope, conf, min_sdk, init_classes_with_side_effects, xstores,
        eligible_ifields, constructor_only_ifields, state);
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

// FinalInlineV2 skips a class whose single constructor takes its own type, so
// the read that the superclass constructor's callback makes before `count` is
// set stays.
TEST_F(FinalInlineTest, ownTypeArgumentKeepsSuperclassCallbackRead) {
  ClassCreator base_cc(DexType::make_type("LBase;"));
  base_cc.set_super(type::java_lang_Object());
  base_cc.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (invoke-virtual (v0) "LBase;.hook:()V") (return-void)))
  )"));
  base_cc.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.hook:()V"
      ((load-param-object v0) (return-void)))
  )"));
  auto* base = base_cc.create();
  m_cc->set_super(base->get_type());
  auto* count = DexField::make_field("LFoo;.count:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(count);
  create_field_with_zero_value("LFoo;.observed:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LFoo;)V"
      ((load-param-object v0) (load-param-object v1)
       (invoke-direct (v0) "LBase;.<init>:()V")
       (const v2 7) (iput v2 v0 "LFoo;.count:I") (return-void)))
  )"));
  auto* hook = assembler::method_from_string(R"(
    (method (public) "LFoo;.hook:()V"
      ((load-param-object v0)
       (iget v0 "LFoo;.count:I") (move-result-pseudo v1)
       (sput v1 "LFoo;.observed:I") (return-void)))
  )");
  m_cc->add_method(hook);
  run({base, m_cc->create()}, nullptr);
  const auto output = assembler::to_string(hook->get_code());
  EXPECT_NE(output.find("iget"), std::string::npos) << output;
}

TEST_F(FinalInlineTest, constructorReadsOtherInstance) {
  auto* depth = DexField::make_field("LFoo;.depth:I")
                    ->make_concrete(ACC_PUBLIC | ACC_FINAL);
  m_cc->add_field(depth);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (instance-of v1 "LFoo;")
      (move-result-pseudo v2)
      (if-eqz v2 :root)
      (check-cast v1 "LFoo;")
      (move-result-pseudo-object v3)
      (iget v3 "LFoo;.depth:I")
      (move-result-pseudo v4)
      (add-int/lit v4 v4 1)
      (iput v4 v0 "LFoo;.depth:I")
      (return-void)
      (:root)
      (const v4 0)
      (iput v4 v0 "LFoo;.depth:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);

  run({m_cc->create()}, /* xstores */ nullptr);

  bool reads_parent_depth = false;
  for (auto& mie : InstructionIterable(ctor->get_code())) {
    if (mie.insn->opcode() == OPCODE_IGET && mie.insn->get_field() == depth) {
      reads_parent_depth = true;
    }
  }
  EXPECT_TRUE(reads_parent_depth) << show(ctor->get_code());
}

TEST_F(FinalInlineTest, constructorRetainsOtherInstanceZeroWrite) {
  m_cc->add_field(
      DexField::make_field("LFoo;.count:I")->make_concrete(ACC_PUBLIC));
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-static () "LRegistry;.current:()LFoo;")
      (move-result-object v2)
      (const v3 0)
      (iput v3 v2 "LFoo;.count:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  auto original = assembler::to_s_expr(ctor->get_code());

  run({m_cc->create()}, /* xstores */ nullptr);

  EXPECT_EQ(assembler::to_s_expr(ctor->get_code()), original);
}

TEST_F(FinalInlineTest, constructorTracksThisAliases) {
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
      (move-object v3 v0)
      (:join)
      (check-cast v3 "LFoo;")
      (move-result-pseudo-object v3)
      (const v4 7)
      (iput v4 v3 "LFoo;.count:I")
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

  run({m_cc->create()}, /* xstores */ nullptr);

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v0 7)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, constructorReassignsThisRegister) {
  m_cc->add_field(
      DexField::make_field("LFoo;.count:I")->make_concrete(ACC_PUBLIC));
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (check-cast v1 "LFoo;")
      (move-result-pseudo-object v0)
      (const v2 0)
      (iput v2 v0 "LFoo;.count:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  auto original = assembler::to_s_expr(ctor->get_code());

  run({m_cc->create()}, /* xstores */ nullptr);

  EXPECT_EQ(assembler::to_s_expr(ctor->get_code()), original);
}

TEST_F(FinalInlineTest, constructorReadAfterThisEscapes) {
  auto* x = DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC);
  m_cc->add_field(x);
  create_field_with_zero_value("LFoo;.sObserved:I", m_cc.get());
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (invoke-static (v0) "LHelper;.mutate:(LFoo;)V")
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v2)
      (sput v2 "LFoo;.sObserved:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  // Another method writes x, so the helper may change it.
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public) "LFoo;.set:(I)V"
     ((load-param-object v0) (load-param v1)
      (iput v1 v0 "LFoo;.x:I") (return-void)))
  )"));

  run({m_cc->create()}, /* xstores */ nullptr);

  bool reads_x = false;
  for (auto& mie : InstructionIterable(ctor->get_code())) {
    if (mie.insn->opcode() == OPCODE_IGET && mie.insn->get_field() == x) {
      reads_x = true;
    }
  }
  EXPECT_TRUE(reads_x) << show(ctor->get_code());
}

TEST_F(FinalInlineTest, constructorReadAfterThisEscapesOfConstructorOnlyField) {
  auto* x = DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC);
  m_cc->add_field(x);
  create_field_with_zero_value("LFoo;.sObserved:I", m_cc.get());
  m_cc->add_field(DexField::make_field("LFoo;.sInstance:LFoo;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  // Only this constructor writes x. Publishing `this` keeps x from being
  // inlined into other code, which may read it before the store, but no
  // code can change x.
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (sput-object v0 "LFoo;.sInstance:LFoo;")
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v2)
      (sput v2 "LFoo;.sObserved:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);

  run({m_cc->create()}, /* xstores */ nullptr);

  bool reads_x = false;
  for (auto& mie : InstructionIterable(ctor->get_code())) {
    if (mie.insn->opcode() == OPCODE_IGET && mie.insn->get_field() == x) {
      reads_x = true;
    }
  }
  EXPECT_FALSE(reads_x) << show(ctor->get_code());
}

TEST_F(FinalInlineTest, constructorKeepsFieldAfterSuperclassConstructor) {
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
     )
    )
  )"));
  auto* base = base_creator.create();
  m_cc->set_super(base->get_type());
  m_cc->add_field(DexField::make_field("LFoo;.count:I")
                      ->make_concrete(ACC_PUBLIC | ACC_FINAL));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (const v1 7)
      (iput v1 v0 "LFoo;.count:I")
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

  run({base, m_cc->create()}, /* xstores */ nullptr);

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v0 7)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, constructorCallOnSameObjectCanOverwriteField) {
  auto* count =
      DexField::make_field("LFoo;.count:I")->make_concrete(ACC_PUBLIC);
  m_cc->add_field(count);
  create_field_with_zero_value("LFoo;.observed:I", m_cc.get());
  // Generated DEX: the constructor calls itself on the same uninitialized
  // object, and the inner call stores 7 before the outer one reads count.
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (const v2 1)
      (iput v2 v0 "LFoo;.count:I")
      (if-eqz v1 :base)
      (const v3 0)
      (invoke-direct (v0 v3) "LFoo;.<init>:(I)V")
      (iget v0 "LFoo;.count:I")
      (move-result-pseudo v2)
      (sput v2 "LFoo;.observed:I")
      (return-void)
      (:base)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 7)
      (iput v2 v0 "LFoo;.count:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);

  run({m_cc->create()}, /* xstores */ nullptr);

  bool reads_count = false;
  for (auto& mie : InstructionIterable(ctor->get_code())) {
    if (mie.insn->opcode() == OPCODE_IGET && mie.insn->get_field() == count) {
      reads_count = true;
    }
  }
  EXPECT_TRUE(reads_count) << show(ctor->get_code());
}

TEST_F(FinalInlineTest, constructorCallOnSameObjectStartsWithStoredField) {
  auto* count =
      DexField::make_field("LFoo;.count:I")->make_concrete(ACC_PUBLIC);
  m_cc->add_field(count);
  // Generated DEX: the outer call stores 1 and then calls the constructor
  // again on the same object, whose store of 0 replaces that 1.
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (if-eqz v1 :base)
      (const v2 1)
      (iput v2 v0 "LFoo;.count:I")
      (const v3 0)
      (invoke-direct (v0 v3) "LFoo;.<init>:(I)V")
      (return-void)
      (:base)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 0)
      (iput v2 v0 "LFoo;.count:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);

  run({m_cc->create()}, /* xstores */ nullptr);

  size_t stores = 0;
  for (auto& mie : InstructionIterable(ctor->get_code())) {
    if (mie.insn->opcode() == OPCODE_IPUT && mie.insn->get_field() == count) {
      ++stores;
    }
  }
  EXPECT_EQ(stores, 2u) << show(ctor->get_code());
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

TEST_F(FinalInlineTest, encodeConstantShiftResult) {
  auto* field = create_field_with_zero_value("LFoo;.bar:J", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
      ((const-wide v0 3)
       (const v2 32)
       (shl-long v0 v0 v2)
       (sput-wide v0 "LFoo;.bar:J")
       (return-void)))
  )"));
  auto* cls = m_cc->create();

  run({cls}, nullptr);

  EXPECT_EQ(cls->get_clinit(), nullptr);
  EXPECT_EQ(field->get_static_value()->value(), 12884901888ULL); // 3L << 32
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

class FinalInlinePutHandleTest : public FinalInlineTest,
                                 public ::testing::WithParamInterface<bool> {};

// Tool-generated: set() writes Foo.x through an instance-put method handle, so
// Foo.x is not always the 5 that the constructor writes. The handle is either
// loaded in set() or loaded in the constructor and passed to set() through a
// field.
TEST_P(FinalInlinePutHandleTest, instanceFieldWrittenThroughPutHandle) {
  const bool handle_in_constructor = GetParam();
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.x:I"));
  field->make_concrete(ACC_PUBLIC);
  m_cc->add_field(field);
  create_field_with_zero_value("LFoo;.h:Ljava/lang/invoke/MethodHandle;",
                               m_cc.get());

  const std::string load_handle = R"(
      (const-method-handle instance-put "LFoo;.x:I")
      (move-result-pseudo-object v2)
  )";
  m_cc->add_method(assembler::method_from_string(
      R"((method (public constructor) "LFoo;.<init>:()V" (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
  )" +
      (handle_in_constructor
           ? load_handle +
                 R"((sput-object v2 "LFoo;.h:Ljava/lang/invoke/MethodHandle;"))"
           : std::string()) +
      R"(
      (const v1 5)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
    ))
  )"));

  m_cc->add_method(assembler::method_from_string(
      R"((method (public static) "LFoo;.set:(LFoo;)V" (
      (load-param-object v0)
  )" +
      (handle_in_constructor
           ? std::string(
                 R"((sget-object "LFoo;.h:Ljava/lang/invoke/MethodHandle;"))"
                 R"((move-result-pseudo-object v2))")
           : load_handle) +
      R"(
      (const v1 7)
      (invoke-polymorphic (v2 v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LFoo;I)V")
      (return-void)
    ))
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
  auto expected = std::make_unique<IRCode>(*reader->get_code());

  auto store = DexStore("store");
  store.add_classes({cls});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

INSTANTIATE_TEST_SUITE_P(HandleLocation,
                         FinalInlinePutHandleTest,
                         ::testing::Bool(),
                         [](const ::testing::TestParamInfo<bool>& info) {
                           return info.param ? "HandleInConstructor"
                                             : "HandleInSetter";
                         });

// Tool-generated: set() writes through an instance-put method handle of
// LChild;.x, which ART resolves to the instance field Foo.x, past the static
// field Child.x. So Foo.x is not always the 5 that the constructor writes.
TEST_F(FinalInlineTest, inheritedInstanceFieldWrittenThroughPutHandle) {
  auto* field = dynamic_cast<DexField*>(DexField::make_field("LFoo;.x:I"));
  field->make_concrete(ACC_PUBLIC);
  m_cc->add_field(field);
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 5)
      (iput v1 v0 "LFoo;.x:I")
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
  auto expected = std::make_unique<IRCode>(*reader->get_code());

  ClassCreator child_creator(DexType::make_type("LChild;"));
  child_creator.set_super(cls->get_type());
  create_field_with_zero_value("LChild;.x:I", &child_creator);
  child_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LChild;.set:(LChild;)V"
     (
      (load-param-object v0)
      (const-method-handle instance-put "LChild;.x:I")
      (move-result-pseudo-object v2)
      (const v1 7)
      (invoke-polymorphic (v2 v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LChild;I)V")
      (return-void)
     )
    )
  )"));
  auto* child_cls = child_creator.create();

  auto store = DexStore("store");
  store.add_classes({cls, child_cls});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

namespace {

// Whether the code of `method` still writes `field`.
bool writes_field(DexMethod* method, const DexField* field) {
  bool writes = false;
  cfg_adapter::iterate(method->get_code(), [&](MethodItemEntry& mie) {
    writes = writes || (opcode::is_an_sput(mie.insn->opcode()) &&
                        mie.insn->get_field() == field);
    return cfg_adapter::LOOP_CONTINUE;
  });
  return writes;
}

} // namespace

// How <clinit> reads Foo.x before it writes 5 to it.
enum class ClinitRead {
  // Tool-generated: invoke-polymorphic of a handle from another class.
  InvokePolymorphic,
  // Tool-generated: invoke-custom of a call site.
  InvokeCustom,
  // Tool-generated: a static-get handle of Foo.x, called by the library.
  FieldHandleCalledByLibrary,
  // Tool-generated: a handle of readX(), called by the library.
  MethodHandleCalledByLibrary,
};

class FinalInlineClinitReadTest
    : public FinalInlineTest,
      public ::testing::WithParamInterface<ClinitRead> {};

// The read sees 0, so Foo.x must keep its zero encoded value and the write.
TEST_P(FinalInlineClinitReadTest, fieldReadBeforeWriteIsNotEncoded) {
  auto* field = create_field_with_zero_value("LFoo;.x:I", m_cc.get());
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.readX:()I"
     (
      (sget "LFoo;.x:I")
      (move-result-pseudo v0)
      (return v0)
     )
    )
  )"));

  std::string read;
  switch (GetParam()) {
  case ClinitRead::InvokePolymorphic:
    read = R"(
      (sget-object "LBar;.h:Ljava/lang/invoke/MethodHandle;")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()I")
    )";
    break;
  case ClinitRead::InvokeCustom:
    read = R"((invoke-static () "LFoo;.placeholder:()I"))";
    break;
  case ClinitRead::FieldHandleCalledByLibrary:
  case ClinitRead::MethodHandleCalledByLibrary:
    read =
        std::string(
            GetParam() == ClinitRead::FieldHandleCalledByLibrary
                ? R"((const-method-handle static-get "LFoo;.x:I"))"
                : R"((const-method-handle invoke-static "LFoo;.readX:()I"))") +
        R"(
      (move-result-pseudo-object v0)
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/Object;)Ljava/lang/Object;")
    )";
    break;
  }
  auto* clinit = assembler::method_from_string(
      R"((method (public static) "LFoo;.<clinit>:()V" ()" + read + R"(
      (const v2 5)
      (sput v2 "LFoo;.x:I")
      (return-void)
    ))
  )");
  if (GetParam() == ClinitRead::InvokeCustom) {
    redex::make_invoke_custom(clinit->get_code(), "readX", "()I");
  }
  m_cc->add_method(clinit);
  auto* cls = m_cc->create();

  run({cls}, /* xstores */ nullptr);

  EXPECT_EQ(field->get_static_value()->value(), 0);
  ASSERT_EQ(cls->get_clinit(), clinit);
  EXPECT_TRUE(writes_field(clinit, field));
}

INSTANTIATE_TEST_SUITE_P(
    ReadKind,
    FinalInlineClinitReadTest,
    ::testing::Values(ClinitRead::InvokePolymorphic,
                      ClinitRead::InvokeCustom,
                      ClinitRead::FieldHandleCalledByLibrary,
                      ClinitRead::MethodHandleCalledByLibrary),
    [](const ::testing::TestParamInfo<ClinitRead>& info) {
      switch (info.param) {
      case ClinitRead::InvokePolymorphic:
        return "InvokePolymorphic";
      case ClinitRead::InvokeCustom:
        return "InvokeCustom";
      case ClinitRead::FieldHandleCalledByLibrary:
        return "FieldHandleCalledByLibrary";
      case ClinitRead::MethodHandleCalledByLibrary:
        return "MethodHandleCalledByLibrary";
      }
      return "Unknown";
    });

// Tool-generated: Base.<clinit> reads through a static-get method handle of
// LChild;.x, called by the library, before it writes 5 to Base.x. ART resolves
// the handle to the static Base.x, past the instance field Child.x, so the read
// sees 0 and Base.x must keep its zero encoded value and the write.
TEST_F(FinalInlineTest,
       inheritedFieldReadThroughHandleBeforeWriteIsNotEncoded) {
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  auto* base_x = create_field_with_zero_value("LBase;.x:I", &base_creator);
  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LBase;.<clinit>:()V"
     (
      (const-method-handle static-get "LChild;.x:I")
      (move-result-pseudo-object v0)
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/Object;)Ljava/lang/Object;")
      (const v2 5)
      (sput v2 "LBase;.x:I")
      (return-void)
     )
    )
  )");
  base_creator.add_method(clinit);
  auto* base_cls = base_creator.create();

  ClassCreator child_creator(DexType::make_type("LChild;"));
  child_creator.set_super(base_cls->get_type());
  child_creator.add_field(
      DexField::make_field("LChild;.x:I")->make_concrete(ACC_PUBLIC));
  auto* child_cls = child_creator.create();

  run({base_cls, child_cls}, /* xstores */ nullptr);

  EXPECT_EQ(base_x->get_static_value()->value(), 0);
  ASSERT_EQ(base_cls->get_clinit(), clinit);
  EXPECT_TRUE(writes_field(clinit, base_x));
}

// Tool-generated: Sub.<clinit> loads an invoke-direct method handle of
// `LBase;.m`. In `LSub;`, whose superclass `LMid;` overrides `m`, the handle
// runs `LMid;.m` on Android 9, which reads Sub.x before <clinit> writes 5 to
// it, so Sub.x must keep its zero encoded value and the write.
TEST_F(FinalInlineTest,
       fieldReadByMethodThatInvokeDirectHandleCanRunIsNotEncoded) {
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.m:()I"
     ((load-param-object v0) (const v1 0) (return v1)))
  )"));
  auto* base_cls = base_creator.create();
  ClassCreator mid_creator(DexType::make_type("LMid;"));
  mid_creator.set_super(base_cls->get_type());
  mid_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LMid;.m:()I"
     (
      (load-param-object v0)
      (sget "LSub;.x:I")
      (move-result-pseudo v1)
      (return v1)
     )
    )
  )"));
  auto* mid_cls = mid_creator.create();
  ClassCreator sub_creator(DexType::make_type("LSub;"));
  sub_creator.set_super(mid_cls->get_type());
  auto* field = create_field_with_zero_value("LSub;.x:I", &sub_creator);
  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LSub;.<clinit>:()V"
     (
      (const-method-handle invoke-direct "LBase;.m:()I")
      (move-result-pseudo-object v0)
      (sput-object v0 "LSub;.h:Ljava/lang/invoke/MethodHandle;")
      (const v2 5)
      (sput v2 "LSub;.x:I")
      (return-void)
     )
    )
  )");
  sub_creator.add_method(clinit);
  create_field_with_zero_value("LSub;.h:Ljava/lang/invoke/MethodHandle;",
                               &sub_creator);
  auto* sub_cls = sub_creator.create();

  run({base_cls, mid_cls, sub_cls}, /* xstores */ nullptr);

  EXPECT_EQ(field->get_static_value()->value(), 0);
  ASSERT_EQ(sub_cls->get_clinit(), clinit);
  EXPECT_TRUE(writes_field(clinit, field));
}

// Tool-generated: Foo.<clinit> loads a static-get method handle of Foo.x that
// Bar holds and runs it through the library's
// MethodHandle.invokeWithArguments before it writes 5 to Foo.x. The read sees
// 0, so Foo.x must keep its zero encoded value and the write.
TEST_F(FinalInlineTest, fieldReadThroughHandleFromElsewhereIsNotEncoded) {
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  create_field_with_zero_value("LBar;.h:Ljava/lang/invoke/MethodHandle;",
                               &bar_creator);
  bar_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.<clinit>:()V"
     (
      (const-method-handle static-get "LFoo;.x:I")
      (move-result-pseudo-object v0)
      (sput-object v0 "LBar;.h:Ljava/lang/invoke/MethodHandle;")
      (return-void)
     )
    )
  )"));
  auto* bar_cls = bar_creator.create();

  auto* field = create_field_with_zero_value("LFoo;.x:I", m_cc.get());
  auto* clinit = assembler::method_from_string(R"(
    (method (public static) "LFoo;.<clinit>:()V"
     (
      (sget-object "LBar;.h:Ljava/lang/invoke/MethodHandle;")
      (move-result-pseudo-object v0)
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/Object;)Ljava/lang/Object;")
      (const v2 5)
      (sput v2 "LFoo;.x:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(clinit);
  auto* cls = m_cc->create();

  run({bar_cls, cls}, /* xstores */ nullptr);

  EXPECT_EQ(field->get_static_value()->value(), 0);
  ASSERT_EQ(cls->get_clinit(), clinit);
  EXPECT_TRUE(writes_field(clinit, field));
}

// A class initializer that calls a method handle of a static method
// initializes the method's class, as an invoke-static would. Here that class
// reads a field of the class under initialization, which still holds its
// default value, so the initializers form a cycle and neither is folded.
TEST_F(FinalInlineTest, clinitCycleThroughMethodHandle) {
  auto* x = create_field_with_zero_value("LFoo;.X:I", m_cc.get(),
                                         ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  // Tool-generated: static { TOUCH_BAR.invokeExact(); X = 5; }
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
     (
      (const-method-handle invoke-static "LBar;.touch:()V")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (const v1 5)
      (sput v1 "LFoo;.X:I")
      (return-void)
     )
    )
  )"));
  auto* foo = m_cc->create();

  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  auto* y = create_field_with_zero_value("LBar;.Y:I", &bar_creator,
                                         ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  // static { Y = Foo.X; }, which reads 0 when Foo's initializer runs first.
  bar_creator.add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LBar;.<clinit>:()V"
     (
      (sget "LFoo;.X:I")
      (move-result-pseudo v0)
      (sput v0 "LBar;.Y:I")
      (return-void)
     )
    )
  )"));
  bar_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.touch:()V"
     (
      (return-void)
     )
    )
  )"));
  auto* bar = bar_creator.create();

  auto store = DexStore("store");
  store.add_classes({foo, bar});
  DexStoresVector stores{store};
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, true);
  run(scope, &xstores);

  EXPECT_NE(bar->get_clinit(), nullptr);
  EXPECT_EQ(y->get_static_value()->value(), 0);
  EXPECT_EQ(x->get_static_value()->value(), 0);
}

TEST_F(FinalInlineTest, passingThisToConstructorOfSameClassBlocksInference) {
  add_instance_field("LFoo;.x:I");
  // Java:
  //   Foo(Object o) {
  //     if (o == null) { new Foo(this); } else { observe(o); }
  //     x = 1;
  //   }
  //   static void observe(Object o) { Log.v(((Foo) o).x); }
  // `new Foo(null)` makes the inner Foo observe the outer one, whose x is still
  // 0. Constructors of the class itself were never checked, so the read in
  // observe() was folded to 1.
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (if-nez v1 :else)
      (new-instance "LFoo;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v0) "LFoo;.<init>:(Ljava/lang/Object;)V")
      (goto :join)
      (:else)
      (invoke-static (v1) "LFoo;.observe:(Ljava/lang/Object;)V")
      (:join)
      (const v3 1)
      (iput v3 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* observe = assembler::method_from_string(R"(
    (method (public static) "LFoo;.observe:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (iget v1 "LFoo;.x:I")
      (move-result-pseudo v2)
      (invoke-static (v2) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  m_cc->add_method(observe);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(observe->get_code()));

  run({cls}, nullptr);

  EXPECT_CODE_EQ(observe->get_code(), expected.get());
}

TEST_F(FinalInlineTest, passingThisToConstructorOfSuperclassBlocksInference) {
  // Java:
  //   class Base { Base(Object o) { if (o != null) Foo.observe(o); } }
  //   class Foo extends Base {
  //     int x;
  //     Foo() { super(null); new Base(this); x = 1; }
  //     static void observe(Object o) { Log.v(((Foo) o).x); }
  //   }
  // `new Base(this)` observes this Foo while its x is still 0. Constructors of
  // a superclass were never checked, so the read was folded to 1.
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (if-eqz v1 :done)
      (invoke-static (v1) "LFoo;.observe:(Ljava/lang/Object;)V")
      (:done)
      (return-void)
     )
    )
  )"));
  auto* base = base_creator.create();

  m_cc->set_super(base->get_type());
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (const v1 0)
      (invoke-direct (v0 v1) "LBase;.<init>:(Ljava/lang/Object;)V")
      (new-instance "LBase;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2 v0) "LBase;.<init>:(Ljava/lang/Object;)V")
      (const v3 1)
      (iput v3 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* observe = assembler::method_from_string(R"(
    (method (public static) "LFoo;.observe:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (iget v1 "LFoo;.x:I")
      (move-result-pseudo v2)
      (invoke-static (v2) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  m_cc->add_method(observe);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(observe->get_code()));

  run({base, cls}, nullptr);

  EXPECT_CODE_EQ(observe->get_code(), expected.get());
}

TEST_F(FinalInlineTest, superclassConstructorPassingThisOnBlocksInference) {
  // Java:
  //   class Base { Base() { Foo.observe(this); } }
  //   class Foo extends Base {
  //     int x;
  //     Foo() { super(); x = 1; }
  //     static void observe(Object o) { Log.v(((Foo) o).x); }
  //   }
  // observe() runs before x is written and logs 0. The superclass constructor
  // was never checked, so its read was folded to 1.
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-static (v0) "LFoo;.observe:(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )"));
  auto* base = base_creator.create();

  m_cc->set_super(base->get_type());
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* observe = assembler::method_from_string(R"(
    (method (public static) "LFoo;.observe:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (iget v1 "LFoo;.x:I")
      (move-result-pseudo v2)
      (invoke-static (v2) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  m_cc->add_method(observe);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(observe->get_code()));

  run({base, cls}, nullptr);

  EXPECT_CODE_EQ(observe->get_code(), expected.get());
}

namespace {

// class Base { Base() { onCreate(); } void onCreate() {} }
DexClass* create_base_calling_on_create() {
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-virtual (v0) "LBase;.onCreate:()V")
      (return-void)
     )
    )
  )"));
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.onCreate:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  return base_creator.create();
}

} // namespace

TEST_F(FinalInlineTest, overrideCalledBySuperclassConstructorBlocksInference) {
  // Java:
  //   class Base { Base() { onCreate(); } void onCreate() {} }
  //   class Foo extends Base {
  //     int x;
  //     Foo() { super(); x = 1; }
  //     @Override void onCreate() { Log.v(x); }
  //   }
  // Base() runs Foo.onCreate() before x is written, which logs 0. The call
  // was only followed to Base.onCreate(), so the read was folded to 1.
  auto* base = create_base_calling_on_create();
  m_cc->set_super(base->get_type());
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* on_create = assembler::method_from_string(R"(
    (method (public) "LFoo;.onCreate:()V"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v1)
      (invoke-static (v1) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  m_cc->add_method(on_create);
  auto* cls = m_cc->create();
  auto expected = assembler::ircode_from_string(
      assembler::to_string(on_create->get_code()));

  run({base, cls}, nullptr);

  EXPECT_CODE_EQ(on_create->get_code(), expected.get());
}

TEST_F(FinalInlineTest, overrideInSubclassBlocksInference) {
  // Java:
  //   class Foo { int x; Foo() { init(); x = 1; } void init() {} }
  //   class Sub extends Foo { @Override void init() { Log.v(x); } }
  // `new Sub()` runs Sub.init() before x is written, which logs 0. The call
  // was only followed to Foo.init(), so the read was folded to 1.
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-virtual (v0) "LFoo;.init:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public) "LFoo;.init:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  ClassCreator sub_creator(DexType::make_type("LSub;"));
  sub_creator.set_super(cls->get_type());
  sub_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LSub;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (return-void)
     )
    )
  )"));
  auto* init = assembler::method_from_string(R"(
    (method (public) "LSub;.init:()V"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v1)
      (invoke-static (v1) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  sub_creator.add_method(init);
  auto* sub = sub_creator.create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(init->get_code()));

  run({cls, sub}, nullptr);

  EXPECT_CODE_EQ(init->get_code(), expected.get());
}

TEST_F(FinalInlineTest, overrideInUnrelatedClassAllowsInference) {
  // Java:
  //   class Base { Base() { onCreate(); } void onCreate() {} }
  //   class Foo extends Base { int x; Foo() { super(); x = 1; } }
  //   class Other extends Base {
  //     static Foo last;
  //     @Override void onCreate() { Log.v(last.x); }
  //   }
  // Other.onCreate() cannot run for a Foo, so reads of x are still folded.
  auto* base = create_base_calling_on_create();
  m_cc->set_super(base->get_type());
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
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

  ClassCreator other_creator(DexType::make_type("LOther;"));
  other_creator.set_super(base->get_type());
  other_creator.add_field(DexField::make_field("LOther;.last:LFoo;")
                              ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  other_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LOther;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (return-void)
     )
    )
  )"));
  other_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LOther;.onCreate:()V"
     (
      (load-param-object v0)
      (sget-object "LOther;.last:LFoo;")
      (move-result-pseudo-object v1)
      (iget v1 "LFoo;.x:I")
      (move-result-pseudo v2)
      (invoke-static (v2) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )"));
  auto* other = other_creator.create();

  run({base, cls, other}, nullptr);

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v0 1)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, undefinedInterfaceMakesInheritedImplementationUnknown) {
  // Java, where Missing has no definition in the input:
  //   interface I { void m(); }
  //   abstract class Foo implements I, Missing {
  //     int x;
  //     Foo() { super(); m(); x = 1; }
  //   }
  // Foo declares no m(), so the m() it inherits may be a default method of
  // Missing, which cannot be inspected: x is treated as read and not inferred.
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  i_creator.add_method(
      DexMethod::make_method("LI;.m:()V")
          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true));
  auto* i_cls = i_creator.create();

  m_cc->set_access(ACC_PUBLIC | ACC_ABSTRACT);
  m_cc->add_interface(i_cls->get_type());
  m_cc->add_interface(DexType::make_type("LMissing;"));
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-interface (v0) "LI;.m:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
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

  run({i_cls, cls}, nullptr);

  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, defaultMethodOfSubclassInterfaceBlocksInference) {
  // Java:
  //   interface I { default void m() {} }
  //   interface J extends I {
  //     @Override default void m() { Log.v(((Foo) this).x); }
  //   }
  //   class Foo implements I {
  //     int x;
  //     Foo() { I self = this; self.m(); x = 1; }
  //   }
  //   class Sub extends Foo implements J {}
  // `new Sub()` runs J.m() before x is written, which logs 0. Only Sub
  // implements J, so a check of the defaults Foo inherits misses J.m().
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  i_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LI;.m:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  auto* i_cls = i_creator.create();

  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  j_creator.add_interface(i_cls->get_type());
  auto* j_m = assembler::method_from_string(R"(
    (method (public) "LJ;.m:()V"
     (
      (load-param-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v0)
      (iget v0 "LFoo;.x:I")
      (move-result-pseudo v1)
      (invoke-static (v1) "LLog;.v:(I)V")
      (return-void)
     )
    )
  )");
  j_creator.add_method(j_m);
  auto* j_cls = j_creator.create();

  m_cc->add_interface(i_cls->get_type());
  add_instance_field("LFoo;.x:I");
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-interface (v0) "LI;.m:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();

  ClassCreator sub_creator(DexType::make_type("LSub;"));
  sub_creator.set_super(cls->get_type());
  sub_creator.add_interface(j_cls->get_type());
  sub_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LSub;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (return-void)
     )
    )
  )"));
  auto* sub = sub_creator.create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(j_m->get_code()));

  run({i_cls, j_cls, cls, sub}, nullptr);

  EXPECT_CODE_EQ(j_m->get_code(), expected.get());
}

TEST_F(FinalInlineTest, readOfOwnFieldOfOtherObjectBlocksInference) {
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  m_cc->add_field(DexField::make_field("LFoo;.y:I")->make_concrete(ACC_PUBLIC));
  // Java: Foo(Holder h) { y = h.foo.x; x = 1; }
  // The read is of another Foo's x, which is 1 for any fully constructed Foo,
  // not of this.x, which is still 0.
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iget-object v1 "LHolder;.foo:LFoo;")
      (move-result-pseudo-object v2)
      (iget v2 "LFoo;.x:I")
      (move-result-pseudo v4)
      (iput v4 v0 "LFoo;.y:I")
      (const v3 1)
      (iput v3 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* reader = assembler::method_from_string(R"(
    (method (public static) "LFoo;.getY:(LFoo;)I"
     (
      (load-param-object v0)
      (iget v0 "LFoo;.y:I")
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

TEST_F(FinalInlineTest, writeToOwnFieldOfOtherObjectIsKept) {
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  // Java: Foo(Holder h) { x = 1; h.foo.x = 1; }
  // The second store goes to another Foo, so it is not a repeated store to
  // this.x.
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v3 1)
      (iput v3 v0 "LFoo;.x:I")
      (iget-object v1 "LHolder;.foo:LFoo;")
      (move-result-pseudo-object v2)
      (iput v3 v2 "LFoo;.x:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(ctor->get_code()));

  run({cls}, nullptr);

  EXPECT_CODE_EQ(ctor->get_code(), expected.get());
}

TEST_F(FinalInlineTest, fieldOfOtherClassOnOtherObjectAllowsInference) {
  // Java:
  //   class Holder { int count; }
  //   class Foo { int x; Foo(Holder h) { h.count = 2; x = 1; } }
  // Only the class's own fields on other objects block inference.
  ClassCreator holder_creator(DexType::make_type("LHolder;"));
  holder_creator.set_super(type::java_lang_Object());
  holder_creator.add_field(
      DexField::make_field("LHolder;.count:I")->make_concrete(ACC_PUBLIC));
  auto* holder = holder_creator.create();

  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 2)
      (iput v2 v1 "LHolder;.count:I")
      (const v3 1)
      (iput v3 v0 "LFoo;.x:I")
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

  run({holder, cls}, nullptr);

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v0 1)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(reader->get_code(), expected.get());
}

TEST_F(FinalInlineTest, innerConstructorWritingOuterObjectBlocksInference) {
  // Java:
  //   class Foo {
  //     static Holder HOLDER;  // HOLDER.foo is the Foo under construction
  //     int x;
  //     Foo(Holder h) {
  //       x = 1;
  //       if (h != null) new Foo(null); else HOLDER.foo.x = 2;
  //     }
  //   }
  // `new Foo(HOLDER)` ends with x == 2, so getX() must not be folded.
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  m_cc->add_field(DexField::make_field("LFoo;.HOLDER:LHolder;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  m_cc->add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LHolder;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 1)
      (iput v2 v0 "LFoo;.x:I")
      (if-eqz v1 :else)
      (new-instance "LFoo;")
      (move-result-pseudo-object v3)
      (const v4 0)
      (invoke-direct (v3 v4) "LFoo;.<init>:(LHolder;)V")
      (:join)
      (return-void)
      (:else)
      (sget-object "LFoo;.HOLDER:LHolder;")
      (move-result-pseudo-object v5)
      (iget-object v5 "LHolder;.foo:LFoo;")
      (move-result-pseudo-object v6)
      (const v7 2)
      (iput v7 v6 "LFoo;.x:I")
      (goto :join)
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
  auto expected_reader =
      assembler::ircode_from_string(assembler::to_string(reader->get_code()));

  run({cls}, nullptr);

  EXPECT_CODE_EQ(reader->get_code(), expected_reader.get());
}

TEST_F(FinalInlineTest, callReceivingThisKeepsStoreOfFieldWrittenElsewhere) {
  // Java:
  //   class Foo { int x; Foo() { x = 1; Util.reset(this); x = 1; } }
  //   class Util { static void reset(Foo f) { f.x = 0; } }
  // reset() changes x, so the second store is not redundant.
  ClassCreator util_creator(DexType::make_type("LUtil;"));
  util_creator.set_super(type::java_lang_Object());
  util_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LUtil;.reset:(LFoo;)V"
     (
      (load-param-object v0)
      (const v1 0)
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* util = util_creator.create();

  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (invoke-static (v0) "LUtil;.reset:(LFoo;)V")
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(ctor->get_code()));

  run({cls, util}, nullptr);

  EXPECT_CODE_EQ(ctor->get_code(), expected.get());
}

TEST_F(FinalInlineTest,
       callReachingSavedThisKeepsStoreOfFieldWrittenElsewhere) {
  // Java:
  //   class Base { Base() { Registry.last = this; } }
  //   class Foo extends Base {
  //     int x;
  //     Foo() { super(); x = 1; Registry.reset(); x = 1; }
  //   }
  //   class Registry {
  //     static Base last;
  //     static void reset() { ((Foo) last).x = 0; }
  //   }
  // reset() takes no arguments but reaches this through Registry.last, so the
  // second store is not redundant.
  ClassCreator registry_creator(DexType::make_type("LRegistry;"));
  registry_creator.set_super(type::java_lang_Object());
  registry_creator.add_field(DexField::make_field("LRegistry;.last:LBase;")
                                 ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  registry_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LRegistry;.reset:()V"
     (
      (sget-object "LRegistry;.last:LBase;")
      (move-result-pseudo-object v0)
      (check-cast v0 "LFoo;")
      (move-result-pseudo-object v1)
      (const v2 0)
      (iput v2 v1 "LFoo;.x:I")
      (return-void)
     )
    )
  )"));
  auto* registry = registry_creator.create();

  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (sput-object v0 "LRegistry;.last:LBase;")
      (return-void)
     )
    )
  )"));
  auto* base = base_creator.create();

  m_cc->set_super(base->get_type());
  m_cc->add_field(DexField::make_field("LFoo;.x:I")->make_concrete(ACC_PUBLIC));
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo;.x:I")
      (invoke-static () "LRegistry;.reset:()V")
      (iput v1 v0 "LFoo;.x:I")
      (return-void)
     )
    )
  )");
  m_cc->add_method(ctor);
  auto* cls = m_cc->create();
  auto expected =
      assembler::ircode_from_string(assembler::to_string(ctor->get_code()));

  run({registry, base, cls}, nullptr);

  EXPECT_CODE_EQ(ctor->get_code(), expected.get());
}

TEST_F(FinalInlineTest, clinitWithNothingToEncodeIsStillSimplified) {
  // Nothing in this <clinit> can be encoded, so its analysis runs once; the
  // dead `const` is removed all the same.
  create_field_with_zero_value("LFoo;.DEFAULT:LFoo;", m_cc.get(),
                               ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  auto* clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
     (
      (const v1 5)
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (sput-object v0 "LFoo;.DEFAULT:LFoo;")
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
      (return-void)
     )
    )
  )"));
  auto* cls = m_cc->create();
  auto expected = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:()V")
      (sput-object v0 "LFoo;.DEFAULT:LFoo;")
      (return-void)
    )
  )");

  run({cls}, /* xstores */ nullptr);

  ASSERT_EQ(cls->get_clinit(), clinit);
  EXPECT_CODE_EQ(clinit->get_code(), expected.get());
}

TEST_F(FinalInlineTest, initClassIsADep) {
  // Java:
  //   class A { static { Sink.record(B.y); } static int five() { return 5; } }
  //   class B { static int y = A.five(); }
  // When B is initialized first, it starts A's initializer, which records 0.
  // Inlining A.five() leaves `init-class A` in B's initializer, so A and B
  // still form an initialization cycle and B.y must not be encoded as 5.
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());
  auto* a_clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LA;.<clinit>:()V"
     (
      (sget "LB;.y:I")
      (move-result-pseudo v0)
      (invoke-static (v0) "LSink;.record:(I)V")
      (return-void)
     )
    )
  )");
  a_creator.add_method(a_clinit);
  a_creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LA;.five:()I"
     (
      (const v0 5)
      (return v0)
     )
    )
  )"));
  auto* a_cls = a_creator.create();

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(type::java_lang_Object());
  auto* field_y = create_field_with_zero_value("LB;.y:I", &b_creator);
  auto* b_clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LB;.<clinit>:()V"
     (
      (init-class "LA;")
      (const v0 5)
      (sput v0 "LB;.y:I")
      (return-void)
     )
    )
  )");
  b_creator.add_method(b_clinit);
  auto* b_cls = b_creator.create();
  auto expected_b =
      assembler::ircode_from_string(assembler::to_string(b_clinit->get_code()));
  auto expected_a =
      assembler::ircode_from_string(assembler::to_string(a_clinit->get_code()));

  run({b_cls, a_cls}, /* xstores */ nullptr);

  EXPECT_EQ(field_y->get_static_value()->value(), 0);
  ASSERT_EQ(b_cls->get_clinit(), b_clinit);
  EXPECT_CODE_EQ(b_clinit->get_code(), expected_b.get());
  ASSERT_EQ(a_cls->get_clinit(), a_clinit);
  EXPECT_CODE_EQ(a_clinit->get_code(), expected_a.get());
}
