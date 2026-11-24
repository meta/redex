/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <array>
#include <gtest/gtest.h>
#include <sstream>

#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
#include "ConstantPropagationWholeProgramState.h"
#include "Creators.h"
#include "DexAccess.h"
#include "IPConstantPropagationAnalysis.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Walkers.h"

namespace cp = constant_propagation;

class ConstructorFieldAnalyzerTest : public RedexTest {
 public:
  void SetUp() override {
    ClassCreator creator(DexType::make_type("LDefaults;"));
    creator.set_super(type::java_lang_Object());
    for (const auto* signature :
         {"LDefaults;.i:I", "LDefaults;.z:Z", "LDefaults;.j:J",
          "LDefaults;.obj:Ljava/lang/Object;", "LDefaults;.f:F",
          "LDefaults;.d:D", "LDefaults;.vol:I", "LDefaults;.kept:I"}) {
      auto* field = DexField::make_field(signature)->make_concrete(ACC_PUBLIC);
      if (field->get_name()->str() == "vol") {
        field->set_access(ACC_PUBLIC | ACC_VOLATILE);
      }
      if (field->get_name()->str() == "kept") {
        field->rstate.set_root();
      }
      creator.add_field(field);
    }
    m_ctor = DexMethod::make_method("LDefaults;.<init>:(ILjava/lang/Object;)V")
                 ->make_concrete(ACC_PUBLIC, false);
    creator.add_method(m_ctor);
    creator.add_method(assembler::method_from_string(R"(
      (method (public) "LDefaults;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (const v1 7) (iput v1 v0 "LDefaults;.i:I") (return-void)))
    )"));
    creator.add_method(assembler::method_from_string(R"(
      (method (public) "LDefaults;.set:(I)V"
        ((load-param-object v0) (load-param v1)
         (iput v1 v0 "LDefaults;.i:I") (return-void)))
    )"));
    creator.add_method(assembler::method_from_string(R"(
      (method (public) "LDefaults;.get:()I"
        ((load-param-object v0) (iget v0 "LDefaults;.i:I")
         (move-result-pseudo v1) (return v1)))
    )"));
    creator.add_field(DexField::make_field("LDefaults;.observed:I")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    creator.add_method(assembler::method_from_string(R"(
      (method (public static) "LDefaults;.consume:(I)V"
        ((load-param v0) (sput v0 "LDefaults;.observed:I") (return-void)))
    )"));
    m_class = creator.create();
  }

 protected:
  // Runs constant propagation with the constructor field analysis over the
  // constructor `m_ctor` and returns how many field stores remain.
  size_t optimize(const std::string& instructions) {
    const std::string initializer =
        m_initializer.empty()
            ? ""
            : "(invoke-direct (v0) \"" + m_initializer + "\") ";
    const std::string prefix =
        "((load-param-object v0) (load-param v1) (load-param-object v2) " +
        initializer;
    m_ctor->set_code(assembler::ircode_from_string(prefix + instructions +
                                                   " (return-void))"));
    walk::code(Scope{m_class},
               [](DexMethod*, IRCode& code) { code.build_cfg(); });
    auto* code = m_ctor->get_code();
    auto& cfg = code->cfg();
    const auto class_fields =
        cp::ClassConstructorFields::create(m_class, m_keeping);
    const auto& state = class_fields.constructors.at(m_ctor);
    auto env = cp::interprocedural::env_with_params(
        /* is_static */ false, code,
        cp::interprocedural::ArgumentDomain::top());
    class_fields.initialize_fields(m_ctor, state.tracked_fields(), &env);
    cp::NullCheckMethods null_check_methods;
    cp::intraprocedural::FixpointIterator fp_iter(
        cfg,
        InstructionAnalyzerCombiner<cp::ConstructorFieldAnalyzer,
                                    cp::PrimitiveAnalyzer>(&state, nullptr),
        cp::intraprocedural::make_default_no_throw_analyzer(
            &null_check_methods));
    fp_iter.run(env);
    cp::Transform::Config config;
    config.constructor_fields = &state;
    cp::Transform tf(config, null_check_methods);
    tf.apply(fp_iter, cp::WholeProgramState(), cfg, nullptr,
             /* is_static */ false, m_class->get_type(), m_ctor->get_proto());
    size_t count = 0;
    for (auto& mie : cfg::InstructionIterable(cfg)) {
      if (opcode::is_an_iput(mie.insn->opcode())) {
        ++count;
      }
    }
    walk::code(Scope{m_class},
               [](DexMethod*, IRCode& code) { code.clear_cfg(); });
    m_last_code = assembler::to_string(code);
    return count;
  }

  std::string m_last_code;
  DexClass* m_class{nullptr};
  DexMethod* m_ctor{nullptr};
  std::string m_initializer{"Ljava/lang/Object;.<init>:()V"};
  std::vector<DexClass*> m_extra_classes;
  UnorderedSet<const DexMethod*> m_keeping;
};

TEST_F(ConstructorFieldAnalyzerTest, NullBooleanAndWideDefaults) {
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput-object v3 v0 "LDefaults;.obj:Ljava/lang/Object;")
    (const v3 0) (iput-boolean v3 v0 "LDefaults;.z:Z")
    (const-wide v4 0) (iput-wide v4 v0 "LDefaults;.j:J")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, NonzeroValuesRemain) {
  EXPECT_EQ(optimize(R"(
    (const v3 1) (iput v3 v0 "LDefaults;.i:I")
    (const-wide v4 -9223372036854775808)
    (iput-wide v4 v0 "LDefaults;.j:J")
  )"),
            2);
}

TEST_F(ConstructorFieldAnalyzerTest, NonzeroHighWordRemains) {
  EXPECT_EQ(optimize(R"(
    (const-wide v4 4294967296)
    (iput-wide v4 v0 "LDefaults;.j:J")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, ReceiverAlias) {
  EXPECT_EQ(optimize(R"(
    (move-object v4 v0) (const v3 0) (iput v3 v4 "LDefaults;.i:I")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, PreviousWriteOnOnePath) {
  EXPECT_EQ(optimize(R"(
    (if-eqz v1 :join) (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (:join) (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            2);
}

TEST_F(ConstructorFieldAnalyzerTest, ReadOnOnePathKeepsValue) {
  EXPECT_EQ(optimize(R"(
    (if-eqz v1 :join) (iget v0 "LDefaults;.i:I")
    (move-result-pseudo v4)
    (:join) (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, DefaultStoreInLoop) {
  EXPECT_EQ(optimize(R"(
    (:loop) (const v3 0) (iput v3 v0 "LDefaults;.i:I")
    (add-int/lit v1 v1 -1) (if-nez v1 :loop)
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, RepeatedStoreOfSameValue) {
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, RepeatedStoreAfterThisEscapes) {
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (invoke-static (v0) "LHelper;.mutate:(LDefaults;)V")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
  )"),
            2);
}

TEST_F(ConstructorFieldAnalyzerTest, RepeatedStoresToVolatileFieldsRemain) {
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.vol:I")
    (iput v3 v0 "LDefaults;.vol:I")
  )"),
            2);
}

// Reflection and native code reach a kept field only through a reference to
// the object, which needs `this` to escape first.
TEST_F(ConstructorFieldAnalyzerTest, KeptFieldsAreTracked) {
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.kept:I")
    (const v3 7) (iput v3 v0 "LDefaults;.kept:I")
    (iput v3 v0 "LDefaults;.kept:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, ReadOfStoredValueBecomesConstant) {
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (iget v0 "LDefaults;.i:I") (move-result-pseudo v4)
    (invoke-static (v4) "LHelper;.use:(I)V")
  )"),
            1);
  EXPECT_EQ(m_last_code.find("iget"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, ReadOfOtherInstanceIsNotFolded) {
  EXPECT_EQ(optimize(R"(
    (check-cast v2 "LDefaults;") (move-result-pseudo-object v4)
    (iget v4 "LDefaults;.i:I") (move-result-pseudo v5)
    (invoke-static (v5) "LHelper;.use:(I)V")
  )"),
            0);
  EXPECT_NE(m_last_code.find("iget"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, SuperclassCallbackMayWriteOwnField) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (invoke-virtual (v0) "LBase;.hook:()V") (return-void)))
  )"));
  base.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.hook:()V"
      ((load-param-object v0) (return-void)))
  )"));
  m_extra_classes.push_back(base.create());
  m_class->set_super_class(DexType::get_type("LBase;"));
  m_initializer = "LBase;.<init>:()V";
  auto* other_ctor = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  other_ctor->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0) (invoke-direct (v0) "LBase;.<init>:()V")
     (const v1 7) (iput v1 v0 "LDefaults;.i:I") (return-void))
  )"));
  m_class->add_method(assembler::method_from_string(R"(
    (method (public) "LDefaults;.hook:()V"
      ((load-param-object v0) (const v1 7)
       (iput v1 v0 "LDefaults;.i:I") (return-void)))
  )"));
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, ConstructorDelegationMayWrite) {
  m_initializer = "LDefaults;.<init>:()V";
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, HelperReceivesThis) {
  EXPECT_EQ(optimize(R"(
    (invoke-static (v0) "LHelper;.mutate:(LDefaults;)V")
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, JoinedAliasMayEscape) {
  EXPECT_EQ(optimize(R"(
    (const v4 0) (if-eqz v1 :join) (move-object v4 v0)
    (:join) (invoke-static (v4) "LHelper;.mutate:(LDefaults;)V")
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, HeapPublication) {
  EXPECT_EQ(optimize(R"(
    (sput-object v0 "LHelper;.published:LDefaults;")
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, ObjectFieldPublication) {
  EXPECT_EQ(optimize(R"(
    (iput-object v0 v0 "LDefaults;.obj:Ljava/lang/Object;")
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            2);
}

TEST_F(ConstructorFieldAnalyzerTest, OtherReceiverIsNotFreshThis) {
  EXPECT_EQ(optimize(R"(
    (check-cast v2 "LDefaults;") (move-result-pseudo-object v4)
    (const v3 0) (iput v3 v4 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, VolatileFieldsRemain) {
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.vol:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, InheritedResetDoesNotHideOwnFieldDefault) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_field(DexField::make_field("LBase;.i:I")->make_concrete(ACC_PUBLIC));
  base.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.<init>:()V"
      ((load-param-object v0)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (const v1 7) (iput v1 v0 "LBase;.i:I") (return-void)))
  )"));
  m_extra_classes.push_back(base.create());
  m_class->set_super_class(DexType::get_type("LBase;"));
  auto* other_ctor = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  other_ctor->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0) (invoke-direct (v0) "LBase;.<init>:()V")
     (const v1 7) (iput v1 v0 "LDefaults;.i:I") (return-void))
  )"));
  m_initializer.clear();
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
    (invoke-direct (v0) "LBase;.<init>:()V")
    (const v3 0) (iput v3 v0 "LBase;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, FloatPositiveZero) {
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.f:F")
    (const-wide v4 0) (iput-wide v4 v0 "LDefaults;.d:D")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, FloatNegativeZeroRemains) {
  EXPECT_EQ(optimize(R"(
    (const v3 -2147483648) (iput v3 v0 "LDefaults;.f:F")
    (const-wide v4 -9223372036854775808)
    (iput-wide v4 v0 "LDefaults;.d:D")
  )"),
            2);
}

TEST_F(ConstructorFieldAnalyzerTest, ArrayPublication) {
  EXPECT_EQ(optimize(R"(
    (const v3 1) (new-array v3 "[LDefaults;")
    (move-result-pseudo-object v4)
    (const v3 0) (aput-object v0 v4 v3)
    (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, FilledArrayPublication) {
  EXPECT_EQ(optimize(R"(
    (filled-new-array (v0) "[LDefaults;") (move-result-object v4)
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, UnresolvedFieldReadChangesNothing) {
  EXPECT_EQ(optimize(R"(
    (iget v0 "LUnmodeledSubclass;.i:I") (move-result-pseudo v3)
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, NoTrackingAfterThisIsPublished) {
  ClassCreator helper(DexType::make_type("LPublishedHelper;"));
  helper.set_super(type::java_lang_Object());
  helper.add_field(
      DexField::make_field("LPublishedHelper;.published:LDefaults;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  helper.add_method(assembler::method_from_string(R"(
    (method (public static) "LPublishedHelper;.mutate:()V"
      ((sget-object "LPublishedHelper;.published:LDefaults;")
       (move-result-pseudo-object v0)
       (const v1 9) (iput v1 v0 "LDefaults;.i:I") (return-void)))
  )"));
  m_extra_classes.push_back(helper.create());
  EXPECT_EQ(optimize(R"(
    (sput-object v0 "LPublishedHelper;.published:LDefaults;")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (invoke-static () "LPublishedHelper;.mutate:()V")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
  )"),
            2)
      << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, NoTrackingAfterEscapeOnOnePath) {
  EXPECT_EQ(optimize(R"(
    (if-eqz v1 :join) (invoke-static (v0) "LHelper;.mutate:(LDefaults;)V")
    (:join) (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
  )"),
            2)
      << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, CastOfThisIsAnAlias) {
  EXPECT_EQ(optimize(R"(
    (check-cast v0 "LDefaults;") (move-result-pseudo-object v4)
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 9) (iput v3 v4 "LDefaults;.i:I")
    (iget v0 "LDefaults;.i:I") (move-result-pseudo v5)
    (invoke-static (v5) "LDefaults;.consume:(I)V")
  )"),
            2);
  EXPECT_NE(m_last_code.find("(const v5 9)"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, ComparingOrLockingThisKeepsTracking) {
  EXPECT_EQ(optimize(R"(
    (monitor-enter v0)
    (if-eq v0 v2 :same) (:same)
    (monitor-exit v0)
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, EscapeBackedgeDisablesEarlierAccesses) {
  m_class->add_field(DexField::make_field("LDefaults;.published:LDefaults;")
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  EXPECT_EQ(optimize(R"(
    (:loop)
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (iget v0 "LDefaults;.i:I") (move-result-pseudo v4)
    (invoke-static (v4) "LDefaults;.consume:(I)V")
    (sput-object v0 "LDefaults;.published:LDefaults;")
    (add-int/lit v1 v1 -1) (if-nez v1 :loop)
  )"),
            2)
      << m_last_code;
  EXPECT_NE(m_last_code.find("iget"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest,
       OnlyAccessesBeforeAcyclicEscapeAreTracked) {
  m_class->add_field(DexField::make_field("LDefaults;.published:LDefaults;")
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (sput-object v0 "LDefaults;.published:LDefaults;")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (iget v0 "LDefaults;.i:I") (move-result-pseudo v4)
    (invoke-static (v4) "LDefaults;.consume:(I)V")
  )"),
            3)
      << m_last_code;
  EXPECT_NE(m_last_code.find("iget"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, NonconstantNarrowStoresDoNotFoldReads) {
  const auto cases =
      std::to_array<std::pair<const char*, const char*>>({{"b:B", "byte"},
                                                          {"s:S", "short"},
                                                          {"c:C", "char"},
                                                          {"z2:Z", "boolean"}});
  for (const auto& [suffix, kind] : cases) {
    const std::string signature = std::string("LDefaults;.") + suffix;
    SCOPED_TRACE(signature);
    m_class->add_field(
        DexField::make_field(signature)->make_concrete(ACC_PUBLIC));
    const std::string get = std::string("iget-") + kind;
    std::ostringstream body;
    body << "(iput-" << kind << " v1 v0 \"" << signature << "\") (" << get
         << " v0 \"" << signature << "\") "
         << "(move-result-pseudo v4) "
         << "(invoke-static (v4) \"LDefaults;.consume:(I)V\")";
    EXPECT_EQ(optimize(body.str()), 1);
    EXPECT_NE(m_last_code.find(get), std::string::npos) << m_last_code;
  }
}

TEST_F(ConstructorFieldAnalyzerTest, ExceptionHandlerAfterUnrelatedCall) {
  EXPECT_EQ(optimize(R"(
    (.try_start a) (invoke-static () "LHelper;.unknown:()V")
    (.try_end a) (goto :end)
    (.catch (a)) (move-exception v4)
    (:end) (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            0);
}

TEST_F(ConstructorFieldAnalyzerTest, ExceptionHandlerKeepsValueStoredBefore) {
  EXPECT_EQ(optimize(R"(
    (const v3 7) (iput v3 v0 "LDefaults;.i:I")
    (.try_start a) (invoke-static () "LHelper;.unknown:()V")
    (.try_end a) (goto :end)
    (.catch (a)) (move-exception v4) (iput v3 v0 "LDefaults;.i:I")
    (:end)
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, ExceptionFromCallReceivingThis) {
  EXPECT_EQ(optimize(R"(
    (.try_start a) (invoke-static (v0) "LHelper;.mutate:(LDefaults;)V")
    (.try_end a) (goto :end)
    (.catch (a)) (move-exception v4)
    (:end) (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1);
}

TEST_F(ConstructorFieldAnalyzerTest, EscapeInLoopForgetsFieldsAtExit) {
  m_ctor->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0) (load-param v1) (load-param-object v2)
     (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
     (const v3 7) (iput v3 v0 "LDefaults;.i:I")
     (:loop)
     (const v4 9) (invoke-virtual (v0 v4) "LDefaults;.set:(I)V")
     (if-nez v1 :loop)
     (return-void))
  )"));
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  auto* code = m_ctor->get_code();
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  const auto class_fields = cp::ClassConstructorFields::create(m_class, {});
  const auto& state = class_fields.constructors.at(m_ctor);
  auto env = cp::interprocedural::env_with_params(
      /* is_static */ false, code, cp::interprocedural::ArgumentDomain::top());
  class_fields.initialize_fields(m_ctor, state.tracked_fields(), &env);
  cp::intraprocedural::FixpointIterator fp_iter(
      cfg, InstructionAnalyzerCombiner<cp::ConstructorFieldAnalyzer,
                                       cp::PrimitiveAnalyzer>(&state, nullptr));
  fp_iter.run(env);
  auto exit = fp_iter.get_exit_state_at(cfg.exit_block());
  const auto* field = DexField::get_field("LDefaults;.i:I")->as_def();
  // Every return follows at least one call to set(9).
  const auto value = exit.get_field_environment().get(field);
  EXPECT_TRUE(value.is_top()) << value;
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(ConstructorFieldAnalyzerTest, OwnConstructorCallForgetsFieldsItKeeps) {
  // `Defaults()` keeps `this`, but it stores 7 to i.
  m_keeping.insert(DexMethod::get_method("LDefaults;.<init>:()V")->as_def());
  m_initializer = "";
  EXPECT_EQ(optimize(R"(
    (invoke-direct (v0) "LDefaults;.<init>:()V")
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
  )"),
            1)
      << m_last_code;
}

TEST_F(ConstructorFieldAnalyzerTest, EntryWriteCycleReachesFixedPoint) {
  auto* a = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  a->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (const v1 0) (invoke-direct (v0 v1) "LDefaults;.<init>:(I)V")
     (return-void))
  )"));
  auto* b = assembler::method_from_string(R"(
    (method (public) "LDefaults;.<init>:(I)V"
      ((load-param-object v0) (load-param v1)
       (const v2 1) (iput-boolean v2 v0 "LDefaults;.z:Z")
       (invoke-direct (v0) "LDefaults;.<init>:()V")
       (return-void)))
  )");
  m_class->add_method(b);
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  const auto entries =
      cp::ClassConstructorFields::create(m_class, {}).entry_writes;
  for (const auto* ctor : {a, b}) {
    auto it = entries.find(ctor);
    ASSERT_NE(it, entries.end());
    EXPECT_EQ(it->second.size(), 2u);
    EXPECT_EQ(it->second.count(DexField::get_field("LDefaults;.i:I")->as_def()),
              1u);
    EXPECT_EQ(it->second.count(DexField::get_field("LDefaults;.z:Z")->as_def()),
              1u);
  }
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(ConstructorFieldAnalyzerTest, SelfCallStartsWithItsEarlierStores) {
  auto* a = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  a->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (sget "LDefaults;.observed:I") (move-result-pseudo v1)
     (if-eqz v1 :done)
     (invoke-direct (v0) "LDefaults;.<init>:()V")
     (:done)
     (return-void))
  )"));
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  const auto entries =
      cp::ClassConstructorFields::create(m_class, {}).entry_writes;
  auto it = entries.find(a);
  ASSERT_NE(it, entries.end());
  EXPECT_EQ(it->second.size(), 1u);
  EXPECT_EQ(it->second.count(DexField::get_field("LDefaults;.i:I")->as_def()),
            1u);
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(ConstructorFieldAnalyzerTest,
       ExcludedConstructorLeavesEveryEntryUnknown) {
  // `Defaults()` stores nothing before it calls `Defaults(int)`, but its code
  // may differ at runtime.
  auto* a = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  a->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 0) (invoke-direct (v0 v1) "LDefaults;.<init>:(I)V")
     (return-void))
  )"));
  a->rstate.set_no_optimizations();
  auto* b = assembler::method_from_string(R"(
    (method (public) "LDefaults;.<init>:(I)V"
      ((load-param-object v0) (load-param v1)
       (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
       (return-void)))
  )");
  m_class->add_method(b);
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  const auto fields = cp::ClassConstructorFields::create(m_class, {});
  auto it = fields.entry_writes.find(b);
  ASSERT_NE(it, fields.entry_writes.end());
  EXPECT_EQ(it->second, fields.constructors.at(b).tracked_fields());
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(ConstructorFieldAnalyzerTest,
       ExcludedConstructorWithoutCodeLeavesEveryEntryUnknown) {
  // `Defaults(long)` has no code Redex sees and is excluded from optimization;
  // at runtime it may store to any field and call `Defaults()` on `this`.
  auto* excluded = DexMethod::make_method("LDefaults;.<init>:(J)V")
                       ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);
  excluded->rstate.set_no_optimizations();
  m_class->add_method(excluded);
  auto* a = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  const auto fields = cp::ClassConstructorFields::create(m_class, {});
  auto it = fields.entry_writes.find(a);
  ASSERT_NE(it, fields.entry_writes.end());
  EXPECT_EQ(it->second, fields.constructors.at(a).tracked_fields());
  walk::code(Scope{m_class},
             [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}
