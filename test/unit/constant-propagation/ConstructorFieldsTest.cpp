/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <array>
#include <gtest/gtest.h>
#include <optional>
#include <sstream>

#include "ConfigFiles.h"
#include "ConstantPropagation.h"
#include "ConstantPropagationPass.h"
#include "Creators.h"
#include "DexAccess.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Walkers.h"

class ConstructorFieldsTest : public RedexTest {
 public:
  void SetUp() override {
    ClassCreator creator(DexType::make_type("LDefaults;"));
    creator.set_super(type::java_lang_Object());
    for (const auto* signature : {"LDefaults;.i:I", "LDefaults;.z:Z"}) {
      creator.add_field(
          DexField::make_field(signature)->make_concrete(ACC_PUBLIC));
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
    creator.add_field(DexField::make_field("LDefaults;.observed:I")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    m_class = creator.create();
  }

 protected:
  size_t optimize(const std::string& instructions,
                  std::optional<bool> enabled = true) {
    const std::string initializer =
        m_initializer.empty()
            ? ""
            : "(invoke-direct (v0) \"" + m_initializer + "\") ";
    const std::string prefix =
        "((load-param-object v0) (load-param v1) (load-param-object v2) " +
        initializer;
    m_ctor->set_code(assembler::ircode_from_string(prefix + instructions +
                                                   " (return-void))"));
    DexStore store("classes");
    store.add_classes({m_class});
    store.add_classes(m_extra_classes);
    DexStoresVector stores;
    stores.emplace_back(std::move(store));
    Json::Value json;
    if (enabled) {
      json["ConstantPropagationPass"]["track_constructor_fields"] = *enabled;
    }
    ConfigFiles conf(json);
    conf.parse_global_config();
    auto tmp = redex::make_tmp_dir("constructor_fields_%%%%%%%%");
    conf.set_outdir(tmp.path);
    ConstantPropagationPass pass;
    PassManager manager({&pass}, conf, RedexOptions{});
    manager.run_passes(stores, conf);
    m_ctor->get_code()->build_cfg();
    size_t count = 0;
    for (auto& mie : cfg::InstructionIterable(m_ctor->get_code()->cfg())) {
      if (opcode::is_an_iput(mie.insn->opcode())) {
        ++count;
      }
    }
    m_ctor->get_code()->clear_cfg();
    m_last_code = assembler::to_string(m_ctor->get_code());
    return count;
  }

  std::string m_last_code;
  DexClass* m_class{nullptr};
  DexMethod* m_ctor{nullptr};
  std::string m_initializer{"Ljava/lang/Object;.<init>:()V"};
  std::vector<DexClass*> m_extra_classes;
};

TEST_F(ConstructorFieldsTest, MutableFieldAndMultipleConstructors) {
  const std::string body = R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))";
  EXPECT_EQ(optimize(body, false), 1);
  EXPECT_EQ(optimize(body), 0);
}

TEST_F(ConstructorFieldsTest, IncomingDelegationAlreadyWroteField) {
  auto* caller = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  caller->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (const v1 0) (const v2 0)
     (invoke-direct (v0 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
     (return-void))
  )"));
  EXPECT_EQ(optimize(R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))"), 1);
}

TEST_F(ConstructorFieldsTest, TransitiveDelegationPreservesIncomingWrites) {
  auto* outer = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  outer->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (const v1 0)
     (invoke-direct (v0 v1) "LDefaults;.<init>:(I)V")
     (return-void))
  )"));
  m_class->add_method(assembler::method_from_string(R"(
    (method (public) "LDefaults;.<init>:(I)V"
      ((load-param-object v0) (load-param v1)
       (const v2 0)
       (invoke-direct (v0 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
       (return-void)))
  )"));
  const std::string reset = R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))";
  EXPECT_EQ(optimize(reset, false), 1);
  EXPECT_EQ(optimize(reset), 1) << m_last_code;
}

TEST_F(ConstructorFieldsTest, ScopeLeavesExcludedConstructorsUnchanged) {
  m_ctor->rstate.set_no_optimizations();
  m_ctor->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0) (load-param v1) (load-param-object v2)
     (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
     (const v3 0) (iput v3 v0 "LDefaults;.i:I")
     (return-void))
  )"));
  const auto original = assembler::to_s_expr(m_ctor->get_code());
  constant_propagation::Config config;
  config.track_constructor_fields = true;
  constant_propagation::ConstantPropagation impl(config);
  const Scope scope{m_class};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  impl.run(scope, nullptr, constant_propagation::NullCheckMethods());
  walk::code(scope, [](DexMethod*, IRCode& code) { code.clear_cfg(); });
  // The store repeats the zero allocation wrote, but the constructor is
  // excluded from optimization.
  EXPECT_EQ(assembler::to_s_expr(m_ctor->get_code()), original);
}

TEST_F(ConstructorFieldsTest, IncomingDelegationKeepsOtherFieldsZero) {
  auto* caller = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  caller->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 1) (iput-boolean v1 v0 "LDefaults;.z:Z")
     (const v1 0) (const v2 0)
     (invoke-direct (v0 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
     (return-void))
  )"));
  EXPECT_EQ(optimize(R"(
    (const v3 0) (iput v3 v0 "LDefaults;.i:I")
    (iput-boolean v3 v0 "LDefaults;.z:Z")
  )"),
            1)
      << m_last_code;
  EXPECT_NE(m_last_code.find("iput-boolean"), std::string::npos) << m_last_code;
}

TEST_F(ConstructorFieldsTest, IncomingDelegationWithoutEarlierStores) {
  auto* caller = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  caller->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 0) (const v2 0)
     (invoke-direct (v0 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (return-void))
  )"));
  EXPECT_EQ(optimize(R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))"), 0);
}

TEST_F(ConstructorFieldsTest, SiblingConstructsAnotherObject) {
  auto* caller = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  caller->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 7) (iput v1 v0 "LDefaults;.i:I")
     (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
     (new-instance "LDefaults;") (move-result-pseudo-object v3)
     (const v1 0) (const v2 0)
     (invoke-direct (v3 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
     (return-void))
  )"));
  EXPECT_EQ(optimize(R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))"), 0);
}

TEST_F(ConstructorFieldsTest, DefaultOffOutputParity) {
  const std::string body = R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))";
  EXPECT_EQ(optimize(body, false), 1);
  const auto off_code = m_last_code;
  EXPECT_EQ(optimize(body, std::nullopt), 1);
  EXPECT_EQ(m_last_code, off_code);
}

TEST_F(ConstructorFieldsTest, ExcludedSiblingConstructorKeepsStores) {
  // `Defaults()` stores nothing before it calls `Defaults(int, Object)`, but
  // it is excluded from optimization, so its runtime code may store first.
  auto* sibling = DexMethod::get_method("LDefaults;.<init>:()V")->as_def();
  sibling->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (const v1 0) (const v2 0)
     (invoke-direct (v0 v1 v2) "LDefaults;.<init>:(ILjava/lang/Object;)V")
     (return-void))
  )"));
  sibling->rstate.set_no_optimizations();
  EXPECT_EQ(optimize(R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))"), 1)
      << m_last_code;
}

TEST_F(ConstructorFieldsTest, SuperclassConstructorIsEscape) {
  // `Base()` does nothing but call Object's constructor; still, the call
  // passes `this` to other code, after which the store may not be redundant.
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     ((load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)))
  )"));
  m_extra_classes.push_back(base.create());
  m_class->set_super_class(DexType::make_type("LBase;"));
  m_initializer = "LBase;.<init>:()V";
  EXPECT_EQ(optimize(R"((const v3 0) (iput v3 v0 "LDefaults;.i:I"))"), 1)
      << m_last_code;
}
