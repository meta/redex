/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <boost/algorithm/string/replace.hpp>
#include <gtest/gtest.h>

#include <array>
#include <string>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "Instrument.h"
#include "PassManager.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

namespace {

constexpr const char* kPrefix = "Lcom/analysis/";
constexpr const char* kDefined = "Lcom/analysis/Defined;";
constexpr const char* kMissing = "Lcom/analysis/Missing;";

// Code that names `CLS` only inside a method handle, a method type or a call's
// prototype. Each `invoke-static` becomes an `invoke-custom` of a call site
// with the prototype `(CLS)V` when `invoke_custom` is set.
struct Case {
  const char* name;
  const char* code;
  bool invoke_custom;
};

const auto kCases = std::to_array<Case>({
    {"ConstMethodHandle", R"(
      (
        (const-method-handle invoke-static "CLS.m:()V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )",
     false},
    {"ConstMethodType", R"(
      (
        (const-method-type "(CLS)V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )",
     false},
    {"InvokePolymorphic", R"(
      (
        (const v0 0)
        (const v1 0)
        (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(CLS)V")
        (return-void)
      )
    )",
     false},
    {"InvokeCustom", R"(
      (
        (const v0 0)
        (invoke-static (v0) "LUser;.make:(CLS)V")
        (return-void)
      )
    )",
     true},
});

void PrintTo(const Case& test_case, std::ostream* os) { *os << test_case.name; }

class InstrumentTest : public RedexTest,
                       public ::testing::WithParamInterface<Case> {
 protected:
  // Adds `LUser;.run:()V` with the code of the test case, naming `cls`, and
  // `kDefined`, a class under the analysis package prefix.
  void add_classes(const std::string& cls) {
    const auto& test_case = GetParam();

    ClassCreator defined_creator(DexType::make_type(kDefined));
    defined_creator.set_super(type::java_lang_Object());

    ClassCreator user_creator(DexType::make_type("LUser;"));
    user_creator.set_super(type::java_lang_Object());
    auto* method = DexMethod::make_method("LUser;.run:()V")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(assembler::ircode_from_string(
        boost::replace_all_copy(std::string(test_case.code), "CLS", cls)));
    if (test_case.invoke_custom) {
      redex::make_invoke_custom(method->get_code(), "make", "(" + cls + ")V");
    }
    user_creator.add_method(method);

    DexStore store("classes");
    store.add_classes({defined_creator.create(), user_creator.create()});
    m_stores.emplace_back(std::move(store));
  }

  // Runs the check that InstrumentPass makes before any pass runs when it has
  // an analysis package prefix: every type under the prefix that code names
  // must be defined.
  void eval_instrument_pass() {
    Json::Value global_config(Json::objectValue);
    global_config["instrument_pass_enabled"] = true;
    global_config["InstrumentPass"]["analysis_package_prefix"] = kPrefix;
    ConfigFiles conf(global_config);

    instrument::InstrumentPass pass;
    std::vector<Pass*> passes{&pass};
    PassManager manager(passes, conf);
    pass.eval_pass(m_stores, conf, manager);
  }

  DexStoresVector m_stores;
};

TEST_P(InstrumentTest, missingTypeFailsTheIntegrityCheck) {
  add_classes(kMissing);
  EXPECT_THROW(eval_instrument_pass(), RedexException);
}

TEST_P(InstrumentTest, definedTypePassesTheIntegrityCheck) {
  add_classes(kDefined);
  EXPECT_NO_THROW(eval_instrument_pass());
}

INSTANTIATE_TEST_SUITE_P(MethodHandlesAndPrototypes,
                         InstrumentTest,
                         ::testing::ValuesIn(kCases),
                         [](const ::testing::TestParamInfo<Case>& info) {
                           return info.param.name;
                         });

} // namespace
