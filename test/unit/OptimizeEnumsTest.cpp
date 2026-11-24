/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "OptionalIO.h"
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <boost/algorithm/string/replace.hpp>
#include <functional>
#include <mutex>
#include <set>
#include <thread>

#include "ControlFlow.h"
#include "Creators.h"
#include "DexCallSite.h"
#include "EnumAnalyzeGeneratedMethods.h"
#include "EnumClinitAnalysis.h"
#include "EnumConfig.h"
#include "EnumUpcastAnalysis.h"
#include "IRAssembler.h"
#include "IRTypeChecker.h"
#include "InlineEnumValues.h"
#include "MethodOverrideGraph.h"
#include "OptimizeEnums.h"
#include "OptimizeEnumsUnsafeType.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "RemoveNullcheckStringArg.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace testing;

class OptimizeEnumsTest : public RedexTest {};

optimize_enums::ParamSummary get_summary(const std::string& s_expr) {
  auto* method = assembler::method_from_string(s_expr);
  method->get_code()->build_cfg();
  return optimize_enums::calculate_param_summary(method,
                                                 type::java_lang_Object());
}

TEST_F(OptimizeEnumsTest, test_param_summary_generating) {
  auto summary = get_summary(R"(
    (method (static) "LFoo;.upcast_when_return:(Ljava/lang/Enum;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (return-object v0)
      )
    )
  )");
  EXPECT_EQ(summary.returned_param, std::nullopt);
  EXPECT_TRUE(summary.safe_params.empty());

  auto summary2 = get_summary(R"(
    (method (public) "LFoo;.param_0_is_not_safecast:(Ljava/lang/Enum;Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param-object v2)
        (return-void)
      )
    )
  )");
  EXPECT_EQ(summary2.returned_param, std::nullopt);
  EXPECT_THAT(unordered_unsafe_unwrap(summary2.safe_params),
              UnorderedElementsAre(2));

  auto summary2_static = get_summary(R"(
    (method (static public) "LFoo;.param_0_is_not_safecast:(Ljava/lang/Enum;Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (return-void)
      )
    )
  )");
  EXPECT_EQ(summary2_static.returned_param, std::nullopt);
  EXPECT_THAT(unordered_unsafe_unwrap(summary2_static.safe_params),
              UnorderedElementsAre(1));

  auto summary3 = get_summary(R"(
    (method () "LFoo;.check_cast:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v1)
        (load-param-object v0)
        (check-cast v0 "Ljava/lang/Enum;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  EXPECT_EQ(summary3.returned_param, std::nullopt);
  EXPECT_TRUE(summary3.safe_params.empty());

  auto summary4 = get_summary(R"(
    (method () "LFoo;.has_invocation:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v1)
        (load-param-object v0)
        (invoke-virtual (v0) "Ljava/lang/Object;.toString:()Ljava/lang/String;")
        (return-object v0)
      )
    )
  )");
  EXPECT_EQ(summary4.returned_param, std::nullopt);
  EXPECT_TRUE(summary4.safe_params.empty());
}

// A caller can follow an enum through `pick` only if `pick` returns nothing
// but its parameter, or null.
TEST_F(OptimizeEnumsTest, paramSummaryTracksParamReturnedAloneOrWithNull) {
  auto alone = get_summary(R"(
    (method (static) "LFoo;.identity:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (return-object v0)
      )
    )
  )");
  EXPECT_EQ(alone.returned_param, 0);
  EXPECT_THAT(unordered_unsafe_unwrap(alone.safe_params),
              UnorderedElementsAre(0));

  auto or_null = get_summary(R"(
    (method (static) "LFoo;.pick:(Ljava/lang/Object;Z)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param v1)
        (if-eqz v1 :null)
        (return-object v0)
        (:null)
        (const v2 0)
        (return-object v2)
      )
    )
  )");
  EXPECT_EQ(or_null.returned_param, 0);
  EXPECT_THAT(unordered_unsafe_unwrap(or_null.safe_params),
              UnorderedElementsAre(0));
}

// When `pick` may return its parameter or some other object, a caller cannot
// tell which one it gets, so the parameter escapes.
TEST_F(OptimizeEnumsTest, paramSummaryEscapesParamReturnedWithOtherObject) {
  auto or_escaped = get_summary(R"(
    (method (static) "LFoo;.pick:(Ljava/lang/Object;Z)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param v1)
        (if-eqz v1 :cache)
        (return-object v0)
        (:cache)
        (sget-object "LFoo;.CACHE:Ljava/lang/Object;")
        (move-result-pseudo-object v2)
        (return-object v2)
      )
    )
  )");
  EXPECT_EQ(or_escaped.returned_param, std::nullopt);
  EXPECT_TRUE(or_escaped.safe_params.empty());

  auto or_fresh = get_summary(R"(
    (method (static) "LFoo;.pick:(Ljava/lang/Object;Z)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param v1)
        (if-eqz v1 :fresh)
        (return-object v0)
        (:fresh)
        (new-instance "Ljava/lang/Object;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2) "Ljava/lang/Object;.<init>:()V")
        (return-object v2)
      )
    )
  )");
  EXPECT_EQ(or_fresh.returned_param, std::nullopt);
  EXPECT_TRUE(or_fresh.safe_params.empty());

  auto or_other_param = get_summary(R"(
    (method (static) "LFoo;.pick:(Ljava/lang/Object;Ljava/lang/Object;Z)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (if-eqz v2 :other)
        (return-object v0)
        (:other)
        (return-object v1)
      )
    )
  )");
  EXPECT_EQ(or_other_param.returned_param, std::nullopt);
  EXPECT_TRUE(or_other_param.safe_params.empty());
}

/* Create a Bar enum class and a shell implementations of Enum, Integer, Object
class enum Bar {
  Y(2132351567),
  Z(2132351568);

  @IdRes int x;
  Bar(int x) { this.x = x; }

  int fromInt(int i) {
    if (i == 0) {
      return Y.x;
    } else {
      return Z.x;
    }
  }
}
*/
DexStore create_enum_store() {
  // Make a fake Enum class that Bar can call
  ClassCreator ec(type::java_lang_Enum());
  ec.add_method(assembler::method_from_string(R"(
    (method (public constructor) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (return-void)
      )
    )
  )"));
  ec.add_method(assembler::method_from_string(R"(
    (method (public constructor) "Ljava/lang/Enum;.ordinal:()I"
      (
        (load-param-object v0)
        (const v1 0)
        (return v1)
      )
    )
  )"));
  ec.add_method(assembler::method_from_string(R"(
    (method (public) "Ljava/lang/Enum;.getDeclaringClass:()Ljava/lang/Class;"
      (
        (load-param-object v0)
        (const v1 0)
        (return-object v1)
      )
    )
  )"));
  ec.add_method(assembler::method_from_string(R"(
    (method (public static) "Ljava/lang/Enum;.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v2 0)
        (return-object v2)
      )
    )
  )"));
  // The JDK hierarchy that decides which type checks boxing can change.
  auto* comparable = DexType::make_type("Ljava/lang/Comparable;");
  auto* serializable = DexType::make_type("Ljava/io/Serializable;");
  auto* number = DexType::make_type("Ljava/lang/Number;");
  ec.set_super(type::java_lang_Object());
  ec.add_interface(comparable);
  ec.add_interface(serializable);
  ec.set_access(ACC_PUBLIC);
  auto* enums = ec.create();
  std::vector<DexClass*> jdk_classes;
  for (auto* intf : {comparable, serializable}) {
    ClassCreator creator(intf);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    jdk_classes.push_back(creator.create());
  }
  ClassCreator nc(number);
  nc.set_super(type::java_lang_Object());
  nc.add_interface(serializable);
  nc.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  jdk_classes.push_back(nc.create());

  ClassCreator ic(type::java_lang_Integer());
  ic.add_method(assembler::method_from_string(R"(
    (method (public) "Ljava/lang/Integer;.intValue:()I"
      (
        (load-param-object v0)
        (const v1 0)
        (return v1)
      )
    )
  )"));
  ic.set_super(number);
  ic.add_interface(comparable);
  ic.set_access(ACC_PUBLIC);
  auto* ints = ic.create();

  ClassCreator oc(type::java_lang_Object());
  oc.add_method(assembler::method_from_string(R"(
    (method (public) "Ljava/lang/Object;.getClass:()Ljava/lang/Class;"
      (
        (load-param-object v0)
        (const v1 0)
        (return v1)
      )
    )
  )"));
  oc.set_access(ACC_PUBLIC);
  auto* objs = oc.create();

  ClassCreator cc(DexType::make_type("LBar;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);

  // Add instance field
  auto* x = dynamic_cast<DexField*>(DexField::make_field("LBar;.x:I"));
  x->make_concrete(ACC_PUBLIC);
  cc.add_field(x);

  // Add init
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LBar;.<init>:(Ljava/lang/String;II)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (load-param v3)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (iput v3 v0 "LBar;.x:I")
        (return-void)
      )
    )
  )"));

  // Add static enum fields
  auto* VALUES =
      dynamic_cast<DexField*>(DexField::make_field("LBar;.$VALUES:[LBar;"));
  VALUES->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC);
  cc.add_field(VALUES);
  auto* Y = dynamic_cast<DexField*>(DexField::make_field("LBar;.Y:LBar;"));
  Y->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM);
  cc.add_field(Y);
  auto* Z = dynamic_cast<DexField*>(DexField::make_field("LBar;.Z:LBar;"));
  Z->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM);
  cc.add_field(Z);

  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.fromInt:(I)I"
     (
      (load-param v0)
      (if-eqz v0 :L1)
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v1)
      (iget v1 "LBar;.x:I")
      (move-result-pseudo v1)
      (return v1)
      (:L1)
      (sget-object "LBar;.Z:LBar;")
      (move-result-pseudo-object v1)
      (iget v1 "LBar;.x:I")
      (move-result-pseudo v1)
      (return v1)
     )
    )
  )"));

  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.$values:()[LBar;"
     (
      (const v0 2)
      (new-array v0 "[LBar;")
      (move-result-pseudo-object v0)
      (const v1 0)
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v2)
      (aput-object v2 v0 v1)
      (const v1 1)
      (sget-object "LBar;.Z:LBar;")
      (move-result-pseudo-object v2)
      (aput-object v2 v0 v1)
      (return-object v0)
     )
    )
  )"));

  // Add clinit. This part contains the unique pattern to test, which is when an
  // instance field is a resource ID specified using the R_CONST instruction.
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.<clinit>:()V"
     (
      (r-const v0 2132351567)
      (const-string "Y")
      (move-result-pseudo-object v1)
      (const v2 0)
      (new-instance "LBar;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2 v0) "LBar;.<init>:(Ljava/lang/String;II)V")
      (sput-object v3 "LBar;.Y:LBar;")
      (r-const v0 2132351568)
      (const-string "Z")
      (move-result-pseudo-object v1)
      (const v2 1)
      (new-instance "LBar;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2 v0) "LBar;.<init>:(Ljava/lang/String;II)V")
      (sput-object v3 "LBar;.Z:LBar;")
      (invoke-static () "LBar;.$values:()[LBar;")
      (move-result-object v0)
      (sput-object v0 "LBar;.$VALUES:[LBar;")
      (return-void)
     )
    )
  )"));
  auto* bar = cc.create();

  for (auto* m : bar->get_all_methods()) {
    m->get_code()->build_cfg();
  }

  auto store = DexStore("classes");
  store.add_classes({bar, ints, enums, objs});
  store.add_classes(jdk_classes);
  return store;
}

// Analyzes `cls`'s <clinit> with summaries built over every class the test
// created.
optimize_enums::EnumAttributes analyze_clinit(const DexClass* cls,
                                              bool support_kt_19_enum_entries) {
  Scope scope;
  g_redex->walk_type_class([&](const DexType*, const DexClass* type_cls) {
    scope.push_back(const_cast<DexClass*>(type_cls));
  });
  auto override_graph = method_override_graph::build_graph(scope);
  optimize_enums::ConstantReadSummaries reads(*override_graph);
  return optimize_enums::analyze_enum_clinit(cls, support_kt_19_enum_entries,
                                             &reads);
}

// Run the usage analysis on `scope` and return every reason it records for
// rejecting `type`. The analysis reports reasons from several threads.
std::set<optimize_enums::UnsafeType> rejection_reasons(
    const Scope& scope, optimize_enums::Config* config, const DexType* type) {
  std::mutex reasons_mutex;
  std::set<optimize_enums::UnsafeType> reasons;
  optimize_enums::reject_unsafe_enums(
      scope, config,
      [&](const DexType* rejected, optimize_enums::UnsafeType reason) {
        if (rejected == type) {
          std::lock_guard<std::mutex> lock(reasons_mutex);
          reasons.insert(reason);
        }
      });
  return reasons;
}

TEST_F(OptimizeEnumsTest, analyzeRConstMembers) {
  DexStoresVector stores({create_enum_store()});
  auto scope = build_class_scope(stores);
  auto* bar = scope[0];

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar->get_type());

  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();

  manager.run_passes(stores, dummy_config);

  auto* get_x =
      bar->find_method_from_simple_deobfuscated_name("redex$OE$get_x");
  EXPECT_NE(get_x, nullptr);
  get_x->get_code()->build_cfg();

  auto& cfg = get_x->get_code()->cfg();
  int const_count = 0;
  int rconst_count = 0;
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_CONST) {
      const_count++;
    } else if (it->insn->opcode() == IOPCODE_R_CONST) {
      rconst_count++;
    }
  }
  EXPECT_EQ(const_count, 0);
  EXPECT_EQ(rconst_count, 2);
}

// The substitute for `Enum.hashCode()` multiplies the ordinal by an odd
// constant, adds a seed derived from the enum's name ("LBar;" gives 8261) and
// xors the result with its upper half.
// It does not look up the constant's name, so Bar, whose name is otherwise
// unused, gets no `redex$OE$name`.
TEST_F(OptimizeEnumsTest, hashCodeSubstituteDoesNotLookUpName) {
  DexStoresVector stores({create_enum_store()});
  auto scope = build_class_scope(stores);
  auto* bar = scope[0];
  auto* hash_z = assembler::method_from_string(R"(
    (method (public static) "LBar;.hashZ:()I"
     (
      (sget-object "LBar;.Z:LBar;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "LBar;.hashCode:()I")
      (move-result v0)
      (return v0)
     )
    )
  )");
  hash_z->get_code()->build_cfg();
  bar->add_method(hash_z);

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);

  EXPECT_EQ(bar->find_method_from_simple_deobfuscated_name("redex$OE$name"),
            nullptr);
  auto* hashcode =
      bar->find_method_from_simple_deobfuscated_name("redex$OE$hashCode");
  ASSERT_NE(hashcode, nullptr);
  hashcode->get_code()->clear_cfg();
  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (.pos:dbg_0 "LBar;.redex$OE$hashCode:(Ljava/lang/Integer;)I" RedexGenerated 0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v1)
      (mul-int/lit v1 v1 -25033)
      (add-int/lit v1 v1 8261)
      (ushr-int/lit v2 v1 16)
      (xor-int v1 v1 v2)
      (return v1)
    )
  )");
  EXPECT_CODE_EQ(hashcode->get_code(), expected.get());
}

// An enum with an instance kept only in its values array is not boxed.
TEST_F(OptimizeEnumsTest, unstoredConstantKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  ClassCreator cc(DexType::make_type("LBaz;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  auto* values =
      dynamic_cast<DexField*>(DexField::make_field("LBaz;.$VALUES:[LBaz;"));
  values->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC);
  cc.add_field(values);
  auto* one = dynamic_cast<DexField*>(DexField::make_field("LBaz;.ONE:LBaz;"));
  one->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(one);
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LBaz;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LBaz;.<clinit>:()V"
     (
      (const-string "ONE")
      (move-result-pseudo-object v1)
      (const v2 0)
      (new-instance "LBaz;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2) "LBaz;.<init>:(Ljava/lang/String;I)V")
      (sput-object v3 "LBaz;.ONE:LBaz;")
      (const-string "TWO")
      (move-result-pseudo-object v1)
      (const v2 1)
      (new-instance "LBaz;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v1 v2) "LBaz;.<init>:(Ljava/lang/String;I)V")
      (const v2 2)
      (new-array v2 "[LBaz;")
      (move-result-pseudo-object v0)
      (const v2 0)
      (aput-object v3 v0 v2)
      (const v2 1)
      (aput-object v4 v0 v2)
      (sput-object v0 "LBaz;.$VALUES:[LBaz;")
      (return-void)
     )
    )
  )"));
  auto* baz = cc.create();
  for (auto* m : baz->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  stores[0].add_classes({baz});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);

  EXPECT_EQ(baz->get_super_class(), type::java_lang_Enum());
}

// One allocation instruction inside a loop can create both a named constant
// and an extra instance kept only in the values array.
TEST_F(OptimizeEnumsTest, repeatedAllocationSiteKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  ClassCreator cc(DexType::make_type("LLoopEnum;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(DexField::make_field("LLoopEnum;.$VALUES:[LLoopEnum;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  cc.add_field(
      DexField::make_field("LLoopEnum;.ONLY:LLoopEnum;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LLoopEnum;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoopEnum;.values:()[LLoopEnum;"
      (
        (sget-object "LLoopEnum;.$VALUES:[LLoopEnum;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LLoopEnum;.<clinit>:()V"
      (
        (const v4 0)
        (const v5 2)
        (new-array v5 "[LLoopEnum;")
        (move-result-pseudo-object v0)
        (:loop)
        (const-string "ONLY")
        (move-result-pseudo-object v1)
        (const v2 0)
        (new-instance "LLoopEnum;")
        (move-result-pseudo-object v3)
        (invoke-direct (v3 v1 v2) "LLoopEnum;.<init>:(Ljava/lang/String;I)V")
        (aput-object v3 v0 v4)
        (if-nez v4 :done)
        (const v4 1)
        (goto :loop)
        (:done)
        (sput-object v3 "LLoopEnum;.ONLY:LLoopEnum;")
        (sput-object v0 "LLoopEnum;.$VALUES:[LLoopEnum;")
        (return-void)
      )
    )
  )"));
  auto* loop_enum = cc.create();
  for (auto* method : loop_enum->get_all_methods()) {
    method->get_code()->build_cfg();
  }

  ClassCreator uc(DexType::make_type("LLoopUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  auto* count = assembler::method_from_string(R"(
    (method (public static) "LLoopUser;.count:()I"
      (
        (invoke-static () "LLoopEnum;.values:()[LLoopEnum;")
        (move-result-object v0)
        (array-length v0)
        (move-result-pseudo v1)
        (return v1)
      )
    )
  )");
  uc.add_method(count);
  auto* user = uc.create();
  count->get_code()->build_cfg();
  stores[0].add_classes({loop_enum, user});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  count->get_code()->build_cfg();

  EXPECT_EQ(loop_enum->get_super_class(), type::java_lang_Enum())
      << show(count->get_code()->cfg());
}

namespace {

// Creates a Kotlin enum `type` with constants A and B and the synthetic
// `$VALUES` and `$ENTRIES` fields. Its `<clinit>` creates A in v3 and B in v4,
// stores the values array in v0 to `$VALUES`, and then runs `clinit_tail`.
DexClass* make_kotlin_enum(const std::string& type,
                           const std::string& clinit_tail) {
  DexType::make_type(optimize_enums::KT_ENUM_ENTRIES_TYPE);
  DexType::make_type("Lkotlin/enums/EnumEntriesList;");
  ClassCreator cc(DexType::make_type(type));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  for (const auto& name :
       {".$VALUES:[" + type,
        std::string(".$ENTRIES:Lkotlin/enums/EnumEntries;")}) {
    auto* synth = dynamic_cast<DexField*>(DexField::make_field(type + name));
    synth->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC);
    cc.add_field(synth);
  }
  for (const auto* name : {".A:", ".B:"}) {
    auto* constant =
        dynamic_cast<DexField*>(DexField::make_field(type + name + type));
    constant->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM);
    cc.add_field(constant);
  }
  const auto ctor = "\"" + type + ".<init>:(Ljava/lang/String;I)V\"";
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) )" + ctor + R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) ")" + type + R"(.<clinit>:()V"
     (
      (const-string "A")
      (move-result-pseudo-object v1)
      (const v2 0)
      (new-instance ")" + type + R"(")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2) )" + ctor + R"()
      (sput-object v3 ")" + type + ".A:" + type +
                                              R"(")
      (const-string "B")
      (move-result-pseudo-object v1)
      (const v2 1)
      (new-instance ")" + type + R"(")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v1 v2) )" + ctor + R"()
      (sput-object v4 ")" + type + ".B:" + type +
                                              R"(")
      (const v2 2)
      (new-array v2 "[)" + type + R"(")
      (move-result-pseudo-object v0)
      (const v2 0)
      (aput-object v3 v0 v2)
      (const v2 1)
      (aput-object v4 v0 v2)
      (sput-object v0 ")" + type + ".$VALUES:[" +
                                              type + R"(")
      )" + clinit_tail + R"(
     )
    )
  )"));
  auto* cls = cc.create();
  for (auto* m : cls->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  return cls;
}

void run_optimize_enums_with_entries(DexStoresVector& stores) {
  optimize_enums::OptimizeEnumsPass pass;
  Json::Value conf_obj;
  conf_obj["OptimizeEnumsPass"]["support_kt_19_enum_entries"] = true;
  ConfigFiles conf(conf_obj);
  conf.parse_global_config();
  PassManager manager({&pass}, conf, RedexOptions{});
  manager.run_passes(stores, conf);
}

} // namespace

// Only Kotlin's factory, whose return type ResolveRefsPass may specialize to
// `EnumEntriesList`, builds `$ENTRIES`. A method with the same name and
// arguments but another return type is other code, which the cleanup of
// `<clinit>` must not take to be free of side effects.
TEST_F(OptimizeEnumsTest, enumEntriesFactoryIsMatchedByItsReturnType) {
  EXPECT_TRUE(optimize_enums::is_kt_enum_entries_factory(DexMethod::make_method(
      "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/"
      "enums/EnumEntries;")));
  EXPECT_TRUE(optimize_enums::is_kt_enum_entries_factory(DexMethod::make_method(
      "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/"
      "enums/EnumEntriesList;")));
  EXPECT_FALSE(
      optimize_enums::is_kt_enum_entries_factory(DexMethod::make_method(
          "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)I")));
}

// A Kotlin enum whose `<clinit>` reads `$VALUES` back, casts it to `Enum[]`
// and passes it to the `enumEntries` factory, as kotlinc emits it, is boxed.
TEST_F(OptimizeEnumsTest, kotlincEnumEntriesFactoryIsRemoved) {
  DexStoresVector stores({create_enum_store()});
  auto* mode = make_kotlin_enum("LMode;", R"(
      (sget-object "LMode;.$VALUES:[LMode;")
      (move-result-pseudo-object v5)
      (check-cast v5 "[Ljava/lang/Enum;")
      (move-result-pseudo-object v5)
      (invoke-static (v5) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;")
      (move-result-object v5)
      (sput-object v5 "LMode;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (return-void)
  )");
  stores[0].add_classes({mode});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Object());
}

// The same enum keeps its `$ENTRIES` when the app's copy of the factory is
// marked `no_optimizations`: its code may not be what runs, so it may do more
// than allocate, and deleting the call could drop that.
TEST_F(OptimizeEnumsTest, untrustedEnumEntriesFactoryKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  ClassCreator kc(DexType::make_type("Lkotlin/enums/EnumEntriesKt;"));
  kc.set_super(type::java_lang_Object());
  kc.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* factory = assembler::method_from_string(R"(
    (method (public static) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;"
      (
        (load-param-object v0)
        (sget "Lkotlin/enums/EnumEntriesKt;.calls:I")
        (move-result-pseudo v1)
        (add-int/lit v1 v1 1)
        (sput v1 "Lkotlin/enums/EnumEntriesKt;.calls:I")
        (const v1 0)
        (return-object v1)
      )
    )
  )");
  factory->rstate.set_no_optimizations();
  kc.add_method(factory);
  auto* calls = dynamic_cast<DexField*>(
      DexField::make_field("Lkotlin/enums/EnumEntriesKt;.calls:I"));
  calls->make_concrete(ACC_PUBLIC | ACC_STATIC);
  kc.add_field(calls);
  factory->get_code()->build_cfg();
  auto* mode = make_kotlin_enum("LMode;", R"(
      (sget-object "LMode;.$VALUES:[LMode;")
      (move-result-pseudo-object v5)
      (check-cast v5 "[Ljava/lang/Enum;")
      (move-result-pseudo-object v5)
      (invoke-static (v5) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;")
      (move-result-object v5)
      (sput-object v5 "LMode;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (return-void)
  )");
  stores[0].add_classes({kc.create(), mode});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Enum());
}

// A Kotlin enum whose `<clinit>` calls the `enumEntries` factory through a
// reference with a specialized return type, as ResolveRefsPass leaves it, is
// boxed, and the factory call goes away with the `$ENTRIES` field it fed.
TEST_F(OptimizeEnumsTest, specializedEnumEntriesFactoryIsRemoved) {
  DexStoresVector stores({create_enum_store()});
  auto* mode = make_kotlin_enum("LMode;", R"(
      (invoke-static (v0) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntriesList;")
      (move-result-object v5)
      (sput-object v5 "LMode;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (return-void)
  )");
  stores[0].add_classes({mode});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Object());
  auto* clinit = mode->get_clinit();
  if (clinit != nullptr) {
    for (const auto& mie :
         cfg::InstructionIterable(clinit->get_code()->cfg())) {
      EXPECT_FALSE(mie.insn->has_method() &&
                   mie.insn->get_method()->str() == "enumEntries")
          << show(mie.insn);
    }
  }
}

// A Kotlin enum whose companion object reads `entries`, like
//
//   enum class Tab { HOME, SEARCH; companion object { val COUNT = entries.size
//   } }
//
// reads `$ENTRIES` in `<clinit>` once MethodInlinePass has inlined the
// `getEntries()` accessor. The read would outlive the deleted field, so the
// enum is not boxed.
TEST_F(OptimizeEnumsTest, enumEntriesReadInClinitKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  auto* tab = make_kotlin_enum("LTab;", R"(
      (invoke-static (v0) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;")
      (move-result-object v5)
      (sput-object v5 "LTab;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (sget-object "LTab;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (move-result-pseudo-object v6)
      (invoke-interface (v6) "Lkotlin/enums/EnumEntries;.size:()I")
      (move-result v7)
      (sput v7 "LTabCompanion;.COUNT:I")
      (return-void)
  )");
  stores[0].add_classes({tab});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(tab->get_super_class(), type::java_lang_Enum());
}

// A read of the values array field in `<clinit>` that does not build
// `$ENTRIES` would outlive the deleted field, so the enum is not boxed.
// Defensive: kotlinc and javac read the field there only for `$ENTRIES`.
TEST_F(OptimizeEnumsTest, valuesFieldReadInClinitKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  auto* tab = make_kotlin_enum("LTab;", R"(
      (sget-object "LTab;.$VALUES:[LTab;")
      (move-result-pseudo-object v5)
      (array-length v5)
      (move-result-pseudo v6)
      (sput v6 "LTabCompanion;.COUNT:I")
      (return-void)
  )");
  stores[0].add_classes({tab});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(tab->get_super_class(), type::java_lang_Enum());
}

// The values array passed as `Enum[]` to anything but the `enumEntries`
// factory or the `EnumEntriesList` constructor would receive boxed integers,
// so the enum is not boxed. Defensive: kotlinc passes it only to the factory.
TEST_F(OptimizeEnumsTest, valuesArrayPassedAsEnumArrayKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  auto* reg = make_kotlin_enum("LReg;", R"(
      (invoke-static (v0) "LRegistry;.register:([Ljava/lang/Enum;)V")
      (return-void)
  )");
  stores[0].add_classes({reg});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(reg->get_super_class(), type::java_lang_Enum());
}

// An `EnumEntries` that the factory builds from the values array and that
// `<clinit>` stores anywhere but in `$ENTRIES` stays alive and would wrap
// boxed integers, so the enum is not boxed. Defensive: kotlinc stores it only
// in `$ENTRIES`.
TEST_F(OptimizeEnumsTest, escapingEnumEntriesKeepsEnum) {
  DexStoresVector stores({create_enum_store()});
  auto* mode = make_kotlin_enum("LMode;", R"(
      (invoke-static (v0) "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/enums/EnumEntries;")
      (move-result-object v5)
      (sput-object v5 "LMode;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (sput-object v5 "LHolder;.ENTRIES:Lkotlin/enums/EnumEntries;")
      (return-void)
  )");
  stores[0].add_classes({mode});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Enum());
}

// A Kotlin enum whose `<clinit>` has the `enumEntries` factory inlined, as
// MethodInlinePass leaves it, is boxed, and the `EnumEntriesList` goes away
// with the `$ENTRIES` field it fed.
TEST_F(OptimizeEnumsTest, inlinedEnumEntriesFactoryIsRemoved) {
  DexStoresVector stores({create_enum_store()});
  auto* mode = make_kotlin_enum("LMode;", R"(
      (new-instance "Lkotlin/enums/EnumEntriesList;")
      (move-result-pseudo-object v5)
      (invoke-direct (v5 v0) "Lkotlin/enums/EnumEntriesList;.<init>:([Ljava/lang/Enum;)V")
      (sput-object v5 "LMode;.$ENTRIES:Lkotlin/enums/EnumEntries;")
      (return-void)
  )");
  stores[0].add_classes({mode});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Object());
  auto* clinit = mode->get_clinit();
  if (clinit != nullptr) {
    for (const auto& mie :
         cfg::InstructionIterable(clinit->get_code()->cfg())) {
      EXPECT_FALSE(mie.insn->has_type() && mie.insn->get_type()->str() ==
                                               "Lkotlin/enums/EnumEntriesList;")
          << show(mie.insn);
    }
  }
}

// When a candidate enum is unsafe for several reasons across different methods,
// every reason must be recorded -- not just whichever one a worker thread
// happened to observe first. `reject_unsafe_enums` runs the usage analysis in
// parallel; before it stopped gating analysis on rejection progress, once Bar
// was rejected by one method the other referencing method was skipped and its
// reason was dropped, making the reported reasons depend on thread scheduling.
TEST_F(OptimizeEnumsTest, rejectionReasonsAreComplete) {
  auto store = create_enum_store();

  // `LUser;` uses Bar unsafely in two separate methods, each triggering a
  // distinct rejection reason: const-class -> kUsageUsedAsClassObject and
  // instance-of -> kUsageUsedInInstanceOf.
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.use_as_class:()Ljava/lang/Class;"
      (
        (const-class "LBar;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"));
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.use_instance_of:(Ljava/lang/Object;)Z"
      (
        (load-param-object v0)
        (instance-of v0 "LBar;")
        (move-result-pseudo v1)
        (return v1)
      )
    )
  )"));
  store.add_classes({uc.create()});

  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  // reject_unsafe_enums (via reject_enums_for_relaxed_inits) walks the code of
  // every method, so all must have their CFG built.
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  ASSERT_NE(bar_type, nullptr);

  const std::set<optimize_enums::UnsafeType> kExpectedReasons = {
      optimize_enums::UnsafeType::kUsageUsedAsClassObject,
      optimize_enums::UnsafeType::kUsageUsedInInstanceOf};

  // The reasons are collected by a parallel walk, so repeat the analysis a few
  // times to exercise different thread schedulings: the fix must yield the same
  // complete reason set on every run, not a scheduling-dependent subset. The
  // count is kept small on purpose -- each iteration spins up the parallel
  // walkers, which is expensive under sanitizers/debug builds, and a handful of
  // iterations is enough to shake out scheduling differences.
  for (size_t iteration = 0; iteration < 10; ++iteration) {
    optimize_enums::Config config(100);
    config.candidate_enums.insert(bar_type);

    auto bar_reasons = rejection_reasons(scope, &config, bar_type);

    EXPECT_EQ(bar_reasons, kExpectedReasons) << "iteration " << iteration;
    // The enum is rejected -- outcome is unchanged by the determinism fix.
    EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type), 0u)
        << "iteration " << iteration;
  }
}

// `Outer` stays an enum, since code uses its class object, and its
// constructor ignores a parameter of type `Enum`:
//
//   enum Outer {
//     A(Bar.Y);
//     Outer(Enum<?> tag) {}
//   }
//
// `<clinit>` passes `Bar.Y` to that parameter, so `Bar` must stay an enum too:
// boxed, it would pass an `Integer` where an `Enum` is expected.
TEST_F(OptimizeEnumsTest, enumPassedToConstructorAsWiderTypeStaysEnum) {
  auto store = create_enum_store();
  ClassCreator cc(DexType::make_type("LOuter;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(DexField::make_field("LOuter;.$VALUES:[LOuter;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  cc.add_field(
      DexField::make_field("LOuter;.A:LOuter;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LOuter;.<init>:(Ljava/lang/String;ILjava/lang/Enum;)V"
      ((load-param-object v0)
       (load-param-object v1)
       (load-param v2)
       (load-param-object v3)
       (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
       (return-void)))
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LOuter;.<clinit>:()V"
      ((sget-object "LBar;.Y:LBar;")
       (move-result-pseudo-object v0)
       (const-string "A")
       (move-result-pseudo-object v1)
       (const v2 0)
       (new-instance "LOuter;")
       (move-result-pseudo-object v3)
       (invoke-direct (v3 v1 v2 v0) "LOuter;.<init>:(Ljava/lang/String;ILjava/lang/Enum;)V")
       (sput-object v3 "LOuter;.A:LOuter;")
       (const v4 1)
       (new-array v4 "[LOuter;")
       (move-result-pseudo-object v4)
       (aput-object v3 v4 v2)
       (sput-object v4 "LOuter;.$VALUES:[LOuter;")
       (return-void)))
  )"));
  auto* outer = cc.create();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.use_as_class:()Ljava/lang/Class;"
      ((const-class "LOuter;")
       (move-result-pseudo-object v0)
       (return-object v0)))
  )"));
  store.add_classes({outer, uc.create()});
  DexStoresVector stores({std::move(store)});
  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(outer->get_super_class(), type::java_lang_Enum());
  EXPECT_EQ(type_class(DexType::get_type("LBar;"))->get_super_class(),
            type::java_lang_Enum());
}

namespace {
/* Run the pass on Bar and a class `LRows;` whose method `show` takes a
`Bar[][] rows` and formats what `read` reads from it, like

  static String show(Bar[][] rows) { return String.valueOf(rows[0][0]); }

Returns `show` after the pass. */
DexMethod* run_pass_on_two_dimensional_array_user(const std::string& read) {
  auto store = create_enum_store();
  ClassCreator rc(DexType::make_type("LRows;"));
  rc.set_super(type::java_lang_Object());
  rc.set_access(ACC_PUBLIC);
  rc.add_method(assembler::method_from_string(R"(
    (method (public static) "LRows;.show:([[LBar;)Ljava/lang/String;"
      (
        (load-param-object v0)
        (const v1 0)
)" + read + R"(
        (invoke-static (v2) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
        (move-result-object v3)
        (return-object v3)
      )
    )
  )"));
  auto* rows = rc.create();
  store.add_classes({rows});
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);
  // Boxing Bar changes the proto of `show`, the only method of `LRows;`.
  auto* show = only(rows->get_dmethods());
  show->get_code()->build_cfg();
  return show;
}
} // namespace

// `String.valueOf(rows[0])` hands a whole row, a `Bar[]`, to code that sees it
// as an Object, so Bar must stay an enum.
TEST_F(OptimizeEnumsTest, rowOfTwoDimensionalArrayFormattedAsObjectKeepsEnum) {
  run_pass_on_two_dimensional_array_user(R"(
        (aget-object v0 v1)
        (move-result-pseudo-object v2)
  )");
  EXPECT_TRUE(is_enum(type_class(DexType::get_type("LBar;"))));
}

// `String.valueOf(rows[0][0])` formats one constant, so once Bar is boxed it
// must still print the constant's name, not its ordinal.
TEST_F(OptimizeEnumsTest, constantOfTwoDimensionalArrayIsFormattedByName) {
  auto* method = run_pass_on_two_dimensional_array_user(R"(
        (aget-object v0 v1)
        (move-result-pseudo-object v2)
        (aget-object v2 v1)
        (move-result-pseudo-object v2)
  )");
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  size_t name_helpers = 0;
  for (const auto& mie : cfg::InstructionIterable(method->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_STATIC &&
        mie.insn->get_method()->get_name()->str() ==
            "redex$OE$String_valueOf") {
      ++name_helpers;
    }
  }
  EXPECT_EQ(name_helpers, 1u) << show(method->get_code()->cfg());
}

namespace {
// Runs the pass on Bar and a class `LRows;` with `make`, which returns a
// `Bar[][]`, and returns `make` after the pass.
DexMethod* run_pass_on_rows_maker(const std::string& make) {
  auto store = create_enum_store();
  ClassCreator rc(DexType::make_type("LRows;"));
  rc.set_super(type::java_lang_Object());
  rc.set_access(ACC_PUBLIC);
  rc.add_method(assembler::method_from_string(make));
  auto* rows = rc.create();
  store.add_classes({rows});
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  return only(rows->get_dmethods());
}
} // namespace

// `Bar[][] rows = {new Bar[] {Bar.Y}};` stores a row, a `Bar[]`, into the
// `Bar[][]`, so every value stays a Bar, and Bar is boxed in both array types.
TEST_F(OptimizeEnumsTest, rowStoredIntoTwoDimensionalArrayLetsEnumBeBoxed) {
  auto* make = run_pass_on_rows_maker(R"(
    (method (public static) "LRows;.make:()[[LBar;"
      (
        (const v0 1)
        (new-array v0 "[[LBar;")
        (move-result-pseudo-object v1)
        (new-array v0 "[LBar;")
        (move-result-pseudo-object v2)
        (const v3 0)
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v4)
        (aput-object v4 v2 v3)
        (aput-object v2 v1 v3)
        (return-object v1)
      )
    )
  )");
  EXPECT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  EXPECT_EQ(show(make->get_proto()->get_rtype()), "[[Ljava/lang/Integer;");
  make->get_code()->build_cfg();
  for (const auto& mie : cfg::InstructionIterable(make->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_NEW_ARRAY) {
      EXPECT_EQ(type::make_array_element_type(mie.insn->get_type()),
                type::java_lang_Integer());
    }
  }
}

// `Bar[] row = {Bar.Y};` with the array built by filled-new-array: Bar is
// boxed, so the array becomes an `Integer[]`.
TEST_F(OptimizeEnumsTest, arrayBuiltByFilledNewArrayIsBoxed) {
  auto* make = run_pass_on_rows_maker(R"(
    (method (public static) "LRows;.make:()[LBar;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (filled-new-array (v0) "[LBar;")
        (move-result-object v1)
        (return-object v1)
      )
    )
  )");
  EXPECT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  make->get_code()->build_cfg();
  for (const auto& mie : cfg::InstructionIterable(make->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_FILLED_NEW_ARRAY) {
      EXPECT_EQ(show(mie.insn->get_type()), "[Ljava/lang/Integer;");
    }
  }
}

/* Run the usage analysis with `LUser;.x_of_y`, which reads `Bar.Y.x`, and
return the reasons that keep Bar, or an empty set if Bar can be boxed. */
std::set<optimize_enums::UnsafeType> reasons_with_user_method(
    bool no_optimizations) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LUser;.x_of_y:()I"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (iget v0 "LBar;.x:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");
  if (no_optimizations) {
    user->rstate.set_no_optimizations();
  }
  uc.add_method(user);
  store.add_classes({uc.create()});

  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  std::mutex reasons_mutex;
  std::set<optimize_enums::UnsafeType> bar_reasons;
  optimize_enums::reject_unsafe_enums(
      scope, &config, [&](const DexType* type, optimize_enums::UnsafeType u) {
        std::lock_guard<std::mutex> lock(reasons_mutex);
        if (type == bar_type) {
          bar_reasons.insert(u);
        }
      });
  EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type) == 0,
            !bar_reasons.empty());
  return bar_reasons;
}

// Redex must not change a method marked `no_optimizations`, and boxing an enum
// would rewrite every method that refers to it, so such a method keeps the
// enum.
TEST_F(OptimizeEnumsTest, noOptimizationsMethodKeepsEnum) {
  EXPECT_EQ(reasons_with_user_method(/* no_optimizations */ true),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageNoOptimizationsMethod});
}

TEST_F(OptimizeEnumsTest, optimizableMethodLetsEnumBeBoxed) {
  EXPECT_TRUE(reasons_with_user_method(/* no_optimizations */ false).empty());
}

/* Run the pass with `LUser;.use`, which reads `(Bar) Prebuilt.identity(Bar.Y)`
and `identity` returns its `Object` parameter. Return whether Bar is boxed. */
bool bar_boxed_through_identity(bool no_optimizations) {
  auto store = create_enum_store();
  ClassCreator pc(DexType::make_type("LPrebuilt;"));
  pc.set_super(type::java_lang_Object());
  pc.set_access(ACC_PUBLIC);
  auto* identity = assembler::method_from_string(R"(
    (method (public static) "LPrebuilt;.identity:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (return-object v0)
      )
    )
  )");
  if (no_optimizations) {
    identity->rstate.set_no_optimizations();
  }
  pc.add_method(identity);
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.use:()I"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (invoke-static (v0) "LPrebuilt;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
        (move-result-object v0)
        (check-cast v0 "LBar;")
        (move-result-pseudo-object v0)
        (iget v0 "LBar;.x:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )"));
  store.add_classes({pc.create(), uc.create()});
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  return type_class(DexType::get_type("LBar;"))->get_super_class() ==
         type::java_lang_Object();
}

// The body of a method marked `no_optimizations` may not be the code that
// runs, so a call to it may return its argument or anything else.
TEST_F(OptimizeEnumsTest, noOptimizationsCalleeKeepsEnum) {
  EXPECT_FALSE(bar_boxed_through_identity(/* no_optimizations */ true));
}

TEST_F(OptimizeEnumsTest, optimizableCalleeLetsEnumBeBoxed) {
  EXPECT_TRUE(bar_boxed_through_identity(/* no_optimizations */ false));
}

constexpr const char* kCheckNotNullParameter =
    "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/"
    "Object;Ljava/lang/String;)V";

/* Run OptimizeEnums with `LUser;.use(Bar bar)`, which passes `bar` to the
in-APK method `check_method` with the given body, like Kotlin's parameter check
`Intrinsics.checkNotNullParameter(bar, "bar")`. With `wrap_null_checks`,
RemoveNullcheckStringArg runs first, as in app builds, and routes the call
through the wrapper it adds to `Intrinsics`. Return whether Bar is boxed. */
bool bar_boxed_through_in_apk_null_check(
    const std::string& body,
    bool no_optimizations,
    const std::string& check_method = kCheckNotNullParameter,
    bool wrap_null_checks = false) {
  auto store = create_enum_store();
  ClassCreator cc(DexMethod::make_method(check_method)->get_class());
  cc.set_super(type::java_lang_Object());
  cc.set_access(ACC_PUBLIC);
  auto* check = assembler::method_from_string(
      "(method (public static) \"" + check_method + "\" (" + body + "))");
  if (no_optimizations) {
    check->rstate.set_no_optimizations();
  }
  cc.add_method(check);
  ClassCreator sc(DexType::make_type("LSink;"));
  sc.set_super(type::java_lang_Object());
  sc.set_access(ACC_PUBLIC);
  sc.add_field(DexField::make_field("LSink;.sink:Ljava/lang/Object;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  std::string use = R"(
    (method (public static) "LUser;.use:(LBar;)I"
      (
        (load-param-object v0)
        (const-string "bar")
        (move-result-pseudo-object v1)
        (invoke-static (v0 v1) "CHECK")
        (iget v0 "LBar;.x:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )";
  boost::replace_all(use, "CHECK", check_method);
  uc.add_method(assembler::method_from_string(use));
  store.add_classes({cc.create(), sc.create(), uc.create()});
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  // The wrapper's message building calls these.
  DexMethod::make_method("Ljava/lang/Integer;.toString:(I)Ljava/lang/String;");
  DexMethod::make_method("Ljava/lang/StringBuilder;.<init>:()V");
  RemoveNullcheckStringArg wrap_pass;
  optimize_enums::OptimizeEnumsPass pass;
  std::vector<Pass*> passes;
  if (wrap_null_checks) {
    passes.push_back(&wrap_pass);
  }
  passes.push_back(&pass);
  PassManager manager(passes);
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  if (wrap_null_checks) {
    EXPECT_NE(kotlin_nullcheck_wrapper::
                  kotlin_jvm_internal_Intrinsics_WrCheckParameter_V1_4(),
              nullptr);
  }
  return type_class(DexType::get_type("LBar;"))->get_super_class() ==
         type::java_lang_Object();
}

constexpr const char* kNullCheckBody = R"(
  (load-param-object v0)
  (load-param-object v1)
  (if-nez v0 :ok)
  (invoke-static (v1) "Lkotlin/jvm/internal/Intrinsics;.throwParameterIsNullNPE:(Ljava/lang/String;)V")
  (:ok)
  (return-void)
)";

// The code of an in-APK Kotlin null check marked `no_optimizations` may not be
// what runs, so it gets no summary at all.
TEST_F(OptimizeEnumsTest, noOptimizationsInApkNullCheckKeepsEnum) {
  EXPECT_FALSE(bar_boxed_through_in_apk_null_check(
      kNullCheckBody, /* no_optimizations */ true));
}

TEST_F(OptimizeEnumsTest, inApkNullCheckLetsEnumBeBoxed) {
  EXPECT_TRUE(bar_boxed_through_in_apk_null_check(
      kNullCheckBody, /* no_optimizations */ false));
}

// Apps ship the Kotlin standard library, and RemoveNullcheckStringArg routes
// each parameter check through a wrapper in `Intrinsics` that passes the
// argument on to the original check. Kotlin specifies what both do, so their
// code in the APK does not decide whether the argument escapes.
TEST_F(OptimizeEnumsTest, inApkNullCheckBehindRedexWrapperLetsEnumBeBoxed) {
  EXPECT_TRUE(bar_boxed_through_in_apk_null_check(
      kNullCheckBody, /* no_optimizations */ false, kCheckNotNullParameter,
      /* wrap_null_checks */ true));
}

// A wrapper does what the null check it calls does, so it is no more trusted
// than one marked `no_optimizations`.
TEST_F(OptimizeEnumsTest,
       noOptimizationsInApkNullCheckBehindRedexWrapperKeepsEnum) {
  EXPECT_FALSE(bar_boxed_through_in_apk_null_check(
      kNullCheckBody, /* no_optimizations */ true, kCheckNotNullParameter,
      /* wrap_null_checks */ true));
}

// An unknown helper of the same shape is summarized from its code alone, so
// one that lets its argument escape keeps the enum.
TEST_F(OptimizeEnumsTest, inApkHelperLettingArgumentEscapeKeepsEnum) {
  EXPECT_FALSE(bar_boxed_through_in_apk_null_check(
      R"(
        (load-param-object v0)
        (load-param-object v1)
        (sput-object v0 "LSink;.sink:Ljava/lang/Object;")
        (return-void)
      )",
      /* no_optimizations */ false,
      "LUtil;.checkNotNull:(Ljava/lang/Object;Ljava/lang/String;)V"));
}

// The switch-map cleanup, which runs for enums that are not boxed too, leaves
// a method marked `no_optimizations` as it is.
TEST_F(OptimizeEnumsTest, noOptimizationsSwitchMapUserIsUnchanged) {
  DexStoresVector stores({create_enum_store()});
  auto* enum_cls = type_class(type::java_lang_Enum());
  auto* ordinal = dynamic_cast<DexMethod*>(
      DexMethod::get_method("Ljava/lang/Enum;.ordinal:()I"));
  enum_cls->remove_method(ordinal);
  ordinal->set_access(ACC_PUBLIC | ACC_FINAL);
  ordinal->set_virtual(true);
  enum_cls->add_method(ordinal);

  ClassCreator gc(DexType::make_type("LFoo$1;"));
  gc.set_super(type::java_lang_Object());
  gc.set_access(ACC_FINAL | ACC_SYNTHETIC);
  gc.add_field(DexField::make_field("LFoo$1;.$SwitchMap$Bar:[I")
                   ->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC));
  gc.add_method(assembler::method_from_string(R"(
    (method (static constructor) "LFoo$1;.<clinit>:()V"
     (
      (const v0 2)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (sput-object v1 "LFoo$1;.$SwitchMap$Bar:[I")
      (sget-object "LFoo$1;.$SwitchMap$Bar:[I")
      (move-result-pseudo-object v1)
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v2)
      (invoke-virtual (v2) "Ljava/lang/Enum;.ordinal:()I")
      (move-result v3)
      (const v4 1)
      (aput v4 v1 v3)
      (return-void)
     )
    )
  )"));
  ClassCreator pc(DexType::make_type("LPrebuilt;"));
  pc.set_super(type::java_lang_Object());
  pc.set_access(ACC_PUBLIC);
  auto* is_y = assembler::method_from_string(R"(
    (method (public static) "LPrebuilt;.isY:(LBar;)I"
     (
      (load-param-object v0)
      (sget-object "LFoo$1;.$SwitchMap$Bar:[I")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0) "Ljava/lang/Enum;.ordinal:()I")
      (move-result v2)
      (aget v1 v2)
      (move-result-pseudo v3)
      (switch v3 (:y))
      (const v4 0)
      (return v4)
      (:y 1)
      (const v4 1)
      (return v4)
     )
    )
  )");
  is_y->rstate.set_no_optimizations();
  pc.add_method(is_y);
  stores[0].add_classes({gc.create(), pc.create()});
  const auto before = assembler::to_string(is_y->get_code());
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);

  is_y->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_string(is_y->get_code()), before);
}

/* Run the usage analysis with `method` added to Bar and return the reasons
that keep Bar. */
std::set<optimize_enums::UnsafeType> reasons_with_bar_method(
    const char* method) {
  auto store = create_enum_store();
  auto* bar = type_class(DexType::get_type("LBar;"));
  bar->add_method(assembler::method_from_string(method));
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) {
    if (!code.cfg_built()) {
      code.build_cfg();
    }
  });

  auto* bar_type = bar->get_type();
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  std::mutex reasons_mutex;
  std::set<optimize_enums::UnsafeType> bar_reasons;
  optimize_enums::reject_unsafe_enums(
      scope, &config, [&](const DexType* type, optimize_enums::UnsafeType u) {
        std::lock_guard<std::mutex> lock(reasons_mutex);
        if (type == bar_type) {
          bar_reasons.insert(u);
        }
      });
  EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type) == 0,
            !bar_reasons.empty());
  return bar_reasons;
}

// `Bar.first()` reads `$VALUES` itself instead of calling `values()`, as
// once an accessor has been inlined. Boxing deletes `$VALUES`, so the enum is
// kept.
TEST_F(OptimizeEnumsTest, valuesArrayReadOutsideValuesKeepsEnum) {
  EXPECT_EQ(reasons_with_bar_method(R"(
    (method (public static) "LBar;.first:()LBar;"
      (
        (sget-object "LBar;.$VALUES:[LBar;")
        (move-result-pseudo-object v0)
        (const v1 0)
        (aget-object v0 v1)
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageUsedValuesField});
}

// `User.first()` reads `Bar.$VALUES`, as `Bar.values()` inlined into another
// class leaves it. Boxing deletes `$VALUES`, so the enum is kept.
TEST_F(OptimizeEnumsTest, valuesArrayReadInAnotherClassKeepsEnum) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.first:()LBar;"
      (
        (sget-object "LBar;.$VALUES:[LBar;")
        (move-result-pseudo-object v0)
        (const v1 0)
        (aget-object v0 v1)
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  EXPECT_EQ(rejection_reasons(scope, &config, bar_type),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageUsedValuesField});
}

// A store to `$VALUES` outside <clinit>, which only hand-written bytecode
// contains, would be left behind when boxing deletes the field.
TEST_F(OptimizeEnumsTest, valuesArrayWrittenOutsideClinitKeepsEnum) {
  EXPECT_EQ(reasons_with_bar_method(R"(
    (method (public static) "LBar;.reset:()V"
      (
        (const v0 0)
        (new-array v0 "[LBar;")
        (move-result-pseudo-object v0)
        (sput-object v0 "LBar;.$VALUES:[LBar;")
        (return-void)
      )
    )
  )"),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageUsedValuesField});
}

/* Run the pass on Bar after removing its values array, as a first
OptimizeEnums run that deletes an unused `values()` followed by
RemoveUnusedFieldsPass leaves it, and giving it javac's `$assertionsDisabled`
field, written in <clinit> and read by `Bar.assertionsOn()`. `clinit_tail` runs
at the end of <clinit>. Return whether Bar is boxed. */
bool bar_with_only_assertions_field_boxed(const std::string& clinit_tail) {
  auto store = create_enum_store();
  auto* bar = type_class(DexType::get_type("LBar;"));
  bar->remove_field(DexField::get_field("LBar;.$VALUES:[LBar;")->as_def());
  bar->remove_method(DexMethod::get_method("LBar;.$values:()[LBar;")->as_def());
  bar->add_field(DexField::make_field("LBar;.$assertionsDisabled:Z")
                     ->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC));
  auto* clinit = bar->get_clinit();
  clinit->get_code()->clear_cfg();
  clinit->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (sput-boolean v0 "LBar;.$assertionsDisabled:Z")
      (r-const v0 2132351567)
      (const-string "Y")
      (move-result-pseudo-object v1)
      (const v2 0)
      (new-instance "LBar;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2 v0) "LBar;.<init>:(Ljava/lang/String;II)V")
      (sput-object v3 "LBar;.Y:LBar;")
      (r-const v0 2132351568)
      (const-string "Z")
      (move-result-pseudo-object v1)
      (const v2 1)
      (new-instance "LBar;")
      (move-result-pseudo-object v3)
      (invoke-direct (v3 v1 v2 v0) "LBar;.<init>:(Ljava/lang/String;II)V")
      (sput-object v3 "LBar;.Z:LBar;")
  )" + clinit_tail + ")"));
  bar->add_method(assembler::method_from_string(R"(
    (method (public static) "LBar;.assertionsOn:()Z"
      (
        (sget-boolean "LBar;.$assertionsDisabled:Z")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )"));
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores), [](DexMethod*, IRCode& code) {
    if (!code.cfg_built()) {
      code.build_cfg();
    }
  });

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  return bar->get_super_class() == type::java_lang_Object();
}

// Boxing deletes the enum's static synthetic field as its values array. When
// the only one is javac's `$assertionsDisabled`, deleting it would leave
// `Bar.assertionsOn()` reading a field that no longer exists.
TEST_F(OptimizeEnumsTest, onlySyntheticFieldNotValuesArrayKeepsEnum) {
  EXPECT_FALSE(bar_with_only_assertions_field_boxed("(return-void)"));
}

// The same, with an `assert` in <clinit> that reads `$assertionsDisabled`.
TEST_F(OptimizeEnumsTest, assertionsFieldReadInClinitKeepsEnum) {
  EXPECT_FALSE(bar_with_only_assertions_field_boxed(R"(
    (sget-boolean "LBar;.$assertionsDisabled:Z")
    (move-result-pseudo v0)
    (if-nez v0 :done)
    (new-instance "Ljava/lang/AssertionError;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "Ljava/lang/AssertionError;.<init>:()V")
    (throw v1)
    (:done)
    (return-void)
  )"));
}

// Boxing deletes the constant fields. A store to one outside <clinit>, which
// only hand-written bytecode contains, would be left behind.
TEST_F(OptimizeEnumsTest, constantWrittenOutsideClinitKeepsEnum) {
  EXPECT_EQ(reasons_with_bar_method(R"(
    (method (public static) "LBar;.swap:()V"
      (
        (sget-object "LBar;.Z:LBar;")
        (move-result-pseudo-object v0)
        (sput-object v0 "LBar;.Y:LBar;")
        (return-void)
      )
    )
  )"),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageConstantSetOutsideClinit});
}

/* Build the CFGs of `cls` and of the stub `java.lang.Enum`, which the <clinit>
analysis may follow calls into, as it can in a pass. */
void build_cfgs_for_clinit_analysis(DexClass* cls) {
  for (auto* c : {cls, type_class(type::java_lang_Enum())}) {
    for (auto* m : c->get_all_methods()) {
      if (m->get_code() != nullptr && !m->get_code()->cfg_built()) {
        m->get_code()->build_cfg();
      }
    }
  }
}

// Run the rejection analysis on Bar and a `LUser;.pick` that returns its
// parameter or the value that `other_return` computes into v2:
//
//   static Object pick(Object o, boolean b) { return b ? o : <other>; }
//   pick(Bar.Y, true).toString();  // "Y", but "0" once Y is boxed
//
// Return whether Bar stays a candidate.
bool is_candidate_after_pick(const std::string& other_return) {
  auto store = create_enum_store();

  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_field(DexField::make_field("LUser;.CACHE:Ljava/lang/Object;")
                   ->make_concrete(ACC_STATIC | ACC_FINAL));
  std::string pick = R"(
    (method (public static) "LUser;.pick:(Ljava/lang/Object;Z)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param v1)
        (if-eqz v1 :other)
        (return-object v0)
        (:other)
        OTHER_RETURN
        (return-object v2)
      )
    )
  )";
  boost::replace_all(pick, "OTHER_RETURN", other_return);
  uc.add_method(assembler::method_from_string(pick));
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.print:()Ljava/lang/String;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (const v1 1)
        (invoke-static (v0 v1) "LUser;.pick:(Ljava/lang/Object;Z)Ljava/lang/Object;")
        (move-result-object v0)
        (invoke-virtual (v0) "Ljava/lang/Object;.toString:()Ljava/lang/String;")
        (move-result-object v0)
        (return-object v0)
      )
    )
  )"));
  store.add_classes({uc.create()});

  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  always_assert(bar_type != nullptr);
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  auto override_graph = method_override_graph::build_graph(scope);
  optimize_enums::calculate_param_summaries(scope, *override_graph,
                                            &config.param_summary_map);
  optimize_enums::reject_unsafe_enums(
      scope, &config, [](const DexType*, optimize_enums::UnsafeType) {});
  return config.candidate_enums.count_unsafe(bar_type) != 0u;
}

// `pick` may return Y or an object that has already escaped, so the caller's
// `toString()` may run on Y.
TEST_F(OptimizeEnumsTest, rejectsEnumReturnedWithEscapedObject) {
  EXPECT_FALSE(is_candidate_after_pick(R"(
        (sget-object "LUser;.CACHE:Ljava/lang/Object;")
        (move-result-pseudo-object v2)
  )"));
}

// `pick` returns Y or null, so the caller's `toString()` is checked on Y.
TEST_F(OptimizeEnumsTest, rejectsEnumReturnedWithNull) {
  EXPECT_FALSE(is_candidate_after_pick("(const v2 0)"));
}

// A call through Bar, or through an array of Bar, that resolves to a method
// Bar does not define has no form on the boxed representation, so Bar must
// stay an enum, like these calls in Java code:
//
//   Class<?> c = Bar.Y.getDeclaringClass();  // Enum.getDeclaringClass()
//   Bar.valueOf(Bar.class, "Y");             // Enum.valueOf(Class, String)
//   Object copy = bars.clone();              // [LBar;.clone(), no cast back
struct InheritedCallCase {
  const char* name;
  const char* method;
};

class OptimizeEnumsInheritedCallTest
    : public OptimizeEnumsTest,
      public WithParamInterface<InheritedCallCase> {};

TEST_P(OptimizeEnumsInheritedCallTest, keepsEnum) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(GetParam().method));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  auto bar_reasons = rejection_reasons(scope, &config, bar_type);

  EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type), 0u);
  EXPECT_TRUE(bar_reasons.contains(
      optimize_enums::UnsafeType::kUsageUnsafeInvocationOnCandidateEnum));
}

INSTANTIATE_TEST_SUITE_P(InheritedCalls,
                         OptimizeEnumsInheritedCallTest,
                         Values(InheritedCallCase{"virtual", R"(
          (method (public static) "LUser;.f:()Ljava/lang/Class;"
            (
              (sget-object "LBar;.Y:LBar;")
              (move-result-pseudo-object v0)
              (invoke-virtual (v0) "LBar;.getDeclaringClass:()Ljava/lang/Class;")
              (move-result-object v0)
              (return-object v0)
            )
          )
        )"},
                                InheritedCallCase{"static", R"(
          (method (public static) "LUser;.f:()Ljava/lang/Enum;"
            (
              (const v0 0)
              (const-string "Y")
              (move-result-pseudo-object v1)
              (invoke-static (v0 v1) "LBar;.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;")
              (move-result-object v0)
              (return-object v0)
            )
          )
        )"},
                                InheritedCallCase{"arrayClone", R"(
          (method (public static) "LUser;.f:([LBar;)V"
            (
              (load-param-object v0)
              (invoke-virtual (v0) "[LBar;.clone:()Ljava/lang/Object;")
              (move-result-object v1)
              (return-void)
            )
          )
        )"}),
                         [](const auto& info) { return info.param.name; });

// A field reference through Bar that names a field Bar does not define has no
// form on the boxed representation either. An enum that implements no
// interface inherits no field javac could name, so this check is defensive.
TEST_F(OptimizeEnumsTest, inheritedFieldRefKeepsEnum) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.f:()Ljava/lang/Object;"
      (
        (sget-object "LBar;.inherited:Ljava/lang/Object;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  auto bar_reasons = rejection_reasons(scope, &config, bar_type);

  EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type), 0u);
  EXPECT_TRUE(bar_reasons.contains(
      optimize_enums::UnsafeType::kUsageInheritedFieldRef));
}

/* Create an enum with constants A and B whose <clinit> runs `clinit_prefix`
and then passes the given ordinals to the constructor, like this hand-written
Java-like code:

enum E {
  A("A", 0), B("B", ordinal_b);  // javac would pass ordinal 1 for B
}
*/
DexClass* create_two_constant_enum(const std::string& name,
                                   int ordinal_b,
                                   const std::string& clinit_prefix = "") {
  auto with_names = [&](std::string s_expr) {
    boost::replace_all(s_expr, "LE;", name);
    boost::replace_all(s_expr, "ORDINAL_B", std::to_string(ordinal_b));
    boost::replace_all(s_expr, "CLINIT_PREFIX", clinit_prefix);
    return s_expr;
  };
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  for (const char* constant : {"A", "B"}) {
    cc.add_field(DexField::make_field(
                     with_names("LE;." + std::string(constant) + ":LE;"))
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM));
  }
  cc.add_method(assembler::method_from_string(with_names(R"(
    (method (private constructor) "LE;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )")));
  cc.add_method(assembler::method_from_string(with_names(R"(
    (method (public static) "LE;.<clinit>:()V"
      (
        CLINIT_PREFIX
        (const-string "A")
        (move-result-pseudo-object v0)
        (const v1 0)
        (new-instance "LE;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LE;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LE;.A:LE;")
        (const-string "B")
        (move-result-pseudo-object v0)
        (const v1 ORDINAL_B)
        (new-instance "LE;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LE;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LE;.B:LE;")
        (return-void)
      )
    )
  )")));
  auto* cls = cc.create();
  build_cfgs_for_clinit_analysis(cls);
  return cls;
}

// Ordinals of an enum with N constants must be exactly 0..N-1. An ordinal of
// N is out of range and must reject the enum.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsOrdinalEqualToConstantCount) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LOrdinalTooLarge;", 2);
  auto attributes = analyze_clinit(cls, false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// A negative ordinal is out of range too and must reject the enum rather than
// abort Redex.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsNegativeOrdinal) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LNegativeOrdinal;", -1);
  auto attributes = analyze_clinit(cls, false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// The same clinit with in-range ordinals is accepted, so the rejections above
// come from the ordinals alone.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsConsecutiveOrdinals) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LConsecutiveOrdinals;", 1);
  auto attributes = analyze_clinit(cls, false);
  EXPECT_EQ(attributes.m_constants_map.size(), 2);
}

// enum E {
//   A, B;
//   static final long START;
//   static { START = (long) NOW.invokeExact(); }  // NOW is a MethodHandle
// }
// The analysis cannot model a method handle call, which may run any code, so
// the enum is kept.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsMethodHandleCall) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LHandleCall;", 1, R"(
    (const v3 0)
    (invoke-polymorphic (v3) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
  )");
  auto attributes = analyze_clinit(cls, false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// Likewise a call site, which `invoke-custom` calls through a bootstrap
// method. S-expressions cannot spell `invoke-custom`, so it replaces a
// placeholder call.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsCallSite) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LCallSite;", 1, R"(
    (invoke-static () "LCallSite;.placeholder:()V")
  )");
  for (auto& mie :
       cfg::InstructionIterable(cls->get_clinit()->get_code()->cfg())) {
    if (mie.insn->has_method() &&
        mie.insn->get_method()->str() == "placeholder") {
      mie.insn->set_opcode(OPCODE_INVOKE_CUSTOM)
          ->set_callsite(redex::make_callsite("run", "()V"));
    }
  }
  auto attributes = analyze_clinit(cls, false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// A signature-polymorphic call in the constructor is just as unsupported as
// one in <clinit>. An ordinary Java enum constructor can make this call.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsConstructorMethodHandleCall) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LHandleCtor;", 1);
  auto* ctor = cls->get_ctors().front();
  ctor->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
      (sget-object "LHandles;.NOW:Ljava/lang/invoke/MethodHandle;")
      (move-result-pseudo-object v3)
      (invoke-polymorphic (v3) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (return-void)
    )
  )"));
  ctor->get_code()->build_cfg();
  const auto before = show(ctor->get_code()->cfg());
  for (size_t run = 0; run < 2; ++run) {
    const auto attributes = analyze_clinit(cls, false);
    EXPECT_TRUE(attributes.m_constants_map.empty());
    EXPECT_EQ(show(ctor->get_code()->cfg()), before);
  }
}

// enum E {
//   A, B;
//   static final boolean B_WAS_NULL = E.B == null;  // placed before A and B
// }
// The read of B before <clinit> assigns it sees null. Once boxed, it would see
// B's boxed ordinal, so the enum is kept.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsReadBeforeAssignment) {
  auto store = create_enum_store();
  ClassCreator cc(DexType::make_type("LForward;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  for (const char* constant :
       {"LForward;.A:LForward;", "LForward;.B:LForward;"}) {
    cc.add_field(DexField::make_field(constant)->make_concrete(
        ACC_PUBLIC | ACC_STATIC | ACC_ENUM));
  }
  cc.add_field(DexField::make_field("LForward;.B_WAS_NULL:Z")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LForward;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LForward;.<clinit>:()V"
      (
        (sget-object "LForward;.B:LForward;")
        (move-result-pseudo-object v3)
        (const v4 0)
        (if-nez v3 :assigned)
        (const v4 1)
        (:assigned)
        (sput-boolean v4 "LForward;.B_WAS_NULL:Z")
        (const-string "A")
        (move-result-pseudo-object v0)
        (const v1 0)
        (new-instance "LForward;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LForward;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LForward;.A:LForward;")
        (const-string "B")
        (move-result-pseudo-object v0)
        (const v1 1)
        (new-instance "LForward;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LForward;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LForward;.B:LForward;")
        (return-void)
      )
    )
  )"));
  auto* cls = cc.create();
  build_cfgs_for_clinit_analysis(cls);
  auto attributes = analyze_clinit(cls, false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

/* Direct tests of the read summaries, over the enum `LBar;` of
`create_enum_store()` and the methods of a class `LReads;` the test adds. */
class OptimizeEnumsReadSummaryTest : public OptimizeEnumsTest {
 protected:
  using Summary = optimize_enums::ConstantReadSummaries::Summary;

  // Adds `LReads;` with `methods`, and its subclass `LSubReads;` with
  // `sub_methods`, and returns the summaries of the methods named `names`,
  // which `num_threads` threads all ask for at once from the same summaries;
  // every thread must get the same ones.
  std::vector<Summary> summaries_of(
      const std::vector<std::string>& methods,
      const std::vector<std::string>& names,
      size_t num_threads = 1,
      const std::vector<std::string>& sub_methods = {}) {
    auto store = create_enum_store();
    ClassCreator cc(DexType::make_type("LReads;"));
    cc.set_super(type::java_lang_Object());
    cc.set_access(ACC_PUBLIC);
    for (const auto& method : methods) {
      cc.add_method(assembler::method_from_string(method));
    }
    ClassCreator sc(DexType::make_type("LSubReads;"));
    sc.set_super(DexType::get_type("LReads;"));
    sc.set_access(ACC_PUBLIC);
    for (const auto& method : sub_methods) {
      sc.add_method(assembler::method_from_string(method));
    }
    store.add_classes({cc.create(), sc.create()});
    DexStoresVector stores({std::move(store)});
    auto scope = build_class_scope(stores);
    walk::code(scope, [](DexMethod*, IRCode& code) {
      if (!code.cfg_built()) {
        code.build_cfg();
      }
    });
    auto override_graph = method_override_graph::build_graph(scope);
    optimize_enums::ConstantReadSummaries reads(*override_graph);
    std::vector<std::vector<Summary>> per_thread(num_threads);
    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    for (size_t t = 0; t < num_threads; ++t) {
      threads.emplace_back([&, t] {
        for (const auto& name : names) {
          per_thread[t].push_back(
              reads.of(DexMethod::get_method(name)->as_def()));
        }
      });
    }
    for (auto& thread : threads) {
      thread.join();
    }
    for (size_t t = 1; t < num_threads; ++t) {
      for (size_t i = 0; i < names.size(); ++i) {
        const auto& a = per_thread[0][i];
        const auto& b = per_thread[t][i];
        EXPECT_EQ(a.has_value(), b.has_value()) << names[i];
        if (a && b) {
          EXPECT_EQ(a->size(), b->size()) << names[i];
          EXPECT_TRUE(unordered_all_of(*b, [&](const DexField* f) {
            return a->count(f) != 0u;
          })) << names[i];
        }
      }
    }
    return per_thread[0];
  }

  // `ping()` calls `pong()`, which reads Bar.Y and calls `ping()`.
  static std::vector<std::string> ping_pong_methods() {
    return {R"(
      (method (public static) "LReads;.ping:()V"
        (
          (invoke-static () "LReads;.pong:()V")
          (return-void)
        )
      )
    )",
            R"(
      (method (public static) "LReads;.pong:()V"
        (
          (sget-object "LBar;.Y:LBar;")
          (move-result-pseudo-object v0)
          (invoke-static () "LReads;.ping:()V")
          (return-void)
        )
      )
    )"};
  }

  Summary summary_of(const std::vector<std::string>& methods,
                     const std::string& name) {
    return summaries_of(methods, {name}).front();
  }

  // The summary of `LCaller;.call`, which calls `read()` on an `LReader;`, an
  // interface with the abstract method `read()` that only `LReads;`
  // implements, with `impl`. When `impl` is a method of `LSubReader;`
  // instead, it is a default method of that sub-interface of `LReader;`, which
  // `LReads;` implements without a `read()` of its own.
  Summary interface_call_summary(const std::string& impl) {
    auto store = create_enum_store();
    ClassCreator ic(DexType::make_type("LReader;"));
    ic.set_super(type::java_lang_Object());
    ic.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    auto* read = DexMethod::make_method("LReader;.read:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                                     /* is_virtual */ true);
    ic.add_method(read);
    auto* impl_method = assembler::method_from_string(impl);
    ClassCreator rc(DexType::make_type("LReads;"));
    rc.set_super(type::java_lang_Object());
    rc.set_access(ACC_PUBLIC);
    if (impl_method->get_class() == DexType::get_type("LReads;")) {
      rc.add_interface(DexType::get_type("LReader;"));
      rc.add_method(impl_method);
    } else {
      ClassCreator sc(DexType::make_type("LSubReader;"));
      sc.set_super(type::java_lang_Object());
      sc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
      sc.add_interface(DexType::get_type("LReader;"));
      sc.add_method(impl_method);
      store.add_classes({sc.create()});
      rc.add_interface(DexType::get_type("LSubReader;"));
    }
    ClassCreator cc(DexType::make_type("LCaller;"));
    cc.set_super(type::java_lang_Object());
    cc.set_access(ACC_PUBLIC);
    cc.add_method(assembler::method_from_string(R"(
      (method (public static) "LCaller;.call:(LReader;)V"
        (
          (load-param-object v0)
          (invoke-interface (v0) "LReader;.read:()V")
          (return-void)
        )
      )
    )"));
    store.add_classes({ic.create(), rc.create(), cc.create()});
    DexStoresVector stores({std::move(store)});
    auto scope = build_class_scope(stores);
    walk::code(scope, [](DexMethod*, IRCode& code) {
      if (!code.cfg_built()) {
        code.build_cfg();
      }
    });
    auto override_graph = method_override_graph::build_graph(scope);
    optimize_enums::ConstantReadSummaries reads(*override_graph);
    return reads.of(
        DexMethod::get_method("LCaller;.call:(LReader;)V")->as_def());
  }

  static const DexField* bar_y() {
    return dynamic_cast<DexField*>(DexField::get_field("LBar;.Y:LBar;"));
  }
};

// A method that reads no constant has an empty summary.
TEST_F(OptimizeEnumsReadSummaryTest, readsNothing) {
  auto summary = summary_of({R"(
    (method (public static) "LReads;.nothing:()V"
      ((return-void))
    )
  )"},
                            "LReads;.nothing:()V");
  ASSERT_TRUE(summary);
  EXPECT_TRUE(summary->empty());
}

// A method that reads one constant has exactly that one in its summary.
TEST_F(OptimizeEnumsReadSummaryTest, readsOneConstant) {
  auto summary = summary_of({R"(
    (method (public static) "LReads;.one:()Ljava/lang/Object;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )"},
                            "LReads;.one:()Ljava/lang/Object;");
  ASSERT_TRUE(summary);
  EXPECT_EQ(summary->size(), 1);
  EXPECT_EQ(summary->count(bar_y()), 1);
}

// An interface call runs one of the interface's implementations; the abstract
// interface method itself runs nothing. The only implementation reads
// nothing, so neither does the call.
TEST_F(OptimizeEnumsReadSummaryTest, interfaceCallWithQuietImplementation) {
  auto summary = interface_call_summary(R"(
    (method (public) "LReads;.read:()V"
      (
        (load-param-object v0)
        (return-void)
      )
    )
  )");
  ASSERT_TRUE(summary);
  EXPECT_TRUE(summary->empty());
}

// The same call, whose only implementation reads a constant.
TEST_F(OptimizeEnumsReadSummaryTest, interfaceCallReadsThroughImplementation) {
  auto summary = interface_call_summary(R"(
    (method (public) "LReads;.read:()V"
      (
        (load-param-object v0)
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )
  )");
  ASSERT_TRUE(summary);
  EXPECT_EQ(summary->size(), 1);
  EXPECT_EQ(summary->count(bar_y()), 1);
}

// The same call, where the only implementation is a default method of a
// sub-interface, which reads a constant.
TEST_F(OptimizeEnumsReadSummaryTest,
       interfaceCallReadsThroughSubInterfaceDefaultMethod) {
  auto summary = interface_call_summary(R"(
    (method (public) "LSubReader;.read:()V"
      (
        (load-param-object v0)
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )
  )");
  ASSERT_TRUE(summary);
  EXPECT_EQ(summary->size(), 1);
  EXPECT_EQ(summary->count(bar_y()), 1);
}

// A static call of a trusted method that Redex has only a reference to, as a
// Kotlin null check is when the Kotlin library is not in the input, runs
// exactly that method, so the summary stays known.
TEST_F(OptimizeEnumsReadSummaryTest, trustedReferenceOnlyCalleeIsKnown) {
  auto summary = summary_of({R"(
    (method (public static) "LReads;.check:(Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (const-string "value")
        (move-result-pseudo-object v1)
        (invoke-static (v0 v1) "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/Object;Ljava/lang/String;)V")
        (return-void)
      )
    )
  )"},
                            "LReads;.check:(Ljava/lang/Object;)V");
  ASSERT_TRUE(summary);
  EXPECT_TRUE(summary->empty());
}

// A call of a method Redex has no code for may run anything, so the summary
// is unknown.
TEST_F(OptimizeEnumsReadSummaryTest, opaqueCallIsUnknown) {
  auto summary = summary_of({R"(
    (method (public static) "LReads;.opaque:()V"
      (
        (invoke-static () "LUnknown;.run:()V")
        (return-void)
      )
    )
  )"},
                            "LReads;.opaque:()V");
  EXPECT_FALSE(summary);
}

// A constant read in a method that two methods call each other through is in
// the summary of both.
TEST_F(OptimizeEnumsReadSummaryTest, readThroughCycle) {
  auto summaries = summaries_of(ping_pong_methods(),
                                {"LReads;.ping:()V", "LReads;.pong:()V"});
  for (const auto& summary : summaries) {
    ASSERT_TRUE(summary);
    EXPECT_EQ(summary->count(bar_y()), 1);
  }
}

// Threads that ask for the same summaries at once, as the analyses of several
// enums do, get the same ones.
TEST_F(OptimizeEnumsReadSummaryTest, concurrentQueriesAgree) {
  auto summaries =
      summaries_of(ping_pong_methods(),
                   {"LReads;.ping:()V", "LReads;.pong:()V"}, /*num_threads=*/8);
  for (const auto& summary : summaries) {
    ASSERT_TRUE(summary);
    EXPECT_EQ(summary->count(bar_y()), 1);
  }
}

// A virtual call runs any override, so what an override reads is in the
// caller's summary.
TEST_F(OptimizeEnumsReadSummaryTest, overrideReadIsFollowed) {
  const std::string base = R"(
    (method (public) "LReads;.read:()V"
      (
        (load-param-object v0)
        (return-void)
      )
    )
  )";
  const std::string caller = R"(
    (method (public static) "LReads;.call:(LReads;)V"
      (
        (load-param-object v0)
        (invoke-virtual (v0) "LReads;.read:()V")
        (return-void)
      )
    )
  )";
  const std::string override = R"(
    (method (public) "LSubReads;.read:()V"
      (
        (load-param-object v0)
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )
  )";
  auto summary = summaries_of({base, caller}, {"LReads;.call:(LReads;)V"},
                              /*num_threads=*/1, {override})
                     .front();
  ASSERT_TRUE(summary);
  EXPECT_EQ(summary->size(), 1);
  EXPECT_EQ(summary->count(bar_y()), 1);
}

/* Create the enum `LMode;` with constants FAST and SLOW, its values array, a
static fields `sink` and `ready` and the given extra `methods`, and analyze its
<clinit>, which runs `middle` after assigning FAST and before creating SLOW, as
code in SLOW's arguments does, once `edit` has changed the code:

enum Mode { FAST, SLOW(middle); ... }

`java.lang.String` is an external final class with external `valueOf(Object)`
and `toUpperCase()`, and `java.lang.Class` one with external `newInstance()`,
as in an app. Return the number of constants found, which is 0 when the enum is
kept. */
size_t constants_with_code_before_slow(
    const std::string& middle,
    const std::vector<std::string>& methods = {},
    const std::function<void()>& edit = {}) {
  auto store = create_enum_store();
  auto add_external_method = [](ClassCreator& creator, const char* name,
                                DexAccessFlags access, bool is_virtual) {
    auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(name));
    method->set_access(access);
    method->set_virtual(is_virtual);
    method->set_external();
    creator.add_method(method);
  };
  ClassCreator sc(type::java_lang_String());
  sc.set_super(type::java_lang_Object());
  sc.set_access(ACC_PUBLIC | ACC_FINAL);
  add_external_method(
      sc, "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;",
      ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  add_external_method(sc, "Ljava/lang/String;.toUpperCase:()Ljava/lang/String;",
                      ACC_PUBLIC, /* is_virtual */ true);
  sc.set_external();
  sc.create();
  ClassCreator kc(type::java_lang_Class());
  kc.set_super(type::java_lang_Object());
  kc.set_access(ACC_PUBLIC | ACC_FINAL);
  add_external_method(kc, "Ljava/lang/Class;.newInstance:()Ljava/lang/Object;",
                      ACC_PUBLIC, /* is_virtual */ true);
  kc.set_external();
  kc.create();

  ClassCreator cc(DexType::make_type("LMode;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  for (const char* constant : {"LMode;.FAST:LMode;", "LMode;.SLOW:LMode;"}) {
    cc.add_field(DexField::make_field(constant)->make_concrete(
        ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  }
  cc.add_field(DexField::make_field("LMode;.$VALUES:[LMode;")
                   ->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC));
  cc.add_field(DexField::make_field("LMode;.sink:Ljava/lang/Object;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  cc.add_field(DexField::make_field("LMode;.ready:Z")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  cc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LMode;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  for (const auto& method : methods) {
    cc.add_method(assembler::method_from_string(method));
  }
  cc.add_method(assembler::method_from_string(R"(
    (method (public static) "LMode;.<clinit>:()V"
      (
        (const-string "FAST")
        (move-result-pseudo-object v1)
        (const v2 0)
        (new-instance "LMode;")
        (move-result-pseudo-object v3)
        (invoke-direct (v3 v1 v2) "LMode;.<init>:(Ljava/lang/String;I)V")
        (sput-object v3 "LMode;.FAST:LMode;")
  )" + middle + R"(
        (const-string "SLOW")
        (move-result-pseudo-object v1)
        (const v2 1)
        (new-instance "LMode;")
        (move-result-pseudo-object v4)
        (invoke-direct (v4 v1 v2) "LMode;.<init>:(Ljava/lang/String;I)V")
        (sput-object v4 "LMode;.SLOW:LMode;")
        (return-void)
      )
    )
  )"));
  auto* cls = cc.create();
  build_cfgs_for_clinit_analysis(cls);
  if (edit) {
    edit();
  }
  return analyze_clinit(cls, false).m_constants_map.size();
}

// enum Mode {
//   FAST, SLOW(String.valueOf(FAST));
//   @Override public String toString() { return SLOW == null ? "a" : "b"; }
// }
// `String.valueOf(Object)` calls the overridden `FAST.toString()`, which reads
// SLOW before it is assigned.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsLibraryCallThatCallsBack) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (sget-object "LMode;.FAST:LMode;")
                  (move-result-pseudo-object v0)
                  (invoke-static (v0) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
                  (move-result-object v0)
                  (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
                )",
                {R"(
                  (method (public) "LMode;.toString:()Ljava/lang/String;"
                    (
                      (load-param-object v0)
                      (const-string "a")
                      (move-result-pseudo-object v1)
                      (sget-object "LMode;.SLOW:LMode;")
                      (move-result-pseudo-object v2)
                      (if-eqz v2 :unassigned)
                      (const-string "b")
                      (move-result-pseudo-object v1)
                      (:unassigned)
                      (return-object v1)
                    )
                  )
                )"}),
            0);
}

// enum Mode {
//   FAST, SLOW(label(FAST));
//   @Override public String toString() { return SLOW == null ? "a" : "b"; }
//   static String label(Enum<?> e) { return e.toString(); }
// }
// `label` calls `Enum.toString()`, which Redex treats as pure, but the call
// runs the override, which reads SLOW before it is assigned.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsCallOfOverriddenPureMethod) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (sget-object "LMode;.FAST:LMode;")
                  (move-result-pseudo-object v0)
                  (invoke-static (v0) "LMode;.label:(Ljava/lang/Enum;)Ljava/lang/String;")
                  (move-result-object v0)
                  (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
                )",
                {R"(
                  (method (public) "LMode;.toString:()Ljava/lang/String;"
                    (
                      (load-param-object v0)
                      (const-string "a")
                      (move-result-pseudo-object v1)
                      (sget-object "LMode;.SLOW:LMode;")
                      (move-result-pseudo-object v2)
                      (if-eqz v2 :unassigned)
                      (const-string "b")
                      (move-result-pseudo-object v1)
                      (:unassigned)
                      (return-object v1)
                    )
                  )
                )",
                 R"(
                  (method (private static) "LMode;.label:(Ljava/lang/Enum;)Ljava/lang/String;"
                    (
                      (load-param-object v0)
                      (invoke-virtual (v0) "Ljava/lang/Enum;.toString:()Ljava/lang/String;")
                      (move-result-object v0)
                      (return-object v0)
                    )
                  )
                )"},
                [] {
                  // As in an app, `Enum.toString()` is defined outside it.
                  auto* to_string =
                      dynamic_cast<DexMethod*>(DexMethod::make_method(
                          "Ljava/lang/Enum;.toString:()Ljava/lang/String;"));
                  to_string->set_access(ACC_PUBLIC);
                  to_string->set_virtual(true);
                  to_string->set_external();
                  type_class(type::java_lang_Enum())->add_method(to_string);
                }),
            0);
}

// `SLOW(new Probe().ready())` where `ready()` is a method of the non-final
// class `Probe`: a subclass may override it with code that reads SLOW.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsCallThatMayReachOverride) {
  ClassCreator pc(DexType::make_type("LProbe;"));
  pc.set_super(type::java_lang_Object());
  pc.set_access(ACC_PUBLIC);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LProbe;.<init>:()V"
      (
        (load-param-object v0)
        (return-void)
      )
    )
  )");
  auto* ready = assembler::method_from_string(R"(
    (method (public) "LProbe;.ready:()Z"
      (
        (load-param-object v0)
        (const v1 1)
        (return v1)
      )
    )
  )");
  pc.add_method(ctor);
  pc.add_method(ready);
  pc.create();
  ctor->get_code()->build_cfg();
  ready->get_code()->build_cfg();
  // A subclass overrides `ready()` with code that reads SLOW.
  ClassCreator sc(DexType::make_type("LSlowProbe;"));
  sc.set_super(DexType::get_type("LProbe;"));
  sc.set_access(ACC_PUBLIC);
  auto* overriding = assembler::method_from_string(R"(
    (method (public) "LSlowProbe;.ready:()Z"
      (
        (load-param-object v0)
        (sget-object "LMode;.SLOW:LMode;")
        (move-result-pseudo-object v1)
        (if-eqz v1 :unassigned)
        (const v2 1)
        (return v2)
        (:unassigned)
        (const v2 0)
        (return v2)
      )
    )
  )");
  sc.add_method(overriding);
  sc.create();
  overriding->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (new-instance "LProbe;")
              (move-result-pseudo-object v0)
              (invoke-direct (v0) "LProbe;.<init>:()V")
              (invoke-virtual (v0) "LProbe;.ready:()Z")
              (move-result v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )"),
            0);
}

// The same call where `Probe` has no subclass: the analysis follows the one
// method the call can run, which reads no constant, so the enum is boxed.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsCallOfSoleImplementation) {
  ClassCreator pc(DexType::make_type("LProbe;"));
  pc.set_super(type::java_lang_Object());
  pc.set_access(ACC_PUBLIC);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LProbe;.<init>:()V"
      (
        (load-param-object v0)
        (return-void)
      )
    )
  )");
  auto* ready = assembler::method_from_string(R"(
    (method (public) "LProbe;.ready:()Z"
      (
        (load-param-object v0)
        (const v1 1)
        (return v1)
      )
    )
  )");
  pc.add_method(ctor);
  pc.add_method(ready);
  pc.create();
  ctor->get_code()->build_cfg();
  ready->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (new-instance "LProbe;")
              (move-result-pseudo-object v0)
              (invoke-direct (v0) "LProbe;.<init>:()V")
              (invoke-virtual (v0) "LProbe;.ready:()Z")
              (move-result v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )"),
            2);
}

// `SLOW("fast".toUpperCase())`: `String.toUpperCase()` is pure, so it runs no
// app code.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsPureLibraryCall) {
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (const-string "fast")
              (move-result-pseudo-object v0)
              (invoke-virtual (v0) "Ljava/lang/String;.toUpperCase:()Ljava/lang/String;")
              (move-result-object v0)
              (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
            )"),
            2);
}

/* `values()` and `valueOf(String)` of `LMode;`, as javac generates them. */
std::vector<std::string> mode_values_methods() {
  return {R"(
            (method (public static) "LMode;.values:()[LMode;"
              (
                (sget-object "LMode;.$VALUES:[LMode;")
                (move-result-pseudo-object v0)
                (invoke-virtual (v0) "[LMode;.clone:()Ljava/lang/Object;")
                (move-result-object v0)
                (check-cast v0 "[LMode;")
                (move-result-pseudo-object v0)
                (return-object v0)
              )
            )
          )",
          R"(
            (method (public static) "LMode;.valueOf:(Ljava/lang/String;)LMode;"
              (
                (load-param-object v0)
                (const-class "LMode;")
                (move-result-pseudo-object v1)
                (invoke-static (v1 v0) "Ljava/lang/Enum;.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;")
                (move-result-object v0)
                (check-cast v0 "LMode;")
                (move-result-pseudo-object v0)
                (return-object v0)
              )
            )
          )"};
}

// `SLOW(new Tag())` with `class Tag { Tag() {} }`: the constructor only calls
// `Object.<init>`, whose body is empty, so it runs no app code.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsObjectConstructorCall) {
  ClassCreator tc(DexType::make_type("LTag;"));
  tc.set_super(type::java_lang_Object());
  tc.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LTag;.<init>:()V"
      (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )
    )
  )");
  tc.add_method(ctor);
  tc.create();
  ctor->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (new-instance "LTag;")
                  (move-result-pseudo-object v0)
                  (invoke-direct (v0) "LTag;.<init>:()V")
                  (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
                )",
                {},
                [] {
                  // As in an app, `Object.<init>` is defined outside it.
                  auto* object_ctor = dynamic_cast<DexMethod*>(
                      DexMethod::get_method("Ljava/lang/Object;.<init>:()V"));
                  object_ctor->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
                  object_ctor->set_external();
                  type_class(type::java_lang_Object())->add_method(object_ctor);
                }),
            2);
}

// `SLOW(Tag(FAST))` with `class Tag(val value: Any)`, whose constructor passes
// FAST to Kotlin's null assertion. The assertion only throws, through library
// code, when its argument is null, so it runs no app code.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsKotlinNullAssertion) {
  ClassCreator ic(DexType::make_type("Lkotlin/jvm/internal/Intrinsics;"));
  ic.set_super(type::java_lang_Object());
  ic.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* check = assembler::method_from_string(R"(
    (method (public static) "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/Object;Ljava/lang/String;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (if-nez v0 :not_null)
        (new-instance "Ljava/lang/NullPointerException;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
        (throw v2)
        (:not_null)
        (return-void)
      )
    )
  )");
  ic.add_method(check);
  ic.create();
  check->get_code()->build_cfg();
  ClassCreator tc(DexType::make_type("LTag;"));
  tc.set_super(type::java_lang_Object());
  tc.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LTag;.<init>:(Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (const-string "value")
        (move-result-pseudo-object v2)
        (invoke-static (v1 v2) "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/Object;Ljava/lang/String;)V")
        (return-void)
      )
    )
  )");
  tc.add_method(ctor);
  tc.create();
  ctor->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (new-instance "LTag;")
              (move-result-pseudo-object v0)
              (sget-object "LMode;.FAST:LMode;")
              (move-result-pseudo-object v5)
              (invoke-direct (v0 v5) "LTag;.<init>:(Ljava/lang/Object;)V")
              (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
            )"),
            2);
}

// A wrapper that RemoveNullcheckStringArg made for a null check whose code is
// marked `no_optimizations`: the code that runs may be anything, so the
// wrapper is no more trusted than the check it calls.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsUntrustedKotlinNullAssertion) {
  ClassCreator ic(DexType::make_type("Lkotlin/jvm/internal/Intrinsics;"));
  ic.set_super(type::java_lang_Object());
  ic.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* check = assembler::method_from_string(R"(
    (method (public static) "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/Object;Ljava/lang/String;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (return-void)
      )
    )
  )");
  auto* wrapper = assembler::method_from_string(R"(
    (method (public static) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V"
      (
        (load-param-object v0)
        (load-param v1)
        (const-string "value")
        (move-result-pseudo-object v2)
        (invoke-static (v0 v2) "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/Object;Ljava/lang/String;)V")
        (return-void)
      )
    )
  )");
  ic.add_method(check);
  ic.add_method(wrapper);
  ic.create();
  check->get_code()->build_cfg();
  wrapper->get_code()->build_cfg();
  check->rstate.set_no_optimizations();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (sget-object "LMode;.FAST:LMode;")
              (move-result-pseudo-object v0)
              (const v1 0)
              (invoke-static (v0 v1) "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/Object;I)V")
            )"),
            0);
}

// Reading a static field of another class runs that class's initializer,
// which here reads SLOW while it is still null:
//
//   class Registry { static final boolean SLOW_KNOWN = Mode.SLOW != null; }
//   enum Mode { FAST, SLOW(record(Registry.SLOW_KNOWN)); ... }
//
// The enum is still boxed: Redex may change when static initializers run
// (specbreaker.md, Static Initializers).
TEST_F(OptimizeEnumsTest, clinitAnalysisIgnoresTriggeredClassInitializer) {
  ClassCreator rc(DexType::make_type("LRegistry;"));
  rc.set_super(type::java_lang_Object());
  rc.set_access(ACC_PUBLIC | ACC_FINAL);
  rc.add_field(DexField::make_field("LRegistry;.SLOW_KNOWN:Z")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  auto* clinit = assembler::method_from_string(R"(
    (method (public static constructor) "LRegistry;.<clinit>:()V"
      (
        (sget-object "LMode;.SLOW:LMode;")
        (move-result-pseudo-object v0)
        (if-eqz v0 :unassigned)
        (const v1 1)
        (goto :store)
        (:unassigned)
        (const v1 0)
        (:store)
        (sput-boolean v1 "LRegistry;.SLOW_KNOWN:Z")
        (return-void)
      )
    )
  )");
  rc.add_method(clinit);
  rc.create();
  clinit->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (sget-boolean "LRegistry;.SLOW_KNOWN:Z")
              (move-result-pseudo v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )"),
            2);
}

// A call into another class whose method reads SLOW: the analysis follows
// callees wherever they are defined.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsReadInAnotherClass) {
  ClassCreator rc(DexType::make_type("LReader;"));
  rc.set_super(type::java_lang_Object());
  rc.set_access(ACC_PUBLIC | ACC_FINAL);
  auto* read = assembler::method_from_string(R"(
    (method (public static) "LReader;.readsSlow:()Z"
      (
        (sget-object "LMode;.SLOW:LMode;")
        (move-result-pseudo-object v0)
        (if-eqz v0 :unassigned)
        (const v1 1)
        (return v1)
        (:unassigned)
        (const v1 0)
        (return v1)
      )
    )
  )");
  rc.add_method(read);
  rc.create();
  read->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (invoke-static () "LReader;.readsSlow:()Z")
              (move-result v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )"),
            0);
}

// enum Mode { FAST, SLOW(probe()); ... }
// static boolean probe() { Callback.class.newInstance(); return true; }
// class Callback { Callback() { Mode.sink = Mode.SLOW; } }
// `Class.newInstance()`, a library method, runs the app constructor
// `Callback()`, which reads SLOW before it is assigned.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsClassNewInstance) {
  ClassCreator cbc(DexType::make_type("LCallback;"));
  cbc.set_super(type::java_lang_Object());
  cbc.set_access(ACC_PUBLIC);
  auto* ctor = assembler::method_from_string(R"(
    (method (public constructor) "LCallback;.<init>:()V"
      (
        (load-param-object v0)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (sget-object "LMode;.SLOW:LMode;")
        (move-result-pseudo-object v1)
        (sput-object v1 "LMode;.sink:Ljava/lang/Object;")
        (return-void)
      )
    )
  )");
  cbc.add_method(ctor);
  cbc.create();
  ctor->get_code()->build_cfg();
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (invoke-static () "LMode;.probe:()Z")
              (move-result v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )",
                                            {R"(
              (method (private static) "LMode;.probe:()Z"
                (
                  (const-class "LCallback;")
                  (move-result-pseudo-object v0)
                  (invoke-virtual (v0) "Ljava/lang/Class;.newInstance:()Ljava/lang/Object;")
                  (move-result-object v0)
                  (const v1 1)
                  (return v1)
                )
              )
            )"}),
            0);
}

// Before SLOW is assigned, `values()` throws, as the values array is still
// null, but would return the boxed constants once Mode is boxed.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsValuesCallBeforeAllAssigned) {
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (invoke-static () "LMode;.values:()[LMode;")
              (move-result-object v0)
              (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
            )",
                                            mode_values_methods()),
            0);
}

// Likewise `valueOf("SLOW")`, which looks the name up in the values array
// through the library method `Enum.valueOf`, whose code Redex does not have.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsValueOfCallBeforeAllAssigned) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (const-string "SLOW")
                  (move-result-pseudo-object v0)
                  (invoke-static (v0) "LMode;.valueOf:(Ljava/lang/String;)LMode;")
                  (move-result-object v0)
                  (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
                )",
                mode_values_methods(),
                [] {
                  DexMethod::get_method(
                      "Ljava/lang/Enum;.valueOf:(Ljava/lang/Class;Ljava/lang/"
                      "String;)Ljava/lang/Enum;")
                      ->as_def()
                      ->set_code(nullptr);
                }),
            0);
}

// Likewise a read of the values array itself, which is still null.
TEST_F(OptimizeEnumsTest,
       clinitAnalysisRejectsValuesArrayReadBeforeAllAssigned) {
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (sget-object "LMode;.$VALUES:[LMode;")
              (move-result-pseudo-object v0)
              (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
            )"),
            0);
}

// The code of a callee marked `no_optimizations` may not be what runs, so it
// may read SLOW.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsNoOptimizationsCallee) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (invoke-static () "LMode;.ready:()Z")
                  (move-result v0)
                  (sput-boolean v0 "LMode;.ready:Z")
                )",
                {R"(
                  (method (private static) "LMode;.ready:()Z"
                    (
                      (const v0 1)
                      (return v0)
                    )
                  )
                )"},
                [] {
                  DexMethod::get_method("LMode;.ready:()Z")
                      ->as_def()
                      ->rstate.set_no_optimizations();
                }),
            0);
}

// A callee that reads a constant through a second method, which calls back
// into the first: neither reads SLOW, so the enum is boxed.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsMutuallyRecursiveCallees) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (const v0 1)
                  (invoke-static (v0) "LMode;.ping:(I)Z")
                  (move-result v0)
                  (sput-boolean v0 "LMode;.ready:Z")
                )",
                {R"(
                  (method (private static) "LMode;.ping:(I)Z"
                    (
                      (load-param v0)
                      (if-eqz v0 :done)
                      (const v1 0)
                      (invoke-static (v1) "LMode;.pong:(I)Z")
                      (move-result v0)
                      (return v0)
                      (:done)
                      (const v0 1)
                      (return v0)
                    )
                  )
                )",
                 R"(
                  (method (private static) "LMode;.pong:(I)Z"
                    (
                      (load-param v0)
                      (invoke-static (v0) "LMode;.ping:(I)Z")
                      (move-result v0)
                      (return v0)
                    )
                  )
                )"}),
            2);
}

// The same two methods, where the second reads SLOW: the cycle does not hide
// the read.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsReadThroughRecursiveCallees) {
  EXPECT_EQ(constants_with_code_before_slow(
                R"(
                  (const v0 1)
                  (invoke-static (v0) "LMode;.ping:(I)Z")
                  (move-result v0)
                  (sput-boolean v0 "LMode;.ready:Z")
                )",
                {R"(
                  (method (private static) "LMode;.ping:(I)Z"
                    (
                      (load-param v0)
                      (if-eqz v0 :done)
                      (const v1 0)
                      (invoke-static (v1) "LMode;.pong:(I)Z")
                      (move-result v0)
                      (return v0)
                      (:done)
                      (const v0 1)
                      (return v0)
                    )
                  )
                )",
                 R"(
                  (method (private static) "LMode;.pong:(I)Z"
                    (
                      (load-param v0)
                      (sget-object "LMode;.SLOW:LMode;")
                      (move-result-pseudo-object v1)
                      (if-eqz v1 :unassigned)
                      (invoke-static (v0) "LMode;.ping:(I)Z")
                      (move-result v0)
                      (return v0)
                      (:unassigned)
                      (const v0 0)
                      (return v0)
                    )
                  )
                )"}),
            0);
}

/* `SLOW(Mode.viaHandle())` where `viaHandle()` makes the method handle call
`handle_call`. */
size_t constants_with_method_handle_call_before_slow(
    const std::string& handle_call, const std::function<void()>& edit = {}) {
  return constants_with_code_before_slow(
      R"(
        (invoke-static () "LMode;.viaHandle:()V")
      )",
      {R"(
        (method (private static) "LMode;.viaHandle:()V"
          (
            (sget-object "LMode;.sink:Ljava/lang/Object;")
            (move-result-pseudo-object v0)
            (check-cast v0 "Ljava/lang/invoke/MethodHandle;")
            (move-result-pseudo-object v0)
      )" +
       handle_call + R"(
            (return-void)
          )
        )
      )"},
      edit);
}

// A method handle call may run any code, which may read SLOW.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsCalleeInvokingMethodHandle) {
  EXPECT_EQ(constants_with_method_handle_call_before_slow(R"(
              (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
            )"),
            0);
}

// Likewise a call site. S-expressions cannot spell `invoke-custom`, so it
// replaces a placeholder call.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsCalleeInvokingCallSite) {
  EXPECT_EQ(constants_with_method_handle_call_before_slow(
                R"(
            (invoke-static () "LMode;.placeholder:()V")
          )",
                [] {
                  auto* via_handle =
                      DexMethod::get_method("LMode;.viaHandle:()V")->as_def();
                  for (auto& mie : cfg::InstructionIterable(
                           via_handle->get_code()->cfg())) {
                    if (mie.insn->has_method() &&
                        mie.insn->get_method()->str() == "placeholder") {
                      auto* call_site = new DexCallSite(
                          nullptr, DexString::make_string("run"),
                          DexProto::make_proto(type::_void(),
                                               DexTypeList::make_type_list({})),
                          {});
                      mie.insn->set_opcode(OPCODE_INVOKE_CUSTOM)
                          ->set_callsite(call_site);
                    }
                  }
                }),
            0);
}

// `SLOW(fastReady())` where `fastReady()` reads only FAST, which is assigned on
// every path to the call.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsCalleeReadingAssignedConstant) {
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (invoke-static () "LMode;.fastReady:()Z")
              (move-result v0)
              (sput-boolean v0 "LMode;.ready:Z")
            )",
                                            {R"(
              (method (private static) "LMode;.fastReady:()Z"
                (
                  (sget-object "LMode;.FAST:LMode;")
                  (move-result-pseudo-object v0)
                  (if-eqz v0 :unassigned)
                  (const v1 1)
                  (return v1)
                  (:unassigned)
                  (const v1 0)
                  (return v1)
                )
              )
            )"}),
            2);
}

// A read of SLOW in code that never runs cannot see null.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsReadInUnreachableCode) {
  EXPECT_EQ(constants_with_code_before_slow(R"(
              (const v0 0)
              (if-eqz v0 :skip)
              (sget-object "LMode;.SLOW:LMode;")
              (move-result-pseudo-object v0)
              (sput-object v0 "LMode;.sink:Ljava/lang/Object;")
              (:skip)
            )"),
            2);
}

/* An enum whose synthetic `$values()` never returns (not javac output):

  enum Tab {
    A;
    private static final Map<String, Tab> MAP = new HashMap<>();
    private static Tab[] $values() { throw new IllegalStateException(); }
    static { $VALUES = $values(); MAP.put("a", A); }
  }

OptimizeEnums' own inline_enum_values step inlines `$values()` into <clinit>,
which leaves the rest of <clinit> unreachable. The usage analysis that runs
next requires every block to be reachable.
*/
TEST_F(OptimizeEnumsTest, inlinedNonReturningValuesLeavesNoUnreachableBlocks) {
  auto store = create_enum_store();
  ClassCreator tc(DexType::make_type("LTab;"));
  tc.set_super(type::java_lang_Enum());
  tc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  tc.add_field(
      DexField::make_field("LTab;.A:LTab;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  tc.add_field(DexField::make_field("LTab;.$VALUES:[LTab;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  tc.add_field(DexField::make_field("LTab;.MAP:Ljava/util/Map;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL));
  tc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LTab;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  tc.add_method(assembler::method_from_string(R"(
    (method (private static synthetic) "LTab;.$values:()[LTab;"
      (
        (new-instance "Ljava/lang/IllegalStateException;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "Ljava/lang/IllegalStateException;.<init>:()V")
        (throw v0)
      )
    )
  )"));
  tc.add_method(assembler::method_from_string(R"(
    (method (public static) "LTab;.<clinit>:()V"
      (
        (new-instance "LTab;")
        (move-result-pseudo-object v0)
        (const-string "A")
        (move-result-pseudo-object v1)
        (const v2 0)
        (invoke-direct (v0 v1 v2) "LTab;.<init>:(Ljava/lang/String;I)V")
        (sput-object v0 "LTab;.A:LTab;")
        (invoke-static () "LTab;.$values:()[LTab;")
        (move-result-object v3)
        (sput-object v3 "LTab;.$VALUES:[LTab;")
        (new-instance "Ljava/util/HashMap;")
        (move-result-pseudo-object v4)
        (invoke-direct (v4) "Ljava/util/HashMap;.<init>:()V")
        (const-string "a")
        (move-result-pseudo-object v1)
        (sget-object "LTab;.A:LTab;")
        (move-result-pseudo-object v0)
        (invoke-interface (v4 v1 v0) "Ljava/util/Map;.put:(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
        (sput-object v4 "LTab;.MAP:Ljava/util/Map;")
        (return-void)
      )
    )
  )"));
  auto* tab = tc.create();
  store.add_classes({tab});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  ASSERT_EQ(inline_enum_values::run(tab), inline_enum_values::Result::kChanged);

  auto* tab_type = DexType::get_type("LTab;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(tab_type);
  optimize_enums::reject_unsafe_enums(scope, &config, [](auto, auto) {});
  EXPECT_EQ(inline_enum_values::run(tab),
            inline_enum_values::Result::kIneligible);

  optimize_enums::OptimizeEnumsPass first_pass;
  optimize_enums::OptimizeEnumsPass second_pass;
  PassManager manager({&first_pass, &second_pass});
  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  manager.run_passes(stores, conf);
  EXPECT_EQ(tab->get_super_class(), type::java_lang_Enum());
}

namespace {

// enum Tab { A; }, as javac 15+ compiles it, with `$values()`, and with
// `clinit_extra` at the end of <clinit> and `other_method` as another method
// when they are not empty.
DexClass* make_tab_enum(const std::string& clinit_extra,
                        const std::string& other_method) {
  ClassCreator tc(DexType::make_type("LTab;"));
  tc.set_super(type::java_lang_Enum());
  tc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  tc.add_field(
      DexField::make_field("LTab;.A:LTab;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  tc.add_field(DexField::make_field("LTab;.$VALUES:[LTab;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  tc.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LTab;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )"));
  tc.add_method(assembler::method_from_string(R"(
    (method (private static synthetic) "LTab;.$values:()[LTab;"
      (
        (const v0 1)
        (new-array v0 "[LTab;")
        (move-result-pseudo-object v1)
        (const v0 0)
        (sget-object "LTab;.A:LTab;")
        (move-result-pseudo-object v2)
        (aput-object v2 v1 v0)
        (return-object v1)
      )
    )
  )"));
  tc.add_method(assembler::method_from_string(R"(
    (method (public static) "LTab;.<clinit>:()V"
      (
        (new-instance "LTab;")
        (move-result-pseudo-object v0)
        (const-string "A")
        (move-result-pseudo-object v1)
        (const v2 0)
        (invoke-direct (v0 v1 v2) "LTab;.<init>:(Ljava/lang/String;I)V")
        (sput-object v0 "LTab;.A:LTab;")
        (invoke-static () "LTab;.$values:()[LTab;")
        (move-result-object v3)
        (sput-object v3 "LTab;.$VALUES:[LTab;")
        )" + clinit_extra +
                                              R"(
        (return-void)
      )
    )
  )"));
  if (!other_method.empty()) {
    tc.add_method(assembler::method_from_string(other_method));
  }
  auto* tab = tc.create();
  walk::code(std::vector<DexClass*>{tab},
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  return tab;
}

} // namespace

TEST_F(OptimizeEnumsTest, inlineEnumValuesInlinesValuesCalledOnlyByClinit) {
  auto* tab = make_tab_enum("", "");
  EXPECT_EQ(inline_enum_values::run(tab), inline_enum_values::Result::kChanged);
  EXPECT_EQ(DexMethod::get_method("LTab;.$values:()[LTab;"), nullptr);
}

// `$values()` stays when a method handle calls it, in <clinit> or elsewhere in
// the enum: deleting it would leave the handle naming a method that does not
// exist. Such handles are tool-generated bytecode.
TEST_F(OptimizeEnumsTest, inlineEnumValuesKeepsValuesCalledByMethodHandle) {
  auto* tab = make_tab_enum(R"(
        (const-method-handle invoke-static "LTab;.$values:()[LTab;")
        (move-result-pseudo-object v4)
  )",
                            "");
  EXPECT_EQ(inline_enum_values::run(tab),
            inline_enum_values::Result::kIneligible);
}

TEST_F(OptimizeEnumsTest,
       inlineEnumValuesKeepsValuesCalledByMethodHandleInOtherMethod) {
  auto* tab = make_tab_enum("", R"(
    (method (public static) "LTab;.valuesHandle:()Ljava/lang/invoke/MethodHandle;"
      (
        (const-method-handle invoke-static "LTab;.$values:()[LTab;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  EXPECT_EQ(inline_enum_values::run(tab),
            inline_enum_values::Result::kIneligible);
}

// An Object parameter passed to a method handle call may reach any code, so an
// enum passed for it cannot be boxed:
//
//   static void print(Object value) throws Throwable { PRINT.invoke(value); }
TEST_F(OptimizeEnumsTest, objectParamPassedToMethodHandleCallIsNotSafe) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.call:(Ljava/lang/invoke/MethodHandle;Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  method->get_code()->build_cfg();
  auto summary =
      optimize_enums::calculate_param_summary(method, type::java_lang_Object());
  EXPECT_FALSE(summary.safe_params.contains(1));
}

// The same for an Object parameter passed to a call site.
TEST_F(OptimizeEnumsTest, objectParamPassedToCallSiteIsNotSafe) {
  // The `invoke-static` becomes an `invoke-custom`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.link:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (invoke-static (v0) "LFoo;.placeholder:(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  redex::make_invoke_custom(method->get_code(), "run", "(Ljava/lang/Object;)V");
  method->get_code()->build_cfg();
  auto summary =
      optimize_enums::calculate_param_summary(method, type::java_lang_Object());
  EXPECT_FALSE(summary.safe_params.contains(0));
}

// `Arrays.asList(new Object[] {Bar.Y})`, with the array built by
// filled-new-array: the enum escapes into an Object[], so Bar must not be boxed
// as an Integer.
TEST_F(OptimizeEnumsTest, enumStoredByFilledNewArrayIsRejected) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.list:()Ljava/util/List;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (filled-new-array (v0) "[Ljava/lang/Object;")
        (move-result-object v1)
        (invoke-static (v1) "Ljava/util/Arrays;.asList:([Ljava/lang/Object;)Ljava/util/List;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  std::set<optimize_enums::UnsafeType> bar_reasons;
  std::mutex reasons_mutex;
  optimize_enums::reject_unsafe_enums(
      scope, &config, [&](const DexType* type, optimize_enums::UnsafeType u) {
        if (type == bar_type) {
          std::lock_guard<std::mutex> lock(reasons_mutex);
          bar_reasons.insert(u);
        }
      });
  EXPECT_EQ(bar_reasons,
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageCastFilledNewArray});
}

// `Bar[][] rows = {new Bar[] {Bar.Y}};` with both arrays built by
// filled-new-array: the outer one stores a row, a `Bar[]`, so every value stays
// a Bar, and Bar is boxed in both array types.
TEST_F(OptimizeEnumsTest, rowStoredByFilledNewArrayLetsEnumBeBoxed) {
  auto* make = run_pass_on_rows_maker(R"(
    (method (public static) "LRows;.make:()[[LBar;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (filled-new-array (v0) "[LBar;")
        (move-result-object v1)
        (filled-new-array (v1) "[[LBar;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )");
  EXPECT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  EXPECT_EQ(show(make->get_proto()->get_rtype()), "[[Ljava/lang/Integer;");
  make->get_code()->build_cfg();
  for (const auto& mie : cfg::InstructionIterable(make->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_FILLED_NEW_ARRAY) {
      EXPECT_EQ(type::make_array_element_type(mie.insn->get_type()),
                type::java_lang_Integer());
    }
  }
}

namespace {

// Run the usage analysis over the Bar store plus `LUser;` with `methods`, and
// return the reasons Bar was rejected for.
std::set<optimize_enums::UnsafeType> bar_rejection_reasons(
    const std::vector<DexMethod*>& methods) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  for (auto* method : methods) {
    uc.add_method(method);
  }
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  std::mutex reasons_mutex;
  std::set<optimize_enums::UnsafeType> reasons;
  optimize_enums::reject_unsafe_enums(
      scope, &config,
      [&](const DexType* type, optimize_enums::UnsafeType reason) {
        if (type == bar_type) {
          std::lock_guard<std::mutex> lock(reasons_mutex);
          reasons.insert(reason);
        }
      });
  EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type) == 0u,
            !reasons.empty());
  return reasons;
}

} // namespace

TEST_F(OptimizeEnumsTest, enumPassedToMethodHandleCallIsRejected) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.call:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v1)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsagePassedToCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumNamedByMethodHandleCallPrototypeIsRejected) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.callTyped:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()LBar;")
      (return-void)
     )
    )
  )");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumPassedToCallSiteIsRejected) {
  // The `invoke-static` becomes an `invoke-custom`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.link:()V"
     (
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LUser;.placeholder:(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  redex::make_invoke_custom(method->get_code(), "run", "(Ljava/lang/Object;)V");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsagePassedToCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumNamedByCallSiteMethodHandleIsRejected) {
  // A tool-generated call site with an app-defined bootstrap method, whose
  // bootstrap arguments include a method handle to `User.take(Bar)`.
  auto* take = assembler::method_from_string(R"(
    (method (public static) "LUser;.take:(LBar;)V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  // The `invoke-static` becomes an `invoke-custom`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.lambda:()V"
     (
      (invoke-static () "LUser;.placeholder:()Ljava/util/function/Consumer;")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LUser;.take:(LBar;)V")));
  redex::make_invoke_custom(method->get_code(), "accept",
                            "()Ljava/util/function/Consumer;", std::move(args));
  EXPECT_EQ(
      bar_rejection_reasons({take, method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumNamedByCallSiteMethodTypeIsRejected) {
  // A tool-generated call site with an app-defined bootstrap method, whose
  // bootstrap arguments include the method type `(LBar;)V`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.lambda:()V"
     (
      (invoke-static () "LUser;.placeholder:()Ljava/util/function/Consumer;")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto("(LBar;)V")));
  redex::make_invoke_custom(method->get_code(), "accept",
                            "()Ljava/util/function/Consumer;", std::move(args));
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumNamedByConstMethodTypeIsRejected) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.type:()V"
     (
      (const-method-type "(LBar;)V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumFieldTypeOfConstMethodHandleIsRejected) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.handle:()V"
     (
      (const-method-handle static-get "LUser;.f:LBar;")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

TEST_F(OptimizeEnumsTest, enumInMethodOfConstMethodHandleIsRejected) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.handle:()V"
     (
      (const-method-handle invoke-static "LUser;.take:(LBar;)V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");
  EXPECT_EQ(
      bar_rejection_reasons({method}),
      std::set<optimize_enums::UnsafeType>{
          optimize_enums::UnsafeType::kUsageNamedByCallSiteOrMethodHandle});
}

namespace {

// Adds the generated `values` and `valueOf` to `bar` and returns them.
std::pair<DexMethod*, DexMethod*> add_generated_methods(DexClass* bar) {
  auto* values = assembler::method_from_string(R"(
    (method (public static) "LBar;.values:()[LBar;"
     (
      (sget-object "LBar;.$VALUES:[LBar;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  auto* value_of = assembler::method_from_string(R"(
    (method (public static) "LBar;.valueOf:(Ljava/lang/String;)LBar;"
     (
      (load-param-object v0)
      (const-class "LBar;")
      (move-result-pseudo-object v1)
      (invoke-static (v1 v0) "Ljava/lang/Enum;.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;")
      (move-result-object v1)
      (check-cast v1 "LBar;")
      (move-result-pseudo-object v1)
      (return-object v1)
     )
    )
  )");
  bar->add_method(values);
  bar->add_method(value_of);
  return {values, value_of};
}

// Run the analysis that deletes unused generated enum methods over the Bar
// store, with `values` and `valueOf` added to Bar, plus `LUser;` with
// `caller`, and return the names of the generated methods it keeps.
std::set<std::string> generated_methods_kept(DexMethod* caller) {
  auto store = create_enum_store();
  auto* bar = type_class(DexType::get_type("LBar;"));
  auto [values, value_of] = add_generated_methods(bar);
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(caller);
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::EnumAnalyzeGeneratedMethods analyzer;
  analyzer.consider_enum_type(bar->get_type(), value_of, values);
  analyzer.transform_code(scope);
  std::set<std::string> kept;
  for (const auto* method : bar->get_dmethods()) {
    if (method == values || method == value_of) {
      kept.insert(method->get_name()->str_copy());
    }
  }
  return kept;
}

} // namespace

// `static Object[] all() { return new Object[] {Bar.Y}; }` with the array built
// by filled-new-array: the enum escapes as an Object, and code that receives
// it can call `values` reflectively through its class, so both are kept.
TEST_F(OptimizeEnumsTest, enumStoredByFilledNewArrayKeepsGeneratedMethods) {
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.all:()[Ljava/lang/Object;"
     (
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v0)
      (filled-new-array (v0) "[Ljava/lang/Object;")
      (move-result-object v1)
      (return-object v1)
     )
    )
  )");
  EXPECT_EQ(generated_methods_kept(caller),
            (std::set<std::string>{"valueOf", "values"}));
}

// `static int ordinal(Bar bar) { return bar.ordinal(); }` makes an allowed
// call, so the pass deletes Bar's `values` and `valueOf` with boxing disabled.
// The input defines only some of the allowlisted `java.lang.Enum` methods, as
// an input loaded without the SDK does, and the pass runs in two contexts in a
// row.
TEST_F(OptimizeEnumsTest, allowedCallWithoutSdkLetsGeneratedMethodsGo) {
  for (int run = 0; run < 2; ++run) {
    if (run > 0) {
      delete g_redex;
      g_redex = new RedexContext();
    }
    auto store = create_enum_store();
    auto* bar = type_class(DexType::get_type("LBar;"));
    auto [values, value_of] = add_generated_methods(bar);
    ClassCreator uc(DexType::make_type("LUser;"));
    uc.set_super(type::java_lang_Object());
    uc.set_access(ACC_PUBLIC);
    uc.add_method(assembler::method_from_string(R"(
      (method (public static) "LUser;.ordinal:(LBar;)I"
       (
        (load-param-object v0)
        (invoke-virtual (v0) "LBar;.ordinal:()I")
        (move-result v1)
        (return v1)
       )
      )
    )"));
    store.add_classes({uc.create()});
    DexStoresVector stores({std::move(store)});
    walk::code(build_class_scope(stores),
               [](DexMethod*, IRCode& code) { code.build_cfg(); });

    Json::Value json_conf;
    json_conf["OptimizeEnumsPass"]["max_enum_size"] = 0;
    ConfigFiles conf(json_conf);
    conf.parse_global_config();
    optimize_enums::OptimizeEnumsPass pass;
    PassManager manager({&pass}, conf, RedexOptions{});
    manager.run_passes(stores, conf);

    const auto& dmethods = bar->get_dmethods();
    EXPECT_EQ(std::find(dmethods.begin(), dmethods.end(), values),
              dmethods.end());
    EXPECT_EQ(std::find(dmethods.begin(), dmethods.end(), value_of),
              dmethods.end());
  }
}

// A method handle to `values` keeps it.
TEST_F(OptimizeEnumsTest, methodHandleToValuesKeepsIt) {
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.handle:()Ljava/lang/invoke/MethodHandle;"
     (
      (const-method-handle invoke-static "LBar;.values:()[LBar;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  EXPECT_EQ(generated_methods_kept(caller), std::set<std::string>{"values"});
}

// A method handle to `valueOf` keeps it, and `values`, which it calls.
TEST_F(OptimizeEnumsTest, methodHandleToValueOfKeepsBoth) {
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.handle:()Ljava/lang/invoke/MethodHandle;"
     (
      (const-method-handle invoke-static "LBar;.valueOf:(Ljava/lang/String;)LBar;")
      (move-result-pseudo-object v0)
      (return-object v0)
     )
    )
  )");
  EXPECT_EQ(generated_methods_kept(caller),
            (std::set<std::string>{"valueOf", "values"}));
}

// A tool-generated call site with an app-defined bootstrap method, whose
// bootstrap arguments include a method handle to `Bar.values`, keeps `values`.
TEST_F(OptimizeEnumsTest, callSiteNamingValuesKeepsIt) {
  // The `invoke-static` becomes an `invoke-custom`.
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.supplier:()Ljava/util/function/Supplier;"
     (
      (invoke-static () "LUser;.placeholder:()Ljava/util/function/Supplier;")
      (move-result-object v0)
      (return-object v0)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LBar;.values:()[LBar;")));
  redex::make_invoke_custom(caller->get_code(), "get",
                            "()Ljava/util/function/Supplier;", std::move(args));
  EXPECT_EQ(generated_methods_kept(caller), std::set<std::string>{"values"});
}

// An enum passed to a method handle call may reach code that calls `valueOf`
// or `values` on its class, so both are kept.
TEST_F(OptimizeEnumsTest, enumPassedToMethodHandleCallKeepsBoth) {
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.call:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (sget-object "LBar;.Y:LBar;")
      (move-result-pseudo-object v1)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  EXPECT_EQ(generated_methods_kept(caller),
            (std::set<std::string>{"valueOf", "values"}));
}

// `Bar bar = (Bar) handle.invokeExact(); bar.getClass();` exposes Bar's class,
// through which code can call `values` reflectively, so both are kept.
TEST_F(OptimizeEnumsTest, classOfEnumReturnedByMethodHandleCallKeepsBoth) {
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "LUser;.call:(Ljava/lang/invoke/MethodHandle;)Ljava/lang/Class;"
     (
      (load-param-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()LBar;")
      (move-result-object v1)
      (invoke-virtual (v1) "Ljava/lang/Object;.getClass:()Ljava/lang/Class;")
      (move-result-object v2)
      (return-object v2)
     )
    )
  )");
  EXPECT_EQ(generated_methods_kept(caller),
            (std::set<std::string>{"valueOf", "values"}));
}

/* Run OptimizeEnumsPass over Bar and a user of Bar that passes a constant
through an Object-typed identity method, like this Java code:

class User {
  static Object identity(Object x) { return x; }
  static String show() { return String.valueOf(identity(Bar.Y)); }
  ...
}

javac emits no check-cast on the result of identity(), so the verifier types it
as Object, while the parameter summary of identity() tells the analysis that it
is a Bar.
*/
DexClass* run_pass_with_user(const std::vector<std::string>& user_methods) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (return-object v0)
      )
    )
  )"));
  for (const auto& method : user_methods) {
    uc.add_method(assembler::method_from_string(method));
  }
  auto* user = uc.create();
  for (auto* m : user->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  store.add_classes({user});
  DexStoresVector stores({std::move(store)});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);
  for (auto* m : user->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  return user;
}

size_t count_integer_casts(DexMethod* method) {
  size_t count = 0;
  for (const auto& mie : cfg::InstructionIterable(method->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_CHECK_CAST &&
        mie.insn->get_type() == type::java_lang_Integer()) {
      ++count;
    }
  }
  return count;
}

// String.valueOf(Object) and StringBuilder.append(Object) on such a value are
// rewritten into helpers that take an Integer, so the value needs a cast to
// Integer for the method to verify.
TEST_F(OptimizeEnumsTest, objectReturningCallResultIsCastToInteger) {
  auto* user = run_pass_with_user({R"(
      (method (public static) "LUser;.show:()Ljava/lang/String;"
        (
          (sget-object "LBar;.Y:LBar;")
          (move-result-pseudo-object v0)
          (invoke-static (v0) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
          (move-result-object v1)
          (invoke-static (v1) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
          (move-result-object v2)
          (return-object v2)
        )
      )
    )",
                                   R"(
      (method (public static) "LUser;.append:(Ljava/lang/StringBuilder;)Ljava/lang/String;"
        (
          (load-param-object v0)
          (sget-object "LBar;.Z:LBar;")
          (move-result-pseudo-object v1)
          (invoke-static (v1) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
          (move-result-object v2)
          (move-object v3 v2)
          (invoke-virtual (v0 v3) "Ljava/lang/StringBuilder;.append:(Ljava/lang/Object;)Ljava/lang/StringBuilder;")
          (move-result-object v0)
          (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
          (move-result-object v0)
          (return-object v0)
        )
      )
    )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))))
      << "Bar must be transformed for this test to be meaningful";
  for (const char* name : {"show", "append"}) {
    auto* method = user->find_method_from_simple_deobfuscated_name(name);
    ASSERT_NE(method, nullptr) << name;
    EXPECT_EQ(count_integer_casts(method), 1) << show(method);
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << name << ": " << checker.what();
  }
}

// Inside a try region the inserted cast can throw like any check-cast, so it
// gets the same exception edge as the call that takes the value.
TEST_F(OptimizeEnumsTest, castInsideTryKeepsExceptionEdge) {
  auto* user = run_pass_with_user({R"(
      (method (public static) "LUser;.show:()Ljava/lang/String;"
        (
          (.try_start a)
          (sget-object "LBar;.Y:LBar;")
          (move-result-pseudo-object v0)
          (invoke-static (v0) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
          (move-result-object v1)
          (invoke-static (v1) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
          (move-result-object v2)
          (.try_end a)
          (return-object v2)
          (.catch (a) "Ljava/lang/RuntimeException;")
          (const-string "")
          (move-result-pseudo-object v2)
          (return-object v2)
        )
      )
    )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  auto* method = user->find_method_from_simple_deobfuscated_name("show");
  ASSERT_NE(method, nullptr);
  auto& cfg = method->get_code()->cfg();
  size_t casts = 0;
  for (auto* block : cfg.blocks()) {
    for (const auto& mie : InstructionIterable(block)) {
      if (mie.insn->opcode() == OPCODE_CHECK_CAST &&
          mie.insn->get_type() == type::java_lang_Integer()) {
        ++casts;
        EXPECT_FALSE(cfg.get_succ_edges_of_type(block, cfg::EDGE_THROW).empty())
            << show(cfg);
      }
    }
  }
  EXPECT_EQ(casts, 1) << show(cfg);
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

// Bar b = null; int x = b.x; int y = b.x; takesEnum(b);
// `b` is the constant null, which the verifier accepts as an Integer, so its
// field reads get no cast, and it can still be passed as an `Enum`.
TEST_F(OptimizeEnumsTest, nullConstantGetsNoIntegerCast) {
  auto* user = run_pass_with_user({R"(
      (method (public static) "LUser;.takesEnum:(Ljava/lang/Enum;)V"
        (
          (load-param-object v0)
          (return-void)
        )
      )
    )",
                                   R"(
      (method (public static) "LUser;.readTwice:()I"
        (
          (const v0 0)
          (iget v0 "LBar;.x:I")
          (move-result-pseudo v1)
          (iget v0 "LBar;.x:I")
          (move-result-pseudo v2)
          (invoke-static (v0) "LUser;.takesEnum:(Ljava/lang/Enum;)V")
          (return v1)
        )
      )
    )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  auto* method = user->find_method_from_simple_deobfuscated_name("readTwice");
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(count_integer_casts(method), 0) << show(method);
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

// A value that no rewritten instruction needs as an Integer gets no cast.
TEST_F(OptimizeEnumsTest, noCastWithoutIntegerUse) {
  auto* user = run_pass_with_user({R"(
      (method (public static) "LUser;.isNull:()Z"
        (
          (sget-object "LBar;.Y:LBar;")
          (move-result-pseudo-object v0)
          (invoke-static (v0) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
          (move-result-object v1)
          (const v2 0)
          (if-nez v1 :nonnull)
          (const v2 1)
          (:nonnull)
          (return v2)
        )
      )
    )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  auto* method = user->find_method_from_simple_deobfuscated_name("isNull");
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(count_integer_casts(method), 0) << show(method);
}

// javac emits the enum cast in String.valueOf((Bar) identity(Bar.Y)).
// Rewriting that cast already gives the verifier an Integer.
TEST_F(OptimizeEnumsTest, explicitEnumCastNeedsNoAdditionalIntegerCast) {
  auto* user = run_pass_with_user({R"(
    (method (public static) "LUser;.show:()Ljava/lang/String;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (invoke-static (v0) "LUser;.identity:(Ljava/lang/Object;)Ljava/lang/Object;")
        (move-result-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v1)
        (invoke-static (v1) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  auto* method = user->find_method_from_simple_deobfuscated_name("show");
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(count_integer_casts(method), 1) << show(method->get_code()->cfg());
}

// Defensive bytecode: a redundant Object cast erases the verifier's type.
TEST_F(OptimizeEnumsTest, objectCastResultGetsIntegerCast) {
  auto* user = run_pass_with_user({R"(
    (method (public static) "LUser;.show:()Ljava/lang/String;"
      (
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v0)
        (check-cast v0 "Ljava/lang/Object;")
        (move-result-pseudo-object v1)
        (invoke-static (v1) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
        (move-result-object v2)
        (return-object v2)
      )
    )
  )"});
  ASSERT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
  auto* method = user->find_method_from_simple_deobfuscated_name("show");
  ASSERT_NE(method, nullptr);
  EXPECT_EQ(count_integer_casts(method), 1) << show(method->get_code()->cfg());
  IRTypeChecker checker(method);
  checker.run();
  EXPECT_TRUE(checker.good()) << checker.what();
}

/* An enum whose constructor writes a field of another object, like this Java
code:

class Box { int n; }
class Holder { static Box BOX = new Box(); }
enum WritesBox {
  A(Holder.BOX);
  WritesBox(Box b) { b.n = 7; }
}

Initializing WritesBox sets Holder.BOX.n to 7. Boxing the enum would delete
the constructor call from <clinit>, and the write with it, so the enum must
stay.
*/
TEST_F(OptimizeEnumsTest, constructorWritingAnotherObjectKeepsEnum) {
  auto store = create_enum_store();

  ClassCreator bc(DexType::make_type("LBox;"));
  bc.set_super(type::java_lang_Object());
  bc.set_access(ACC_PUBLIC);
  bc.add_field(DexField::make_field("LBox;.n:I")->make_concrete(ACC_PUBLIC));
  auto* box = bc.create();

  ClassCreator hc(DexType::make_type("LHolder;"));
  hc.set_super(type::java_lang_Object());
  hc.set_access(ACC_PUBLIC);
  hc.add_field(DexField::make_field("LHolder;.BOX:LBox;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  auto* holder = hc.create();

  ClassCreator ec(DexType::make_type("LWritesBox;"));
  ec.set_super(type::java_lang_Enum());
  ec.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  ec.add_field(DexField::make_field("LWritesBox;.A:LWritesBox;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM));
  ec.add_field(DexField::make_field("LWritesBox;.$VALUES:[LWritesBox;")
                   ->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC));
  ec.add_method(assembler::method_from_string(R"(
    (method (private constructor) "LWritesBox;.<init>:(Ljava/lang/String;ILBox;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (load-param-object v3)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (const v4 7)
        (iput v4 v3 "LBox;.n:I")
        (return-void)
      )
    )
  )"));
  ec.add_method(assembler::method_from_string(R"(
    (method (public static) "LWritesBox;.<clinit>:()V"
      (
        (sget-object "LHolder;.BOX:LBox;")
        (move-result-pseudo-object v3)
        (const-string "A")
        (move-result-pseudo-object v0)
        (const v1 0)
        (new-instance "LWritesBox;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1 v3) "LWritesBox;.<init>:(Ljava/lang/String;ILBox;)V")
        (sput-object v2 "LWritesBox;.A:LWritesBox;")
        (const v4 1)
        (new-array v4 "[LWritesBox;")
        (move-result-pseudo-object v4)
        (const v5 0)
        (aput-object v2 v4 v5)
        (sput-object v4 "LWritesBox;.$VALUES:[LWritesBox;")
        (return-void)
      )
    )
  )"));
  auto* writes_box = ec.create();
  for (auto* m : writes_box->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  store.add_classes({box, holder, writes_box});
  DexStoresVector stores({std::move(store)});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);

  EXPECT_TRUE(is_enum(writes_box));
  EXPECT_FALSE(writes_box->get_ctors().empty());
  // Bar, whose constructor writes only its own field, is still boxed.
  EXPECT_FALSE(is_enum(type_class(DexType::get_type("LBar;"))));
}
/* Create an enum whose int and long constructors delegate to each other, like
this hand-written Java-like code (javac and kotlinc reject recursive
constructor invocation, so only hand-written bytecode has this shape):

enum Cycle {
  A;
  Cycle() { super(); }
  Cycle(int i) { this(0L); }
  Cycle(long l) { this(0); }
}
*/
DexClass* create_ctor_cycle_enum(const std::string& name) {
  auto with_name = [&](std::string s_expr) {
    boost::replace_all(s_expr, "LE;", name);
    return s_expr;
  };
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(DexField::make_field(with_name("LE;.A:LE;"))
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM));
  cc.add_field(DexField::make_field(with_name("LE;.$VALUES:[LE;"))
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (private constructor) "LE;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
        (return-void)
      )
    )
  )")));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (private constructor) "LE;.<init>:(Ljava/lang/String;II)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (load-param v3)
        (const-wide v4 0)
        (invoke-direct (v0 v1 v2 v4) "LE;.<init>:(Ljava/lang/String;IJ)V")
        (return-void)
      )
    )
  )")));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (private constructor) "LE;.<init>:(Ljava/lang/String;IJ)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (load-param-wide v3)
        (const v5 0)
        (invoke-direct (v0 v1 v2 v5) "LE;.<init>:(Ljava/lang/String;II)V")
        (return-void)
      )
    )
  )")));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (public static) "LE;.<clinit>:()V"
      (
        (const-string "A")
        (move-result-pseudo-object v0)
        (const v1 0)
        (new-instance "LE;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LE;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LE;.A:LE;")
        (const v3 1)
        (new-array v3 "[LE;")
        (move-result-pseudo-object v4)
        (aput-object v2 v4 v1)
        (sput-object v4 "LE;.$VALUES:[LE;")
        (return-void)
      )
    )
  )")));
  auto* cls = cc.create();
  for (auto* m : cls->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  return cls;
}

int64_t get_metric(const PassManager& manager,
                   const Pass& pass,
                   const std::string& key) {
  for (const auto& info : manager.get_pass_info()) {
    if (info.pass == &pass) {
      auto it = info.metrics.find(key);
      return it == info.metrics.end() ? 0 : it->second;
    }
  }
  ADD_FAILURE() << "OptimizeEnumsPass did not run";
  return -1;
}

/* Create an enum whose only constructor calls `delegate` where it would call
`Enum.<init>`, like this hand-written Java-like code:

enum E {
  A;
  E() { delegate(); }
}
*/
DexClass* create_enum_with_ctor_delegating_to(const std::string& name,
                                              const std::string& delegate) {
  auto with_name = [&](std::string s_expr) {
    boost::replace_all(s_expr, "LE;", name);
    boost::replace_all(s_expr, "DELEGATE", delegate);
    return s_expr;
  };
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(DexField::make_field(with_name("LE;.A:LE;"))
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_ENUM));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (private constructor) "LE;.<init>:(Ljava/lang/String;I)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (invoke-direct (v0 v1 v2) "DELEGATE")
        (return-void)
      )
    )
  )")));
  cc.add_method(assembler::method_from_string(with_name(R"(
    (method (public static) "LE;.<clinit>:()V"
      (
        (const-string "A")
        (move-result-pseudo-object v0)
        (const v1 0)
        (new-instance "LE;")
        (move-result-pseudo-object v2)
        (invoke-direct (v2 v0 v1) "LE;.<init>:(Ljava/lang/String;I)V")
        (sput-object v2 "LE;.A:LE;")
        (return-void)
      )
    )
  )")));
  auto* cls = cc.create();
  for (auto* m : cls->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  return cls;
}

// Defensive: a constructor whose delegating call names a constructor its class
// does not define has no known ordinal parameter, so the ordinal analysis
// leaves the enum unanalyzed.
TEST_F(OptimizeEnumsTest, ctorDelegatingToUndefinedCtorLeavesEnumUnoptimized) {
  auto store = create_enum_store();
  auto* undefined = create_enum_with_ctor_delegating_to(
      "LDelegatesToUndefined;",
      "LDelegatesToUndefined;.<init>:(Ljava/lang/String;Z)V");
  store.add_classes({undefined});
  DexStoresVector stores({std::move(store)});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();

  manager.run_passes(stores, dummy_config);

  EXPECT_EQ(undefined->get_super_class(), type::java_lang_Enum());
  EXPECT_EQ(get_metric(manager, pass, "num_ordinal_bail_non_unique_delegate"),
            1);
}

// The ordinal analysis runs for every enum, candidate or not. A cycle of
// delegating constructors never reaches `Enum.<init>`, so it must leave the
// enum unanalyzed instead of following the cycle forever.
TEST_F(OptimizeEnumsTest, ctorDelegationCycleLeavesEnumUnoptimized) {
  auto store = create_enum_store();
  auto* cycle = create_ctor_cycle_enum("LCtorCycle;");
  store.add_classes({cycle});
  DexStoresVector stores({std::move(store)});

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();

  manager.run_passes(stores, dummy_config);

  EXPECT_EQ(cycle->get_super_class(), type::java_lang_Enum());
  EXPECT_TRUE(is_enum(cycle));
  EXPECT_EQ(get_metric(manager, pass, "num_ordinal_bail_ctor_delegation_cycle"),
            1);
}

namespace {

struct EnumObservationCase {
  const char* name;
  const char* instructions;
  bool bar_safe;
  bool baz_safe;
  // Baz has no constants, so the pass itself keeps it an enum. Bar is boxed
  // by the pass where its only problem was meeting a candidate Baz, since
  // comparing with an enum that stays an enum keeps its result.
  bool bar_boxed_beside_enum_baz{false};
};

class OptimizeEnumsObservationTest
    : public OptimizeEnumsTest,
      public WithParamInterface<EnumObservationCase> {};

TEST_P(OptimizeEnumsObservationTest, preservesObservedObjects) {
  const auto& test = GetParam();
  auto store = create_enum_store();
  auto* bar_type = DexType::get_type("LBar;");
  auto* baz_type = DexType::make_type("LBaz;");
  ClassCreator bc(baz_type);
  bc.set_super(type::java_lang_Enum());
  bc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  store.add_classes({bc.create()});
  ClassCreator mc(DexType::make_type("LMarker;"));
  mc.set_super(type::java_lang_Object());
  mc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  store.add_classes({mc.create()});
  ClassCreator sc(type::java_lang_String());
  sc.set_super(type::java_lang_Object());
  sc.set_access(ACC_PUBLIC | ACC_FINAL);
  store.add_classes({sc.create()});

  ClassCreator gc(DexType::make_type("Lcom/google/common/base/Objects;"));
  gc.set_super(type::java_lang_Object());
  gc.set_access(ACC_PUBLIC);
  auto* equal = assembler::method_from_string(R"(
    (method (public static) "Lcom/google/common/base/Objects;.equal:(Ljava/lang/Object;Ljava/lang/Object;)Z"
      ((load-param-object v0)
       (load-param-object v1)
       (if-eq v0 v1 :equal)
       (if-eqz v0 :unequal)
       (invoke-virtual (v0 v1) "Ljava/lang/Object;.equals:(Ljava/lang/Object;)Z")
       (move-result v2)
       (return v2)
       (:equal)
       (const v2 1)
       (return v2)
       (:unequal)
       (const v2 0)
       (return v2)))
  )");
  gc.add_method(equal);
  store.add_classes({gc.create()});

  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(std::string(R"(
        (method (public static) "LUser;.observe:(LBar;LBar;LBaz;Ljava/lang/Integer;Ljava/lang/Object;Z)V"
          (
            (load-param-object v0)
            (load-param-object v1)
            (load-param-object v2)
            (load-param-object v3)
            (load-param-object v4)
            (load-param v5)
      )") + test.instructions + R"(
            (return-void)
          )
        )
      )"));
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.isNumber:(Ljava/lang/Object;)Z"
      ((load-param-object v0)
       (instance-of v0 "Ljava/lang/Number;")
       (move-result-pseudo v1)
       (return v1)))
  )"));
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.isEnum:(Ljava/lang/Object;)Z"
      ((load-param-object v0)
       (instance-of v0 "Ljava/lang/Enum;")
       (move-result-pseudo v1)
       (return v1)))
  )"));
  for (const auto& [name, type] :
       std::vector<std::pair<std::string, std::string>>{
           {"Integer", "Ljava/lang/Integer;"},
           {"Comparable", "Ljava/lang/Comparable;"},
           {"User", "LUser;"},
           {"IntegerArray", "[Ljava/lang/Integer;"},
           {"ObjectArray", "[Ljava/lang/Object;"}}) {
    uc.add_method(assembler::method_from_string(
        "(method (public static) \"LUser;.is" + name +
        ":(Ljava/lang/Object;)Z\" ((load-param-object v0) (instance-of v0 \"" +
        type + "\") (move-result-pseudo v1) (return v1)))"));
  }
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.same:(Ljava/lang/Object;Ljava/lang/Object;)Z"
      ((load-param-object v0)
       (load-param-object v1)
       (if-eq v0 v1 :equal)
       (const v2 0)
       (return v2)
       (:equal)
       (const v2 1)
       (return v2)))
  )"));
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.lock:(Ljava/lang/Object;)V"
      ((load-param-object v0)
       (monitor-enter v0)
       (monitor-exit v0)
       (return-void)))
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  config.candidate_enums.insert(baz_type);
  auto graph = method_override_graph::build_graph(scope);
  optimize_enums::calculate_param_summaries(scope, *graph,
                                            &config.param_summary_map);
  optimize_enums::reject_unsafe_enums(
      scope, &config, [](const DexType*, optimize_enums::UnsafeType) {});
  EXPECT_EQ(config.candidate_enums.count(bar_type), test.bar_safe ? 1u : 0u);
  EXPECT_EQ(config.candidate_enums.count(baz_type), test.baz_safe ? 1u : 0u);

  optimize_enums::OptimizeEnumsPass pass;
  PassManager manager({&pass});
  ConfigFiles files(Json::nullValue);
  files.parse_global_config();
  manager.run_passes(stores, files);
  EXPECT_EQ(type_class(bar_type)->get_super_class(),
            test.bar_safe || test.bar_boxed_beside_enum_baz
                ? type::java_lang_Object()
                : type::java_lang_Enum());
}

INSTANTIATE_TEST_SUITE_P(
    ObjectObservations,
    OptimizeEnumsObservationTest,
    Values(
        EnumObservationCase{
            "ObjectParameterInstanceOfNumber",
            R"((invoke-static (v0) "LUser;.isNumber:(Ljava/lang/Object;)Z"))",
            false, true},
        EnumObservationCase{
            "ObjectParameterInstanceOfEnum",
            R"((invoke-static (v0) "LUser;.isEnum:(Ljava/lang/Object;)Z"))",
            false, true},
        EnumObservationCase{
            "ObjectParameterIdentity",
            R"((invoke-static (v0 v3) "LUser;.same:(Ljava/lang/Object;Ljava/lang/Object;)Z"))",
            false, true},
        EnumObservationCase{
            "ObjectParameterMonitor",
            R"((invoke-static (v0) "LUser;.lock:(Ljava/lang/Object;)V"))",
            false, true},
        EnumObservationCase{"InstanceOfNumber",
                            R"((instance-of v0 "Ljava/lang/Number;")
                               (move-result-pseudo v6))",
                            false, true},
        EnumObservationCase{"InstanceOfEnum",
                            R"((instance-of v0 "Ljava/lang/Enum;")
                               (move-result-pseudo v6))",
                            false, true},
        EnumObservationCase{"EqualInteger", "(if-eq v0 v3 :done) (:done)",
                            false, true},
        EnumObservationCase{"EqualInterface",
                            R"((sget-object "LUser;.marker:LMarker;")
                               (move-result-pseudo-object v6)
                               (if-eq v0 v6 :done)
                               (:done))",
                            false, true},
        EnumObservationCase{"NotEqualObject", "(if-ne v4 v0 :done) (:done)",
                            false, true},
        EnumObservationCase{.name = "EqualDifferentEnums",
                            .instructions = "(if-eq v0 v2 :done) (:done)",
                            .bar_safe = false,
                            .baz_safe = false,
                            .bar_boxed_beside_enum_baz = true},
        EnumObservationCase{
            "EqualsInteger",
            R"((invoke-virtual (v0 v3) "LBar;.equals:(Ljava/lang/Object;)Z")
               (move-result v6))",
            false, true},
        EnumObservationCase{
            .name = "EqualsDifferentEnums",
            .instructions =
                R"((invoke-virtual (v0 v2) "LBar;.equals:(Ljava/lang/Object;)Z")
               (move-result v6))",
            .bar_safe = false,
            .baz_safe = false,
            .bar_boxed_beside_enum_baz = true},
        EnumObservationCase{.name = "EqualJoinedEnums",
                            .instructions = R"((if-eqz v5 :baz)
                               (move-object v6 v0)
                               (goto :compare)
                               (:baz)
                               (move-object v6 v2)
                               (:compare)
                               (if-ne v6 v1 :done)
                               (:done))",
                            .bar_safe = false,
                            .baz_safe = false,
                            .bar_boxed_beside_enum_baz = true},
        EnumObservationCase{"EqualUnloaded",
                            R"((sget-object "LUser;.unknown:LUnknownType;")
                               (move-result-pseudo-object v6)
                               (if-eq v0 v6 :done)
                               (:done))",
                            false, true},
        EnumObservationCase{"Monitor", "(monitor-enter v0) (monitor-exit v0)",
                            false, true},
        EnumObservationCase{
            "ObjectParameterInstanceOfInteger",
            R"((invoke-static (v0) "LUser;.isInteger:(Ljava/lang/Object;)Z"))",
            false, true},
        EnumObservationCase{"InstanceOfInteger",
                            R"((instance-of v0 "Ljava/lang/Integer;")
                               (move-result-pseudo v6))",
                            false, true},
        EnumObservationCase{"InstanceOfBar",
                            R"((instance-of v4 "LBar;")
                               (move-result-pseudo v6))",
                            false, true},
        EnumObservationCase{"ObjectParameterArrayInstanceOfIntegerArray",
                            R"((const v6 1)
                               (new-array v6 "[LBar;")
                               (move-result-pseudo-object v7)
                               (invoke-static (v7) "LUser;.isIntegerArray:(Ljava/lang/Object;)Z"))",
                            false, true},
        EnumObservationCase{"NestedArrayInstanceOfNestedNumberArray",
                            R"((const v6 1)
                               (new-array v6 "[[LBar;")
                               (move-result-pseudo-object v7)
                               (instance-of v7 "[[Ljava/lang/Number;")
                               (move-result-pseudo v6))",
                            false, true},
        EnumObservationCase{
            "GuavaEqual",
            R"((invoke-static (v0 v2) "Lcom/google/common/base/Objects;.equal:(Ljava/lang/Object;Ljava/lang/Object;)Z"))",
            false, false},
        EnumObservationCase{"EqualSameEnum", "(if-eq v0 v1 :done) (:done)",
                            true, true},
        EnumObservationCase{
            "EqualsSameEnum",
            R"((invoke-virtual (v0 v1) "LBar;.equals:(Ljava/lang/Object;)Z")
               (move-result v6))",
            true, true},
        EnumObservationCase{"EqualsString",
                            R"((const-string "RED")
               (move-result-pseudo-object v6)
               (invoke-virtual (v0 v6) "LBar;.equals:(Ljava/lang/Object;)Z")
               (move-result v6))",
                            true, true},
        EnumObservationCase{
            "ObjectParameterInstanceOfComparable",
            R"((invoke-static (v0) "LUser;.isComparable:(Ljava/lang/Object;)Z"))",
            true, true},
        EnumObservationCase{
            "ObjectParameterInstanceOfAppClass",
            R"((invoke-static (v0) "LUser;.isUser:(Ljava/lang/Object;)Z"))",
            true, true},
        EnumObservationCase{"InstanceOfComparable",
                            R"((instance-of v0 "Ljava/lang/Comparable;")
                               (move-result-pseudo v6))",
                            true, true},
        EnumObservationCase{"InstanceOfString",
                            R"((instance-of v0 "Ljava/lang/String;")
                               (move-result-pseudo v6))",
                            true, true},
        EnumObservationCase{"ObjectParameterArrayInstanceOfObjectArray",
                            R"((const v6 1)
                               (new-array v6 "[LBar;")
                               (move-result-pseudo-object v7)
                               (invoke-static (v7) "LUser;.isObjectArray:(Ljava/lang/Object;)Z"))",
                            true, true},
        EnumObservationCase{"EqualString",
                            R"((const-string "RED")
                               (move-result-pseudo-object v6)
                               (if-eq v0 v6 :done)
                               (:done))",
                            true, true},
        EnumObservationCase{"EnumArrayEqualObject",
                            R"((const v7 1)
                               (new-array v7 "[LBar;")
                               (move-result-pseudo-object v6)
                               (if-eq v6 v4 :done)
                               (:done))",
                            true, true},
        EnumObservationCase{"EqualObjectArray",
                            R"((const v7 1)
                               (new-array v7 "[Ljava/lang/Object;")
                               (move-result-pseudo-object v6)
                               (if-eq v0 v6 :done)
                               (:done))",
                            true, true},
        EnumObservationCase{"EqualEnumKeptForAnotherReason",
                            R"((instance-of v2 "Ljava/lang/Number;")
                               (move-result-pseudo v6)
                               (if-eq v0 v2 :done)
                               (:done))",
                            true, false},
        EnumObservationCase{"MergedSameEnumComparisons",
                            R"((if-eqz v5 :baz)
                               (move-object v6 v0)
                               (move-object v7 v1)
                               (goto :compare)
                               (:baz)
                               (move-object v6 v2)
                               (move-object v7 v2)
                               (:compare)
                               (if-ne v6 v7 :done)
                               (:done))",
                            true, true},
        EnumObservationCase{"MergedComparisonAfterMoves",
                            R"((if-eqz v5 :baz)
                               (move-object v6 v0)
                               (move-object v7 v1)
                               (goto :compare)
                               (:baz)
                               (move-object v6 v2)
                               (move-object v7 v2)
                               (:compare)
                               (move-object v8 v6)
                               (move-object v9 v7)
                               (if-ne v8 v9 :done)
                               (:done))",
                            true, true},
        EnumObservationCase{"NotEqualSameEnum", "(if-ne v0 v1 :done) (:done)",
                            true, true},
        EnumObservationCase{"EqualNull",
                            "(const v6 0) (if-eq v0 v6 :done) (:done)", true,
                            true},
        EnumObservationCase{"NullCheck", "(if-nez v0 :done) (:done)", true,
                            true}),
    [](const TestParamInfo<EnumObservationCase>& info) {
      return info.param.name;
    });

} // namespace

// `const-method-handle` and `const-method-type` cannot reach
// OptimizeEnumsPass, but the analysis takes each of their results to be an
// object, never null, even where a register held a candidate before.
TEST_F(OptimizeEnumsTest, methodHandleConstantsHaveObjectTypes) {
  auto code = assembler::ircode_from_string("((return-void))");
  code->build_cfg();
  optimize_enums::Config config(100);
  optimize_enums::EnumFixpointIterator analysis(code->cfg(), config);
  auto check = [&](const IRInstruction& insn) {
    optimize_enums::EnumTypeEnvironment env;
    env.set(RESULT_REGISTER,
            optimize_enums::EnumTypes(DexType::make_type("LBar;")));
    analysis.analyze_instruction(&insn, &env);
    EXPECT_EQ(env.get(RESULT_REGISTER),
              optimize_enums::EnumTypes(type::java_lang_Object()))
        << show(&insn);
  };
  IRInstruction handle(OPCODE_CONST_METHOD_HANDLE);
  check(handle);
  IRInstruction method_type(OPCODE_CONST_METHOD_TYPE);
  check(method_type);
}

// Java: `Bar.Y == handle.invoke()`, where the handle may return any object,
// like an unrelated Integer, so the comparison keeps Bar.
TEST_F(OptimizeEnumsTest, comparisonWithMethodHandleResultKeepsEnum) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.same:(Ljava/lang/invoke/MethodHandle;)Z"
      (
        (load-param-object v0)
        (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:()Ljava/lang/Object;" "()Ljava/lang/Object;")
        (move-result-object v1)
        (sget-object "LBar;.Y:LBar;")
        (move-result-pseudo-object v2)
        (if-eq v1 v2 :same)
        (const v3 0)
        (return v3)
        (:same)
        (const v3 1)
        (return v3)
      )
    )
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  EXPECT_EQ(rejection_reasons(scope, &config, bar_type),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageComparedByIdentity});
  EXPECT_EQ(config.candidate_enums.count(bar_type), 0u);
}

// The method entry is a path into the entry block even when a back edge
// enters it too: there, `v1` is the `Object` parameter, compared with Bar.
TEST_F(OptimizeEnumsTest, comparisonInEntryBlockWithBackEdgeKeepsEnum) {
  auto store = create_enum_store();
  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  uc.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.loop:(LBar;Ljava/lang/Object;)V"
      (
        (:top)
        (load-param-object v0)
        (load-param-object v1)
        (if-eq v0 v1 :out)
        (move-object v1 v0)
        (goto :top)
        (:out)
        (return-void)
      )
    )
  )"));
  store.add_classes({uc.create()});
  DexStoresVector stores({std::move(store)});
  auto scope = build_class_scope(stores);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  auto* bar_type = DexType::get_type("LBar;");
  optimize_enums::Config config(100);
  config.candidate_enums.insert(bar_type);
  EXPECT_EQ(rejection_reasons(scope, &config, bar_type),
            std::set<optimize_enums::UnsafeType>{
                optimize_enums::UnsafeType::kUsageComparedByIdentity});
  EXPECT_EQ(config.candidate_enums.count(bar_type), 0u);
}

TEST_F(OptimizeEnumsTest, objectParameterObservationsAreUnsafe) {
  struct ObservationCase {
    std::string instructions;
    bool second_param_safe;
  };
  const std::vector<ObservationCase> observations = {
      {R"((instance-of v0 "Ljava/lang/Number;") (move-result-pseudo v2))",
       true},
      {R"((instance-of v0 "Ljava/lang/Enum;") (move-result-pseudo v2))", true},
      {"(if-eq v0 v1 :done) (:done)", false},
      {"(if-ne v1 v0 :done) (:done)", false},
      {"(monitor-enter v0) (monitor-exit v0)", true},
      {R"((if-eqz v2 :other)
          (move-object v3 v0)
          (goto :observe)
          (:other)
          (move-object v3 v1)
          (:observe)
          (instance-of v3 "Ljava/lang/Number;")
          (move-result-pseudo v4))",
       false}};
  for (size_t i = 0; i < observations.size(); ++i) {
    const auto& [instructions, second_param_safe] = observations[i];
    SCOPED_TRACE(instructions);
    auto summary = get_summary(
        "(method (public static) \"LFoo;.observe" + std::to_string(i) +
        ":(Ljava/lang/Object;Ljava/lang/Object;Z)Ljava/lang/Object;\" "
        "((load-param-object v0) (load-param-object v1) (load-param v2) " +
        instructions + " (return-object v0)))");
    EXPECT_FALSE(summary.safe_params.contains(0));
    EXPECT_EQ(summary.returned_param, std::nullopt);
    EXPECT_EQ(summary.safe_params.contains(1), second_param_safe);
  }
}

TEST_F(OptimizeEnumsTest, objectParameterNullChecksRemainSafe) {
  auto summary = get_summary(R"(
    (method (public static) "LFoo;.nullCheck:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (move-object v1 v0)
        (if-eqz v1 :done)
        (const v2 0)
        (if-ne v1 v2 :done)
        (:done)
        (return-object v0)
      )
    )
  )");
  EXPECT_TRUE(summary.safe_params.contains(0));
  EXPECT_EQ(summary.returned_param, 0);
}

TEST_F(OptimizeEnumsTest, nullableParameterObservationsAreUnsafe) {
  const std::vector<std::string> observations = {
      "(if-eq v3 v1 :done) (:done)", "(monitor-enter v3) (monitor-exit v3)"};
  for (size_t i = 0; i < observations.size(); ++i) {
    auto summary = get_summary(
        "(method (public static) \"LFoo;.nullable" + std::to_string(i) +
        ":(Ljava/lang/Object;Ljava/lang/Object;Z)Ljava/lang/Object;\" "
        "((load-param-object v0) (load-param-object v1) (load-param v2) "
        "(if-eqz v2 :null) (move-object v3 v0) (goto :observe) "
        "(:null) (const v3 0) (:observe) " +
        observations[i] + " (return-object v0)))");
    EXPECT_FALSE(summary.safe_params.contains(0));
    EXPECT_EQ(summary.safe_params.contains(1), i != 0);
    EXPECT_EQ(summary.returned_param, std::nullopt);
  }
}

TEST_F(OptimizeEnumsTest, joinedNullChecksRemainSafe) {
  auto summary = get_summary(R"(
    (method (public static) "LFoo;.joinedNull:(Ljava/lang/Object;Z)Ljava/lang/Object;"
      ((load-param-object v0)
       (load-param v1)
       (if-eqz v1 :other)
       (const v2 0)
       (goto :compare)
       (:other)
       (const v2 0)
       (:compare)
       (if-eq v0 v2 :done)
       (:done)
       (return-object v0)))
  )");
  EXPECT_TRUE(summary.safe_params.contains(0));
  EXPECT_EQ(summary.returned_param, 0);
}

TEST_F(OptimizeEnumsTest, instanceParameterObservationUsesArgumentIndex) {
  auto summary = get_summary(R"(
    (method (public) "LFoo;.observeInstance:(Ljava/lang/Object;)Ljava/lang/Object;"
      ((load-param-object v4)
       (load-param-object v0)
       (move-object v1 v0)
       (instance-of v1 "Ljava/lang/Number;")
       (move-result-pseudo v2)
       (return-object v0)))
  )");
  EXPECT_TRUE(summary.safe_params.empty());
  EXPECT_EQ(summary.returned_param, std::nullopt);
}

// Runs OptimizeEnumsPass on `store` and returns the metrics it reports.
UnorderedMap<std::string, int64_t> run_optimize_enums(DexStore store) {
  DexStoresVector stores({std::move(store)});
  optimize_enums::OptimizeEnumsPass pass;
  Json::Value conf_obj = Json::nullValue;
  ConfigFiles conf(conf_obj);
  conf.parse_global_config();
  PassManager manager({&pass});
  manager.run_passes(stores, conf);
  for (const auto& info : manager.get_pass_info()) {
    if (info.pass == &pass) {
      return info.metrics;
    }
  }
  ADD_FAILURE() << "OptimizeEnumsPass did not run";
  return {};
}

// The opcodes of the method of `LOuter;` whose name starts with `prefix`.
std::vector<IROpcode> outer_method_opcodes(const std::string& prefix) {
  for (auto* m : type_class(DexType::get_type("LOuter;"))->get_all_methods()) {
    auto* code = m->get_code();
    if (code == nullptr || !m->str().starts_with(prefix)) {
      continue;
    }
    std::vector<IROpcode> opcodes;
    for (const auto& mie : InstructionIterable(*code)) {
      opcodes.push_back(mie.insn->opcode());
    }
    return opcodes;
  }
  return {};
}

void build_outer(DexStore& store,
                 const std::string& field,
                 const std::string& ctor,
                 const std::string& clinit,
                 const std::string& read) {
  ClassCreator cc(DexType::make_type("LOuter;"));
  cc.set_super(type::java_lang_Enum());
  cc.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);
  cc.add_field(
      DexField::make_field(field)->make_concrete(ACC_PUBLIC | ACC_FINAL));
  cc.add_field(DexField::make_field("LOuter;.$VALUES:[LOuter;")
                   ->make_concrete(ACC_PRIVATE | ACC_STATIC | ACC_FINAL |
                                   ACC_SYNTHETIC));
  cc.add_field(
      DexField::make_field("LOuter;.A:LOuter;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM));
  for (const auto& method : {ctor, clinit, read}) {
    cc.add_method(assembler::method_from_string(method));
  }
  auto* outer = cc.create();
  for (auto* m : outer->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  store.add_classes({outer});
}

// `<clinit>` reads a field of a constant before it assigns the constant, as in
// this Java-like view of hand-written or transformed code:
//
//   enum Outer {
//     A(5);
//     final int i;
//     Outer(int i) { this.i = i; }
//     static {
//       Outer a = new Outer("A", 0, 5);
//       use(a.i);
//       A = a;
//     }
//   }
//
// Once boxed, every use of the allocation reads the boxed constant, so no
// instance of `Outer` remains.
TEST_F(OptimizeEnumsTest, constantUsedBeforeItsAssignmentIsBoxed) {
  auto store = create_enum_store();
  build_outer(store, "LOuter;.i:I", R"(
    (method (private constructor) "LOuter;.<init>:(Ljava/lang/String;II)V"
      ((load-param-object v0)
       (load-param-object v1)
       (load-param v2)
       (load-param v3)
       (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
       (iput v3 v0 "LOuter;.i:I")
       (return-void)))
  )",
              R"(
    (method (public static) "LOuter;.<clinit>:()V"
      ((const-string "A")
       (move-result-pseudo-object v1)
       (const v2 0)
       (const v6 5)
       (new-instance "LOuter;")
       (move-result-pseudo-object v3)
       (invoke-direct (v3 v1 v2 v6) "LOuter;.<init>:(Ljava/lang/String;II)V")
       (iget v3 "LOuter;.i:I")
       (move-result-pseudo v7)
       (invoke-static (v7) "LOuter;.use:(I)V")
       (sput-object v3 "LOuter;.A:LOuter;")
       (const v4 1)
       (new-array v4 "[LOuter;")
       (move-result-pseudo-object v4)
       (aput-object v3 v4 v2)
       (sput-object v4 "LOuter;.$VALUES:[LOuter;")
       (return-void)))
  )",
              R"(
    (method (public static) "LOuter;.use:(I)V"
      ((load-param v0)
       (return-void)))
  )");
  run_optimize_enums(std::move(store));

  EXPECT_EQ(type_class(DexType::get_type("LOuter;"))->get_super_class(),
            type::java_lang_Object());
  EXPECT_THAT(outer_method_opcodes("<clinit>"),
              ::testing::Not(::testing::Contains(OPCODE_NEW_INSTANCE)));
}

// `<clinit>` keeps a copy of a constant's allocation in a second register and
// stores it in another static field, as a pass that reuses the register instead
// of reading `A` again may leave this Java code:
//
//   enum Outer {
//     A(5);
//     static final Outer ALIAS = A;
//     final int i;
//     Outer(int i) { this.i = i; }
//   }
//
// Once boxed, the copy holds the boxed constant too, so no instance of `Outer`
// remains.
TEST_F(OptimizeEnumsTest, constantCopiedToAnotherFieldIsBoxed) {
  auto store = create_enum_store();
  build_outer(store, "LOuter;.i:I", R"(
    (method (private constructor) "LOuter;.<init>:(Ljava/lang/String;II)V"
      ((load-param-object v0)
       (load-param-object v1)
       (load-param v2)
       (load-param v3)
       (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
       (iput v3 v0 "LOuter;.i:I")
       (return-void)))
  )",
              R"(
    (method (public static) "LOuter;.<clinit>:()V"
      ((const-string "A")
       (move-result-pseudo-object v1)
       (const v2 0)
       (const v6 5)
       (new-instance "LOuter;")
       (move-result-pseudo-object v3)
       (invoke-direct (v3 v1 v2 v6) "LOuter;.<init>:(Ljava/lang/String;II)V")
       (move-object v7 v3)
       (sput-object v3 "LOuter;.A:LOuter;")
       (sput-object v7 "LOuter;.ALIAS:LOuter;")
       (const v4 1)
       (new-array v4 "[LOuter;")
       (move-result-pseudo-object v4)
       (aput-object v3 v4 v2)
       (sput-object v4 "LOuter;.$VALUES:[LOuter;")
       (return-void)))
  )",
              R"(
    (method (public static) "LOuter;.alias:()LOuter;"
      ((sget-object "LOuter;.ALIAS:LOuter;")
       (move-result-pseudo-object v0)
       (return-object v0)))
  )");
  type_class(DexType::get_type("LOuter;"))
      ->add_field(DexField::make_field("LOuter;.ALIAS:LOuter;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  run_optimize_enums(std::move(store));

  EXPECT_EQ(type_class(DexType::get_type("LOuter;"))->get_super_class(),
            type::java_lang_Object());
  EXPECT_THAT(outer_method_opcodes("<clinit>"),
              ::testing::Not(::testing::Contains(OPCODE_NEW_INSTANCE)));
}

// A switch-map class whose <clinit> fills a second table that it stores in no
// field, as after RemoveUnusedFieldsPass removed the field of a table nothing
// reads: no switch can read that table, so collecting the switch cases skips
// it, and a switch over the table that is stored is still unmapped.
TEST_F(OptimizeEnumsTest, switchMapArrayStoredInNoFieldIsSkipped) {
  DexStoresVector stores({create_enum_store()});
  // create_enum_store declares Enum.ordinal as a constructor; the switch-map
  // matcher resolves it as a virtual method, so declare a virtual one.
  auto* enum_cls = type_class(type::java_lang_Enum());
  auto* ordinal = dynamic_cast<DexMethod*>(
      DexMethod::get_method("Ljava/lang/Enum;.ordinal:()I"));
  enum_cls->remove_method(ordinal);
  ordinal->set_access(ACC_PUBLIC | ACC_FINAL);
  ordinal->set_virtual(true);
  enum_cls->add_method(ordinal);

  auto* mode = make_kotlin_enum("LMode;", "(return-void)");
  stores[0].add_classes({mode});

  ClassCreator gc(DexType::make_type("LFoo$1;"));
  gc.set_super(type::java_lang_Object());
  gc.set_access(ACC_FINAL | ACC_SYNTHETIC);
  auto* table = dynamic_cast<DexField*>(
      DexField::make_field("LFoo$1;.$SwitchMap$Mode:[I"));
  table->make_concrete(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC);
  gc.add_field(table);
  gc.add_method(assembler::method_from_string(R"(
    (method (static constructor) "LFoo$1;.<clinit>:()V"
     (
      (const v0 2)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (sput-object v1 "LFoo$1;.$SwitchMap$Mode:[I")
      (sget-object "LMode;.A:LMode;")
      (move-result-pseudo-object v2)
      (invoke-virtual (v2) "Ljava/lang/Enum;.ordinal:()I")
      (move-result v3)
      (const v4 1)
      (aput v4 v1 v3)
      (const v0 2)
      (new-array v0 "[I")
      (move-result-pseudo-object v5)
      (sget-object "LMode;.A:LMode;")
      (move-result-pseudo-object v2)
      (invoke-virtual (v2) "Ljava/lang/Enum;.ordinal:()I")
      (move-result v3)
      (const v4 1)
      (aput v4 v5 v3)
      (return-void)
     )
    )
  )"));
  auto* generated = gc.create();
  generated->get_clinit()->get_code()->build_cfg();
  stores[0].add_classes({generated});

  ClassCreator uc(DexType::make_type("LUser;"));
  uc.set_super(type::java_lang_Object());
  uc.set_access(ACC_PUBLIC);
  auto* pick = assembler::method_from_string(R"(
    (method (public static) "LUser;.pick:(LMode;)I"
      (
        (load-param-object v0)
        (sget-object "LFoo$1;.$SwitchMap$Mode:[I")
        (move-result-pseudo-object v1)
        (invoke-virtual (v0) "Ljava/lang/Enum;.ordinal:()I")
        (move-result v2)
        (aget v1 v2)
        (move-result-pseudo v3)
        (switch v3 (:case1))
        (const v4 30)
        (return v4)
        (:case1 1)
        (const v4 10)
        (return v4)
      )
    )
  )");
  uc.add_method(pick);
  pick->get_code()->build_cfg();
  stores[0].add_classes({uc.create()});

  run_optimize_enums_with_entries(stores);

  EXPECT_EQ(mode->get_super_class(), type::java_lang_Object());
  // The switch map is unmapped: the case that was 1 is now A's ordinal, 0.
  cfg::ScopedCFG cfg(pick->get_code());
  std::set<int32_t> cases;
  for (auto* block : cfg->blocks()) {
    if (block->branchingness() != opcode::BRANCH_SWITCH) {
      continue;
    }
    for (auto* edge : block->succs()) {
      if (edge->case_key()) {
        cases.insert(*edge->case_key());
      }
    }
  }
  EXPECT_EQ(cases, std::set<int32_t>{0});
}
