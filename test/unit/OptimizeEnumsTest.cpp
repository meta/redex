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
#include <mutex>
#include <set>

#include "ControlFlow.h"
#include "Creators.h"
#include "EnumClinitAnalysis.h"
#include "EnumConfig.h"
#include "EnumUpcastAnalysis.h"
#include "IRAssembler.h"
#include "OptimizeEnums.h"
#include "OptimizeEnumsUnsafeType.h"
#include "RedexTest.h"
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
  ec.set_super(type::java_lang_Object());
  ec.set_access(ACC_PUBLIC);
  auto* enums = ec.create();

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
  ic.set_super(type::java_lang_Object());
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
  return store;
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

    std::mutex reasons_mutex;
    std::set<optimize_enums::UnsafeType> bar_reasons;
    auto reject_fn = [&](const DexType* type, optimize_enums::UnsafeType u) {
      if (type != bar_type) {
        return;
      }
      std::lock_guard<std::mutex> lock(reasons_mutex);
      bar_reasons.insert(u);
    };

    optimize_enums::reject_unsafe_enums(scope, &config, reject_fn);

    EXPECT_EQ(bar_reasons, kExpectedReasons) << "iteration " << iteration;
    // The enum is rejected -- outcome is unchanged by the determinism fix.
    EXPECT_EQ(config.candidate_enums.count_unsafe(bar_type), 0u)
        << "iteration " << iteration;
  }
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

/* Create an enum with constants A and B whose <clinit> passes the given
ordinals to the constructor, like this hand-written Java-like code:

enum E {
  A("A", 0), B("B", ordinal_b);  // javac would pass ordinal 1 for B
}
*/
DexClass* create_two_constant_enum(const std::string& name, int ordinal_b) {
  auto with_names = [&](std::string s_expr) {
    boost::replace_all(s_expr, "LE;", name);
    boost::replace_all(s_expr, "ORDINAL_B", std::to_string(ordinal_b));
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
  for (auto* m : cls->get_all_methods()) {
    m->get_code()->build_cfg();
  }
  return cls;
}

// Ordinals of an enum with N constants must be exactly 0..N-1. An ordinal of
// N is out of range and must reject the enum.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsOrdinalEqualToConstantCount) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LOrdinalTooLarge;", 2);
  auto attributes =
      optimize_enums::analyze_enum_clinit(cls, /*support_kt_19_enum_entries*/
                                          false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// A negative ordinal is out of range too and must reject the enum rather than
// abort Redex.
TEST_F(OptimizeEnumsTest, clinitAnalysisRejectsNegativeOrdinal) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LNegativeOrdinal;", -1);
  auto attributes =
      optimize_enums::analyze_enum_clinit(cls, /*support_kt_19_enum_entries*/
                                          false);
  EXPECT_TRUE(attributes.m_constants_map.empty());
}

// The same clinit with in-range ordinals is accepted, so the rejections above
// come from the ordinals alone.
TEST_F(OptimizeEnumsTest, clinitAnalysisAcceptsConsecutiveOrdinals) {
  auto store = create_enum_store();
  auto* cls = create_two_constant_enum("LConsecutiveOrdinals;", 1);
  auto attributes =
      optimize_enums::analyze_enum_clinit(cls, /*support_kt_19_enum_entries*/
                                          false);
  EXPECT_EQ(attributes.m_constants_map.size(), 2);
}
