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
#include "DexCallSite.h"
#include "EnumClinitAnalysis.h"
#include "EnumConfig.h"
#include "EnumUpcastAnalysis.h"
#include "IRAssembler.h"
#include "InlineEnumValues.h"
#include "OptimizeEnums.h"
#include "OptimizeEnumsUnsafeType.h"
#include "RedexTest.h"
#include "RemoveNullcheckStringArg.h"
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
    (invoke-polymorphic (v3) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;")
  )");
  auto attributes =
      optimize_enums::analyze_enum_clinit(cls, /*support_kt_19_enum_entries*/
                                          false);
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
          ->set_callsite(new DexCallSite(
              nullptr, DexString::make_string("run"),
              DexProto::make_proto(type::_void(),
                                   DexTypeList::make_type_list({})),
              {}));
    }
  }
  auto attributes =
      optimize_enums::analyze_enum_clinit(cls, /*support_kt_19_enum_entries*/
                                          false);
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
      (invoke-polymorphic (v3) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;")
      (return-void)
    )
  )"));
  ctor->get_code()->build_cfg();
  const auto before = show(ctor->get_code()->cfg());
  for (size_t run = 0; run < 2; ++run) {
    const auto attributes = optimize_enums::analyze_enum_clinit(cls, false);
    EXPECT_TRUE(attributes.m_constants_map.empty());
    EXPECT_EQ(show(ctor->get_code()->cfg()), before);
  }
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
