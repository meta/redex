/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <optional>

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "Creators.h"
#include "DexLimits.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MethodProfiles.h"
#include "MethodSplitter.h"
#include "MethodSplittingTestUtil.h"
#include "RedexTest.h"
#include "Show.h"
#include "SplittableClosures.h"
#include "TypeUtil.h"

namespace {

// A Kotlin-style parameter check: the null arm builds and throws an exception
// with two runtime calls (the allocation and the constructor call).
constexpr const char* kCheck = R"(
  (
    (load-param-object v0)
    (if-nez v0 :ok)
    (new-instance "Ljava/lang/NullPointerException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
    (throw v1)
    (:ok)
    (return-void)
  )
)";

// Two throwing suffixes in one method: a null arm for each parameter.
constexpr const char* kTwoChecks = R"(
  (
    (load-param-object v0)
    (load-param-object v1)
    (if-nez v0 :ok1)
    (new-instance "Ljava/lang/NullPointerException;")
    (move-result-pseudo-object v2)
    (invoke-direct (v2) "Ljava/lang/NullPointerException;.<init>:()V")
    (throw v2)
    (:ok1)
    (if-nez v1 :ok2)
    (new-instance "Ljava/lang/IllegalStateException;")
    (move-result-pseudo-object v2)
    (invoke-direct (v2) "Ljava/lang/IllegalStateException;.<init>:()V")
    (throw v2)
    (:ok2)
    (return-void)
  )
)";

// Enough compiled copies for any of the tails below to pay for its split.
constexpr size_t kManyCopies = 100;

class RareSuffixSelectionTest : public RedexTest {
 public:
  RareSuffixSelectionTest() {
    create_object_class();
    m_cls = std::make_unique<ClassCreator>(DexType::make_type("LFoo;"));
    m_cls->set_super(type::java_lang_Object());
  }

  DexMethod* add_method(const std::string& name_and_proto,
                        const std::string& code,
                        DexAccessFlags access = ACC_PUBLIC | ACC_STATIC) {
    bool is_virtual =
        (access & (ACC_STATIC | ACC_PRIVATE | ACC_CONSTRUCTOR)) == 0;
    auto* method = DexMethod::make_method("LFoo;." + name_and_proto)
                       ->make_concrete(access, is_virtual);
    method->set_code(assembler::ircode_from_string(code));
    method->set_deobfuscated_name(show(method));
    m_cls->add_method(method);
    return method;
  }

  struct Result {
    size_t selected_methods{0};
    size_t split_methods{0};
    size_t too_few_runtime_calls{0};
    size_t not_splittable{0};
    method_splitting_impl::FateSnapshot fates;
  };

  // Selects the rare suffixes of `methods`, given `copies(method)` compiled
  // copies of each, under `m_config`, splits them in a dex with room
  // for `room` more method refs (no limit by default), and gives the methods
  // not split their code back.
  Result select_and_split(
      const std::vector<DexMethod*>& methods,
      const std::function<size_t(const DexMethod*)>& copies =
          [](const DexMethod*) { return kManyCopies; },
      std::optional<size_t> room = std::nullopt) {
    for (auto* m : methods) {
      m->get_code()->build_cfg();
    }
    m_created = m_cls->create();
    DexStoresVector stores;
    stores.emplace_back("classes");
    stores.front().add_classes({m_created});
    size_t reserved_mrefs = 0;
    if (room) {
      UnorderedSet<DexMethodRef*> refs;
      m_created->gather_methods(refs);
      reserved_mrefs = kMaxMethodRefs - refs.size() - *room;
    }
    auto env = method_splitting_test::split_environment(
        stores, /* normal_primary_dex */ true, /* min_sdk */ 21,
        reserved_mrefs);
    Result result;
    method_splitting_impl::RareSuffixSelectionStats selection_stats;
    method_splitting_impl::Stats stats;
    method_splitting_impl::RareSuffixSelection selection(
        methods, m_config, /* min_suffix_runtime_calls */ 2, copies,
        env.store_ref_checkers, stats, selection_stats);
    result.too_few_runtime_calls = selection_stats.too_few_runtime_calls;
    result.not_splittable = selection_stats.not_splittable;
    result.selected_methods = selection.selected_method_count();
    method_profiles::MethodProfiles method_profiles;
    auto selected = method_splitting_impl::split_selected_closures(
        stores, env, selection.splittable_closures(), "$rare_suffix$",
        method_profiles, &stats);
    std::move(selection).finish(selected.split_methods);
    result.split_methods = selected.split_methods.size();
    result.fates = stats.snapshot().suffix_fates;
    // Every evaluated suffix is recorded once, at its final fate.
    EXPECT_EQ(result.fates.recorded(), result.fates.candidates);
    return result;
  }

  // The rare-suffix splits made in the class, in order.
  std::vector<DexMethod*> splits() const {
    std::vector<DexMethod*> result;
    for (auto* d : m_created->get_dmethods()) {
      if (d->str().find("$rare_suffix$") != std::string_view::npos) {
        result.push_back(d);
      }
    }
    return result;
  }

  static bool calls(const DexMethod* caller, const DexMethodRef* callee) {
    auto& cfg = const_cast<DexMethod*>(caller)->get_code()->cfg();
    for (const auto& mie : cfg::InstructionIterable(cfg)) {
      if (mie.insn->has_method() && mie.insn->get_method() == callee) {
        return true;
      }
    }
    return false;
  }

  std::unique_ptr<ClassCreator> m_cls;
  DexClass* m_created{nullptr};
  method_splitting_impl::Config m_config;
};

TEST_F(RareSuffixSelectionTest, selectsTheThrowingSuffix) {
  auto* check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  auto result = select_and_split({check});
  EXPECT_EQ(result.split_methods, 1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_EQ(all[0]->str(), "check$split$cold$rare_suffix$0");
  EXPECT_TRUE(calls(check, all[0]));
}

TEST_F(RareSuffixSelectionTest, countsUnreachableAsACall) {
  // Kotlin's `x!!`: a call of a throw helper that never returns, after which
  // Redex knows the code is unreachable. The `unreachable` is lowered to a
  // call of `UnreachableException.createAndThrow`, so the tail makes two calls.
  auto* bang = add_method("bang:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (if-nez v0 :ok)
      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwJavaNpe:()V")
      (unreachable v1)
      (throw v1)
      (:ok)
      (return-void)
    )
  )");
  EXPECT_EQ(select_and_split({bang}).split_methods, 1);
}

TEST_F(RareSuffixSelectionTest, countsUnreachableAtItsLoweredSize) {
  // The `unreachable` after the throw helper is lowered to a call and a
  // move-result: each compiled copy loses 8 code units for a 4-unit
  // launchpad, so three copies pay for the 32 the dex pays once. Sized as the
  // 1-unit `unreachable`, the tail would save only 1 code unit per copy.
  auto* bang = add_method("bang:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (if-nez v0 :ok)
      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwJavaNpe:()V")
      (unreachable v1)
      (throw v1)
      (:ok)
      (return-void)
    )
  )");
  EXPECT_EQ(select_and_split({bang}, [](const DexMethod*) { return 3; })
                .split_methods,
            1);
}

TEST_F(RareSuffixSelectionTest, skipsCheapTailsAndLeavesTheirCodeAlone) {
  // Like `ResultKt.throwOnFailure`: the throwing part only reads a field and
  // throws, which one call would not make smaller.
  auto* cheap = add_method("cheap:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (instance-of v0 "LFoo$Failure;")
      (move-result-pseudo v1)
      (if-eqz v1 :ok)
      (check-cast v0 "LFoo$Failure;")
      (move-result-pseudo-object v0)
      (iget-object v0 "LFoo$Failure;.exception:Ljava/lang/Throwable;")
      (move-result-pseudo-object v0)
      (throw v0)
      (:ok)
      (return-void)
    )
  )");
  ClassCreator failure(DexType::make_type("LFoo$Failure;"));
  failure.set_super(type::java_lang_Object());
  failure.add_field(
      DexField::make_field("LFoo$Failure;.exception:Ljava/lang/Throwable;")
          ->make_concrete(ACC_PUBLIC));
  failure.create();
  auto s_expr_before = assembler::to_s_expr(cheap->get_code());
  auto* code_before = cheap->get_code();
  auto result = select_and_split({cheap});
  EXPECT_EQ(result.selected_methods, 0);
  EXPECT_EQ(result.too_few_runtime_calls, 1);
  EXPECT_EQ(cheap->get_code(), code_before);
  cheap->get_code()->clear_cfg();
  EXPECT_EQ(assembler::to_s_expr(cheap->get_code()), s_expr_before);
}

TEST_F(RareSuffixSelectionTest, splitsOnlyWhenItsCompiledCopiesPayForTheSplit) {
  // Each compiled copy loses the 6-unit throwing part for a 4-unit launchpad,
  // 2 code units weighed at a `net_oat_weight` of 4. The dex pays for the split
  // once: the launchpad and the split method's metadata, 32 code units. Four
  // copies only break even; five pay.
  m_config.net_oat_weight = 4;
  auto* four = add_method("four:(Ljava/lang/Object;)V", kCheck);
  auto* five = add_method("five:(Ljava/lang/Object;)V", kCheck);
  auto result =
      select_and_split({four, five}, [&](const DexMethod* m) -> size_t {
        return m == five ? 5 : 4;
      });
  EXPECT_EQ(result.split_methods, 1);
  EXPECT_EQ(
      result.fates
          [method_splitting_impl::CandidateFate::Evaluation_NetNotPositive],
      1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_EQ(all[0]->str(), "five$split$cold$rare_suffix$0");
}

TEST_F(RareSuffixSelectionTest, countsOnlyTheCodeThatLeavesTheMethod) {
  // The throwing suffix entered after `side1()` shares `side2(); throw` with
  // the `flag != 0` branch, which stays in the method. Splitting it would
  // remove only the `side1()` call from the compiled copy while copying the
  // shared code into the split. Credited with all of its code, it would pay at
  // this weight; the shared suffix on its own does not.
  m_config.net_oat_weight = 6;
  add_method("side1:()V", "((return-void))");
  add_method("side2:()V", "((return-void))");
  auto* shared = add_method("shared:(Ljava/lang/Object;I)V", R"(
    (
      (load-param-object v0)
      (load-param v1)
      (if-nez v0 :other)
      (invoke-static () "LFoo;.side1:()V")
      (goto :shared)
      (:other)
      (if-eqz v1 :ok)
      (:shared)
      (invoke-static () "LFoo;.side2:()V")
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v2)
      (:ok)
      (return-void)
    )
  )");
  auto result = select_and_split({shared}, [](const DexMethod*) { return 1; });
  EXPECT_EQ(result.split_methods, 0);
  EXPECT_TRUE(splits().empty());
}

TEST_F(RareSuffixSelectionTest, namesAColdTailOfAHotMethodHotCold) {
  // The method runs, its throwing arm does not: the split is cold code entered
  // from hot code, as MethodSplittingPass classifies it.
  auto* hot = add_method("hot:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 0 (1.0 1.0))
      (if-nez v0 :ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 1 (0.0 0.0))
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 2 (1.0 1.0))
      (return-void)
    )
  )");
  EXPECT_EQ(select_and_split({hot}).split_methods, 1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_EQ(all[0]->str(), "hot$split$hot_cold$rare_suffix$0");
}

TEST_F(RareSuffixSelectionTest, splitsAHotTailWithEnoughCopiesAsHot) {
  // The profile says the throwing arm runs. A Hot split is compiled, so one
  // copy of the arm stays compiled, and each other copy saves it.
  auto* hot = add_method("hot:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 0 (1.0 1.0))
      (if-nez v0 :ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 2 (1.0 1.0))
      (return-void)
    )
  )");
  EXPECT_EQ(select_and_split({hot}).split_methods, 1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_EQ(all[0]->str(), "hot$split$hot$rare_suffix$0");
}

TEST_F(RareSuffixSelectionTest, leavesAHotTailWithOneCompiledCopy) {
  // With one compiled copy, a Hot split's code stays compiled in the split,
  // and the split saves nothing.
  auto* hot = add_method("hot:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 0 (1.0 1.0))
      (if-nez v0 :ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (.src_block "LFoo;.hot:(Ljava/lang/Object;)V" 2 (1.0 1.0))
      (return-void)
    )
  )");
  auto result = select_and_split({hot}, [](const DexMethod*) { return 1; });
  EXPECT_EQ(result.split_methods, 0);
  EXPECT_EQ(
      result.fates
          [method_splitting_impl::CandidateFate::Evaluation_NetNotPositive],
      1);
}

TEST_F(RareSuffixSelectionTest,
       skipsConstructorTailsBeforeTheReceiverIsInitialized) {
  // A Kotlin constructor that checks a parameter before calling the superclass
  // constructor: splitting the throwing arm would leave a path that returns
  // without initializing the receiver.
  auto* init = add_method("<init>:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (if-nez v1 :ok)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v2)
      (:ok)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )",
                          ACC_PUBLIC | ACC_CONSTRUCTOR);
  auto result = select_and_split({init});
  EXPECT_EQ(result.split_methods, 0);
  EXPECT_EQ(result.not_splittable, 1);
  EXPECT_EQ(result.fates[method_splitting_impl::CandidateFate::
                             Evaluation_ReceiverUninitialized],
            1);
}

TEST_F(RareSuffixSelectionTest, restoresSelectedMethodsThatWereNotSplit) {
  // A selected method that is not split, for example because its dex ran out
  // of method refs, gets its original code back.
  auto* check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  auto* cls = m_cls->create();
  check->get_code()->build_cfg();
  auto* original = check->get_code();
  DexStoresVector stores;
  stores.emplace_back("classes");
  stores.front().add_classes({cls});
  auto env = method_splitting_test::split_environment(
      stores, /* normal_primary_dex */ true);
  method_splitting_impl::RareSuffixSelectionStats selection_stats;
  method_splitting_impl::Stats stats;
  {
    method_splitting_impl::RareSuffixSelection selection(
        {check}, method_splitting_impl::Config{},
        /* min_suffix_runtime_calls */ 2,
        /* compiled_copies */ [](auto*) { return kManyCopies; },
        env.store_ref_checkers, stats, selection_stats);
    ASSERT_EQ(selection.selected_method_count(), 1);
    EXPECT_NE(check->get_code(), original);
  }
  EXPECT_EQ(check->get_code(), original);
}

TEST_F(RareSuffixSelectionTest, keepsSplitsMadeBeforeTheDexIsFull) {
  auto* a = add_method("a:(Ljava/lang/Object;)V", kCheck);
  auto* b = add_method("b:(Ljava/lang/Object;)V", kCheck);
  auto result = select_and_split(
      {a, b}, [](const DexMethod*) { return kManyCopies; }, /* room */ 1);
  EXPECT_EQ(result.split_methods, 1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_TRUE(calls(a, all[0]) || calls(b, all[0]));
}

TEST_F(RareSuffixSelectionTest, keepsAPartialSplitWhenTheDexIsFull) {
  auto* m = add_method("m:(Ljava/lang/Object;Ljava/lang/Object;)V", kTwoChecks);
  auto result = select_and_split(
      {m}, [](const DexMethod*) { return kManyCopies; }, /* room */ 1);
  EXPECT_EQ(result.split_methods, 1);
  auto all = splits();
  ASSERT_EQ(all.size(), 1);
  EXPECT_TRUE(calls(m, all[0]));
}

} // namespace
