/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MaterializeNullChecksPass.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"
#include "RareSuffixMethodSplittingPass.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"
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

class RareSuffixMethodSplittingTest : public RedexTest {
 public:
  RareSuffixMethodSplittingTest() {
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

  // Adds `count` static callers of `callee` that the baseline profile compiles
  // unless `compiled` is false.
  void add_callers(DexMethod* callee,
                   size_t count,
                   const std::string& args = "(const v0 0)",
                   bool compiled = true) {
    for (size_t i = 0; i < count; i++) {
      auto* caller =
          add_method("caller" + std::to_string(m_callers++) + ":()V",
                     "(" + args + " (invoke-" +
                         std::string(is_static(callee) ? "static" : "direct") +
                         " (v0) \"" + show(callee) + "\") (return-void))");
      if (compiled) {
        m_compiled.push_back(caller);
      }
    }
  }

  UnorderedMap<std::string, int64_t> run(bool enabled = true,
                                         bool materialize = false) {
    Json::Value json_conf;
    json_conf["RareSuffixMethodSplittingPass"]["enabled"] = enabled;
    json_conf["RareSuffixMethodSplittingPass"]["net_oat_weight"] =
        m_net_oat_weight;
    if (!m_call_counts.empty()) {
      json_conf["baseline_profile"]["default"]["deep_data_interaction_config"]
               [method_profiles::COLD_START]["name"] =
                   method_profiles::COLD_START;
    }
    m_conf = std::make_unique<ConfigFiles>(json_conf);
    auto& conf = *m_conf;
    conf.parse_global_config();
    UnorderedMap<const DexMethodRef*, method_profiles::Stats> hot;
    for (auto* m : m_compiled) {
      hot[m] = method_profiles::Stats{};
    }
    if (m_call_counts.empty()) {
      conf.get_method_profiles() =
          method_profiles::MethodProfiles::initialize("manual_hot", hot);
    } else {
      // A cold-start profile that reports call counts, and compiles every
      // method it has.
      for (auto& [m, stats] : UnorderedIterable(hot)) {
        stats.appear_percent = 100;
        stats.call_count = 1;
      }
      for (const auto& [m, call_count] : m_call_counts) {
        hot[m].call_count = call_count;
      }
      conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
          method_profiles::COLD_START, hot);
    }

    RareSuffixMethodSplittingPass pass;
    MaterializeNullChecksPass materialize_pass;
    std::vector<Pass*> passes{&pass};
    if (materialize) {
      passes.push_back(&materialize_pass);
    }
    PassManager manager(passes, conf, RedexOptions{});
    DexStore store("classes");
    store.add_classes({m_cls->create()});
    for (auto* cls : m_extra_classes) {
      store.add_classes({cls});
    }
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    manager.run_passes(stores, conf);
    for (const auto& info : manager.get_pass_info()) {
      if (info.pass == &pass) {
        return info.metrics;
      }
    }
    return {};
  }

  static DexMethod* helper(const DexMethod* m, size_t index = 0) {
    std::string base = method::is_init(m) ? "$init$" : std::string(m->str());
    for (auto* d : type_class(m->get_class())->get_dmethods()) {
      if (d->str() ==
          base + "$split$cold$rare_suffix$" + std::to_string(index)) {
        return d;
      }
    }
    return nullptr;
  }

  // Every instruction of `method`, whether or not its CFG is built (the pass
  // manager clears CFGs after the last pass).
  static std::vector<IRInstruction*> insns(const DexMethod* method) {
    std::vector<IRInstruction*> result;
    auto* code = const_cast<DexMethod*>(method)->get_code();
    if (code->cfg_built()) {
      for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
        result.push_back(mie.insn);
      }
    } else {
      for (const auto& mie : InstructionIterable(*code)) {
        result.push_back(mie.insn);
      }
    }
    return result;
  }

  static bool calls(const DexMethod* caller, const DexMethodRef* callee) {
    for (auto* insn : insns(caller)) {
      if (insn->has_method() && insn->get_method() == callee) {
        return true;
      }
    }
    return false;
  }

  static bool has_opcode(const DexMethod* method, IROpcode op) {
    auto* code = const_cast<DexMethod*>(method)->get_code();
    return (code->cfg_built() ? method::count_opcode_of_types(code->cfg(), {op})
                              : method::count_opcode_of_types(*code, {op})) > 0;
  }

  static bool returns(const DexMethod* method) {
    for (auto* insn : insns(method)) {
      if (opcode::is_a_return(insn->opcode())) {
        return true;
      }
    }
    return false;
  }

  std::unique_ptr<ClassCreator> m_cls;
  std::unique_ptr<ConfigFiles> m_conf;
  // Most tests check what is split, not whether it pays.
  double m_net_oat_weight{1000.0};
  std::vector<DexClass*> m_extra_classes;
  std::vector<DexMethod*> m_compiled;
  // Call counts the profile reports for these methods.
  std::vector<std::pair<DexMethod*, double>> m_call_counts;
  size_t m_callers{0};
};

TEST_F(RareSuffixMethodSplittingTest, splitsTheThrowingSuffix) {
  auto* check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  add_callers(check, 2);
  auto metrics = run();
  auto* split = helper(check);
  ASSERT_NE(split, nullptr);
  EXPECT_TRUE(is_static(split));
  EXPECT_TRUE(calls(check, split));
  EXPECT_FALSE(has_opcode(check, OPCODE_NEW_INSTANCE));
  EXPECT_TRUE(has_opcode(split, OPCODE_NEW_INSTANCE));
  EXPECT_TRUE(has_opcode(split, OPCODE_THROW));
  EXPECT_FALSE(returns(split));
  EXPECT_EQ(metrics["split_count"], 1);
  EXPECT_EQ(metrics["split_compiled_call_sites"], 2);
}

TEST_F(RareSuffixMethodSplittingTest,
       countsCallsOfFinalMethodsThatImplementInterfaces) {
  // `check` implements `Checker.check`, so another class could implement the
  // interface method too, but an invoke-virtual of the final `Foo.check` can
  // only reach this method.
  auto* iface_type = DexType::make_type("LChecker;");
  ClassCreator iface(iface_type);
  iface.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  iface.set_super(type::java_lang_Object());
  iface.add_method(
      DexMethod::make_method("LChecker;.check:(Ljava/lang/Object;)V")
          ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, true));
  m_extra_classes.push_back(iface.create());
  m_cls->add_interface(iface_type);
  auto* check = add_method("check:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v2)
      (load-param-object v0)
      (if-nez v0 :ok)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (return-void)
    )
  )",
                           ACC_PUBLIC | ACC_FINAL);
  for (int i = 0; i < 2; i++) {
    m_compiled.push_back(
        add_method("caller" + std::to_string(m_callers++) + ":(LFoo;)V", R"(
      (
        (load-param-object v1)
        (const v0 0)
        (invoke-virtual (v1 v0) "LFoo;.check:(Ljava/lang/Object;)V")
        (return-void)
      )
    )"));
  }
  run();
  EXPECT_NE(helper(check), nullptr);
}

TEST_F(RareSuffixMethodSplittingTest,
       countsNoCallSitesInCallersArtDoesNotInlineInto) {
  // ART does not inline into a caller with more instructions than its budget,
  // so calls from such callers do not count as inlined copies.
  auto* check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  std::string large = "(const v0 0)";
  for (size_t i = 0; i <= never_inline_analysis::kDefaultMaxCallerInstructions;
       i++) {
    large += " (const v1 1)";
  }
  add_callers(check, 2, large);
  auto metrics = run();
  EXPECT_EQ(helper(check), nullptr);
  EXPECT_EQ(metrics["callers_too_many_instructions"], 2);
}

TEST_F(RareSuffixMethodSplittingTest, reportsTheTopSplitMethods) {
  auto* rare = add_method("rare:(Ljava/lang/Object;)V", kCheck);
  add_callers(rare, 3);
  auto* frequent = add_method("frequent:(Ljava/lang/Object;)V", kCheck);
  add_callers(frequent, 2);
  m_call_counts = {{rare, 5}, {frequent, 100}};
  auto metrics = run();
  const std::string rare_name = "cold_LFoo;.rare:(Ljava/lang/Object;)V";
  const std::string frequent_name = "cold_LFoo;.frequent:(Ljava/lang/Object;)V";
  EXPECT_EQ(metrics["top_split_by_call_count_0_" + frequent_name], 100);
  EXPECT_EQ(metrics["top_split_by_call_count_1_" + rare_name], 5);
  EXPECT_EQ(metrics["top_split_by_compiled_call_sites_0_" + rare_name], 3);
  EXPECT_EQ(metrics["top_split_by_compiled_call_sites_1_" + frequent_name], 2);
  EXPECT_GT(metrics["top_split_by_call_count_0_" + frequent_name +
                    "_split_code_units"],
            0);
}

TEST_F(RareSuffixMethodSplittingTest, isOffByDefault) {
  auto* check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  add_callers(check, 2);
  run(/* enabled */ false);
  EXPECT_EQ(helper(check), nullptr);
}

TEST_F(RareSuffixMethodSplittingTest, skipsMethodsWithFewCompiledCallSites) {
  auto* once = add_method("once:(Ljava/lang/Object;)V", kCheck);
  add_callers(once, 1);
  auto* cold = add_method("cold:(Ljava/lang/Object;)V", kCheck);
  add_callers(cold, 2, "(const v0 0)", /* compiled */ false);
  auto metrics = run();
  EXPECT_EQ(helper(once), nullptr);
  EXPECT_EQ(helper(cold), nullptr);
  EXPECT_EQ(metrics["split_count"], 0);
}

TEST_F(RareSuffixMethodSplittingTest, skipsMethodsTooLargeForArtToInline) {
  std::string padding;
  for (int i = 0; i < 12; i++) {
    padding += "(const-wide v2 1234567890123)\n";
  }
  auto* large = add_method("large:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
    )" + padding + R"(
      (if-nez v0 :ok)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (return-void)
    )
  )");
  add_callers(large, 2);
  auto metrics = run();
  EXPECT_EQ(helper(large), nullptr);
  EXPECT_EQ(metrics["rejected_too_large"], 1);
}

TEST_F(RareSuffixMethodSplittingTest, sizesUnreachableAsLowered) {
  // Redex's estimate puts this method under the inline limit, but `unreachable`
  // is lowered to a call and a move-result, which put it over.
  auto* large = add_method("large:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (const-wide v2 1234567890123)
      (const-wide v2 1234567890123)
      (const-wide v2 1234567890123)
      (const-wide v2 1234567890123)
      (const v4 1)
      (if-nez v0 :ok)
      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwJavaNpe:()V")
      (unreachable v1)
      (throw v1)
      (:ok)
      (return-void)
    )
  )");
  add_callers(large, 2);
  auto metrics = run();
  EXPECT_EQ(helper(large), nullptr);
  EXPECT_EQ(metrics["rejected_too_large"], 1);
}

TEST_F(RareSuffixMethodSplittingTest, skipsNeverInlineMethods) {
  auto* annotated = add_method("annotated:(Ljava/lang/Object;)V", kCheck);
  auto anno_set = std::make_unique<DexAnnotationSet>();
  anno_set->add_annotation(std::make_unique<DexAnnotation>(
      type::dalvik_annotation_optimization_NeverInline(),
      DexAnnotationVisibility::DAV_BUILD));
  annotated->set_access(annotated->get_access() | ACC_SYNTHETIC);
  ASSERT_TRUE(annotated->attach_annotation_set(std::move(anno_set)));
  annotated->set_access(annotated->get_access() & ~ACC_SYNTHETIC);
  add_callers(annotated, 2);
  auto metrics = run();
  EXPECT_EQ(helper(annotated), nullptr);
  EXPECT_EQ(metrics["rejected_art_never_inlines"], 1);
}

TEST_F(RareSuffixMethodSplittingTest, skipsMethodsWithCatchHandlers) {
  auto* guarded = add_method("guarded:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (.try_start a)
      (invoke-static () "LFoo;.side:()V")
      (.try_end a)
      (if-nez v0 :ok)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v1)
      (:ok)
      (return-void)
      (.catch (a))
      (move-exception v2)
      (return-void)
    )
  )");
  add_method("side:()V", "((return-void))");
  add_callers(guarded, 2);
  auto metrics = run();
  EXPECT_EQ(helper(guarded), nullptr);
  EXPECT_EQ(metrics["rejected_catch"], 1);
}

TEST_F(RareSuffixMethodSplittingTest, namesOverloadsApart) {
  auto* object_check = add_method("check:(Ljava/lang/Object;)V", kCheck);
  auto* string_check = add_method("check:(Ljava/lang/String;)V", kCheck);
  add_callers(object_check, 2);
  add_callers(string_check, 2);
  auto metrics = run();
  EXPECT_EQ(metrics["split_count"], 2);
  auto* first = helper(object_check, 0);
  auto* second = helper(object_check, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_TRUE(calls(object_check, first) || calls(object_check, second));
  EXPECT_TRUE(calls(string_check, first) || calls(string_check, second));
}

TEST_F(RareSuffixMethodSplittingTest, namesConstructorSplits) {
  auto* init = add_method("<init>:(Ljava/lang/Object;)V", R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (if-nez v1 :ok)
      (new-instance "Ljava/lang/NullPointerException;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/NullPointerException;.<init>:()V")
      (throw v2)
      (:ok)
      (return-void)
    )
  )",
                          ACC_PUBLIC | ACC_CONSTRUCTOR);
  for (int i = 0; i < 2; i++) {
    auto* caller = add_method("caller" + std::to_string(m_callers++) + ":()V",
                              R"(
      (
        (new-instance "LFoo;")
        (move-result-pseudo-object v0)
        (const v1 0)
        (invoke-direct (v0 v1) "LFoo;.<init>:(Ljava/lang/Object;)V")
        (return-void)
      )
    )");
    m_compiled.push_back(caller);
  }
  auto metrics = run();
  auto* split = helper(init);
  ASSERT_NE(split, nullptr);
  EXPECT_TRUE(calls(init, split));
}

TEST_F(RareSuffixMethodSplittingTest, compilesTheSplitOfAHotTail) {
  // The profile says the throwing arm runs. Its split inherits the method's
  // profile, so the baseline profile compiles it, and the launchpad keeps its
  // count. One copy of the arm stays compiled, in the split; four call sites
  // in compiled callers make it pay.
  auto* m = add_method("hot:(Ljava/lang/Object;)V", R"(
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
  add_callers(m, 4);
  m_compiled.push_back(m);
  auto metrics = run();
  EXPECT_EQ(metrics["hot_split_count"], 1);
  DexMethod* split = nullptr;
  for (auto* d : type_class(m->get_class())->get_dmethods()) {
    if (d->str() == "hot$split$hot$rare_suffix$0") {
      split = d;
    }
  }
  ASSERT_NE(split, nullptr);
  Scope scope{type_class(m->get_class())};
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, m_conf->get_baseline_profile_configs(),
      m_conf->get_method_profiles());
  EXPECT_TRUE(baseline_profiles::is_compiled(baseline_profile, split));
  auto* code = m->get_code();
  if (code->cfg_built()) {
    code->clear_cfg();
  }
  const SourceBlock* last_sb = nullptr;
  bool checked = false;
  for (const auto& mie : *code) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      last_sb = mie.src_block.get();
    } else if (mie.type == MFLOW_OPCODE && mie.insn->has_method() &&
               mie.insn->get_method() == split) {
      ASSERT_NE(last_sb, nullptr);
      EXPECT_GT(last_sb->get_val(0).value_or(0), 0.0f);
      checked = true;
    }
  }
  EXPECT_TRUE(checked);
}

TEST_F(RareSuffixMethodSplittingTest,
       keepsTheNullCheckIntrinsicMaterializable) {
  // The shape `IntrinsifyNullChecksPass` gives `Lredex/$NullCheck;.null_check`.
  ClassCreator null_check_cls(DexType::make_type("Lredex/$NullCheck;"));
  null_check_cls.set_super(type::java_lang_Object());
  auto* null_check = DexMethod::make_method(
                         "Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V")
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  null_check->set_code(assembler::ircode_from_string(kCheck));
  null_check_cls.add_method(null_check);
  m_extra_classes.push_back(null_check_cls.create());
  DexMethod::make_method("Ljava/lang/Object;.getClass:()Ljava/lang/Class;");
  add_callers(null_check, 2);
  run(/* enabled */ true, /* materialize */ true);
  auto* split = helper(null_check);
  ASSERT_NE(split, nullptr);
  EXPECT_TRUE(calls(null_check, split));
}

} // namespace
