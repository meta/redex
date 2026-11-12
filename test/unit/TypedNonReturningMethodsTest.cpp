/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "DedupBlocksPass.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "DexStructure.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRTypeChecker.h"
#include "InstructionLowering.h"
#include "MethodProfiles.h"
#include "Pass.h"
#include "PassManager.h"
#include "RedexOptions.h"
#include "RedexTest.h"
#include "RegisterAllocation.h"
#include "Resolver.h"
#include "Show.h"
#include "TypeUtil.h"
#include "TypedNonReturningMethods.h"
#include "UnreachableLoweringPass.h"
#include "Walkers.h"

namespace {

constexpr const char* FAIL = "LFailures;.fail:(Ljava/lang/String;)V";
constexpr const char* TYPED_FAIL =
    "LFailures;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;";
constexpr const char* UNREACHABLE_EXCEPTION =
    "Lcom/redex/UnreachableException;";
constexpr const char* CREATE_AND_THROW =
    "Lcom/redex/UnreachableException;.createAndThrow:()Lcom/redex/"
    "UnreachableException;";

constexpr const char* FAIL_CODE = R"((
  (load-param-object v0)
  (new-instance "Ljava/lang/IllegalStateException;")
  (move-result-pseudo-object v1)
  (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
  (throw v1)
))";

constexpr const char* CALLER_CODE = R"((
  (const-string "name")
  (move-result-pseudo-object v0)
  (.pos:dbg_0 "LCaller;.caller:()V" "Caller.java" 42)
  (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
  (unreachable v1)
  (throw v1)
))";

struct MethodSpec {
  std::string signature;
  DexAccessFlags access;
  std::string code;
};

} // namespace

// Records the references reserved for later passes when it runs.
class ReservedRefsProbePass : public Pass {
 public:
  ReservedRefsProbePass() : Pass("ReservedRefsProbePass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return {};
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager& mgr) override {
    reserved = mgr.get_reserved_refs();
  }

  ReserveRefsInfo reserved;
};

class TypedNonReturningMethodsTest : public RedexTest {
 public:
  TypedNonReturningMethodsTest() { add_library_classes(); }

  // Setup.

  // Starts over in a fresh context, for tests that loop over cases.
  void reset() {
    delete g_redex;
    g_redex = new RedexContext();
    m_dexen = {DexClasses()};
    m_compiled.clear();
    m_startup_classes.clear();
    m_huge_method_max.reset();
    m_instrumented = false;
    add_library_classes();
  }

  void add_library_classes() {
    create_object_class();
    auto* throwable =
        add_class("Ljava/lang/Throwable;", type::java_lang_Object(), {});
    add_class("Ljava/lang/RuntimeException;", throwable->get_type(), {});
    add_class("Ljava/lang/IllegalStateException;",
              type::java_lang_RuntimeException(), {});
  }

  void add_existing_class(DexClass* cls) { m_dexen.back().push_back(cls); }

  // The signatures of the callers that `add_callers` adds to `cls_name`.
  static std::vector<std::string> caller_signatures(
      size_t count, const std::string& cls_name = "LCaller;") {
    std::vector<std::string> res;
    res.reserve(count);
    for (size_t i = 0; i < count; ++i) {
      res.push_back(cls_name.substr(0, cls_name.size() - 1) + ";.caller" +
                    std::to_string(i) + ":()V");
    }
    return res;
  }

  // Marks `signatures` as compiled in the baseline profile, through the manual
  // profile `interaction` ("manual_hot" or "manual_startup").
  void mark_compiled(std::vector<std::string> signatures,
                     std::string interaction = "manual_hot") {
    m_compiled = std::move(signatures);
    m_compiled_interaction = std::move(interaction);
  }

  void set_instrumented() { m_instrumented = true; }

  void set_huge_method_max(uint32_t huge_method_max) {
    m_huge_method_max = huge_method_max;
  }

  // Makes `classes` the cold-start classes that the baseline profile adds
  // methods of, if Redex writes the default profile.
  void set_startup_classes(std::vector<std::string> classes,
                           bool redex_writes_profile = true) {
    m_startup_classes = std::move(classes);
    m_redex_writes_profile = redex_writes_profile;
  }

  DexClass* add_class(const std::string& name,
                      DexType* super,
                      const std::vector<MethodSpec>& methods) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(super);
    for (const auto& spec : methods) {
      auto* method = DexMethod::make_method(spec.signature)
                         ->make_concrete(spec.access, false);
      method->set_code(assembler::ircode_from_string(spec.code));
      creator.add_method(method);
    }
    auto* cls = creator.create();
    m_dexen.back().push_back(cls);
    return cls;
  }

  DexClass* add_failures_class(const std::string& code = FAIL_CODE,
                               DexAccessFlags access = ACC_PUBLIC |
                                                       ACC_STATIC) {
    return add_class("LFailures;", type::java_lang_Object(),
                     {{FAIL, access, code}});
  }

  // `count` callers in class `cls_name`, named `caller0`, `caller1`, ...,
  // each with the code `code`.
  void add_callers(size_t count,
                   const std::string& code = CALLER_CODE,
                   const std::string& cls_name = "LCaller;") {
    std::vector<MethodSpec> methods;
    methods.reserve(count);
    for (auto& signature : caller_signatures(count, cls_name)) {
      methods.push_back({std::move(signature), ACC_PUBLIC | ACC_STATIC, code});
    }
    add_class(cls_name, type::java_lang_Object(), methods);
  }

  // Starts a new dex for the classes added after this call.
  void start_new_dex() { m_dexen.emplace_back(); }

  static std::unique_ptr<DexAnnotationSet> make_method_anno(DexMethodRef* m) {
    auto anno = std::make_unique<DexAnnotation>(DexType::make_type("LAnno;"),
                                                DAV_RUNTIME);
    anno->add_element("value", std::make_unique<DexEncodedValueMethod>(m));
    auto set = std::make_unique<DexAnnotationSet>();
    set->add_annotation(std::move(anno));
    return set;
  }

  // Running.

  std::vector<DexStore> make_stores() const {
    std::vector<DexStore> stores{DexStore("classes")};
    for (const auto& dex : m_dexen) {
      stores.back().add_classes(dex);
    }
    return stores;
  }

  // Runs only the typing, for inputs that the PassManager's IR type checker
  // does not support, such as method handles.
  typed_nonreturning_methods::Stats run_typing_only() {
    auto stores = make_stores();
    walk::code(build_class_scope(stores), [](DexMethod*, IRCode& code) {
      if (!code.cfg_built()) {
        code.build_cfg();
      }
    });
    baseline_profiles::BaselineProfile profile;
    for (const auto& signature : m_compiled) {
      profile.methods[get_def(signature)].hot = true;
    }
    return typed_nonreturning_methods::type_nonreturning_methods(
        stores, build_class_scope(stores),
        DexType::make_type(UNREACHABLE_EXCEPTION), profile,
        baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX);
  }

  // Runs `probe` (if any), UnreachableLoweringPass, then `after` (if any).
  void run_pass(bool enabled, Pass* probe = nullptr, Pass* after = nullptr) {
    Json::Value cfg(Json::objectValue);
    cfg["UnreachableLoweringPass"]["typed_nonreturning_methods"] = enabled;
    if (m_huge_method_max) {
      cfg["dex2oat"]["huge_method_max"] = *m_huge_method_max;
    }
    if (!m_startup_classes.empty()) {
      cfg["baseline_profile"]["default"]["include_all_startup_classes"] = true;
      cfg["baseline_profile"]["default"]["use_final_redex_generated_profile"] =
          m_redex_writes_profile;
    }
    ConfigFiles conf(cfg);
    conf.parse_global_config();
    if (!m_startup_classes.empty()) {
      conf.update_coldstart_classes(m_startup_classes);
    }
    if (!m_compiled.empty()) {
      UnorderedMap<const DexMethodRef*, method_profiles::Stats> stats;
      for (const auto& signature : m_compiled) {
        stats[DexMethod::get_method(signature)] = method_profiles::Stats{};
      }
      conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
          m_compiled_interaction, stats);
    }
    RedexOptions options;
    options.instrument_pass_enabled = m_instrumented;
    UnreachableLoweringPass pass;
    std::vector<Pass*> passes;
    if (probe != nullptr) {
      passes.push_back(probe);
    }
    passes.push_back(&pass);
    if (after != nullptr) {
      passes.push_back(after);
    }
    PassManager manager(passes, conf, options);
    m_output_stores = make_stores();
    manager.run_passes(m_output_stores, conf);
    for (const auto& info : manager.get_pass_info()) {
      if (info.pass == &pass) {
        m_metrics = info.metrics;
      }
    }
  }

  std::vector<DexStore>& output_stores() { return m_output_stores; }

  int64_t metric(const std::string& name) const {
    auto it = m_metrics.find(name);
    return it == m_metrics.end() ? 0 : it->second;
  }

  // Inspection.

  static DexMethod* get_def(const std::string& signature) {
    auto* ref = DexMethod::get_method(signature);
    return ref == nullptr ? nullptr : ref->as_def();
  }

  static IRCode* get_linear_code(const std::string& signature) {
    auto* method = get_def(signature);
    always_assert_log(method != nullptr, "%s", signature.c_str());
    auto* code = method->get_code();
    if (code->cfg_built()) {
      code->clear_cfg();
    }
    return code;
  }

  static ::testing::AssertionResult code_is(const std::string& signature,
                                            const std::string& expected) {
    auto actual = assembler::to_s_expr(get_linear_code(signature));
    auto expected_s_expr =
        assembler::to_s_expr(assembler::ircode_from_string(expected).get());
    if (actual == expected_s_expr) {
      return ::testing::AssertionSuccess();
    }
    return ::testing::AssertionFailure() << signature << " is\n"
                                         << actual.str() << "\ninstead of\n"
                                         << expected_s_expr.str();
  }

  static size_t count_invokes(const std::string& in, const std::string& of) {
    size_t count = 0;
    for (const auto& mie : InstructionIterable(*get_linear_code(in))) {
      if (opcode::is_an_invoke(mie.insn->opcode()) &&
          show(mie.insn->get_method()) == of) {
        count++;
      }
    }
    return count;
  }

  // The method kept its signature and body, and every caller still lowers
  // its `unreachable` to a fallback call.
  static void expect_unchanged(const DexMethod* fail,
                               size_t callers,
                               const std::string& code = FAIL_CODE) {
    EXPECT_EQ(get_def(FAIL), fail);
    EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), nullptr);
    EXPECT_TRUE(code_is(FAIL, code));
    for (size_t i = 0; i < callers; ++i) {
      auto caller = "LCaller;.caller" + std::to_string(i) + ":()V";
      EXPECT_EQ(count_invokes(caller, FAIL), 1) << caller;
      EXPECT_EQ(count_invokes(caller, CREATE_AND_THROW), 1) << caller;
    }
  }

  static void expect_typed(const DexMethod* fail,
                           size_t callers,
                           const std::string& code = FAIL_CODE) {
    EXPECT_EQ(get_def(TYPED_FAIL), fail);
    EXPECT_EQ(DexMethod::get_method(FAIL), nullptr);
    EXPECT_TRUE(code_is(TYPED_FAIL, code));
    for (size_t i = 0; i < callers; ++i) {
      auto caller = "LCaller;.caller" + std::to_string(i) + ":()V";
      EXPECT_EQ(count_invokes(caller, TYPED_FAIL), 1) << caller;
      EXPECT_EQ(count_invokes(caller, CREATE_AND_THROW), 0) << caller;
    }
  }

 private:
  std::vector<DexClasses> m_dexen{DexClasses()};
  // The stores the last `run_pass` ran on.
  std::vector<DexStore> m_output_stores;
  UnorderedMap<std::string, int64_t> m_metrics;
  std::vector<std::string> m_compiled;
  std::string m_compiled_interaction;
  std::vector<std::string> m_startup_classes;
  bool m_redex_writes_profile{true};
  std::optional<uint32_t> m_huge_method_max;
  bool m_instrumented{false};
};

// Method eligibility.

TEST_F(TypedNonReturningMethodsTest, method_that_can_return) {
  const auto* code = R"((
    (load-param-object v0)
    (if-eqz v0 :ret)
    (new-instance "Ljava/lang/IllegalStateException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
    (throw v1)
    (:ret)
    (return-void)
  ))";
  auto* fail = add_failures_class(code)->get_dmethods().front();
  add_callers(20);
  run_pass(/* enabled */ true);
  expect_unchanged(fail, 20, code);
  EXPECT_EQ(metric("typed_nonreturning_methods_rejected"), 1);
}

TEST_F(TypedNonReturningMethodsTest, methods_that_loop_or_branch) {
  const auto* code = R"((
    (load-param-object v0)
    (if-eqz v0 :loop)
    (new-instance "Ljava/lang/IllegalStateException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
    (throw v1)
    (:loop)
    (goto :loop)
  ))";
  auto* fail = add_failures_class(code)->get_dmethods().front();
  add_callers(20);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20, code);
}

TEST_F(TypedNonReturningMethodsTest, rejected_definitions) {
  enum class Kind { NoOptimizations, Kept, StringReferenced, Native };
  for (auto kind : {Kind::NoOptimizations, Kind::Kept, Kind::StringReferenced,
                    Kind::Native}) {
    SCOPED_TRACE(static_cast<int>(kind));
    reset();
    DexClass* cls = nullptr;
    if (kind == Kind::Native) {
      ClassCreator creator(DexType::make_type("LFailures;"));
      creator.set_super(type::java_lang_Object());
      creator.add_method(DexMethod::make_method(FAIL)->make_concrete(
          ACC_PUBLIC | ACC_STATIC | ACC_NATIVE, false));
      cls = creator.create();
      add_existing_class(cls);
    } else {
      cls = add_failures_class();
    }
    auto* fail = cls->get_dmethods().front();
    if (kind == Kind::NoOptimizations) {
      fail->rstate.set_no_optimizations();
    } else if (kind == Kind::Kept) {
      fail->rstate.set_root();
    } else if (kind == Kind::StringReferenced) {
      cls->rstate.referenced_by_string();
    }
    add_callers(20);
    run_pass(/* enabled */ true);
    EXPECT_EQ(get_def(FAIL), fail);
    EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), nullptr);
    for (size_t i = 0; i < 20; ++i) {
      auto caller = "LCaller;.caller" + std::to_string(i) + ":()V";
      EXPECT_EQ(count_invokes(caller, CREATE_AND_THROW), 1) << caller;
    }
  }
}

TEST_F(TypedNonReturningMethodsTest, native_method_with_code) {
  // Malformed input: a native method that also carries code.
  auto* fail =
      add_failures_class(FAIL_CODE, ACC_PUBLIC | ACC_STATIC | ACC_NATIVE)
          ->get_dmethods()
          .front();
  add_callers(20);
  auto stats = run_typing_only();
  EXPECT_EQ(stats.rejected_methods, 1);
  EXPECT_EQ(get_def(FAIL), fail);
  EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), nullptr);
}

TEST_F(TypedNonReturningMethodsTest, method_with_artificial_exit_block) {
  const auto* code = R"((
    (load-param-object v0)
    (if-eqz v0 :other)
    (new-instance "Ljava/lang/IllegalStateException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
    (throw v1)
    (:other)
    (new-instance "Ljava/lang/RuntimeException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "Ljava/lang/RuntimeException;.<init>:()V")
    (throw v1)
  ))";
  // An exit block that has been given a return is checked like any other.
  for (bool exit_block_returns : {false, true}) {
    SCOPED_TRACE(exit_block_returns);
    reset();
    auto* fail = add_failures_class(code)->get_dmethods().front();
    add_callers(20);
    fail->get_code()->build_cfg();
    auto& cfg = fail->get_code()->cfg();
    cfg.calculate_exit_block();
    ASSERT_NE(cfg.exit_block(), nullptr);
    if (exit_block_returns) {
      cfg.exit_block()->push_back(new IRInstruction(OPCODE_RETURN_VOID));
    }
    auto stats = run_typing_only();
    EXPECT_EQ(stats.typed_methods, exit_block_returns ? 0 : 1);
    EXPECT_EQ(get_def(exit_block_returns ? FAIL : TYPED_FAIL), fail);
  }
}

TEST_F(TypedNonReturningMethodsTest, return_in_handler_or_with_exit_block) {
  // A handler that returns, with and without the artificial exit block that
  // gives returning blocks an edge.
  const auto* code = R"((
    (load-param-object v0)
    (.try_start t)
    (new-instance "Ljava/lang/IllegalStateException;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1 v0) "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V")
    (throw v1)
    (.try_end t)
    (.catch (t))
    (return-void)
  ))";
  for (bool exit_block : {false, true}) {
    SCOPED_TRACE(exit_block);
    reset();
    auto* fail = add_failures_class(code)->get_dmethods().front();
    add_callers(20);
    if (exit_block) {
      fail->get_code()->build_cfg();
      fail->get_code()->cfg().calculate_exit_block();
    }
    auto stats = run_typing_only();
    EXPECT_EQ(stats.rejected_methods, 1);
    EXPECT_EQ(get_def(FAIL), fail);
    EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), nullptr);
  }
}

TEST_F(TypedNonReturningMethodsTest, interface_static_method) {
  ClassCreator creator(DexType::make_type("LFailures;"));
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* fail = DexMethod::make_method(FAIL)->make_concrete(
      ACC_PUBLIC | ACC_STATIC, false);
  fail->set_code(assembler::ircode_from_string(FAIL_CODE));
  creator.add_method(fail);
  add_existing_class(creator.create());
  add_callers(20);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
}

TEST_F(TypedNonReturningMethodsTest, recursive_method) {
  const auto* code = R"((
    (load-param-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1)
    (throw v1)
  ))";
  auto* fail = add_failures_class(code)->get_dmethods().front();
  add_callers(20);
  run_pass(/* enabled */ true);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
  EXPECT_TRUE(code_is(TYPED_FAIL, R"((
    (load-param-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
    (move-result-object v1)
    (throw v1)
  ))"));
}

TEST_F(TypedNonReturningMethodsTest, wrapper_of_typed_method) {
  constexpr const char* WRAPPER = "LFailures;.wrap:(Ljava/lang/String;)V";
  constexpr const char* TYPED_WRAPPER =
      "LFailures;.wrap:(Ljava/lang/String;)Lcom/redex/UnreachableException;";
  auto* cls = add_class("LFailures;", type::java_lang_Object(),
                        {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE},
                         {WRAPPER, ACC_PUBLIC | ACC_STATIC, R"((
    (load-param-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1)
    (throw v1)
  ))"}});
  auto* fail = get_def(FAIL);
  auto* wrapper = get_def(WRAPPER);
  std::vector<MethodSpec> callers;
  callers.reserve(20);
  for (size_t i = 0; i < 20; ++i) {
    callers.push_back({"LCaller;.caller" + std::to_string(i) + ":()V",
                       ACC_PUBLIC | ACC_STATIC, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFailures;.wrap:(Ljava/lang/String;)V")
      (unreachable v1)
      (throw v1)
    ))"});
  }
  add_class("LCaller;", type::java_lang_Object(), callers);
  // The inner method needs more sites to pay for its signature.
  add_callers(20, CALLER_CODE, "LMoreCallers;");
  (void)cls;
  run_pass(/* enabled */ true);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
  EXPECT_EQ(get_def(TYPED_WRAPPER), wrapper);
  EXPECT_TRUE(code_is(TYPED_WRAPPER, R"((
    (load-param-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
    (move-result-object v1)
    (throw v1)
  ))"));
  EXPECT_EQ(count_invokes("LCaller;.caller0:()V", CREATE_AND_THROW), 0);
}

// Call-site shapes.

TEST_F(TypedNonReturningMethodsTest, call_sites_throw_the_typed_result) {
  add_class("LFailures;", type::java_lang_Object(),
            {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE}});
  add_callers(20);
  auto* fail = get_def(FAIL);
  run_pass(/* enabled */ true);

  size_t fallback_calls = 0;
  for (size_t i = 0; i < 20; ++i) {
    fallback_calls += count_invokes(
        "LCaller;.caller" + std::to_string(i) + ":()V", CREATE_AND_THROW);
  }
  EXPECT_EQ(fallback_calls, 0);

  // Same method, same body, new return type.
  ASSERT_EQ(get_def(TYPED_FAIL), fail);
  EXPECT_EQ(DexMethod::get_method(FAIL), nullptr);
  EXPECT_TRUE(code_is(TYPED_FAIL, FAIL_CODE));
  for (size_t i = 0; i < 20; ++i) {
    auto caller = "LCaller;.caller" + std::to_string(i) + ":()V";
    EXPECT_TRUE(code_is(caller, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (.pos:dbg_0 "LCaller;.caller:()V" "Caller.java" 42)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
      (move-result-object v1)
      (throw v1)
    ))"));
  }
}

TEST_F(TypedNonReturningMethodsTest, callers_ignoring_the_result) {
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  add_class("LIgnoring;", type::java_lang_Object(),
            {{"LIgnoring;.ignore:()V", ACC_PUBLIC | ACC_STATIC, R"((
    (const-string "name")
    (move-result-pseudo-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (return-void)
  ))"}});
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_TRUE(code_is("LIgnoring;.ignore:()V", R"((
    (const-string "name")
    (move-result-pseudo-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
    (return-void)
  ))"));
  EXPECT_EQ(metric("typed_nonreturning_methods"), 1);
  EXPECT_EQ(metric("typed_nonreturning_method_call_sites"), 20);
}

TEST_F(TypedNonReturningMethodsTest, call_sites_in_try_regions) {
  // The invoke alone, or the invoke and the throw, are covered by a handler
  // that does not read the result; a second shape reads the value in the
  // handler and keeps its fallback call.
  auto* fail = add_failures_class()->get_dmethods().front();
  std::vector<MethodSpec> callers;
  callers.reserve(20);
  for (size_t i = 0; i < 20; ++i) {
    callers.push_back({"LCaller;.caller" + std::to_string(i) + ":()V",
                       ACC_PUBLIC | ACC_STATIC,
                       i % 2 == 0 ? R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (.try_start t)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (.try_end t)
      (unreachable v1)
      (throw v1)
      (.catch (t))
      (return-void)
    ))"
                                  : R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (.try_start t)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (unreachable v1)
      (throw v1)
      (.try_end t)
      (.catch (t))
      (return-void)
    ))"});
  }
  add_class("LCaller;", type::java_lang_Object(), callers);
  add_class("LReader;", type::java_lang_Object(),
            {{"LReader;.call:()V", ACC_PUBLIC | ACC_STATIC, R"((
    (const-string "name")
    (move-result-pseudo-object v0)
    (const v1 0)
    (.try_start t)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1)
    (throw v1)
    (.try_end t)
    (.catch (t))
    (move-object v2 v1)
    (throw v2)
  ))"}});
  run_pass(/* enabled */ true);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
  EXPECT_EQ(count_invokes("LReader;.call:()V", CREATE_AND_THROW), 1);
  for (size_t i = 0; i < 20; ++i) {
    auto signature = "LCaller;.caller" + std::to_string(i) + ":()V";
    SCOPED_TRACE(signature);
    EXPECT_EQ(count_invokes(signature, CREATE_AND_THROW), 0);
    auto* method = get_def(signature);
    auto* code = method->get_code();
    code->build_cfg();
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << checker.what();
    regalloc::graph_coloring::Allocator::Config config;
    regalloc::graph_coloring::allocate(config, method);
    code->clear_cfg();
    instruction_lowering::lower(method);
    auto dex_code = code->sync(method);
    const auto& insns = dex_code->get_instructions();
    size_t pairs = 0;
    for (size_t j = 0; j + 1 < insns.size(); ++j) {
      if (!insns[j]->has_method()) {
        continue;
      }
      const auto* invoke = dynamic_cast<const DexOpcodeMethod*>(insns[j]);
      ASSERT_NE(invoke, nullptr) << show(insns[j]);
      if (invoke->get_method() == fail) {
        EXPECT_EQ(insns[j + 1]->opcode(), DOPCODE_MOVE_RESULT_OBJECT);
        EXPECT_EQ(insns[j + 2]->opcode(), DOPCODE_THROW);
        pairs++;
      }
    }
    EXPECT_EQ(pairs, 1);
    // One try item covering the invoke, with one catch-all handler.
    ASSERT_EQ(dex_code->get_tries().size(), 1);
  }
}

TEST_F(TypedNonReturningMethodsTest, handler_reads_the_value) {
  // A handler of the throw reads the `unreachable` directly, or through a
  // move; either use keeps the fallback call.
  for (bool through_move : {false, true}) {
    SCOPED_TRACE(through_move);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(20);
    std::string handler =
        through_move ? "(move-object v2 v1) (throw v2)" : "(throw v1)";
    add_class("LReader;", type::java_lang_Object(),
              {{"LReader;.call:()V", ACC_PUBLIC | ACC_STATIC, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (const v1 0)
      (.try_start t)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (unreachable v1)
      (throw v1)
      (.try_end t)
      (.catch (t))
    )" + handler + ")"}});
    run_pass(/* enabled */ true);
    expect_typed(fail, 20);
    EXPECT_EQ(count_invokes("LReader;.call:()V", CREATE_AND_THROW), 1);
  }
}

TEST_F(TypedNonReturningMethodsTest, metadata_between_call_and_unreachable) {
  // A source block and a position right before the `unreachable`, in the
  // invoke's block or in the block after an invoke that may throw.
  for (bool in_try : {false, true}) {
    SCOPED_TRACE(in_try);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    std::string body = in_try ? R"(
      (.try_start t)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (.try_end t)
      (.src_block "LCaller;.caller:()V" 1 (1.0 1.0))
      (.pos:dbg_1 "LCaller;.caller:()V" "Caller.java" 43)
      (unreachable v1)
      (throw v1)
      (.catch (t))
      (return-void)
    )"
                              : R"(
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (.src_block "LCaller;.caller:()V" 1 (1.0 1.0))
      (.pos:dbg_1 "LCaller;.caller:()V" "Caller.java" 43)
      (unreachable v1)
      (throw v1)
    )";
    add_callers(20, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (.src_block "LCaller;.caller:()V" 0 (1.0 1.0))
      (.pos:dbg_0 "LCaller;.caller:()V" "Caller.java" 42)
    )" + body + ")");
    run_pass(/* enabled */ true);
    EXPECT_EQ(get_def(TYPED_FAIL), fail);
    auto signature = std::string("LCaller;.caller0:()V");
    EXPECT_EQ(count_invokes(signature, CREATE_AND_THROW), 0);
    auto* method = get_def(signature);
    auto* code = method->get_code();
    code->build_cfg();
    regalloc::graph_coloring::Allocator::Config config;
    regalloc::graph_coloring::allocate(config, method);
    code->clear_cfg();
    instruction_lowering::lower(method);
    auto dex_code = code->sync(method);
    const auto& insns = dex_code->get_instructions();
    size_t pairs = 0;
    for (size_t j = 0; j + 2 < insns.size(); ++j) {
      if (insns[j]->has_method() &&
          dynamic_cast<const DexOpcodeMethod*>(insns[j])->get_method() ==
              fail) {
        EXPECT_EQ(insns[j + 1]->opcode(), DOPCODE_MOVE_RESULT_OBJECT);
        EXPECT_EQ(insns[j + 2]->opcode(), DOPCODE_THROW);
        pairs++;
      }
    }
    EXPECT_EQ(pairs, 1);
  }
}

TEST_F(TypedNonReturningMethodsTest, unreachable_after_merge) {
  // The `unreachable` also follows a branch that skips the call, so it is not
  // the call's result.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  // The second variant has a handler on the call.
  add_class("LMerge;", type::java_lang_Object(),
            {{"LMerge;.call:(I)V", ACC_PUBLIC | ACC_STATIC, R"((
    (load-param v2)
    (const-string "name")
    (move-result-pseudo-object v0)
    (if-eqz v2 :skip)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (:skip)
    (unreachable v1)
    (throw v1)
  ))"},
             {"LMerge;.call_in_try:(I)V", ACC_PUBLIC | ACC_STATIC, R"((
    (load-param v2)
    (const-string "name")
    (move-result-pseudo-object v0)
    (if-eqz v2 :skip)
    (.try_start t)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (.try_end t)
    (:skip)
    (unreachable v1)
    (throw v1)
    (.catch (t))
    (return-void)
  ))"}});
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes("LMerge;.call:(I)V", CREATE_AND_THROW), 1);
  EXPECT_EQ(count_invokes("LMerge;.call_in_try:(I)V", CREATE_AND_THROW), 1);
}

TEST_F(TypedNonReturningMethodsTest, unreachable_split_off_without_handler) {
  // An invoke without a handler that ends its block is not split from its
  // result by the CFG itself; such a site keeps its fallback call.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  add_callers(1, CALLER_CODE, "LSplit;");
  auto* split = get_def("LSplit;.caller0:()V");
  split->get_code()->build_cfg();
  auto& cfg = split->get_code()->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    if (it->insn->opcode() == OPCODE_INVOKE_STATIC) {
      cfg.split_block(it);
      break;
    }
  }
  auto stats = run_typing_only();
  EXPECT_EQ(stats.typed_methods, 1);
  EXPECT_EQ(stats.typed_call_sites, 20);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
}

// References and signature collisions.

TEST_F(TypedNonReturningMethodsTest, no_optimizations_caller) {
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  auto* cls =
      add_class("LBlocked;", type::java_lang_Object(),
                {{"LBlocked;.call:()V", ACC_PUBLIC | ACC_STATIC, CALLER_CODE}});
  cls->get_dmethods().front()->rstate.set_no_optimizations();
  run_pass(/* enabled */ true);
  expect_unchanged(fail, 20);
}

TEST_F(TypedNonReturningMethodsTest, reference_from_no_optimizations_clinit) {
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  auto* cls =
      add_class("LBlocked;", type::java_lang_Object(),
                {{"LBlocked;.<clinit>:()V", ACC_STATIC | ACC_CONSTRUCTOR,
                  R"((
    (const-string "name")
    (move-result-pseudo-object v0)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (return-void)
  ))"}});
  cls->get_clinit()->rstate.set_no_optimizations();
  run_pass(/* enabled */ true);
  expect_unchanged(fail, 20);
}

TEST_F(TypedNonReturningMethodsTest, metadata_references) {
  enum class Kind {
    ClassAnnotation,
    MethodAnnotation,
    ParamAnnotation,
    FieldAnnotation,
    StaticValue,
    StaticMethodHandle,
    AnnotationDefault,
    StaticArray,
    ConstMethodHandle,
    CallSiteArgument,
  };
  for (auto kind :
       {Kind::ClassAnnotation, Kind::MethodAnnotation, Kind::ParamAnnotation,
        Kind::FieldAnnotation, Kind::StaticValue, Kind::StaticMethodHandle,
        Kind::AnnotationDefault, Kind::StaticArray, Kind::ConstMethodHandle,
        Kind::CallSiteArgument}) {
    SCOPED_TRACE(static_cast<int>(kind));
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(20);
    auto* holder =
        add_class("LHolder;", type::java_lang_Object(),
                  // Synthetic, so that annotations can be attached to it.
                  {{"LHolder;.m:(I)V", ACC_PUBLIC | ACC_STATIC | ACC_SYNTHETIC,
                    R"(((load-param v0) (return-void)))"}});
    auto* m = holder->get_dmethods().front();
    auto make_field = [&]() {
      auto* field =
          DexField::make_field("LHolder;.f:Ljava/lang/Object;")
              ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_SYNTHETIC);
      holder->add_field(field);
      return field;
    };
    auto make_handle = [&]() {
      auto* handle =
          new DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_STATIC, fail);
      g_redex->publish_methodhandle(handle);
      return handle;
    };
    switch (kind) {
    case Kind::ClassAnnotation:
      ASSERT_TRUE(holder->attach_annotation_set(make_method_anno(fail)));
      break;
    case Kind::MethodAnnotation:
      ASSERT_TRUE(m->attach_annotation_set(make_method_anno(fail)));
      break;
    case Kind::ParamAnnotation:
      m->attach_param_annotation_set(0, make_method_anno(fail));
      break;
    case Kind::FieldAnnotation:
      ASSERT_TRUE(make_field()->attach_annotation_set(make_method_anno(fail)));
      break;
    case Kind::StaticValue:
      make_field()->set_value(std::make_unique<DexEncodedValueMethod>(fail));
      break;
    case Kind::StaticMethodHandle:
      make_field()->set_value(
          std::make_unique<DexEncodedValueMethodHandle>(make_handle()));
      break;
    case Kind::AnnotationDefault: {
      // The method is a default value, nested in an annotation value.
      EncodedAnnotations defaults;
      defaults.emplace_back(DexString::make_string("value"),
                            std::make_unique<DexEncodedValueMethod>(fail));
      auto anno = std::make_unique<DexAnnotation>(
          DexType::make_type("Ldalvik/annotation/AnnotationDefault;"),
          DAV_SYSTEM);
      anno->add_element("value",
                        std::make_unique<DexEncodedValueAnnotation>(
                            DexType::make_type("LAnno;"), std::move(defaults)));
      auto set = std::make_unique<DexAnnotationSet>();
      set->add_annotation(std::move(anno));
      ASSERT_TRUE(holder->attach_annotation_set(std::move(set)));
      break;
    }
    case Kind::StaticArray: {
      auto* values = new DexEncodedValueArray::Storage();
      values->push_back(std::make_unique<DexEncodedValueMethod>(fail));
      make_field()->set_value(std::make_unique<DexEncodedValueArray>(values));
      break;
    }
    case Kind::ConstMethodHandle: {
      auto* code = m->get_code();
      auto it = code->begin();
      ++it; // after load-param
      code->insert_before(it, (new IRInstruction(OPCODE_CONST_METHOD_HANDLE))
                                  ->set_methodhandle(make_handle()));
      code->insert_before(
          it,
          (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))->set_dest(1));
      code->set_registers_size(2);
      break;
    }
    case Kind::CallSiteArgument: {
      auto* bootstrap = DexMethod::make_method(
          "LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/"
          "String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/"
          "MethodHandle;)Ljava/lang/invoke/CallSite;");
      auto* boot_handle =
          new DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_STATIC, bootstrap);
      g_redex->publish_methodhandle(boot_handle);
      std::vector<std::unique_ptr<DexEncodedValue>> args;
      args.push_back(
          std::make_unique<DexEncodedValueMethodHandle>(make_handle()));
      auto* callsite = new DexCallSite(
          boot_handle, DexString::make_string("run"),
          DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})),
          std::move(args));
      g_redex->publish_callsite(callsite);
      auto* code = m->get_code();
      auto it = code->begin();
      ++it;
      code->insert_before(
          it,
          (new IRInstruction(OPCODE_INVOKE_CUSTOM))->set_callsite(callsite));
      break;
    }
    }
    if (kind == Kind::ConstMethodHandle || kind == Kind::CallSiteArgument) {
      auto stats = run_typing_only();
      EXPECT_EQ(stats.rejected_methods, 1);
      EXPECT_EQ(stats.typed_methods, 0);
      EXPECT_EQ(get_def(FAIL), fail);
      EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), nullptr);
      EXPECT_TRUE(code_is(FAIL, FAIL_CODE));
      EXPECT_TRUE(code_is("LCaller;.caller0:()V", CALLER_CODE));
      continue;
    }
    run_pass(/* enabled */ true);
    expect_unchanged(fail, 20);
  }
}

TEST_F(TypedNonReturningMethodsTest, existing_method_with_new_signature) {
  auto* cls = add_class("LFailures;", type::java_lang_Object(),
                        {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE},
                         {TYPED_FAIL, ACC_PUBLIC | ACC_STATIC,
                          R"(((load-param-object v0) (const v1 0)
                              (return-object v1)))"}});
  auto* fail = get_def(FAIL);
  auto* existing = get_def(TYPED_FAIL);
  add_callers(20);
  run_pass(/* enabled */ true);
  EXPECT_EQ(get_def(FAIL), fail);
  EXPECT_EQ(get_def(TYPED_FAIL), existing);
  EXPECT_EQ(count_invokes("LCaller;.caller0:()V", CREATE_AND_THROW), 1);
  (void)cls;
}

TEST_F(TypedNonReturningMethodsTest, interned_reference_with_new_signature) {
  // A reference with the new signature that no instruction uses still blocks
  // the change, which would otherwise collide with it.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  auto* interned = DexMethod::make_method(TYPED_FAIL);
  run_pass(/* enabled */ true);
  EXPECT_EQ(get_def(FAIL), fail);
  EXPECT_EQ(DexMethod::get_method(TYPED_FAIL), interned);
  EXPECT_TRUE(code_is(FAIL, FAIL_CODE));
  EXPECT_EQ(count_invokes("LCaller;.caller0:()V", CREATE_AND_THROW), 1);
}

TEST_F(TypedNonReturningMethodsTest, static_methods_hiding_each_other) {
  // LSub;.fail hides LFailures;.fail; both are typed, and each call keeps its
  // target.
  constexpr const char* SUB_FAIL = "LSub;.fail:(Ljava/lang/String;)V";
  constexpr const char* TYPED_SUB_FAIL =
      "LSub;.fail:(Ljava/lang/String;)Lcom/redex/UnreachableException;";
  auto* failures = add_failures_class();
  auto* fail = failures->get_dmethods().front();
  auto* sub = add_class("LSub;", failures->get_type(),
                        {{SUB_FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE}})
                  ->get_dmethods()
                  .front();
  add_callers(20);
  std::vector<MethodSpec> callers;
  callers.reserve(20);
  for (size_t i = 0; i < 20; ++i) {
    callers.push_back({"LSubCaller;.caller" + std::to_string(i) + ":()V",
                       ACC_PUBLIC | ACC_STATIC, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LSub;.fail:(Ljava/lang/String;)V")
      (unreachable v1)
      (throw v1)
    ))"});
  }
  add_class("LSubCaller;", type::java_lang_Object(), callers);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(get_def(TYPED_SUB_FAIL), sub);
  EXPECT_EQ(count_invokes("LSubCaller;.caller0:()V", TYPED_SUB_FAIL), 1);
  EXPECT_EQ(count_invokes("LSubCaller;.caller0:()V", CREATE_AND_THROW), 0);
}

TEST_F(TypedNonReturningMethodsTest, lookup_after_typing) {
  auto* cls = add_class(
      "LFailures;", type::java_lang_Object(),
      {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE},
       {"LFailures;.fail:(Ljava/lang/Object;)V", ACC_PUBLIC | ACC_STATIC,
        R"(((load-param-object v0) (return-void)))"}});
  auto* fail = get_def(FAIL);
  add_callers(20);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(resolve_method(cls, fail->get_name(), fail->get_proto(),
                           MethodSearch::Static),
            fail);
}

// Cost.

TEST_F(TypedNonReturningMethodsTest, profitability_threshold) {
  // In the single dex, the new signature adds a proto (12 bytes). Each site
  // saves 6 bytes.
  for (size_t sites : {2, 3}) {
    SCOPED_TRACE(sites);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(sites);
    run_pass(/* enabled */ true);
    if (sites == 2) {
      expect_unchanged(fail, sites);
      EXPECT_EQ(metric("typed_nonreturning_methods_unprofitable"), 1);
    } else {
      expect_typed(fail, sites);
    }
  }
}

TEST_F(TypedNonReturningMethodsTest, existing_signature_in_dex) {
  add_class(
      "LOther;", type::java_lang_Object(),
      {{"LOther;.make:(Ljava/lang/String;)Lcom/redex/UnreachableException;",
        ACC_PUBLIC | ACC_STATIC,
        R"(((load-param-object v0) (const v1 0) (return-object v1)))"}});
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(1);
  run_pass(/* enabled */ true);
  expect_typed(fail, 1);
}

TEST_F(TypedNonReturningMethodsTest, methods_sharing_a_signature) {
  // The first method pays for the proto that both new signatures share, so the
  // second one is typed for a single site.
  add_class("LFailures;", type::java_lang_Object(),
            {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE},
             {"LFailures;.fail2:(Ljava/lang/String;)V", ACC_PUBLIC | ACC_STATIC,
              FAIL_CODE}});
  add_callers(3);
  std::string other_caller_code = CALLER_CODE;
  auto pos = other_caller_code.find("LFailures;.fail:");
  other_caller_code.replace(pos, std::string("LFailures;.fail:").size(),
                            "LFailures;.fail2:");
  add_callers(1, other_caller_code, "LOtherCaller;");
  auto stats = run_typing_only();
  EXPECT_EQ(stats.typed_methods, 2);
}

TEST_F(TypedNonReturningMethodsTest, referenced_from_several_dexes) {
  // Each of the three dexes adds the 12-byte proto.
  for (size_t sites_per_dex : {3, 4}) {
    SCOPED_TRACE(sites_per_dex);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    start_new_dex();
    add_callers(sites_per_dex, CALLER_CODE, "LCaller;");
    start_new_dex();
    add_callers(sites_per_dex, CALLER_CODE, "LOtherCaller;");
    run_pass(/* enabled */ true);
    if (sites_per_dex == 3) {
      expect_unchanged(fail, sites_per_dex);
      EXPECT_EQ(metric("typed_nonreturning_methods_unprofitable"), 1);
    } else {
      expect_typed(fail, sites_per_dex);
    }
  }
}

TEST_F(TypedNonReturningMethodsTest, dex_with_only_ignored_results) {
  // A dex that only ignores the result also references the new signature, so
  // it adds the proto too: 24 bytes for the two dexes.
  for (size_t sites : {4, 5}) {
    SCOPED_TRACE(sites);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(sites);
    start_new_dex();
    add_class("LIgnoring;", type::java_lang_Object(),
              {{"LIgnoring;.ignore:()V", ACC_PUBLIC | ACC_STATIC, R"((
      (const-string "name")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
      (return-void)
    ))"}});
    run_pass(/* enabled */ true);
    if (sites == 4) {
      expect_unchanged(fail, sites);
      EXPECT_EQ(metric("typed_nonreturning_methods_unprofitable"), 1);
    } else {
      expect_typed(fail, sites);
    }
  }
}

// Compiled callers.

TEST_F(TypedNonReturningMethodsTest, compiled_caller_outside_try) {
  // ART would keep the typed throw in a compiled caller: the site keeps its
  // fallback call, and the method is typed for the other callers only.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  add_callers(1, CALLER_CODE, "LHot;");
  mark_compiled({"LHot;.caller0:()V"});
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes("LHot;.caller0:()V", TYPED_FAIL), 1);
  EXPECT_EQ(count_invokes("LHot;.caller0:()V", CREATE_AND_THROW), 1);
  EXPECT_EQ(metric("typed_nonreturning_method_call_sites"), 20);
  EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"), 1);
}

TEST_F(TypedNonReturningMethodsTest, compiled_startup_caller) {
  // dex2oat also compiles startup methods.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  add_callers(1, CALLER_CODE, "LHot;");
  mark_compiled({"LHot;.caller0:()V"}, "manual_startup");
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes("LHot;.caller0:()V", CREATE_AND_THROW), 1);
}

TEST_F(TypedNonReturningMethodsTest, compiled_caller_in_try) {
  // In a try region ART keeps the code after the call anyway, so the site is
  // converted even in a compiled caller.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20, R"((
    (const-string "name")
    (move-result-pseudo-object v0)
    (.try_start t)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (.try_end t)
    (unreachable v1)
    (throw v1)
    (.catch (t))
    (return-void)
  ))");
  mark_compiled(caller_signatures(20));
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"), 0);
}

TEST_F(TypedNonReturningMethodsTest, only_compiled_callers) {
  // A method whose sites are all in compiled callers is not typed.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  mark_compiled(caller_signatures(20));
  run_pass(/* enabled */ true);
  expect_unchanged(fail, 20);
  EXPECT_EQ(metric("typed_nonreturning_method_candidates"), 0);
  EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"), 20);
}

TEST_F(TypedNonReturningMethodsTest, cost_counts_converted_sites_only) {
  // 3 converted sites pay for the 12-byte proto; 2 do not, however many sites
  // in compiled callers there are.
  for (size_t sites : {2, 3}) {
    SCOPED_TRACE(sites);
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(sites);
    add_callers(10, CALLER_CODE, "LHot;");
    mark_compiled(caller_signatures(10, "LHot;"));
    run_pass(/* enabled */ true);
    if (sites == 2) {
      expect_unchanged(fail, sites);
      EXPECT_EQ(metric("typed_nonreturning_methods_unprofitable"), 1);
    } else {
      expect_typed(fail, sites);
    }
  }
}

TEST_F(TypedNonReturningMethodsTest, unconverted_site_of_typed_method) {
  // A compiled caller's site of a typed method ignores the result and is
  // lowered as before; DedupBlocks keeps such sites apart, and the DEX pairs
  // the fallback call with its result.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  constexpr const char* HOT = "LHot;.two:(I)V";
  add_class("LHot;", type::java_lang_Object(),
            {{HOT, ACC_PUBLIC | ACC_STATIC, R"((
    (load-param v2)
    (const-string "name")
    (move-result-pseudo-object v0)
    (if-eqz v2 :other)
    (.pos:dbg_0 "LHot;.two:(I)V" "Hot.java" 10)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1)
    (throw v1)
    (:other)
    (.pos:dbg_1 "LHot;.two:(I)V" "Hot.java" 20)
    (invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1)
    (throw v1)
  ))"}});
  mark_compiled({HOT});
  DedupBlocksPass dedup;
  run_pass(/* enabled */ true, /* probe */ nullptr, &dedup);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes(HOT, TYPED_FAIL), 2);
  EXPECT_EQ(count_invokes(HOT, CREATE_AND_THROW), 2);
  auto* method = get_def(HOT);
  auto* code = method->get_code();
  code->build_cfg();
  regalloc::graph_coloring::Allocator::Config config;
  regalloc::graph_coloring::allocate(config, method);
  code->clear_cfg();
  instruction_lowering::lower(method);
  auto dex_code = code->sync(method);
  const auto& insns = dex_code->get_instructions();
  size_t pairs = 0;
  for (size_t j = 0; j + 3 < insns.size(); ++j) {
    if (insns[j]->has_method() &&
        dynamic_cast<const DexOpcodeMethod*>(insns[j])->get_method() == fail) {
      // The typed call's result is not moved; the fallback call's is.
      EXPECT_TRUE(insns[j + 1]->has_method());
      EXPECT_EQ(insns[j + 2]->opcode(), DOPCODE_MOVE_RESULT_OBJECT);
      EXPECT_EQ(insns[j + 3]->opcode(), DOPCODE_THROW);
      pairs++;
    }
  }
  EXPECT_EQ(pairs, 2);
}

TEST_F(TypedNonReturningMethodsTest, startup_class_callers) {
  // With include_all_startup_classes, the profile that Redex writes also
  // compiles the methods of the cold-start classes before the marker.
  enum class Case { BeforeMarker, AfterMarker, ProfileNotWrittenByRedex };
  for (auto c : {Case::BeforeMarker, Case::AfterMarker,
                 Case::ProfileNotWrittenByRedex}) {
    SCOPED_TRACE(static_cast<int>(c));
    reset();
    auto* fail = add_failures_class()->get_dmethods().front();
    add_callers(20);
    add_callers(1, CALLER_CODE, "LHot;");
    if (c == Case::AfterMarker) {
      set_startup_classes({"LColdStart20PctEnd;", "LHot;"});
    } else {
      set_startup_classes({"LHot;", "LColdStart20PctEnd;"},
                          c == Case::BeforeMarker);
    }
    run_pass(/* enabled */ true);
    expect_typed(fail, 20);
    size_t compiled = c == Case::BeforeMarker ? 1 : 0;
    EXPECT_EQ(count_invokes("LHot;.caller0:()V", CREATE_AND_THROW), compiled);
    EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"),
              compiled);
  }
}

TEST_F(TypedNonReturningMethodsTest, global_huge_method_max) {
  // A caller above dex2oat.huge_method_max is not compiled, even if hot.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  add_callers(1, CALLER_CODE, "LHot;");
  mark_compiled({"LHot;.caller0:()V"});
  set_huge_method_max(3);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes("LHot;.caller0:()V", CREATE_AND_THROW), 0);
  EXPECT_EQ(metric("typed_nonreturning_method_call_sites"), 21);
  EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"), 0);
}

TEST_F(TypedNonReturningMethodsTest, uncompilable_profiled_callers) {
  // dex2oat compiles neither a <clinit> nor a huge method, even if the
  // profile asks for it, so their sites are converted.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  std::string huge_code =
      R"(((const-string "name") (move-result-pseudo-object v0))";
  for (uint32_t i = 0; i < baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX;
       ++i) {
    huge_code += "(nop)";
  }
  huge_code += R"((invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V")
    (unreachable v1) (throw v1)))";
  add_class("LUncompilable;", type::java_lang_Object(),
            {{"LUncompilable;.<clinit>:()V", ACC_STATIC | ACC_CONSTRUCTOR,
              CALLER_CODE},
             {"LUncompilable;.huge:()V", ACC_PUBLIC | ACC_STATIC, huge_code}});
  mark_compiled({"LUncompilable;.<clinit>:()V", "LUncompilable;.huge:()V"});
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  EXPECT_EQ(count_invokes("LUncompilable;.<clinit>:()V", CREATE_AND_THROW), 0);
  EXPECT_EQ(count_invokes("LUncompilable;.huge:()V", CREATE_AND_THROW), 0);
  EXPECT_EQ(metric("typed_nonreturning_method_compiled_call_sites"), 0);
}

TEST_F(TypedNonReturningMethodsTest, instrumented_build) {
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  set_instrumented();
  run_pass(/* enabled */ true);
  expect_unchanged(fail, 20);
  EXPECT_EQ(metric("typed_nonreturning_method_candidates"), 0);
}

// Pass integration.

TEST_F(TypedNonReturningMethodsTest, disabled_by_default) {
  auto* cls = add_failures_class();
  add_callers(20);
  auto* fail = cls->get_dmethods().front();
  run_pass(/* enabled */ false);
  expect_unchanged(fail, 20);
  EXPECT_EQ(metric("typed_nonreturning_methods"), 0);
}

TEST_F(TypedNonReturningMethodsTest, reserved_references) {
  for (bool enabled : {false, true}) {
    SCOPED_TRACE(enabled);
    reset();
    add_failures_class();
    add_callers(20);
    ReservedRefsProbePass probe;
    run_pass(enabled, &probe);
    EXPECT_EQ(probe.reserved.frefs, 0);
    EXPECT_EQ(probe.reserved.trefs, 1);
    EXPECT_EQ(probe.reserved.mrefs, 1);
  }
}

TEST_F(TypedNonReturningMethodsTest, deterministic) {
  // Two methods with the same new signature compete for the shared metadata;
  // the outcome must not depend on thread scheduling.
  std::vector<std::string> results;
  for (int run = 0; run < 3; ++run) {
    reset();
    add_class("LFailures;", type::java_lang_Object(),
              {{FAIL, ACC_PUBLIC | ACC_STATIC, FAIL_CODE},
               {"LFailures;.fail2:(Ljava/lang/String;)V",
                ACC_PUBLIC | ACC_STATIC, FAIL_CODE}});
    std::vector<MethodSpec> callers;
    callers.reserve(6);
    for (size_t i = 0; i < 6; ++i) {
      callers.push_back({"LCaller;.caller" + std::to_string(i) + ":()V",
                         ACC_PUBLIC | ACC_STATIC,
                         i % 2 == 0 ? CALLER_CODE : R"((
        (const-string "name")
        (move-result-pseudo-object v0)
        (invoke-static (v0) "LFailures;.fail2:(Ljava/lang/String;)V")
        (unreachable v1)
        (throw v1)
      ))"});
    }
    add_class("LCaller;", type::java_lang_Object(), callers);
    run_pass(/* enabled */ true);
    std::string result;
    for (size_t i = 0; i < 6; ++i) {
      result +=
          assembler::to_s_expr(
              get_linear_code("LCaller;.caller" + std::to_string(i) + ":()V"))
              .str();
    }
    results.push_back(result);
  }
  EXPECT_EQ(results[0], results[1]);
  EXPECT_EQ(results[0], results[2]);
}

TEST_F(TypedNonReturningMethodsTest, second_run_changes_nothing) {
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  EXPECT_EQ(run_typing_only().typed_methods, 1);
  auto caller = assembler::to_s_expr(get_linear_code("LCaller;.caller0:()V"));
  auto stats = run_typing_only();
  EXPECT_EQ(stats.candidate_methods, 0);
  EXPECT_EQ(stats.typed_methods, 0);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
  EXPECT_EQ(assembler::to_s_expr(get_linear_code("LCaller;.caller0:()V")),
            caller);
}

TEST_F(TypedNonReturningMethodsTest, original_descriptor_for_profiles) {
  // ArtProfileWriter names methods by their deobfuscated name, which keeps the
  // original descriptor; the full rename map pairs it with the new one.
  auto* fail = add_failures_class()->get_dmethods().front();
  fail->set_deobfuscated_name(FAIL);
  add_callers(20);
  run_pass(/* enabled */ true);
  EXPECT_EQ(show(fail), TYPED_FAIL);
  EXPECT_EQ(show_deobfuscated(fail), FAIL);
}

TEST_F(TypedNonReturningMethodsTest, result_type_kept_without_fallback_calls) {
  // Every site is typed, so no fallback call remains; the result type and its
  // createAndThrow method stay, as roots, in the primary dex.
  auto* fail = add_failures_class()->get_dmethods().front();
  add_callers(20);
  run_pass(/* enabled */ true);
  expect_typed(fail, 20);
  auto scope = build_class_scope(output_stores());
  auto* result_type = fail->get_proto()->get_rtype();
  EXPECT_EQ(show(result_type), UNREACHABLE_EXCEPTION);
  auto* result_cls = type_class(result_type);
  ASSERT_NE(result_cls, nullptr);
  EXPECT_NE(std::find(scope.begin(), scope.end(), result_cls), scope.end());
  const auto& primary = output_stores().front().get_dexen().front();
  EXPECT_NE(std::find(primary.begin(), primary.end(), result_cls),
            primary.end());
  auto* create_and_throw = get_def(CREATE_AND_THROW);
  ASSERT_NE(create_and_throw, nullptr);
  EXPECT_EQ(create_and_throw->get_class(), result_type);
  size_t fallback_calls = 0;
  walk::code(scope, [&](DexMethod*, IRCode& code) {
    if (code.cfg_built()) {
      code.clear_cfg();
    }
    for (const auto& mie : InstructionIterable(code)) {
      if (mie.insn->has_method() &&
          mie.insn->get_method() == create_and_throw) {
        fallback_calls++;
      }
    }
  });
  EXPECT_EQ(fallback_calls, 0);
}

TEST_F(TypedNonReturningMethodsTest, dedup_blocks_keeps_call_site_lines) {
  // DedupBlocks runs after lowering. Typed call sites that differ only in
  // their positions must stay apart, or every failure reports one line.
  auto* fail = add_failures_class()->get_dmethods().front();
  constexpr size_t SITES = 8;
  std::string signature = "LCaller;.many:(";
  for (size_t i = 0; i < SITES; ++i) {
    signature += "I";
  }
  signature += ")V";
  std::string code = "(";
  for (size_t i = 0; i < SITES; ++i) {
    code += "(load-param v" + std::to_string(i + 2) + ")";
  }
  code += R"((const-string "name") (move-result-pseudo-object v0))";
  for (size_t i = 0; i < SITES; ++i) {
    code += "(if-eqz v" + std::to_string(i + 2) + " :site" + std::to_string(i) +
            ")";
  }
  code += "(return-void)";
  for (size_t i = 0; i < SITES; ++i) {
    code += "(:site" + std::to_string(i) + ")(.pos:dbg_" + std::to_string(i) +
            " \"" + signature + "\" \"Caller.java\" " +
            std::to_string(100 + i) +
            R"()(invoke-static (v0) "LFailures;.fail:(Ljava/lang/String;)V"))" +
            "(unreachable v1)(throw v1)";
  }
  code += ")";
  add_class("LCaller;", type::java_lang_Object(),
            {{signature, ACC_PUBLIC | ACC_STATIC, code}});
  DedupBlocksPass dedup;
  run_pass(/* enabled */ true, /* probe */ nullptr, &dedup);
  EXPECT_EQ(get_def(TYPED_FAIL), fail);
  std::set<uint32_t> lines;
  size_t calls = 0;
  uint32_t line = 0;
  for (const auto& mie : *get_linear_code(signature)) {
    if (mie.type == MFLOW_POSITION) {
      line = mie.pos->line;
    } else if (mie.type == MFLOW_OPCODE && mie.insn->has_method() &&
               show(mie.insn->get_method()) == TYPED_FAIL) {
      calls++;
      lines.insert(line);
    }
  }
  EXPECT_EQ(calls, SITES);
  EXPECT_EQ(lines.size(), SITES);
  EXPECT_EQ(*lines.begin(), 100u);
  EXPECT_EQ(*lines.rbegin(), 100u + SITES - 1);
}
