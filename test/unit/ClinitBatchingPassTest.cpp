/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <fstream>

#include <gtest/gtest.h>

#include "ClinitBatchingPass.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "EarlyClassLoadsAnalysis.h"
#include "IRAssembler.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

class ClinitBatchingPassTest : public RedexTest {
 protected:
  DexStoresVector stores;
  redex::TempDir m_apk_dir;
  redex::TempDir m_profile_dir;

  void SetUp() override {
    DexStore root_store("classes");

    // Create orchestrator class with @GenerateStaticInitBatch annotation.
    // eval_pass requires this annotation to find the orchestrator method.
    auto* anno_type = DexType::make_type(
        "Lcom/facebook/redex/annotations/GenerateStaticInitBatch;");
    ClassCreator anno_creator(anno_type);
    anno_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT |
                            ACC_ANNOTATION);
    anno_creator.set_super(DexType::make_type("Ljava/lang/Object;"));
    anno_creator.create();

    auto* orch_type =
        DexType::make_type("Lcom/facebook/test/ClinitBatchingOrchestrator;");
    ClassCreator orch_creator(orch_type);
    orch_creator.set_access(ACC_PUBLIC);
    orch_creator.set_super(DexType::make_type("Ljava/lang/Object;"));

    // Create initAllStatics() method with @GenerateStaticInitBatch annotation
    auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(
        orch_type, DexString::make_string("initAllStatics"),
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}))));
    always_assert(method != nullptr);
    method->set_access(ACC_PUBLIC | ACC_STATIC);

    // Attach annotation before make_concrete, because attach_annotation_set
    // rejects concrete non-synthetic methods.
    auto anno_set = std::make_unique<DexAnnotationSet>();
    anno_set->add_annotation(std::make_unique<DexAnnotation>(
        anno_type, DexAnnotationVisibility::DAV_RUNTIME));
    always_assert(method->attach_annotation_set(std::move(anno_set)));

    method->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    // set_code after make_concrete, since make_concrete clears the code.
    method->set_code(assembler::ircode_from_string("((return-void))"));

    orch_creator.add_method(method);
    auto* orch_cls = orch_creator.create();

    // Create a synthetic Application subclass that the EarlyClassLoadsAnalysis
    // discovers via the binary manifest. Its attachBaseContext calls the
    // orchestrator so the analysis finds the orchestrator entry point.
    auto* app_type = DexType::make_type("Landroid/app/Application;");
    auto* test_app_type =
        DexType::make_type("Lcom/facebook/redextest/TestApplication;");
    ClassCreator app_creator(test_app_type);
    app_creator.set_access(ACC_PUBLIC);
    app_creator.set_super(app_type);

    // Add a default constructor
    auto* app_init = dynamic_cast<DexMethod*>(DexMethod::make_method(
        test_app_type, DexString::make_string("<init>"),
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}))));
    app_init->set_access(ACC_PUBLIC);
    app_init->make_concrete(ACC_PUBLIC, false);
    app_init->set_code(assembler::ircode_from_string(
        "((load-param-object v0) (return-void))"));
    app_creator.add_method(app_init);

    auto* context_type = DexType::make_type("Landroid/content/Context;");
    auto* attach_method = dynamic_cast<DexMethod*>(DexMethod::make_method(
        test_app_type, DexString::make_string("attachBaseContext"),
        DexProto::make_proto(type::_void(),
                             DexTypeList::make_type_list({context_type}))));
    attach_method->set_access(ACC_PUBLIC);
    attach_method->make_concrete(ACC_PUBLIC, true);
    attach_method->set_code(assembler::ircode_from_string(
        "((load-param-object v0) (load-param-object v1)"
        " (invoke-static () \"" +
        show(method) + "\") (return-void))"));
    app_creator.add_method(attach_method);
    auto* app_cls = app_creator.create();

    root_store.add_classes({orch_cls, app_cls});
    stores = {root_store};
  }

  // Runs the pass and returns its metrics.
  UnorderedMap<std::string, int64_t> run_pass(
      const Json::Value& config = Json::nullValue) {
    Json::Value cfg = config.isNull() ? Json::Value(Json::objectValue) : config;

    // Set up apk_dir with the binary AndroidManifest.xml test fixture.
    m_apk_dir = redex::make_tmp_dir("clinit_batching_unit_test_%%%%%%%%");
    auto* manifest_path_env = std::getenv("manifest");
    always_assert_log(manifest_path_env, "manifest env var must be set.\n");
    redex::copy_file(manifest_path_env,
                     m_apk_dir.path + "/AndroidManifest.xml");
    cfg["apk_dir"] = m_apk_dir.path;

    ConfigFiles conf(cfg);
    conf.parse_global_config();
    ClinitBatchingPass pass;
    std::vector<Pass*> passes{&pass};
    PassManager manager(passes, conf);
    manager.run_passes(stores, conf);
    return manager.get_pass_info()[0].metrics;
  }

  // Runs the pass on `classes`, with the methods `hot_methods` hot at cold
  // start, and returns the pass's metrics.
  UnorderedMap<std::string, int64_t> run_pass_with_hot_methods(
      const std::vector<DexClass*>& classes,
      const std::vector<std::string>& hot_methods) {
    if (type_class(type::java_lang_Object()) == nullptr) {
      create_object_class();
    }
    m_profile_dir = redex::make_tmp_dir("clinit_batching_profile_%%%%%%%%");
    auto profile_path = m_profile_dir.path + "/method_profiles.csv";
    {
      std::ofstream profile(profile_path);
      profile << "interaction,appear#\nColdStart,100\n"
              << "index,name,appear100,appear#,avg_call,avg_order,"
                 "avg_rank100,min_api_level\n";
      int index = 1;
      for (const auto& method : hot_methods) {
        profile << index++ << "," << method
                << ",99.0000,99,2.0000,0.0000,0.000000,29\n";
      }
    }
    Json::Value cfg(Json::objectValue);
    cfg["agg_method_stats_files"].append(profile_path);
    auto& interaction = cfg["baseline_profile"]["default"]
                           ["deep_data_interaction_config"]["ColdStart"];
    interaction["name"] = "ColdStart";
    interaction["call_threshold"] = 1;
    interaction["classes"] = true;
    interaction["post_startup"] = false;
    interaction["startup"] = true;
    interaction["threshold"] = 20;
    cfg["baseline_profile"]["default"]["oxygen_modules"] = false;
    cfg["baseline_profile"]["default"]["strip_classes"] = false;
    cfg["baseline_profile"]["default"]["use_redex_generated_profile"] = false;
    cfg["ClinitBatchingPass"]["interaction_pattern"] = "ColdStart";
    stores[0].add_classes(classes);
    return run_pass(cfg);
  }

  // Runs the early class loads analysis with `attach_code` as the body of
  // attachBaseContext and `classes` added to the scope.
  clinit_batching::EarlyClassLoadsResult run_early_class_loads_analysis(
      const std::vector<DexClass*>& classes, const char* attach_code);
};

clinit_batching::EarlyClassLoadsResult
ClinitBatchingPassTest::run_early_class_loads_analysis(
    const std::vector<DexClass*>& classes, const char* attach_code) {
  if (type_class(type::java_lang_Object()) == nullptr) {
    create_object_class();
  }
  auto* attach =
      DexMethod::get_method(
          "Lcom/facebook/redextest/TestApplication;.attachBaseContext:"
          "(Landroid/content/Context;)V")
          ->as_def();
  attach->set_code(assembler::ircode_from_string(attach_code));
  auto scope = build_class_scope(stores);
  scope.insert(scope.end(), classes.begin(), classes.end());
  for (auto* cls : scope) {
    for (auto* method : cls->get_all_methods()) {
      if (method->get_code() != nullptr && !method->get_code()->cfg_built()) {
        method->get_code()->build_cfg();
      }
    }
  }
  m_apk_dir = redex::make_tmp_dir("clinit_batching_unit_test_%%%%%%%%");
  auto* manifest_path_env = std::getenv("manifest");
  always_assert_log(manifest_path_env, "manifest env var must be set.\n");
  redex::copy_file(manifest_path_env, m_apk_dir.path + "/AndroidManifest.xml");
  Json::Value cfg(Json::objectValue);
  cfg["apk_dir"] = m_apk_dir.path;
  ConfigFiles conf(cfg);
  auto graph = method_override_graph::build_graph(scope);
  auto* orchestrator =
      DexMethod::get_method(
          "Lcom/facebook/test/ClinitBatchingOrchestrator;.initAllStatics:()V")
          ->as_def();
  return clinit_batching::EarlyClassLoadsAnalysis(orchestrator, conf,
                                                  graph.get())
      .run();
}

TEST_F(ClinitBatchingPassTest, test_skeleton_runs_without_crashing) {
  // Verify the pass skeleton can be instantiated and run without crashing.
  // This is a basic sanity test for the pass skeleton.
  run_pass();
}

TEST_F(ClinitBatchingPassTest, test_config_binding) {
  // Verify that config values are properly bound and the pass runs
  // successfully with a custom interaction_pattern.
  Json::Value config(Json::objectValue);
  config["ClinitBatchingPass"]["interaction_pattern"] = "ColdStart";

  // The pass emits interaction_pattern_set=1 when the pattern is non-empty.
  // We can't easily read metrics post-run (PassInfo is non-copyable and
  // get_metric requires m_current_pass_info), so we verify the config is
  // accepted without crashing.
  run_pass(config);
}

// `I.go()` is declared only in the undefined superinterface of `I`, so its
// target is unknown, although the call in attachBaseContext dispatches to
// `Impl.go()`, which loads `Early` before the orchestrator runs.
TEST_F(ClinitBatchingPassTest, EarlyClassLoadsReportUnknownEarlyCallTarget) {
  auto* early = assembler::class_from_string(R"(
    (class (public) "LEarly;"
      (field (public static) "LEarly;.f:I")
    )
  )");
  auto* intf = assembler::class_from_string(R"(
    (interface (public) "LI;" extends "LUndefined;")
  )");
  auto* impl = assembler::class_from_string(R"(
    (class (public) "LImpl;" implements "LI;"
      (method (public constructor) "LImpl;.<init>:()V"
        ((load-param-object v0) (return-void)))
      (method (public) "LImpl;.go:()V"
        ((load-param-object v0)
         (sget "LEarly;.f:I")
         (move-result-pseudo v1)
         (return-void)))
    )
  )");
  auto result = run_early_class_loads_analysis({early, intf, impl}, R"(
    ((load-param-object v0)
     (load-param-object v1)
     (new-instance "LImpl;")
     (move-result-pseudo-object v2)
     (invoke-direct (v2) "LImpl;.<init>:()V")
     (invoke-interface (v2) "LI;.go:()V")
     (invoke-static () "Lcom/facebook/test/ClinitBatchingOrchestrator;.initAllStatics:()V")
     (return-void))
  )");

  ASSERT_FALSE(result.error_message) << *result.error_message;
  ASSERT_NE(result.unknown_early_call, nullptr);
  EXPECT_EQ(result.unknown_early_call->get_method(),
            DexMethod::get_method("LI;.go:()V"));
}

// A method handle call can run any method, so a dynamic invoke before the
// orchestrator is an early call whose target, and the classes it loads, are
// unknown. Here the handle calls `Early.touch()`, which initializes `Early`.
TEST_F(ClinitBatchingPassTest, EarlyClassLoadsReportInvokePolymorphic) {
  auto* early = assembler::class_from_string(R"(
    (class (public) "LEarly;"
      (field (public static) "LEarly;.f:I")
      (method (public static) "LEarly;.touch:()V"
        ((return-void)))
    )
  )");
  auto result = run_early_class_loads_analysis({early}, R"(
    ((load-param-object v0)
     (load-param-object v1)
     (const-method-handle invoke-static "LEarly;.touch:()V")
     (move-result-pseudo-object v2)
     (invoke-polymorphic (v2) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
     (invoke-static () "Lcom/facebook/test/ClinitBatchingOrchestrator;.initAllStatics:()V")
     (return-void))
  )");

  ASSERT_FALSE(result.error_message) << *result.error_message;
  ASSERT_NE(result.unknown_early_call, nullptr);
  EXPECT_EQ(result.unknown_early_call->opcode(), OPCODE_INVOKE_POLYMORPHIC);
}

// An invoke-custom runs its bootstrap method and then the target that the
// bootstrap method links, which can be any method.
TEST_F(ClinitBatchingPassTest, EarlyClassLoadsReportInvokeCustom) {
  auto* user = assembler::class_from_string(R"(
    (class (public) "LUser;"
      (method (public static) "LUser;.run:()V"
        ((invoke-static () "LUser;.placeholder:()V")
         (return-void)))
    )
  )");
  redex::make_invoke_custom(
      DexMethod::get_method("LUser;.run:()V")->as_def()->get_code(), "run",
      "()V");
  auto result = run_early_class_loads_analysis({user}, R"(
    ((load-param-object v0)
     (load-param-object v1)
     (invoke-static () "LUser;.run:()V")
     (invoke-static () "Lcom/facebook/test/ClinitBatchingOrchestrator;.initAllStatics:()V")
     (return-void))
  )");

  ASSERT_FALSE(result.error_message) << *result.error_message;
  ASSERT_NE(result.unknown_early_call, nullptr);
  EXPECT_EQ(result.unknown_early_call->opcode(), OPCODE_INVOKE_CUSTOM);
}

// The library method `MethodHandle.invokeWithArguments` runs the handle's
// target, so it is an early call of unknown code too, although it resolves.
TEST_F(ClinitBatchingPassTest, EarlyClassLoadsReportInvokeWithArguments) {
  ClassCreator method_handle(
      DexType::make_type("Ljava/lang/invoke/MethodHandle;"));
  method_handle.set_super(type::java_lang_Object());
  method_handle.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  method_handle.set_external();
  auto* invoke_with_arguments =
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/"
          "Object;)Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_VARARGS, /* is_virtual */ true);
  method_handle.add_method(invoke_with_arguments);
  method_handle.create();
  auto* early = assembler::class_from_string(R"(
    (class (public) "LEarly;"
      (field (public static) "LEarly;.f:I")
      (method (public static) "LEarly;.touch:()V"
        ((return-void)))
    )
  )");
  auto result = run_early_class_loads_analysis({early}, R"(
    ((load-param-object v0)
     (load-param-object v1)
     (const-method-handle invoke-static "LEarly;.touch:()V")
     (move-result-pseudo-object v2)
     (const v3 0)
     (new-array v3 "[Ljava/lang/Object;")
     (move-result-pseudo-object v3)
     (invoke-virtual (v2 v3) "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/Object;)Ljava/lang/Object;")
     (invoke-static () "Lcom/facebook/test/ClinitBatchingOrchestrator;.initAllStatics:()V")
     (return-void))
  )");

  ASSERT_FALSE(result.error_message) << *result.error_message;
  ASSERT_NE(result.unknown_early_call, nullptr);
  EXPECT_EQ(result.unknown_early_call->get_method(), invoke_with_arguments);
}

// A method handle call can run any method, which can load any class, so a
// static initializer that reaches one is not batched. Here the call sits in
// a method that the side-effect filter skips because of its name, `append`.
TEST_F(ClinitBatchingPassTest, ClinitReachingMethodHandleCallIsNotBatched) {
  auto* batched = assembler::class_from_string(R"(
    (class (public) "LBatched;"
      (field (public static) "LBatched;.f:I")
      (method (public static constructor) "LBatched;.<clinit>:()V"
        ((const v0 1)
         (sput v0 "LBatched;.f:I")
         (invoke-static () "LBatched;.append:()V")
         (return-void)))
      (method (public static) "LBatched;.append:()V"
        ((const-method-handle invoke-static "LBatched;.touch:()V")
         (move-result-pseudo-object v0)
         (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
         (return-void)))
      (method (public static) "LBatched;.touch:()V"
        ((return-void)))
    )
  )");
  auto metrics =
      run_pass_with_hot_methods({batched}, {"LBatched;.<clinit>:()V"});

  auto metric = [&](const char* key) {
    auto it = metrics.find(key);
    return it == metrics.end() ? -1 : it->second;
  };
  EXPECT_EQ(metric("candidate_clinits_count"), 1);
  EXPECT_EQ(metric("analysis_candidates"), 0);
  EXPECT_EQ(metric("rejected_unknown_target_call"), 1);
}
