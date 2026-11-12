/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <filesystem>
#include <optional>
#include <string>
#include <vector>

#include <boost/algorithm/string/join.hpp>
#include <gtest/gtest.h>
#include <json/value.h>

#include "ArtProfileWriterPass.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "JsonWrapper.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Show.h"

class ArtProfileWriterPassTest : public RedexTest {};

class ArtProfileWriterPassWriteFailureTest
    : public ArtProfileWriterPassTest,
      public ::testing::WithParamInterface<const char*> {};

TEST_P(ArtProfileWriterPassWriteFailureTest,
       abortsInsteadOfIgnoringFailedWrites) {
  ClassCreator creator(DexType::make_type("LProfileWrite;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LProfileWrite;.m:()V" ((return-void)))
  )"));
  DexStore store("classes");
  store.add_classes({creator.create()});
  DexStoresVector stores;
  stores.emplace_back(std::move(store));
  Json::Value config;
  config["baseline_profile"]["default"]["use_final_redex_generated_profile"] =
      true;
  auto tmp = redex::make_tmp_dir("profile_write_failure%%%%%%%%");
  ConfigFiles conf(config);
  conf.set_outdir(tmp.path);
  conf.parse_global_config();
  std::filesystem::create_directory(conf.metafile(GetParam()));
  ArtProfileWriterPass pass;
  PassManager manager({&pass}, conf);
  EXPECT_THROW(manager.run_passes(stores, conf), RedexException);
}

INSTANTIATE_TEST_SUITE_P(
    ProfileFiles,
    ArtProfileWriterPassWriteFailureTest,
    ::testing::Values("default-baseline-profile.txt",
                      "additional-baseline-profiles.list"));

// Runs `ArtProfileWriterPass` through a real `PassManager` with never-compile
// enabled and a call-count threshold every method meets, so the only thing
// deciding whether a method is dropped from the baseline profile is its
// control flow: methods that loop are kept, because dropping one leaves its
// loop to the interpreter.

class ArtProfileWriterNeverCompileTest : public ArtProfileWriterPassTest {
 public:
  // The number of methods the pass dropped from the default baseline profile,
  // for a scope holding one static method with the given body.
  int64_t never_compiled_methods(const std::string& body) {
    ClassCreator cc{DexType::make_type("LNeverCompile;")};
    cc.set_super(type::java_lang_Object());
    auto* m = DexMethod::make_method("LNeverCompile;.f:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(body),
                                  /* is_virtual */ false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    DexStore store("classes");
    store.add_classes({cc.create()});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));

    Json::Value json_conf;
    auto& harvest = json_conf["baseline_profile"]["default"]["harvest_config"];
    harvest["enable_never_compile"] = true;
    // Consider methods that are not in the profile, and select every method
    // that is called at most 0 times -- with no interactions, that is all of
    // them.
    harvest["never_compile_ignore_hot"] = true;
    harvest["never_compile_callcount_threshold"] = 0;

    ConfigFiles conf(json_conf);
    conf.parse_global_config();
    auto tmp_dir = redex::make_tmp_dir("apw_never_compile_%%%%%%%%");
    conf.set_outdir(tmp_dir.path);

    ArtProfileWriterPass pass;
    PassManager manager({&pass}, conf, RedexOptions{});
    manager.run_passes(stores, conf);

    for (const auto& info : manager.get_pass_info()) {
      if (info.pass == &pass) {
        auto it = info.metrics.find("never_compiled_methods");
        return it == info.metrics.end() ? -1 : it->second;
      }
    }
    ADD_FAILURE() << "ArtProfileWriterPass did not run";
    return -1;
  }
};

// The control: with the configuration above, a method without a loop is
// dropped. Without this, the tests below would pass on a pass that never drops
// anything.
TEST_F(ArtProfileWriterNeverCompileTest, methodWithoutLoopIsNeverCompiled) {
  EXPECT_EQ(never_compiled_methods(R"(
    (
      (const v0 1)
      (return-void)
    )
  )"),
            1);
}

TEST_F(ArtProfileWriterNeverCompileTest, methodWithLoopStaysCompiled) {
  EXPECT_EQ(never_compiled_methods(R"(
    (
      (const v0 3)
      (:loop)
      (add-int/lit v0 v0 -1)
      (if-gtz v0 :loop)
      (return-void)
    )
  )"),
            0);
}

// A cycle that can be entered at either of its two blocks runs as many times
// as any other loop, so it has to keep the method compiled just the same.
TEST_F(ArtProfileWriterNeverCompileTest, methodWithTwoEntryCycleStaysCompiled) {
  EXPECT_EQ(never_compiled_methods(R"(
    (
      (const v0 3)
      (if-eqz v0 :second)
      (:first)
      (add-int/lit v0 v0 1)
      (:second)
      (add-int/lit v0 v0 -1)
      (if-gtz v0 :first)
      (return-void)
    )
  )"),
            0);
}

namespace {

// The `never_inline_min_hot_callsites_min_code_units` that `run_pass` sets
// unless told otherwise. `kLargeCalleeCodeUnits` clears it.
constexpr int64_t kMinCodeUnits = 12;
constexpr size_t kDefaultMinCodeUnits =
    ArtProfileWriterPass::kDefaultNeverInlineMinHotCallsitesMinCodeUnits;
constexpr size_t kLargeCalleeCodeUnits = 30;
constexpr int64_t kHotCallsites = 3;

struct Fixture {
  DexMethod* callee;
  std::vector<DexMethod*> callers;
  std::vector<DexStore> stores;
};

// Makes a callee exactly `code_units` code units long.
DexMethod* make_callee(ClassCreator& cc, size_t code_units) {
  std::string callee_code =
      "((load-param v0)" +
      boost::algorithm::join(
          std::vector<std::string>(code_units - 1, "(move v1 v0)"), "") +
      "(return-void))";
  auto* callee =
      DexMethod::make_method("LMinHotCallsites;.callee:(I)V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(callee_code), false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  EXPECT_EQ(callee->get_code()->estimate_code_units(), code_units);
  cc.add_method(callee);
  return callee;
}

// Makes a caller that calls the callee `call_count` times from a block whose
// source-block profile is `block_profile`.
DexMethod* make_caller(ClassCreator& cc,
                       const std::string& block_profile,
                       size_t call_count) {
  std::string descriptor =
      "LMinHotCallsites;.caller" +
      std::to_string(cc.get_class()->get_dmethods().size()) + ":()V";
  std::string code =
      "((.src_block \"\" 0 " + block_profile + ")(const v0 0)" +
      boost::algorithm::join(
          std::vector<std::string>(
              call_count,
              "(invoke-static (v0) \"LMinHotCallsites;.callee:(I)V\")"),
          "") +
      "(return-void))";
  auto* caller =
      DexMethod::make_method(descriptor)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(code), false);
  caller->set_deobfuscated_name(show(caller));
  caller->get_code()->build_cfg();
  cc.add_method(caller);
  return caller;
}

// Returns a callee of `code_units` code units, called `hot_callsites` times
// from a hot block and `cold_callsites` times from a cold block.
Fixture make_fixture(size_t code_units,
                     int64_t hot_callsites,
                     int64_t cold_callsites = 0) {
  ClassCreator cc{DexType::make_type("LMinHotCallsites;")};
  cc.set_super(type::java_lang_Object());
  auto* callee = make_callee(cc, code_units);
  auto* hot_caller = make_caller(cc, "(1.0 100)", hot_callsites);
  auto* cold_caller = make_caller(cc, "(0 0)", cold_callsites);
  DexStore store("classes");
  store.add_classes({cc.create()});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  return Fixture{callee, {hot_caller, cold_caller}, std::move(stores)};
}

// Makes `is_compiled` true for `methods`.
void mark_compiled(ConfigFiles& conf, const std::vector<DexMethod*>& methods) {
  UnorderedMap<const DexMethodRef*, method_profiles::Stats> manual_hot_stats;
  for (auto* m : methods) {
    manual_hot_stats[m] = method_profiles::Stats{};
  }
  conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
      "manual_hot", manual_hot_stats);
}

// Pass options to set. An empty one stays at the pass's default.
struct Options {
  std::optional<int64_t> min_hot_callsites;
  std::optional<int64_t> min_code_units = kMinCodeUnits;
};

// Runs the pass on `fx` with `options` and returns its metrics.
UnorderedMap<std::string, int64_t> run_pass(Fixture& fx,
                                            const Options& options) {
  Json::Value json_conf;
  json_conf["ArtProfileWriterPass"]["never_inline_attach_annotations"] = true;
  if (options.min_hot_callsites) {
    json_conf["ArtProfileWriterPass"]["never_inline_min_hot_callsites"] =
        Json::Int64(*options.min_hot_callsites);
  }
  if (options.min_code_units) {
    json_conf["ArtProfileWriterPass"]
             ["never_inline_min_hot_callsites_min_code_units"] =
                 Json::Int64(*options.min_code_units);
  }
  // Makes call sites in a block with source-block profile `(0 0)` cold.
  json_conf["ArtProfileWriterPass"]["never_inline_hot_block_appear_threshold"] =
      50;

  ConfigFiles conf(json_conf);
  conf.parse_global_config();
  auto tmp_dir = redex::make_tmp_dir("min_hot_callsites_%%%%%%%%");
  conf.set_outdir(tmp_dir.path);
  std::vector<DexMethod*> compiled = fx.callers;
  compiled.push_back(fx.callee);
  mark_compiled(conf, compiled);

  ArtProfileWriterPass pass;
  PassManager manager({&pass}, conf, RedexOptions{});
  manager.run_passes(fx.stores, conf);
  for (const auto& info : manager.get_pass_info()) {
    if (info.pass == &pass) {
      return info.metrics;
    }
  }
  ADD_FAILURE() << "ArtProfileWriterPass did not run";
  return {};
}

} // namespace

class ArtProfileWriterNeverInlineMinHotCallsitesTest
    : public ArtProfileWriterPassTest {};

TEST_F(ArtProfileWriterNeverInlineMinHotCallsitesTest,
       CalleeWithEnoughHotCallsitesHasItsHotCallsiteCountReported) {
  auto fx = make_fixture(kLargeCalleeCodeUnits, kHotCallsites);

  auto metrics = run_pass(fx, {.min_hot_callsites = kHotCallsites});

  auto it = metrics.find(
      "never_inline_min_hot_callsites_LMinHotCallsites;.callee:(I)V");
  ASSERT_NE(it, metrics.end());
  EXPECT_EQ(it->second, kHotCallsites);
}

TEST_F(ArtProfileWriterNeverInlineMinHotCallsitesTest,
       AllocatedCallerRegistersStillEnforceTheBudget) {
  auto fx = make_fixture(kLargeCalleeCodeUnits, kHotCallsites, 2);
  for (auto* caller : fx.callers) {
    caller->get_code()->cfg().set_registers_size(33);
  }
  auto metrics = run_pass(fx, {.min_hot_callsites = kHotCallsites});
  EXPECT_EQ(metrics.at("never_inline_callers_too_many_registers"), 2);
  EXPECT_FALSE(
      has_anno(fx.callee, type::dalvik_annotation_optimization_NeverInline()));
}

TEST_F(ArtProfileWriterNeverInlineMinHotCallsitesTest,
       ConfigWithZeroMinHotCallsitesIsRejected) {
  Json::Value json;
  json["never_inline_min_hot_callsites"] = 0;
  ArtProfileWriterPass pass;

  EXPECT_THROW({ pass.parse_config(JsonWrapper(json)); }, RedexException);
}

struct ArtProfileWriterNeverInlineCallsiteCountCase {
  std::string name;
  int64_t hot_callsites;
  int64_t cold_callsites;
  std::optional<int64_t> min_hot_callsites;
  bool annotated;
};

class ArtProfileWriterNeverInlineCallsiteCountTest
    : public ArtProfileWriterNeverInlineMinHotCallsitesTest,
      public ::testing::WithParamInterface<
          ArtProfileWriterNeverInlineCallsiteCountCase> {};

TEST_P(ArtProfileWriterNeverInlineCallsiteCountTest,
       CalleeIsAnnotatedIffHotCallsitesReachMin) {
  const auto& c = GetParam();
  auto fx =
      make_fixture(kLargeCalleeCodeUnits, c.hot_callsites, c.cold_callsites);

  run_pass(fx, {.min_hot_callsites = c.min_hot_callsites});

  EXPECT_EQ(
      has_anno(fx.callee, type::dalvik_annotation_optimization_NeverInline()),
      c.annotated);
}

INSTANTIATE_TEST_SUITE_P(
    ArtProfileWriterNeverInlineCallsiteCountTests,
    ArtProfileWriterNeverInlineCallsiteCountTest,
    ::testing::ValuesIn(
        std::initializer_list<
            ArtProfileWriterNeverInlineCallsiteCountTest::ParamType>{
            {.name = "DefaultMinIsNotAnnotated",
             .hot_callsites = 3,
             .cold_callsites = 0,
             .min_hot_callsites = std::nullopt,
             .annotated = false},
            {.name = "FewerHotCallsitesThanMinIsNotAnnotated",
             .hot_callsites = 3,
             .cold_callsites = 0,
             .min_hot_callsites = 4,
             .annotated = false},
            {.name = "MinReachedOnlyIfColdCallsitesCountIsNotAnnotated",
             .hot_callsites = 2,
             .cold_callsites = 2,
             .min_hot_callsites = 3,
             .annotated = false},
            {.name = "ExactlyMinHotCallsitesIsAnnotated",
             .hot_callsites = 3,
             .cold_callsites = 0,
             .min_hot_callsites = 3,
             .annotated = true},
            {.name = "MoreHotCallsitesThanMinIsAnnotated",
             .hot_callsites = 3,
             .cold_callsites = 0,
             .min_hot_callsites = 2,
             .annotated = true},
            {.name = "ExactlyMinHotCallsitesPlusColdOnesIsAnnotated",
             .hot_callsites = 2,
             .cold_callsites = 2,
             .min_hot_callsites = 2,
             .annotated = true}}),
    [](const testing::TestParamInfo<
        ArtProfileWriterNeverInlineCallsiteCountTest::ParamType>& info) {
      return info.param.name;
    });

struct ArtProfileWriterNeverInlineCodeUnitCountCase {
  std::string name;
  size_t code_units;
  std::optional<int64_t> min_code_units;
  bool annotated;
};

class ArtProfileWriterNeverInlineCodeUnitCountTest
    : public ArtProfileWriterNeverInlineMinHotCallsitesTest,
      public ::testing::WithParamInterface<
          ArtProfileWriterNeverInlineCodeUnitCountCase> {};

TEST_P(ArtProfileWriterNeverInlineCodeUnitCountTest,
       CalleeIsAnnotatedIffItReachesMinCodeUnits) {
  const auto& c = GetParam();
  auto fx = make_fixture(c.code_units, kHotCallsites);

  run_pass(
      fx,
      {.min_hot_callsites = kHotCallsites, .min_code_units = c.min_code_units});

  EXPECT_EQ(
      has_anno(fx.callee, type::dalvik_annotation_optimization_NeverInline()),
      c.annotated);
}

INSTANTIATE_TEST_SUITE_P(
    ArtProfileWriterNeverInlineCodeUnitCountTests,
    ArtProfileWriterNeverInlineCodeUnitCountTest,
    ::testing::ValuesIn(
        std::initializer_list<
            ArtProfileWriterNeverInlineCodeUnitCountTest::ParamType>{
            {.name = "ShorterThanMinIsNotAnnotated",
             .code_units = kMinCodeUnits - 1,
             .min_code_units = kMinCodeUnits,
             .annotated = false},
            {.name = "AsLongAsMinIsAnnotated",
             .code_units = kMinCodeUnits,
             .min_code_units = kMinCodeUnits,
             .annotated = true},
            {.name = "LongerThanMinIsAnnotated",
             .code_units = kLargeCalleeCodeUnits,
             .min_code_units = kMinCodeUnits,
             .annotated = true},
            {.name = "ShorterThanDefaultMinIsNotAnnotated",
             .code_units = kDefaultMinCodeUnits - 1,
             .min_code_units = std::nullopt,
             .annotated = false},
            {.name = "AsLongAsDefaultMinIsAnnotated",
             .code_units = kDefaultMinCodeUnits,
             .min_code_units = std::nullopt,
             .annotated = true}}),
    [](const testing::TestParamInfo<
        ArtProfileWriterNeverInlineCodeUnitCountTest::ParamType>& info) {
      return info.param.name;
    });

class ArtProfileWriterHugeMethodTest : public RedexTest {
 public:
  // Runs the pass on a hot method of 11 code units and returns how many
  // profiled methods it counted as too large to compile, or -1.
  int64_t uncompilable_huge(std::optional<uint32_t> huge_method_max) {
    std::string body = "(";
    for (int i = 0; i < 10; ++i) {
      body += "(nop)";
    }
    body += "(return-void))";
    ClassCreator cc(DexType::make_type("LHuge;"));
    cc.set_super(type::java_lang_Object());
    auto* m = assembler::method_from_string(
        "(method (public static) \"LHuge;.m:()V\" " + body + ")");
    cc.add_method(m);
    DexStore store("classes");
    store.add_classes({cc.create()});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));

    Json::Value json_conf;
    json_conf["baseline_profile"]["default"]
             ["use_final_redex_generated_profile"] = true;
    if (huge_method_max) {
      json_conf["dex2oat"]["huge_method_max"] = *huge_method_max;
    }
    ConfigFiles conf(json_conf);
    conf.parse_global_config();
    UnorderedMap<const DexMethodRef*, method_profiles::Stats> hot;
    hot[m] = method_profiles::Stats{};
    conf.get_method_profiles() =
        method_profiles::MethodProfiles::initialize("manual_hot", hot);
    auto tmp_dir = redex::make_tmp_dir("apw_huge_%%%%%%%%");
    conf.set_outdir(tmp_dir.path);

    ArtProfileWriterPass pass;
    PassManager manager({&pass}, conf, RedexOptions{});
    manager.run_passes(stores, conf);
    for (const auto& info : manager.get_pass_info()) {
      if (info.pass == &pass) {
        auto it = info.metrics.find("profile_default_uncompilable_huge");
        return it == info.metrics.end() ? -1 : it->second;
      }
    }
    ADD_FAILURE() << "ArtProfileWriterPass did not run";
    return -1;
  }
};

TEST_F(ArtProfileWriterHugeMethodTest, defaultLimit) {
  EXPECT_EQ(uncompilable_huge(std::nullopt), 0);
}

TEST_F(ArtProfileWriterHugeMethodTest, globalLimitAtTheMethodSize) {
  EXPECT_EQ(uncompilable_huge(11), 0);
}

TEST_F(ArtProfileWriterHugeMethodTest, globalLimitBelowTheMethodSize) {
  EXPECT_EQ(uncompilable_huge(10), 1);
}
