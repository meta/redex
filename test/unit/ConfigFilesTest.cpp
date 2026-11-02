/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstdlib>
#include <fstream>
#include <gtest/gtest.h>
#include <json/reader.h>
#include <json/value.h>
#include <sstream>
#include <unistd.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "GlobalConfig.h"
#include "MethodProfiles.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "SourceBlocksViolations.h"
#include "TypeUtil.h"

class ConfigFilesTest : public RedexTest {
 public:
  void validate_frequencies(
      const UnorderedMap<const DexString*, std::vector<uint8_t>>&
          class_freq_map,
      const std::string& class_name,
      const std::vector<uint8_t>& expected_frequencies) {
    std::vector<uint8_t> frequencies =
        class_freq_map.at(DexString::make_string(class_name));
    EXPECT_EQ(frequencies, expected_frequencies);
  }
};

TEST_F(ConfigFilesTest, read_class_frequencies) {
  auto* class_frequency_path = std::getenv("class_frequencies_path");

  Json::Value json_cfg;
  std::istringstream temp_json(
      "{\"redex\":{\"passes\":[]}, \"class_frequencies\": \"\"}");

  temp_json >> json_cfg;
  json_cfg["class_frequencies"] = class_frequency_path;
  ConfigFiles conf(json_cfg);

  const UnorderedMap<const DexString*, std::vector<uint8_t>>& class_freq_map =
      conf.get_class_frequencies();
  const std::vector<std::string> interactions = conf.get_interactions();
  validate_frequencies(class_freq_map,
                       "Lcom/facebook/redextest/ColdStart;",
                       {100, 2, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1});
  validate_frequencies(
      class_freq_map, "Lcom/facebook/redextest/C1;", {99, 0, 94});
  validate_frequencies(class_freq_map,
                       "Lcom/facebook/redextest/C2;",
                       {71, 0, 70, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
                        0,  0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0,  0, 0,  0, 0, 0, 0, 0, 0, 0, 0, 0, 3});
  validate_frequencies(class_freq_map,
                       "Lcom/facebook/redextest/C3;",
                       {91, 0, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3});
  validate_frequencies(class_freq_map,
                       "Lcom/facebook/redextest/C4;",
                       {66, 0, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0,  0, 0,  0, 0, 0, 0, 0, 0, 0, 0, 14});

  EXPECT_EQ(interactions.at(0), "ColdStart");
  EXPECT_EQ(interactions.at(11), "000009");

  EXPECT_EQ(
      class_freq_map
          .at(DexString::make_string("Lcom/facebook/redextest/ColdStart;"))
          .at(0),
      100);
  EXPECT_EQ(
      class_freq_map.at(DexString::make_string("Lcom/facebook/redextest/C2;"))
          .at(11),
      1);
}

// Helper: write content to a temp file and return its path.
static std::string write_temp_dead_class_file(const std::string& content) {
  char tmpl[] = "/tmp/dead_class_test_XXXXXX";
  int fd = mkstemp(tmpl);
  EXPECT_NE(fd, -1);
  close(fd);
  std::ofstream out(tmpl);
  out << content;
  out.close();
  return tmpl;
}

// Helper: create a ConfigFiles with a dead_class_list pointing to the given
// file.
static ConfigFiles make_config_with_dead_class_list(const std::string& path) {
  Json::Value json_cfg;
  std::istringstream temp_json("{\"redex\":{\"passes\":[]}}");
  temp_json >> json_cfg;
  json_cfg["dead_class_list"] = path;
  return ConfigFiles(json_cfg);
}

// Standard 6-column format (old pipeline output).
TEST_F(ConfigFilesTest, dead_class_list_standard_format) {
  auto path = write_temp_dead_class_file(
      "com.facebook.Foo\t100\t50\t10\t3\t86400\n"
      "com.facebook.Bar\t200\t0\t0\t8\t172800\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 2);
  EXPECT_NE(dead.find("Lcom/facebook/Foo;"), dead.end());
  EXPECT_NE(dead.find("Lcom/facebook/Bar;"), dead.end());

  const auto& foo = dead.at("Lcom/facebook/Foo;");
  EXPECT_EQ(foo.sampled, 100);
  EXPECT_EQ(foo.unsampled, 50);
  EXPECT_EQ(foo.beta_unsampled, 10);
  EXPECT_EQ(foo.last_modified_count, 3);
  EXPECT_EQ(foo.seconds_since_last_modified, 86400);

  const auto& bar = dead.at("Lcom/facebook/Bar;");
  EXPECT_EQ(bar.sampled, 200);
  EXPECT_EQ(bar.seconds_since_last_modified, 172800);

  std::remove(path.c_str());
}

// "null" string in numeric column — should use struct default, not crash.
TEST_F(ConfigFilesTest, dead_class_list_null_string_value) {
  auto path = write_temp_dead_class_file(
      "com.facebook.NullTest\t100\t50\t10\t0\tnull\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 1);
  EXPECT_NE(dead.find("Lcom/facebook/NullTest;"), dead.end());
  const auto& entry = dead.at("Lcom/facebook/NullTest;");
  EXPECT_EQ(entry.sampled, 100);
  EXPECT_EQ(entry.last_modified_count, 0);
  // "null" is not parseable — should keep default value (0).
  EXPECT_EQ(entry.seconds_since_last_modified, 0);
}

// Quoted class names (new to_csv_file format) — quotes should be stripped.
TEST_F(ConfigFilesTest, dead_class_list_quoted_classname) {
  auto path = write_temp_dead_class_file(
      "\"com.facebook.Quoted\"\t100\t50\t10\t3\t86400\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 1);
  // Class name should have quotes stripped.
  EXPECT_NE(dead.find("Lcom/facebook/Quoted;"), dead.end());
  EXPECT_EQ(dead.at("Lcom/facebook/Quoted;").sampled, 100);

  std::remove(path.c_str());
}

// Extra trailing columns (date + app name from new pipeline) — should be
// ignored.
TEST_F(ConfigFilesTest, dead_class_list_extra_columns) {
  auto path = write_temp_dead_class_file(
      "com.facebook.Extra\t100\t50\t10\t3\t86400\t\"2026-04-"
      "04\"\t\"katana\"\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 1);
  EXPECT_NE(dead.find("Lcom/facebook/Extra;"), dead.end());
  EXPECT_EQ(dead.at("Lcom/facebook/Extra;").seconds_since_last_modified, 86400);

  std::remove(path.c_str());
}

// Fewer columns than expected — missing columns should keep struct defaults.
TEST_F(ConfigFilesTest, dead_class_list_fewer_columns) {
  // Only classname + sampled (2 columns instead of 6).
  auto path = write_temp_dead_class_file("com.facebook.Minimal\t100\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 1);
  EXPECT_NE(dead.find("Lcom/facebook/Minimal;"), dead.end());
  const auto& entry = dead.at("Lcom/facebook/Minimal;");
  EXPECT_EQ(entry.sampled, 100);
  // Rest should be struct defaults.
  EXPECT_EQ(entry.unsampled, 0);
  EXPECT_EQ(entry.beta_unsampled, 0);
  EXPECT_EQ(entry.last_modified_count, 1);
  EXPECT_EQ(entry.seconds_since_last_modified, 0);

  std::remove(path.c_str());
}

// Combined: new pipeline format with quotes, nulls, and extra columns.
TEST_F(ConfigFilesTest, dead_class_list_new_pipeline_format) {
  auto path = write_temp_dead_class_file(
      "\"com.facebook.Normal\"\t100\t50\t10\t3\t86400\t\"2026-04-"
      "04\"\t\"katana\"\n"
      "\"com.facebook.NullCol\"\t200\t30\t0\t0\tnull\t\"2026-04-"
      "04\"\t\"katana\"\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 2);
  // Quotes stripped, values parsed correctly.
  EXPECT_NE(dead.find("Lcom/facebook/Normal;"), dead.end());
  EXPECT_EQ(dead.at("Lcom/facebook/Normal;").seconds_since_last_modified,
            86400);
  // "null" → default 0.
  EXPECT_NE(dead.find("Lcom/facebook/NullCol;"), dead.end());
  EXPECT_EQ(dead.at("Lcom/facebook/NullCol;").seconds_since_last_modified, 0);

  std::remove(path.c_str());
}

// Empty file — should produce an empty dead class list.
TEST_F(ConfigFilesTest, dead_class_list_empty_file) {
  auto path = write_temp_dead_class_file("");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 0);

  std::remove(path.c_str());
}

// A "$relocated" row is filtered out of the dead-class list rather than being
// treated as a dead class in its own right.
TEST_F(ConfigFilesTest, dead_class_list_relocated_class) {
  auto path = write_temp_dead_class_file(
      "com.facebook.Alive$relocated\t100\t50\t10\t3\t86400\n"
      "com.facebook.Dead\t200\t0\t0\t8\t172800\n");
  auto conf = make_config_with_dead_class_list(path);
  const auto& dead = conf.get_dead_class_list();

  EXPECT_EQ(dead.size(), 1);
  EXPECT_NE(dead.find("Lcom/facebook/Dead;"), dead.end());
  EXPECT_EQ(dead.find("Lcom/facebook/Alive;"), dead.end());
  EXPECT_EQ(dead.find("Lcom/facebook/Alive$relocated;"), dead.end());

  std::remove(path.c_str());
}

// The defaults have to keep matching the values that were hardcoded in
// PassManager before they became configurable, or every enabled run silently
// starts measuring something else.
TEST_F(ConfigFilesTest, violations_tracking_config_defaults) {
  Json::Value json_cfg;
  std::istringstream temp_json("{\"redex\":{\"passes\":[]}}");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);
  conf.parse_global_config();

  const auto* config =
      conf.get_global_config().get_config_by_name<ViolationsTrackingConfig>(
          "violations_tracking");
  ASSERT_NE(config, nullptr);
  EXPECT_FALSE(config->enabled);
  EXPECT_EQ(config->violation_kinds, std::vector<std::string>{"ChainAndDom"});
  EXPECT_EQ(config->top_n, 10u);
  EXPECT_TRUE(config->methods_to_vis.empty());
  EXPECT_TRUE(config->source_blocks_to_track.empty());
  EXPECT_FALSE(config->track_intermethod_violations);
  EXPECT_FALSE(config->print_all_violations);
  EXPECT_FALSE(config->ignore_undefined);
}

TEST_F(ConfigFilesTest, violations_tracking_config_from_json) {
  Json::Value json_cfg;
  std::istringstream temp_json(R"({
    "redex": {"passes": []},
    "violations_tracking": {
      "enabled": true,
      "violation_kinds": ["HotImmediateDomNotHot"],
      "top_n": 5,
      "methods_to_vis": ["LFoo;.bar:()V", "LFoo;.baz:()V"],
      "source_blocks_to_track": ["LFoo;.bar:()V@3"],
      "track_intermethod_violations": true,
      "print_all_violations": true,
      "ignore_undefined": true
    }
  })");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);
  conf.parse_global_config();

  const auto* config =
      conf.get_global_config().get_config_by_name<ViolationsTrackingConfig>(
          "violations_tracking");
  ASSERT_NE(config, nullptr);
  EXPECT_TRUE(config->enabled);
  EXPECT_EQ(config->violation_kinds,
            std::vector<std::string>{"HotImmediateDomNotHot"});
  EXPECT_EQ(config->top_n, 5u);
  EXPECT_EQ(config->methods_to_vis,
            (std::vector<std::string>{"LFoo;.bar:()V", "LFoo;.baz:()V"}));
  EXPECT_EQ(config->source_blocks_to_track,
            std::vector<std::string>{"LFoo;.bar:()V@3"});
  EXPECT_TRUE(config->track_intermethod_violations);
  EXPECT_TRUE(config->print_all_violations);
  EXPECT_TRUE(config->ignore_undefined);
}

// Every configured name has to resolve to a violation kind; PassManager aborts
// on one that does not.
TEST_F(ConfigFilesTest, violations_tracking_config_kinds_are_parseable) {
  Json::Value json_cfg;
  std::istringstream temp_json("{\"redex\":{\"passes\":[]}}");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);
  conf.parse_global_config();

  const auto* config =
      conf.get_global_config().get_config_by_name<ViolationsTrackingConfig>(
          "violations_tracking");
  ASSERT_NE(config, nullptr);
  for (const auto& name : config->violation_kinds) {
    EXPECT_TRUE(source_blocks::violation_name_to_enum(name).has_value())
        << "unparseable default violation kind: " << name;
  }
}

// The setting moved out of `pass_manager`. Configurable drops unbound keys
// silently, so without an explicit check an old config would keep parsing and
// quietly stop tracking; make sure it says so instead.
TEST_F(ConfigFilesTest, violations_tracking_old_pass_manager_key_is_rejected) {
  Json::Value json_cfg;
  std::istringstream temp_json(
      R"({"redex": {"passes": []},
          "pass_manager": {"violations_tracking": true}})");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);

  EXPECT_THROW(conf.parse_global_config(), RedexException);
}

// ...and the key is only rejected when it is actually set, so a config that
// merely mentions `pass_manager` is unaffected.
TEST_F(ConfigFilesTest, violations_tracking_unset_old_key_is_fine) {
  Json::Value json_cfg;
  std::istringstream temp_json(
      R"({"redex": {"passes": []},
          "pass_manager": {"violations_tracking": false, "dump_mrefs": true}})");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);
  conf.parse_global_config();

  const auto* pm_config =
      conf.get_global_config().get_config_by_name<PassManagerConfig>(
          "pass_manager");
  ASSERT_NE(pm_config, nullptr);
  EXPECT_TRUE(pm_config->dump_mrefs);
}

namespace {

std::string write_lines(const std::string& dir,
                        const std::string& name,
                        const std::vector<std::string>& lines) {
  std::string path = dir + "/" + name;
  std::ofstream out(path);
  for (const auto& line : lines) {
    out << line << "\n";
  }
  return path;
}

// The betamap complement only considers methods whose class is in scope, so the
// profile entries below need a real class backing them.
void define_class_with_method(const std::string& descriptor) {
  ClassCreator cc(DexType::make_type(descriptor));
  cc.set_super(type::java_lang_Object());
  cc.add_method(DexMethod::make_method(descriptor + ".m:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.create();
}

} // namespace

// `complement_betamap_with_method_profiles_symbols` splits method-profile
// classes at appear_percent 20 and splices each bucket in immediately before
// its own marker. "all-20pct" keeps the 20pct bucket and drops the other.
TEST_F(ConfigFilesTest, complement_betamap_bucket_selection) {
  auto tmp_dir = redex::make_tmp_dir("redex_complement_betamap_%%%%%%%%");

  define_class_with_method("LHot;"); // 50 pct -> 20pct bucket
  define_class_with_method("LWarm;"); // 5 pct -> 1pct bucket

  // Neither class is listed in the betamap, so neither is deduped away.
  auto betamap =
      write_lines(tmp_dir.path,
                  "betamap.txt",
                  {"some/Existing.class", "ColdStart20PctEnd.class",
                   "another/Existing.class", "ColdStart1PctEnd.class"});
  auto profiles = write_lines(
      tmp_dir.path,
      "profiles.csv",
      {"interaction,appear#", "ColdStart,2",
       std::string("index,name,appear100,appear#,avg_call,avg_order,") +
           "avg_rank100,min_api_level",
       "1,LHot;.m:()V,50.0000,1,2.0000,0.0000,0.000000,29",
       "2,LWarm;.m:()V,5.0000,2,3.0000,0.0000,0.000000,29"});

  auto coldstart_classes_for = [&](const std::string& mode) {
    Json::Value cfg;
    std::istringstream ss(R"({"redex": {"passes": []}})");
    ss >> cfg;
    cfg["coldstart_classes"] = betamap;
    Json::Value mp = Json::arrayValue;
    mp.resize(1);
    mp[0] = profiles;
    cfg["agg_method_stats_files"] = mp;
    cfg["complement_betamap_with_method_profiles_symbols"] = mode;
    ConfigFiles conf(cfg);
    return std::vector<std::string>(conf.get_coldstart_classes());
  };

  EXPECT_EQ(coldstart_classes_for("all"),
            (std::vector<std::string>{
                "Lsome/Existing;", "LHot;", "LColdStart20PctEnd;",
                "Lanother/Existing;", "LWarm;", "LColdStart1PctEnd;"}));

  EXPECT_EQ(coldstart_classes_for("all-20pct"),
            (std::vector<std::string>{
                "Lsome/Existing;", "LHot;", "LColdStart20PctEnd;",
                "Lanother/Existing;", "LColdStart1PctEnd;"}));

  // Neither class is anonymous, so "anon" splices nothing.
  EXPECT_EQ(
      coldstart_classes_for("anon"),
      (std::vector<std::string>{"Lsome/Existing;", "LColdStart20PctEnd;",
                                "Lanother/Existing;", "LColdStart1PctEnd;"}));
}

TEST_F(ConfigFilesTest, complement_betamap_rejects_unknown_mode) {
  auto tmp_dir = redex::make_tmp_dir("redex_complement_betamap_%%%%%%%%");
  // A betamap is required: load_coldstart_classes() returns early without one,
  // before it ever parses the mode.
  auto betamap =
      write_lines(tmp_dir.path, "betamap.txt", {"some/Existing.class"});

  Json::Value cfg;
  std::istringstream ss(R"({"redex": {"passes": []}})");
  ss >> cfg;
  cfg["coldstart_classes"] = betamap;
  cfg["complement_betamap_with_method_profiles_symbols"] = "20pct";
  ConfigFiles conf(cfg);
  EXPECT_ANY_THROW(conf.get_coldstart_classes());
}

// `agg_method_stats_ignore_split_methods` keeps method-profile rows for split
// methods from being matched by name to the split methods created later, while
// other generated methods are still matched.
TEST_F(ConfigFilesTest, agg_method_stats_ignore_split_methods) {
  auto tmp_dir = redex::make_tmp_dir("redex_ignore_split_methods_%%%%%%%%");

  // Each case uses its own class, since methods outlive a ConfigFiles. Loading
  // requires at least one row that resolves.
  auto stats_after_creating_methods = [&](const std::string& cls,
                                          bool ignore_split_methods) {
    DexMethod::make_method(cls + ".existing:()V");
    auto profiles = write_lines(
        tmp_dir.path,
        cls.substr(1, cls.size() - 2) + ".csv",
        {"interaction,appear#", "ColdStart,2",
         std::string("index,name,appear100,appear#,avg_call,avg_order,") +
             "avg_rank100,min_api_level",
         "0," + cls + ".existing:()V,90.0000,1,1.0000,0.0000,0.0,-1",
         "1," + cls + ".get$split$hot_cold$0$1:()V,70.0000,1,2.0,0.0,0.0,-1",
         "2," + cls + ".$outlined$0$abcdef:()V,60.0000,1,5.0,0.0,0.0,-1"});
    Json::Value cfg;
    std::istringstream ss(R"({"redex": {"passes": []}})");
    ss >> cfg;
    Json::Value mp = Json::arrayValue;
    mp.resize(1);
    mp[0] = profiles;
    cfg["agg_method_stats_files"] = mp;
    cfg["agg_method_stats_ignore_split_methods"] = ignore_split_methods;
    ConfigFiles conf(cfg);
    auto& method_profiles = conf.get_method_profiles();
    // Both methods are created after the profiles are loaded, as a pass would.
    auto* split = DexMethod::make_method(cls + ".get$split$hot_cold$0$1:()V");
    auto* outlined = DexMethod::make_method(cls + ".$outlined$0$abcdef:()V");
    method_profiles.process_unresolved_lines();
    return std::make_pair(
        method_profiles.get_method_stat(method_profiles::COLD_START, split)
            .has_value(),
        method_profiles.get_method_stat(method_profiles::COLD_START, outlined)
            .has_value());
  };

  EXPECT_EQ(stats_after_creating_methods("LMatched;", false),
            std::make_pair(true, true));
  EXPECT_EQ(stats_after_creating_methods("LIgnored;", true),
            std::make_pair(false, true));
}
