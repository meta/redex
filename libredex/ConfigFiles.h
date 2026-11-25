/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <vector>

#include "DeterministicContainers.h"
#include "JsonWrapper.h"
#include "RedexOptions.h"

class DexClass;
class DexMethodRef;
class DexString;
class DexType;
class GlobalConfig;
struct ProguardMap;

using Scope = std::vector<DexClass*>;

constexpr const char* CLASS_SPLITTING_RELOCATED_SUFFIX = "$relocated";
constexpr const size_t CLASS_SPLITTING_RELOCATED_SUFFIX_LEN = 10;

namespace Json {
class Value;
} // namespace Json

namespace api {
class AndroidSDK;
} // namespace api

namespace baseline_profiles {
struct BaselineProfileConfig;
using BaselineProfileConfigMap =
    UnorderedMap<std::string, BaselineProfileConfig>;
} // namespace baseline_profiles

namespace inliner {
struct InlinerConfig;
} // namespace inliner

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

/**
 * ConfigFiles should be a readonly structure
 */
struct ConfigFiles {
  explicit ConfigFiles(const Json::Value& config);
  ConfigFiles(const Json::Value& config, std::string outdir);
  ~ConfigFiles();

  const UnorderedMap<const DexString*, std::vector<uint8_t>>&
  get_class_frequencies() {
    if (m_class_freq_map.empty()) {
      m_class_freq_map = load_class_frequencies();
    }
    return m_class_freq_map;
  }

  const std::vector<std::string>& get_interactions() {
    if (m_interactions.empty()) {
      load_class_frequencies();
    }
    return m_interactions;
  }

  const std::vector<std::string>& get_coldstart_classes() {
    if (m_coldstart_classes.empty()) {
      m_coldstart_classes = load_coldstart_classes();
    }
    return m_coldstart_classes;
  }

  const std::vector<std::string>& get_coldstart_methods() {
    {
      std::lock_guard<std::mutex> lock(m_coldstart_methods_mutex);
      if (m_coldstart_methods_loaded) {
        return m_coldstart_methods;
      }
    }
    // Parse outside the lock; failed loads leave initialization retryable.
    auto methods = load_coldstart_methods();
    std::lock_guard<std::mutex> lock(m_coldstart_methods_mutex);
    if (!m_coldstart_methods_loaded) {
      m_coldstart_methods = std::move(methods);
      m_coldstart_methods_loaded = true;
    }
    return m_coldstart_methods;
  }

  /**
   * NOTE: ONLY use if you know what you are doing!
   */
  void update_coldstart_classes(
      std::vector<std::string> new_coldstart_classes) {
    m_coldstart_classes = std::move(new_coldstart_classes);
  }

  // Classes a pass synthesized after profile collection that must still land
  // in the baseline profile's class section. MethodProfiles-derived entries
  // can never name these classes, so producers record them here and
  // ArtProfileWriterPass drains the list.
  void add_extra_baseline_profile_class(std::string class_name) {
    m_extra_baseline_profile_classes.push_back(std::move(class_name));
  }

  const std::vector<std::string>& get_extra_baseline_profile_classes() const {
    return m_extra_baseline_profile_classes;
  }

  void ensure_class_lists_loaded() {
    if (!m_load_class_lists_attempted) {
      m_load_class_lists_attempted = true;
      m_class_lists = load_class_lists();
    }
  }

  const UnorderedMap<std::string, std::vector<std::string>>&
  get_all_class_lists() {
    ensure_class_lists_loaded();
    return m_class_lists;
  }

  bool has_class_list(const std::string& name) {
    ensure_class_lists_loaded();
    return m_class_lists.count(name) != 0;
  }

  const std::vector<std::string>& get_class_list(const std::string& name) {
    ensure_class_lists_loaded();
    return m_class_lists.at(name);
  }

  struct DeadClassLoadCounts {
    int64_t sampled{50}; // legacy
    int64_t unsampled{0};
    int64_t beta_unsampled{0}; // Whether is beta sample or not
    int64_t last_modified_count{1}; // number of times that last modified time
                                    // fall into acceptable range. Default value
                                    // 1 is for backward compatibility.
    // The number of seconds since last
    // time the file of this class was modified.
    // 0 is for backward compatibility, meaning data not available.
    // This will be passed in by the data pipeline, the value is calculated by
    // timestamp_of_datapipe_ds - last_modified which is deterministic at given
    // ds
    int64_t seconds_since_last_modified{0};
  };

  const UnorderedMap<std::string, DeadClassLoadCounts>& get_dead_class_list();
  const std::vector<std::string>& get_halfnosis_block_list();

  void clear_dead_class_list() {
    m_dead_class_list_attempted = false;
    m_dead_classes.clear();
  }

  method_profiles::MethodProfiles& get_method_profiles() {
    ensure_agg_method_stats_loaded();
    return *m_method_profiles;
  }

  const method_profiles::MethodProfiles& get_method_profiles() const;

  void process_unresolved_method_profile_lines();

  const UnorderedSet<DexType*>& get_no_optimizations_annos();
  const UnorderedSet<std::string>& get_no_optimizations_blocklist();
  const UnorderedSet<DexMethodRef*>& get_pure_methods();
  const UnorderedSet<const DexString*>& get_finalish_field_names();
  const UnorderedSet<DexType*>& get_do_not_devirt_anon();

  std::string metafile(const std::string& basename) const {
    if (basename.empty()) {
      return std::string();
    }
    return outdir + "/meta/" + basename;
  }

  std::string get_outdir() const { return outdir; }

  // For development only!
  void set_outdir(const std::string& new_outdir);

  const ProguardMap& get_proguard_map() const;

  const std::string& get_printseeds() const { return m_printseeds; }

  uint32_t get_instruction_size_bitwidth_limit() const {
    return m_instruction_size_bitwidth_limit;
  }

  const JsonWrapper& get_json_config() const { return m_json; }
  const GlobalConfig& get_global_config() const;

  void init_baseline_profile_configs();

  const baseline_profiles::BaselineProfileConfigMap&
  get_baseline_profile_configs();

  /**
   * Get the global baseline profile config.
   */
  const baseline_profiles::BaselineProfileConfig&
  get_default_baseline_profile_config();

  bool baseline_profiles_has_manual_profiles();

  bool get_did_use_bzl_baseline_profile_config();

  std::string get_preprocessed_baseline_profile_file(
      const std::string& config_name) const;

  std::optional<std::string> get_android_sdk_api_file(int32_t api_level) {
    std::string api_file;
    std::string key = "android_sdk_api_" + std::to_string(api_level) + "_file";
    m_json.get(key.c_str(), "", api_file);

    if (api_file.empty()) {
      return std::nullopt;
    }
    return std::optional<std::string>(api_file);
  }

  const api::AndroidSDK& get_android_sdk_api(int32_t min_sdk_api);

  UnorderedMap<DexType*, size_t>& get_cls_interdex_groups() {
    if (m_cls_to_interdex_group.empty()) {
      build_cls_interdex_groups();
    }
    return m_cls_to_interdex_group;
  }

  size_t get_num_interdex_groups() {
    if (m_cls_to_interdex_group.empty()) {
      build_cls_interdex_groups();
    }
    return m_num_interdex_groups;
  }

  bool get_recognize_coldstart_pct_marker() const {
    return m_recognize_coldstart_pct_marker;
  }

  void parse_global_config();

  /**
   * Load configurations with the initial scope.
   */
  void load(const Scope& scope,
            Architecture architecture = Architecture::UNKNOWN);

  bool force_single_dex() const;

  bool emit_incoming_hashes() const;

  bool emit_outgoing_hashes() const;

  bool create_init_class_insns() const;

  bool finalize_resource_table() const;

  bool evaluate_package_name() const;

  bool enforce_class_order() const;

  bool disable_violation_fixes() const;
  bool preserve_count_integrity() const;

  // If true, classes.dex is treated like any other dex file in the root of
  // the input program. This is derived from InterDexPass configuration, which
  // also defaults to true.
  bool normal_primary_dex() const;

 private:
  JsonWrapper m_json;
  std::string outdir;
  std::unique_ptr<GlobalConfig> m_global_config;

  std::vector<std::string> load_coldstart_methods();
  std::vector<std::string> load_coldstart_classes();
  UnorderedMap<const DexString*, std::vector<uint8_t>> load_class_frequencies();
  UnorderedMap<std::string, std::vector<std::string>> load_class_lists();
  void ensure_agg_method_stats_loaded();
  void ensure_secondary_method_stats_loaded() const;
  void build_dead_class_list();
  void build_halfnosis_block_list();
  bool is_relocated_class(std::string_view name) const;
  void remove_relocated_part(std::string_view* name);
  void build_cls_interdex_groups();

  // For testing.
  void set_class_lists(UnorderedMap<std::string, std::vector<std::string>> l);

  bool m_load_class_lists_attempted{false};
  std::unique_ptr<ProguardMap> m_proguard_map;
  std::string m_class_frequency_filename;
  mutable std::unique_ptr<
      UnorderedMap<std::string, baseline_profiles::BaselineProfileConfig>>
      m_baseline_profile_config_list;
  std::string m_coldstart_class_filename;
  std::string m_coldstart_methods_filename;
  std::string m_baseline_profile_config_file_name;
  std::string m_preprocessed_baseline_profile_directory;
  std::vector<std::string> m_interactions;
  UnorderedMap<const DexString*, std::vector<uint8_t>> m_class_freq_map;
  std::vector<std::string> m_coldstart_classes;
  std::vector<std::string> m_coldstart_methods;
  std::mutex m_coldstart_methods_mutex;
  bool m_coldstart_methods_loaded{false};
  std::vector<std::string> m_extra_baseline_profile_classes;
  std::vector<std::string> m_halfnosis_block_list;
  UnorderedMap<std::string, std::vector<std::string>> m_class_lists;
  bool m_dead_class_list_attempted{false};
  bool m_halfnosis_block_list_attempted{false};
  std::string m_printseeds; // Filename to dump computed seeds.
  mutable std::unique_ptr<method_profiles::MethodProfiles> m_method_profiles;
  UnorderedMap<std::string, DeadClassLoadCounts> m_dead_classes;

  // limits the output instruction size of any DexMethod to 2^n
  // 0 when limit is not present
  uint32_t m_instruction_size_bitwidth_limit;

  UnorderedSet<DexType*> m_no_devirtualize_annos;
  // global no optimizations annotations
  UnorderedSet<DexType*> m_no_optimizations_annos;
  // global no optimizations blocklist (type prefixes)
  UnorderedSet<std::string> m_no_optimizations_blocklist;
  // global pure methods
  UnorderedSet<DexMethodRef*> m_pure_methods;
  // names of fields that behave similar to final fields, i.e. written once
  // before use
  UnorderedSet<const DexString*> m_finalish_field_names;
  // min_sdk AndroidAPI
  int32_t m_min_sdk_api_level = 0;
  std::unique_ptr<api::AndroidSDK> m_android_min_sdk_api;
  // interdex class group based on betamap
  // 0 when no interdex grouping.
  size_t m_num_interdex_groups = 0;
  UnorderedMap<DexType*, size_t> m_cls_to_interdex_group;

  bool m_recognize_coldstart_pct_marker{false};

  friend struct ClassPreloadTest;
};
