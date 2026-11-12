/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>

#include "Configurable.h"
#include "DeterministicContainers.h"
#include "InlinerConfig.h"

struct InlinerConfig : public inliner::InlinerConfig, Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override { return "InlinerConfig"; }
  std::string get_config_doc() override {
    return "This configuration is used to configure the inlining which "
           "occurs in several Redex passes.";
  }
};

struct IRTypeCheckerConfig : public Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override { return "IRTypeCheckerConfig"; }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex to typecheck the IR "
           "after various stages of optimization.";
  }

  bool run_after_each_pass{true};
  bool verify_moves{true};
  bool validate_invoke_super{true};
  bool check_no_overwrite_this{false};
  bool annotated_cfg_on_error{true};
  bool annotated_cfg_on_error_reduced{true};
  bool check_classes{true};
  bool run_on_input{true};
  bool run_on_input_ignore_access{false};
  bool external_check{false};
  bool definition_check{false};
  UnorderedSet<std::string> run_after_passes;
  UnorderedSet<std::string> external_check_allowlist;
  UnorderedSet<std::string> definition_check_allowlist;
  UnorderedSet<std::string> external_check_allowlist_prefixes;
  UnorderedSet<std::string> definition_check_allowlist_prefixes;
  // Android 10/11 ARMv7 JIT loop checker; a max score of 0 disables it. The
  // default is the lowest score observed to abort on a device.
  uint64_t armv7_jit_loop_max_score{115000};
  uint32_t armv7_jit_loop_large_frame_carried_values{380};
  uint32_t armv7_jit_loop_large_frame_weight_divisor{210};
};

struct HasherConfig : public Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override { return "HasherConfig"; }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex to hash the contents of "
           "the dex"
           "after various stages of optimization to find non-determinism.";
  }

  bool run_after_each_pass;
};

struct AssessorConfig : public Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override { return "AssessorConfig"; }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex to perform internal "
           "quality assessments.";
  }

  bool run_after_each_pass{false};
  bool run_initially{false};
  bool run_finally{false};
  bool run_sb_consistency{false};
};

struct CheckUniqueDeobfuscatedNamesConfig : public Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override {
    return "CheckUniqueDeobfuscatedNamesConfig";
  }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex to perform internal "
           "integrity checks.";
  }

  bool run_after_each_pass{false};
  bool run_initially{false};
  bool run_finally{false};
};

struct OptDecisionsConfig : public Configurable {
 public:
  void bind_config() override;
  std::string get_config_name() override { return "OptDecisionsConfig"; }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex about ordering methods "
           "with profiling data.";
  }

  bool enable_logs;
};

struct MethodProfileOrderingConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override {
    return "MethodProfileOrderingConfig";
  }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex if it should leave a "
           "log that explains the optimizations it has performed.";
  }

  UnorderedSet<std::string> method_sorting_allowlisted_substrings;
  float min_appear_percent{10.0f};
  float second_min_appear_percent{10.0f};
  bool skip_similarity_reordering{false};
};

struct MethodSimilarityOrderingConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override {
    return "MethodSimilarityOrderingConfig";
  }
  std::string get_config_doc() override {
    return "This configuration is used to direct Redex about ordering methods "
           "by similarity.";
  }

  bool disable{true};
  bool use_compression_conscious_order{false};
  bool use_class_level_perf_sensitivity{false};
  std::string store_name_to_disable;
};

struct ProguardConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "ProguardConfig"; }
  std::string get_config_doc() override {
    return "This configuration holds values that switch proguard parsing "
           "behavior.";
  }

  std::vector<std::string> blocklist;
  bool disable_default_blocklist{false};
  bool fail_on_unknown_commands{true};
  std::string frozen_basedirectory;
};

struct PassManagerConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "PassManagerConfig"; }
  std::string get_config_doc() override {
    return "This configuration holds values that influence the PassManager.";
  }

  UnorderedMap<std::string, std::string> pass_aliases;
  bool jemalloc_full_stats{false};
  bool check_pass_order_properties{false};
  bool check_properties_deep{false};
  bool dump_mrefs{false};
};

struct ViolationsTrackingConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "ViolationsTrackingConfig"; }
  std::string get_config_doc() override {
    return "Controls the source-block violations tracking that runs around "
           "every pass, reporting how many violations each pass introduces.";
  }

  bool enabled{false};
  // Names as spelled by source_blocks::get_violation_name.
  std::vector<std::string> violation_kinds{"ChainAndDom"};
  unsigned int top_n{10};
  std::vector<std::string> methods_to_vis;
  // "<method>@<id>" descriptors, or a bare "<method>" for every block
  // attributed to it. Non-empty switches on targeted mode.
  std::vector<std::string> source_blocks_to_track;
  bool track_intermethod_violations{false};
  bool print_all_violations{false};
  bool ignore_undefined{false};
};

struct ResourceConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "ResourceConfig"; }
  std::string get_config_doc() override {
    return "Options used by many resource optimization passes or global "
           "cleanup steps.";
  }

  // Outer R class names that have been customized to hold extra data (which
  // need special treatment when remapping constants). Not used by all apps.
  UnorderedSet<std::string> customized_r_classes;
  // Type names in the resource table (example: "id") which should enable
  // canonical offsets for entries/values.
  UnorderedSet<std::string> canonical_entry_types;
  bool sort_key_strings{false};
  // For instrumentation scenarios, R classes will have unexpected method
  // invocations. Allow certain validation/cleanup behaviors to be omitted.
  bool cleanup_r_class_rewriting{true};
};

struct DexOutputConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "DexOutputConfig"; }
  std::string get_config_doc() override {
    return "Options used by the Dex writer.";
  }

  bool write_class_sizes{false};

  // When enabled, record the authoritative post-lowering per-method code_item
  // byte size (return of DexMethod code->encode()) into
  // enhanced_dex_stats_t::method_size. Forced on by --emit-dexvt.
  bool write_method_sizes{false};

  // When enabled, emit a segment-aware, sampled class-placement fingerprint for
  // root-store (main-APK) classes into output_stats.class_order_sample, used to
  // compare class placement across two builds per dex-ordering regime. On by
  // default.
  bool emit_class_order_sample{true};
  // Target number of sampled classes in the cold (cross-dex-ref-minimized)
  // segment when emit_class_order_sample is set; the primary and betamap
  // segments are always kept in full, so this only bounds the cold segment.
  int class_order_sample_cap{1000};
};

struct JarLoaderConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "JarLoaderConfig"; }
  std::string get_config_doc() override {
    return "This configuration holds values that switch JarLoader behavior.";
  }

  std::vector<std::string> allowed_prefixes;
  bool legacy_mode{true};
};

namespace baseline_profiles {

// ART's default huge_method_threshold_ (art/compiler/driver/compiler_options.h,
// kDefaultHugeMethodThreshold). dex2oat refuses a method STRICTLY larger than
// this. Overridable on the dex2oat command line with --huge-method-max, which
// no Android build of ours passes, so the default is what runs.
constexpr uint32_t DEFAULT_ART_HUGE_METHOD_MAX = 10000;

} // namespace baseline_profiles

struct Dex2oatConfig : public Configurable {
  void bind_config() override;

  std::string get_config_name() override { return "Dex2oatConfig"; }
  std::string get_config_doc() override {
    return "The settings of dex2oat, ART's ahead-of-time compiler, that Redex "
           "takes into account.";
  }

  uint32_t huge_method_max{baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX};
};

class GlobalConfig;

using BindOperationFn = std::function<std::unique_ptr<Configurable>(
    GlobalConfig*, const std::string&)>;

struct GlobalConfigRegistryEntry {
  GlobalConfigRegistryEntry(std::string name, BindOperationFn bind_operation);
  std::string name;
  BindOperationFn bind_operation;
};

using GlobalConfigRegistry = std::vector<GlobalConfigRegistryEntry>;

class GlobalConfig : public Configurable {
 public:
  explicit GlobalConfig(GlobalConfigRegistry registry)
      : m_registry(std::move(registry)) {}

  void bind_config() override;
  std::string get_config_name() override { return "GlobalConfig"; }
  std::string get_config_doc() override {
    return "All the Redex configuration that isn't pass-specific lives here.";
  }

  template <typename ConfigType>
  ConfigType* get_config_by_name(const std::string& name) const {
    const auto& type = m_global_configs.at(name);
    return static_cast<ConfigType*>(type.get());
  }

  bool has_config_by_name(const std::string& name) const {
    return m_global_configs.count(name) != 0;
  }

  template <typename ConfigType>
  static BindOperationFn get_bind_operation() {
    return [](GlobalConfig* global_config,
              const std::string& name) -> std::unique_ptr<Configurable> {
      std::unique_ptr<ConfigType> config_ptr = std::make_unique<ConfigType>();
      auto& config = *config_ptr;
      global_config->bind(
          name, ConfigType(), config, config_ptr->get_config_doc());
      return std::unique_ptr<Configurable>{config_ptr.release()};
    };
  }

  template <typename ConfigType>
  static GlobalConfigRegistryEntry register_as(const std::string& name) {
    return GlobalConfigRegistryEntry(name, get_bind_operation<ConfigType>());
  }

  static GlobalConfigRegistry& default_registry();

 private:
  std::unordered_map<std::string, std::unique_ptr<Configurable>>
      m_global_configs;
  GlobalConfigRegistry m_registry;
};
