/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "GlobalConfig.h"

#include "Debug.h"
#include <utility>

void InlinerConfig::bind_config() {
  bind("delete_non_virtuals", delete_non_virtuals, delete_non_virtuals);
  bind("virtual", virtual_inline, virtual_inline);
  bind("true_virtual_inline", true_virtual_inline, true_virtual_inline);
  bind("relaxed_init_inline", relaxed_init_inline, relaxed_init_inline);
  bind("unfinalize_relaxed_init_inline", unfinalize_relaxed_init_inline,
       unfinalize_relaxed_init_inline);
  bind("unfinalize_perf_mode", "not-cold", unfinalize_perf_mode_str,
       "one of \"none\", \"not-cold\", \"maybe-hot\", \"hot\"");
  bind("strict_throwable_init_inline", strict_throwable_init_inline,
       strict_throwable_init_inline);
  bind("intermediate_shrinking", intermediate_shrinking,
       intermediate_shrinking);
  bind("enforce_method_size_limit", enforce_method_size_limit,
       enforce_method_size_limit);
  bind("armv7_hard_max_instruction_size", uint64_t{0},
       armv7_hard_max_instruction_size,
       "Maximum estimated code units permitted after an inline on ARMv7. Zero "
       "disables this architecture-specific hard cap. Generic ARM, UNKNOWN, "
       "and all other architectures ignore it.");
  bind("throws", throws_inline, throws_inline);
  bind("throw_after_no_return", throw_after_no_return, throw_after_no_return);
  bind("max_cost_for_constant_propagation", max_cost_for_constant_propagation,
       max_cost_for_constant_propagation);
  bind("max_reduced_size", max_reduced_size, max_reduced_size);
  bind("max_partially_inlined_code_units", max_partially_inlined_code_units,
       max_partially_inlined_code_units,
       "Maximum estimated code units of the hot prefix retained when partially "
       "inlining a callee.");
  bind("multiple_callers", multiple_callers, multiple_callers);
  bind("use_call_site_summaries", use_call_site_summaries,
       use_call_site_summaries);
  bind("respect_sketchy_methods", respect_sketchy_methods,
       respect_sketchy_methods);
  bind("debug", debug, debug);
  bind("check_min_sdk_refs", check_min_sdk_refs, check_min_sdk_refs);
  bind("max_relevant_invokes_when_local_only",
       max_relevant_invokes_when_local_only,
       max_relevant_invokes_when_local_only);
  bind("run_const_prop", shrinker.run_const_prop, shrinker.run_const_prop);
  bind("run_cse", shrinker.run_cse, shrinker.run_cse);
  bind("run_dedup_blocks", shrinker.run_dedup_blocks,
       shrinker.run_dedup_blocks);
  bind("run_branch_prefix_hoisting", shrinker.run_branch_prefix_hoisting,
       shrinker.run_branch_prefix_hoisting);
  bind("run_copy_prop", shrinker.run_copy_prop, shrinker.run_copy_prop);
  bind("run_reg_alloc", shrinker.run_reg_alloc, shrinker.run_reg_alloc);
  bind("run_fast_reg_alloc", shrinker.run_fast_reg_alloc,
       shrinker.run_fast_reg_alloc);
  bind("run_local_dce", shrinker.run_local_dce, shrinker.run_local_dce);
  bind("reg_alloc_random_forest", shrinker.reg_alloc_random_forest,
       shrinker.reg_alloc_random_forest);
  bind("no_inline_annos", {}, no_inline_annos,
       "When any of these annotations is present on a method or class, then "
       "this method or all methods of this class will not get inlined at any "
       "callsite, and callsites will not get deduplicated.");
  bind("no_inline_blocklist", {}, no_inline_blocklist,
       "Any method matching any given prefix will not get inlined at any "
       "callsite, and callsites will not get deduplicated.");
  bind("force_inline_annos", {}, force_inline_annos,
       "When any of these annotations is present on a method or class, then "
       "this method or all methods of this class will get inlined at all "
       "callsites if possible.");
  bind("force_inline_prefixes", {}, force_inline_prefixes,
       "When a prefix matches a method then this method will get inlined at "
       "all callsites if possible.");
  bind("blocklist", {}, blocklist,
       "Any method defined in a class matching any given prefix will not get "
       "inlined at any callsite. This is problematic as Redex may move methods "
       "across classes. Avoid this annotation, prefer using "
       "no_inline_blocklist.");
  bind("caller_blocklist", {}, caller_blocklist,
       "Any method defined in a class matching any given prefix will not be "
       "inlined at all callsite if possible. This is problematic as Redex may "
       "move methods across classes.");
  bind("intradex_allowlist", {}, intradex_allowlist,
       "The purpose of this white-list is to remove black-list entries when "
       "inlining after the InterDex pass has run. (This reduces the impact of "
       "black-list entries that avoid inlining conditional control-flow and "
       "catchers that cause issues with the SwitchMethodPartitioning analysis "
       "that tends to be used by passes that run before or during InterDex.)");

  after_configuration([&]() {
    const static UnorderedMap<std::string, inliner::UnfinalizePerfMode>
        unfinalize_perf_mode_mapping = {
            {"none", inliner::UnfinalizePerfMode::NONE},
            {"not-cold", inliner::UnfinalizePerfMode::NOT_COLD},
            {"maybe-hot", inliner::UnfinalizePerfMode::MAYBE_HOT},
            {"hot", inliner::UnfinalizePerfMode::HOT}};
    always_assert_log(
        unfinalize_perf_mode_mapping.count(unfinalize_perf_mode_str) > 0,
        "Unexpected unfinalize perf mode input provided %s",
        unfinalize_perf_mode_str.c_str());
    unfinalize_perf_mode =
        unfinalize_perf_mode_mapping.at(unfinalize_perf_mode_str);
  });
}

void OptDecisionsConfig::bind_config() {
  bind("enable_logs", false, enable_logs,
       "Should we log Redex's optimization decisions?");
}

void IRTypeCheckerConfig::bind_config() {
  bind("run_after_each_pass", run_after_each_pass, run_after_each_pass);
  bind("verify_moves", verify_moves, verify_moves);
  bind("validate_invoke_super", validate_invoke_super, validate_invoke_super);
  bind("run_after_passes", {}, run_after_passes);
  bind("check_no_overwrite_this", check_no_overwrite_this,
       check_no_overwrite_this);
  bind("annotated_cfg_on_error", annotated_cfg_on_error,
       annotated_cfg_on_error);
  bind("annotated_cfg_on_error_reduced", annotated_cfg_on_error_reduced,
       annotated_cfg_on_error_reduced);
  bind("check_classes", check_classes, check_classes);
  bind("armv7_jit_loop_max_score", armv7_jit_loop_max_score,
       armv7_jit_loop_max_score,
       "Fail the build if a method has a loop that would make the Android "
       "10/11 ARMv7 JIT emit at least this many stack-to-stack copies at the "
       "loop's merge block (weighted for large frames). Offenders in the "
       "input are only reported. 0 disables.");
  bind("armv7_jit_loop_large_frame_carried_values",
       armv7_jit_loop_large_frame_carried_values,
       armv7_jit_loop_large_frame_carried_values,
       "Carried values past which the frame passes 4 KB and copies cost more.");
  bind("armv7_jit_loop_large_frame_weight_divisor",
       armv7_jit_loop_large_frame_weight_divisor,
       armv7_jit_loop_large_frame_weight_divisor,
       "Scale of the large-frame weighting. 0 disables it.");
  bind("run_on_input", run_on_input, run_on_input);
  bind("run_on_input_ignore_access", run_on_input_ignore_access,
       run_on_input_ignore_access);
  bind("external_check", external_check, external_check,
       "ON/OFF switch for dex code validation in external class and internal "
       "class hierarchy - no external class should be inheriting internal "
       "class");
  bind(
      "definition_check", definition_check, definition_check,
      "ON/OFF switch for dex code validation in class definition - all classes "
      "in internal class's hierarchy should be either internal class or "
      "external class");
  bind("external_check_allowlist", {}, external_check_allowlist,
       "Allow certain classes to bypass external_check");
  bind("definition_check_allowlist_temporary", {}, definition_check_allowlist,
       "Temporary allow certain classes to bypass definition_check, this list "
       "is to be cleaned up.");
  std::vector<Json::Value> official_definition_check_allowlist;
  bind("definition_check_allowlist", {}, official_definition_check_allowlist,
       "Allow certain classes to bypass definition_check, define in list of "
       "dictionary with classes list and a reason string.");
  for (auto it = official_definition_check_allowlist.begin();
       it != official_definition_check_allowlist.end();
       ++it) {
    const auto& value = *it;
    always_assert_log(value.isObject(),
                      "[IRTypeChecker] Wrong specification: allowlist in array "
                      "not an object");
    JsonWrapper allowlist_item = JsonWrapper(value);
    std::string reason;
    allowlist_item.get("reason", "", reason);
    always_assert_log(
        reason.length() > 10,
        "Please provide a detailed reason for why the classes are allowlisted");
    UnorderedSet<std::string> classes;
    allowlist_item.get("classes", {}, classes);
    insert_unordered_iterable(definition_check_allowlist, classes);
  }
  bind("external_check_allowlist_prefixes", {},
       external_check_allowlist_prefixes,
       "Allow classes that start with given prefixes bypass external_check");
  bind("definition_check_allowlist_prefixes", {},
       definition_check_allowlist_prefixes,
       "Allow classes that start with given prefixes bypass "
       "definition_check");
}

void HasherConfig::bind_config() {
  bind("run_after_each_pass", {}, run_after_each_pass);
}

void AssessorConfig::bind_config() {
  bind("run_after_each_pass", run_after_each_pass, run_after_each_pass);
  bind("run_initially", run_initially, run_initially);
  bind("run_finally", run_finally, run_finally);
  bind("run_sb_consistency", run_sb_consistency, run_sb_consistency);
}

void CheckUniqueDeobfuscatedNamesConfig::bind_config() {
  bind("run_after_each_pass", run_after_each_pass, run_after_each_pass);
  bind("run_initially", run_initially, run_initially);
  bind("run_finally", run_finally, run_finally);
}

void MethodProfileOrderingConfig::bind_config() {
  bind("method_sorting_allowlisted_substrings",
       method_sorting_allowlisted_substrings,
       method_sorting_allowlisted_substrings);
  bind("min_appear_percent", min_appear_percent, min_appear_percent);
  bind("second_min_appear_percent", second_min_appear_percent,
       second_min_appear_percent);
  bind("skip_similarity_reordering", skip_similarity_reordering,
       skip_similarity_reordering);
}

void MethodSimilarityOrderingConfig::bind_config() {
  bind("use_class_level_perf_sensitivity", use_class_level_perf_sensitivity,
       use_class_level_perf_sensitivity);
  bind("use_compression_conscious_order", use_compression_conscious_order,
       use_compression_conscious_order);
  bind("disable", disable, disable);
  bind("store_name_to_disable", store_name_to_disable, store_name_to_disable);
}

void ProguardConfig::bind_config() {
  bind("blocklist", blocklist, blocklist);
  bind("disable_default_blocklist", disable_default_blocklist,
       disable_default_blocklist);
  bind("fail_on_unknown_commands", fail_on_unknown_commands,
       fail_on_unknown_commands);
  bind("frozen_basedirectory", frozen_basedirectory, frozen_basedirectory,
       "When set, ignore -basedirectory directives in the proguard "
       "configuration file and use the given value instead.");
}

void PassManagerConfig::bind_config() {
  bind("pass_aliases", pass_aliases, pass_aliases);
  bind("jemalloc_full_stats", jemalloc_full_stats, jemalloc_full_stats);
  bind("check_pass_order_properties", check_pass_order_properties,
       check_pass_order_properties);
  bind("check_properties_deep", check_properties_deep, check_properties_deep);
  bind("dump_mrefs", dump_mrefs, dump_mrefs);

  // This setting moved to its own config. Unbound keys are silently dropped by
  // Configurable, so without this an old config would keep parsing and quietly
  // stop tracking anything -- the worst outcome for a diagnostic feature.
  bool moved_violations_tracking = false;
  bind("violations_tracking", false, moved_violations_tracking,
       "Removed: set `violations_tracking.enabled` at the top level instead.");
  always_assert_log(!moved_violations_tracking,
                    "pass_manager.violations_tracking has moved. Set "
                    "violations_tracking.enabled instead:\n"
                    "  \"violations_tracking\": { \"enabled\": true }");
}

void ViolationsTrackingConfig::bind_config() {
  bind("enabled", enabled, enabled,
       "Track how many source-block violations each pass introduces, and "
       "report them as `~violation~tracking` metrics of that pass.");
  bind("violation_kinds", violation_kinds, violation_kinds,
       "Which kinds of violation to track. Valid names are ChainAndDom, "
       "HotImmediateDomNotHot, HotAllChildrenCold, HotMethodColdEntry, "
       "UncoveredSourceBlocks, HotNoHotPred and "
       "UncoveredThrowDelineatedBlocks. Several kinds share one pass over the "
       "scope, so naming more than one costs little extra. With a single kind "
       "the metrics are reported flat; with several, each kind gets a "
       "sub-scope named after it. Note that sharing the pass also shares the "
       "CFG: kinds whose counters need unreachable blocks removed do so for "
       "the whole method, so a kind that would otherwise see those blocks "
       "counts fewer violations when co-configured with one of them. Counts "
       "are therefore only comparable between runs that name the same set of "
       "kinds.");
  bind("top_n", top_n, top_n,
       "How many of the worst-offending methods to report per pass.");
  bind("methods_to_vis", methods_to_vis, methods_to_vis,
       "Methods whose violating blocks are printed in full, in addition to "
       "the aggregate counts.");
  bind("source_blocks_to_track", source_blocks_to_track, source_blocks_to_track,
       "Track only the methods that carry these source blocks, instead of the "
       "whole scope. Each entry is a `<method>@<id>` descriptor as printed by "
       "SourceBlock::show, or a bare `<method>` to match every block "
       "attributed to it. Descriptors are re-resolved every pass, so a block "
       "is followed as inlining moves or duplicates it, and every carrier "
       "method is reported even when it has no violations.");
  bind("track_intermethod_violations", track_intermethod_violations,
       track_intermethod_violations,
       "Also track inter-method (hot callee with all-cold callers) "
       "violations. This builds a call graph twice per pass.");
  bind("print_all_violations", print_all_violations, print_all_violations,
       "Print every violating block of every method, not just the ones named "
       "by methods_to_vis.");
  bind("ignore_undefined", ignore_undefined, ignore_undefined,
       "Do not count source blocks with undefined values as violations.");
}

void ResourceConfig::bind_config() {
  bind("customized_r_classes", {}, customized_r_classes);
  bind("canonical_entry_types", {}, canonical_entry_types);
  bind("sort_key_strings", false, sort_key_strings);
}

void DexOutputConfig::bind_config() {
  bind("write_class_sizes", write_class_sizes, write_class_sizes);
  bind("write_method_sizes", write_method_sizes, write_method_sizes,
       "Record the authoritative post-lowering per-method code_item byte size "
       "into enhanced_dex_stats_t::method_size. Forced on by --emit-dexvt.");
  bind(
      "emit_class_order_sample", emit_class_order_sample,
      emit_class_order_sample,
      "Emit a segment-aware, sampled class-placement fingerprint for "
      "root-store (main-APK) classes into output_stats.class_order_sample, "
      "used to compare class placement across builds per dex-ordering regime.");
  bind("class_order_sample_cap", class_order_sample_cap, class_order_sample_cap,
       "Target number of sampled classes in the cold (cross-dex-ref-minimized) "
       "segment when emit_class_order_sample is set; the primary and betamap "
       "segments are always kept in full.");
}

void Dex2oatConfig::bind_config() {
  bind("huge_method_max", huge_method_max, huge_method_max,
       "dex2oat does not compile a method with more code units than this. "
       "Mirrors ART's `huge_method_threshold_`, whose default is 10000 and "
       "which dex2oat applies with a strict `>`. Raise it beyond any real "
       "method to disable the gate.");
}

void JarLoaderConfig::bind_config() {
  bind("legacy_mode", legacy_mode, legacy_mode);
  bind("allowed_prefixes", allowed_prefixes, allowed_prefixes);
}

void GlobalConfig::bind_config() {
  bool bool_param;
  std::string string_param;
  std::unordered_map<std::string, std::string> string_map_param;
  std::vector<std::string> string_vector_param;
  uint32_t uint32_param;
  int64_t int64_param;
  size_t size_t_param;
  Json::Value json_param;
  // Sorted alphabetically
  bind("agg_method_stats_files", {}, string_vector_param);
  bind("baseline_profile_agg_method_stats_files", {}, string_vector_param);
  bind("agg_method_stats_ignore_split_methods", false, bool_param,
       "Never match split methods (names containing `$split$`) to method "
       "profile rows by name. Split names give a position, not the code, so "
       "the split with a given name can hold different code from the "
       "profiled one.");
  bind("android_sdk_api_15_file", "", string_param);
  bind("android_sdk_api_16_file", "", string_param);
  bind("android_sdk_api_17_file", "", string_param);
  bind("android_sdk_api_18_file", "", string_param);
  bind("android_sdk_api_19_file", "", string_param);
  bind("android_sdk_api_21_file", "", string_param);
  bind("android_sdk_api_23_file", "", string_param);
  bind("android_sdk_api_25_file", "", string_param);
  bind("android_sdk_api_26_file", "", string_param);
  bind("android_sdk_api_27_file", "", string_param);
  bind("android_sdk_api_28_file", "", string_param);
  bind("android_sdk_api_29_file", "", string_param);
  bind("bytecode_sort_mode", {}, string_vector_param);
  bind("class_frequencies", "", string_param);
  bind("coldstart_classes", "", string_param);
  bind("coldstart_methods_file", "", string_param);
  bind("compute_xml_reachability", false, bool_param);
  bind("deep_data_enabled_interactions", {}, string_vector_param);
  bind("unused_keep_rule_abort", false, bool_param);
  bind("debug_info_kind", "", string_param);
  bind("default_class_frequencies", "", string_param);
  bind("default_coldstart_classes", "", string_param);
  bind("dex_output_buffer_size", size_t{64} * 1024 * 1024, size_t_param);
  bind("disable_violation_fixes", false, bool_param);
  bind("emit_class_method_info_map", false, bool_param);
  bind("emit_dexvt", false, bool_param);
  bind("iodi_layer_mode", "full", string_param,
       "IODI layer mode. One of \"full\", \"skip-layer-0-at-api-26\" or "
       "\"always-skip-layer-0\"");
  bind("force_single_dex", false, bool_param);
  bind("emit_incoming_hashes", false, bool_param);
  bind("emit_outgoing_hashes", false, bool_param);
  bind("enable_check_cast_value_preservation", false, bool_param,
       "When true, constant propagation keeps a `check-cast` operand's value "
       "across the cast, instead of carrying only null");
  bind("enable_param_exit_value_summary", false, bool_param,
       "When true, infer a per-parameter exit-value summary via IPCP and use "
       "it to refine no-throw facts on statically-dispatched invoke edges");
  bind("ignore_no_keep_rules", {}, bool_param);
  bind("instruction_size_bitwidth_limit", 0u, uint32_param);
  bind("instrument_pass_enabled", false, bool_param);
  bind("json_serde_supercls", {}, string_vector_param);
  bind("keep_all_annotation_classes", true, bool_param);
  bind("record_accessed_rules", true, bool_param);
  bind("keep_methods", {}, string_vector_param);
  bind("keep_packages", {}, string_vector_param);
  bind("lower_with_cfg", {}, bool_param);
  bind("mem_stats", true, bool_param);
  bind("mem_stats_per_pass", true, bool_param);
  bind("min_sdk_override", 0, int64_param);
  bind("no_optimizations_annotations", {}, string_vector_param);
  bind("no_optimizations_blocklist", {}, string_vector_param);
  bind("preserve_count_integrity", false, bool_param);
  bind("preserve_input_dexes", {}, bool_param);
  bind("proguard_map", "", string_param);
  bind("prune_unexported_components", {}, string_vector_param);
  bind("pure_methods", {}, string_vector_param);
  bind("finalish_field_names", {}, string_vector_param);
  bind("record_keep_reasons", {}, bool_param);
  bind("dump_keep_reasons", {}, bool_param);
  bind("dump_proguard_lens", false, bool_param);
  bind("string_sort_mode", "", string_param);
  bind("write_cfg_each_pass", false, bool_param);
  bind("dump_cfg_classes", "", string_param);
  bind("slow_invariants_debug", false, bool_param);
  bind("insert_remarks", false, bool_param);
  // Enabled for ease of testing, apps expected to opt-out
  bind("enable_bleeding_edge_app_bundle_support", true, bool_param);
  bind("no_devirtualize_annos", {}, string_vector_param);
  bind("create_init_class_insns", true, bool_param);
  bind("finalize_resource_table", false, bool_param);
  bind("check_required_resources", {}, string_vector_param);
  bind("update_method_profiles_stats", false, bool_param);
  bind("complement_betamap_with_method_profiles_symbols", "", string_param);
  bind("recognize_betamap_coldstart_pct_marker", false, bool_param);
  bind("baseline_profile", {}, json_param);
  bind("baseline_profile_config", "", string_param);
  bind("preprocessed_baseline_profile_directory", "", string_param);
  bind("evaluate_package_name", true, bool_param,
       "When true, AndroidManifest.xml will be consulted for the application "
       "package name, and applied during constant propagation.");
  bind("enforce_class_order", false, bool_param,
       "When true, check class order is obeyed to fulfill dex37 verifier "
       "requirements.");
  bind("support_dex_version", 35, uint32_param,
       "Dex Version to support. Officially support 35 for now. Allow "
       "configuring for experiment. Do not use higher version.");

  for (const auto& entry : m_registry) {
    m_global_configs.emplace(entry.name,
                             entry.bind_operation(this, entry.name));
  }
}

GlobalConfigRegistryEntry::GlobalConfigRegistryEntry(
    std::string name, BindOperationFn bind_operation)
    : name(std::move(name)), bind_operation(std::move(bind_operation)) {}

GlobalConfigRegistry& GlobalConfig::default_registry() {
  static GlobalConfigRegistry registry{
      register_as<InlinerConfig>("inliner"),
      register_as<IRTypeCheckerConfig>("ir_type_checker"),
      register_as<HasherConfig>("hasher"),
      register_as<AssessorConfig>("assessor"),
      register_as<CheckUniqueDeobfuscatedNamesConfig>(
          "check_unique_deobfuscated_names"),
      register_as<OptDecisionsConfig>("opt_decisions"),
      register_as<MethodProfileOrderingConfig>("method_profile_order"),
      register_as<MethodSimilarityOrderingConfig>("method_similarity_order"),
      register_as<ProguardConfig>("proguard"),
      register_as<PassManagerConfig>("pass_manager"),
      register_as<ViolationsTrackingConfig>("violations_tracking"),
      register_as<ResourceConfig>("resources"),
      register_as<DexOutputConfig>("dex_output"),
      register_as<JarLoaderConfig>("jar_loader"),
      register_as<Dex2oatConfig>("dex2oat"),
  };
  return registry;
}
