/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BaselineProfile.h"

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <fstream>
#include <tuple>

#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodUtil.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace baseline_profiles {

uint32_t get_huge_method_max(const ConfigFiles& conf) {
  const auto& global_config = conf.get_global_config();
  // A config whose global section was never parsed has no "dex2oat" entry;
  // parsing an empty one would give the same default.
  if (!global_config.has_config_by_name("dex2oat")) {
    return DEFAULT_ART_HUGE_METHOD_MAX;
  }
  return global_config.get_config_by_name<Dex2oatConfig>("dex2oat")
      ->huge_method_max;
}

uint32_t dex2oat_code_units(DexMethod* method) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return 0;
  }
  auto code_units = code->estimate_code_units();
  if (code->cfg_built()) {
    code_units += code->cfg().get_size_adjustment();
  }
  return code_units;
}

uint32_t lowered_unreachable_extra_code_units() {
  static const uint32_t extra = [] {
    IRInstruction invoke(OPCODE_INVOKE_STATIC);
    IRInstruction move_result(OPCODE_MOVE_RESULT_OBJECT);
    IRInstruction unreachable(IOPCODE_UNREACHABLE);
    return static_cast<uint32_t>(invoke.size() + move_result.size() -
                                 unreachable.size());
  }();
  return extra;
}

uint32_t dex2oat_code_units_before_unreachable_lowering(DexMethod* method) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return 0;
  }
  const UnorderedSet<IROpcode> unreachable{IOPCODE_UNREACHABLE};
  auto unreachables =
      code->cfg_built()
          ? method::count_opcode_of_types(code->cfg(), unreachable)
          : method::count_opcode_of_types(*code, unreachable);
  return dex2oat_code_units(method) +
         lowered_unreachable_extra_code_units() * unreachables;
}

namespace {

// Every gate of `uncompilable_reason` except the size gate.
UncompilableReason size_independent_uncompilable_reason(DexMethod* method) {
  if (method->get_code() == nullptr || is_abstract(method) ||
      is_native(method)) {
    return UncompilableReason::kNoCode;
  }
  // Test the access flags rather than the name: dex2oat's gate is
  // ACC_CONSTRUCTOR && ACC_STATIC, and matching it exactly keeps this in step
  // with the compiler even if a name-based helper drifts. An instance <init>
  // is ACC_CONSTRUCTOR without ACC_STATIC and is compiled normally.
  if (is_static(method) && method::is_constructor(method)) {
    return UncompilableReason::kClinit;
  }
  if (has_anno(method, type::dalvik_annotation_optimization_NeverCompile())) {
    return UncompilableReason::kNeverCompile;
  }
  return UncompilableReason::kNone;
}

} // namespace

UncompilableReason uncompilable_reason(DexMethod* method,
                                       uint32_t huge_method_max) {
  auto reason = size_independent_uncompilable_reason(method);
  if (reason == UncompilableReason::kNone &&
      dex2oat_code_units(method) > huge_method_max) {
    return UncompilableReason::kHugeMethod;
  }
  return reason;
}

Dex2oatFacts compute_dex2oat_facts(DexMethod* method,
                                   uint32_t huge_method_max) {
  Dex2oatFacts facts{dex2oat_code_units(method),
                     size_independent_uncompilable_reason(method)};
  if (facts.reason == UncompilableReason::kNone &&
      facts.code_units > huge_method_max) {
    facts.reason = UncompilableReason::kHugeMethod;
  }
  return facts;
}

bool flags_request_compilation(const MethodFlags& flags) {
  return flags.hot || flags.startup;
}

namespace {

// How a padding candidate ranks, smallest-first. See the header for why the
// keys after the first carry the selection rather than decorating it.
struct TopOffRank {
  uint32_t code_units{0};
  // 0 for a void return, so void sorts first.
  uint8_t non_void{0};
  uint32_t registers{0};

  bool operator<(const TopOffRank& other) const {
    return std::tie(code_units, non_void, registers) <
           std::tie(other.code_units, other.non_void, other.registers);
  }
  bool operator==(const TopOffRank& other) const {
    return std::tie(code_units, non_void, registers) ==
           std::tie(other.code_units, other.non_void, other.registers);
  }
};

bool returns_void(const DexMethod* method) {
  return type::is_void(method->get_proto()->get_rtype());
}

uint32_t registers_of(const DexMethod* method) {
  const auto* code = method->get_code();
  if (code == nullptr) {
    return 0;
  }
  // IRCode::get_registers_size asserts the CFG is NOT built, and within a pass
  // it always is, so the CFG owns the count there.
  return code->cfg_built() ? code->cfg().get_registers_size()
                           : code->get_registers_size();
}

TopOffRank topoff_rank(DexMethod* method) {
  return TopOffRank{dex2oat_code_units(method),
                    static_cast<uint8_t>(returns_void(method) ? 0 : 1),
                    registers_of(method)};
}

} // namespace

TopOffSelection select_smallest_topoff_methods(
    const Scope& candidate_scope,
    const BaselineProfile& baseline_profile,
    size_t count,
    uint32_t huge_method_max,
    const UnorderedSet<const DexMethod*>* excluded) {
  TopOffSelection selection;
  if (count == 0) {
    return selection;
  }

  InsertOnlyConcurrentMap<DexMethod*, TopOffRank> eligible;
  std::atomic<size_t> excluded_candidates{0};
  walk::parallel::classes(candidate_scope, [&](DexClass* cls) {
    for (auto* method : cls->get_all_methods()) {
      if (baseline_profile.methods.count(method) != 0) {
        continue;
      }
      if (uncompilable_reason(method, huge_method_max) !=
          UncompilableReason::kNone) {
        continue;
      }
      if (excluded != nullptr && excluded->count(method) != 0) {
        excluded_candidates.fetch_add(1, std::memory_order_relaxed);
        continue;
      }
      eligible.emplace(method, topoff_rank(method));
    }
  });
  selection.candidates = eligible.size();
  selection.excluded_candidates = excluded_candidates.load();

  auto take = [&selection](DexMethod* method) {
    selection.methods.push_back(method);
    if (returns_void(method)) {
      ++selection.methods_returning_void;
    }
  };

  std::vector<std::pair<TopOffRank, DexMethod*>> candidates;
  candidates.reserve(eligible.size());
  for (auto&& [method, rank] : UnorderedIterable(eligible)) {
    candidates.emplace_back(rank, method);
    if (rank.non_void == 0) {
      ++selection.candidates_returning_void;
    }
  }

  if (candidates.size() <= count) {
    // The whole pool is taken, so nothing has to be ranked.
    selection.methods.reserve(candidates.size());
    for (auto&& [rank, method] : candidates) {
      take(method);
    }
    return selection;
  }

  auto by_rank = [](const auto& a, const auto& b) { return a.first < b.first; };
  std::nth_element(candidates.begin(),
                   candidates.begin() + static_cast<std::ptrdiff_t>(count - 1),
                   candidates.end(), by_rank);
  auto cutoff = candidates[count - 1].first;

  // Everything strictly below the cutoff is in regardless of ordering; only
  // the methods sitting exactly on it need a tie-break, and the deobfuscated
  // name is the one key expensive enough to be worth deferring this far.
  std::vector<std::pair<std::string, DexMethod*>> at_cutoff;
  selection.methods.reserve(count);
  for (auto&& [rank, method] : candidates) {
    if (rank < cutoff) {
      take(method);
    } else if (rank == cutoff) {
      at_cutoff.emplace_back(show_deobfuscated(method), method);
    }
  }
  // Both follow from nth_element's contract, but a violation would underflow
  // the resize below into an allocation the size of the address space, so pay
  // for the check in opt too.
  always_assert(selection.methods.size() < count);
  size_t remaining = count - selection.methods.size();
  always_assert(at_cutoff.size() >= remaining);
  std::sort(at_cutoff.begin(), at_cutoff.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
  at_cutoff.resize(remaining);
  for (auto&& [name, method] : at_cutoff) {
    take(method);
  }
  return selection;
}

bool dex2oat_compiles(const BaselineProfile& baseline_profile,
                      DexMethod* method,
                      uint32_t huge_method_max) {
  auto it = baseline_profile.methods.find(method);
  // Testing the flags first skips the size gate for entries that do not ask
  // for compilation.
  return it != baseline_profile.methods.end() &&
         flags_request_compilation(it->second) &&
         uncompilable_reason(method, huge_method_max) ==
             UncompilableReason::kNone;
}

bool dex2oat_compiles(const MethodFlags& flags, const Dex2oatFacts& facts) {
  return flags_request_compilation(flags) &&
         facts.reason == UncompilableReason::kNone;
}

size_t apply_forced_method_flags(const Scope& scope, BaselineProfile* profile) {
  size_t changed = 0;
  // `walk::methods`, not `walk::code`: the forced H/S bits live on
  // `ReferencedState` and remain meaningful after a method's `IRCode` has been
  // lowered or released. A code-only walk would skip such methods and omit
  // their forced flags from the profile.
  walk::methods(scope, [&](DexMethod* method) {
    const bool force_hot = method->rstate.force_hot_in_baseline_profile();
    const bool force_startup =
        method->rstate.force_startup_in_baseline_profile();
    if (!force_hot && !force_startup) {
      return;
    }
    auto& flags = profile->methods[method];
    // Count bit transitions, not method visits: a method can flip both H and
    // S at once, and the metric is reported per config as a flag count.
    changed += (force_hot && !flags.hot) ? 1 : 0;
    changed += (force_startup && !flags.startup) ? 1 : 0;
    flags.hot |= force_hot;
    flags.startup |= force_startup;
  });
  return changed;
}

namespace {

void add_startup_class_methods(const std::vector<std::string>& interdexorder,
                               uint32_t huge_method_max,
                               BaselineProfile* baseline_profile) {
  std::vector<DexClass*> coldstart_classes;
  for (const auto& entry : interdexorder) {
    // Limit to just the 20% cold start set
    if (entry.find("ColdStart20PctEnd") != std::string::npos) {
      break;
    }

    DexType* type = DexType::get_type(entry);
    if (type != nullptr) {
      auto* coldstart_class = type_class(type);
      if (coldstart_class != nullptr) {
        coldstart_classes.push_back(coldstart_class);
        if (baseline_profile->classes.insert(coldstart_class).second) {
          baseline_profile->startup_classes.insert(coldstart_class);
        }
      }
    }
  }

  MethodFlags flags;
  flags.hot = true;
  flags.startup = false;
  // walk::code, not walk::methods: the latter also visits abstract and
  // native methods, which have no code for dex2oat to compile. This is the
  // only insertion path that can put a code-less method into a
  // BaselineProfile. <clinit> and @NeverCompile still have code, so the
  // full predicate is applied rather than just a code check.
  InsertOnlyConcurrentSet<const DexMethod*> compilable;
  walk::parallel::code(
      coldstart_classes,
      [&compilable, huge_method_max](DexMethod* method, IRCode&) {
        if (uncompilable_reason(method, huge_method_max) ==
            UncompilableReason::kNone) {
          compilable.insert(method);
        }
      });
  for (const auto* method : UnorderedIterable(compilable)) {
    if (baseline_profile->methods.emplace(method, flags).second) {
      ++baseline_profile->startup_class_methods;
    }
  }
}

} // namespace

BaselineProfile get_default_baseline_profile(
    const Scope& scope,
    const UnorderedMap<std::string, BaselineProfileConfig>& configs,
    const method_profiles::MethodProfiles& method_profiles,
    const std::vector<std::string>& coldstart_classes,
    uint32_t huge_method_max) {
  auto [baseline_profile, _] = get_baseline_profiles(
      scope, configs, method_profiles, coldstart_classes, huge_method_max);
  return baseline_profile;
}

BaselineProfile get_default_baseline_profile(const Scope& scope,
                                             ConfigFiles& conf) {
  auto [baseline_profile, _] = get_baseline_profiles(scope, conf);
  return baseline_profile;
}

std::tuple<BaselineProfile, UnorderedMap<std::string, BaselineProfile>>
get_baseline_profiles(
    const Scope& scope,
    ConfigFiles& conf,
    UnorderedSet<const DexMethodRef*>* method_refs_without_def,
    bool apply_forced_flags) {
  return get_baseline_profiles(
      scope, conf.get_baseline_profile_configs(), conf.get_method_profiles(),
      conf.get_coldstart_classes(), get_huge_method_max(conf),
      method_refs_without_def, apply_forced_flags);
}

std::tuple<BaselineProfile, UnorderedMap<std::string, BaselineProfile>>
get_baseline_profiles(
    const Scope& scope,
    const UnorderedMap<std::string, BaselineProfileConfig>& configs,
    const method_profiles::MethodProfiles& method_profiles,
    const std::vector<std::string>& coldstart_classes,
    uint32_t huge_method_max,
    UnorderedSet<const DexMethodRef*>* method_refs_without_def,
    bool apply_forced_flags) {
  UnorderedSet<const DexMethodRef*> method_candidates;
  UnorderedSet<DexClass*> class_candidates;
  walk::classes(scope, [&](DexClass* cls) { class_candidates.insert(cls); });
  walk::code(scope, [&](DexMethod* method, const IRCode&) {
    method_candidates.insert(method);
  });
  UnorderedMap<std::string, BaselineProfile> baseline_profiles;
  BaselineProfile manual_baseline_profile;
  for (const auto& [config_name, config] : UnorderedIterable(configs)) {
    // If we're not using this as the final pass of baseline profiles, just
    // continue on all configs that aren't the default
    if (!config.options.use_final_redex_generated_profile &&
        config_name != DEFAULT_BASELINE_PROFILE_CONFIG_NAME) {
      continue;
    }
    UnorderedSet<const DexType*> classes;
    UnorderedSet<const DexMethod*> startup_methods;
    UnorderedSet<const DexMethod*> post_startup_methods;
    UnorderedSet<const DexMethod*> hot_methods;
    for (auto&& [interaction_id, interaction_config] :
         UnorderedIterable(config.interaction_configs)) {
      const auto& method_stats =
          method_profiles.method_stats_for_baseline_config(interaction_id,
                                                           config_name);
      for (auto&& [method_ref, stat] : UnorderedIterable(method_stats)) {
        if (method_candidates.count(method_ref) == 0u) {
          continue;
        }
        const auto* method = method_ref->as_def();
        if (method == nullptr) {
          if (method_refs_without_def != nullptr) {
            method_refs_without_def->insert(method_ref);
          }
          continue;
        }

        if (stat.appear_percent <
                static_cast<double>(interaction_config.threshold) ||
            stat.call_count <
                static_cast<double>(interaction_config.call_threshold)) {
          continue;
        }

        if (interaction_config.startup) {
          startup_methods.insert(method);
          hot_methods.insert(method);
        }
        if (interaction_config.post_startup) {
          post_startup_methods.insert(method);
          hot_methods.insert(method);
        }
        if (interaction_config.classes) {
          classes.insert(method->get_class());
        }
      }
    }
    static const std::array<std::string, 3> manual_interaction_ids = {
        "manual_startup", "manual_post_startup", "manual_hot"};
    for (const auto& interaction_id : manual_interaction_ids) {
      const auto& method_stats =
          method_profiles.method_stats_for_baseline_config(interaction_id,
                                                           config_name);
      for (auto&& [method_ref, stat] : UnorderedIterable(method_stats)) {
        if (method_candidates.count(method_ref) == 0u) {
          continue;
        }
        const auto* method = method_ref->as_def();
        if (method == nullptr) {
          if (method_refs_without_def != nullptr) {
            method_refs_without_def->insert(method_ref);
          }
          continue;
        }
        if (interaction_id == "manual_startup") {
          startup_methods.insert(method);
        }
        if (interaction_id == "manual_post_startup") {
          post_startup_methods.insert(method);
        }
        if (interaction_id == "manual_hot") {
          hot_methods.insert(method);
        }
      }
    }
    // methods = startup_methods | post_startup_methods | hot_methods
    UnorderedSet<const DexMethod*> methods;
    insert_unordered_iterable(methods, startup_methods);
    insert_unordered_iterable(methods, post_startup_methods);
    insert_unordered_iterable(methods, hot_methods);

    baseline_profiles::BaselineProfile res;
    for (const auto* method : UnorderedIterable(methods)) {
      auto& flags = res.methods[method];
      if (startup_methods.count(method) != 0u) {
        flags.startup = true;
      }
      if (post_startup_methods.count(method) != 0u) {
        flags.post_startup = true;
      }
      if (hot_methods.count(method) != 0u) {
        flags.hot = true;
      }
    }
    for (const auto* type : UnorderedIterable(classes)) {
      auto* cls = type_class(type);
      if (class_candidates.count(cls) != 0u) {
        res.classes.insert(type_class(type));
      }
    }
    if (config_name != DEFAULT_BASELINE_PROFILE_CONFIG_NAME ||
        config.options.use_final_redex_generated_profile) {
      if (config.options.include_all_startup_classes) {
        add_startup_class_methods(coldstart_classes, huge_method_max, &res);
      }
      baseline_profiles[config_name] = res;
    }
    if (config_name == DEFAULT_BASELINE_PROFILE_CONFIG_NAME) {
      manual_baseline_profile = std::move(res);
    }
  }
  if (apply_forced_flags) {
    apply_forced_method_flags(scope, &manual_baseline_profile);
    for (auto& [_, profile] : UnorderedIterable(baseline_profiles)) {
      apply_forced_method_flags(scope, &profile);
    }
  }
  return {std::move(manual_baseline_profile), std::move(baseline_profiles)};
}

void BaselineProfile::load_classes(const Scope& scope,
                                   const ConfigFiles& config,
                                   const std::string& bp_name) {
  auto preprocessed_profile_name =
      config.get_preprocessed_baseline_profile_file(bp_name);

  if (preprocessed_profile_name.empty()) {
    return;
  }

  // Classes may have been obfuscated. For simplicity create a map
  // ahead of time. We cannot rely on deobfuscated name lookup to be enabled.
  UnorderedMap<std::string_view, DexClass*> unobf_to_type;
  walk::classes(scope, [&](DexClass* cls) {
    const auto* deobf = cls->get_deobfuscated_name_or_null();
    if (deobf != nullptr) {
      unobf_to_type.emplace(deobf->str(), cls);
    } else {
      unobf_to_type.emplace(cls->get_name()->str(), cls);
    }
  });

  std::ifstream preprocessed_profile{preprocessed_profile_name};
  std::string current_line;
  while (std::getline(preprocessed_profile, current_line)) {
    if (current_line.empty() || current_line[0] != 'L') {
      continue;
    }

    auto it = unobf_to_type.find(current_line);
    if (it == unobf_to_type.end() || it->second->is_external()) {
      unmatched_classes.emplace(std::move(current_line));
    } else {
      classes.emplace(it->second);
    }
  }
}

void BaselineProfile::transitively_close_classes(const Scope& scope) {
  // This may not be the most efficient implementation but it is simple and
  // uses common functionality.

  UnorderedSet<const DexType*> closed_types;

  unordered_for_each(classes, [&](auto* cls_def) {
    if (cls_def->is_external()) {
      return;
    }

    cls_def->gather_load_types(closed_types);
  });

  // Filter out classes that are not in the scope. For speed that requires
  // temporary storage. Consider removing this.

  UnorderedSet<const DexClass*> class_defs;
  unordered_for_each(closed_types, [&](auto* type) {
    auto* cls_def = type_class_internal(type);
    if (cls_def == nullptr) {
      return;
    }
    class_defs.emplace(cls_def);
  });

  walk::classes(scope, [&](const auto* cls) {
    if (class_defs.count(cls)) {
      classes.emplace(cls);
    }
  });
}

} // namespace baseline_profiles
