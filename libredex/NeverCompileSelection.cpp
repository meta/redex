/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "NeverCompileSelection.h"

#include <algorithm>
#include <boost/regex.hpp> // NOLINT
#include <cmath>
#include <cstdint>

#include "BaselineProfile.h"
#include "BaselineProfileConfig.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "IRCode.h"
#include "InstructionLowering.h"
#include "LoopInfo.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace never_compile_analysis {

namespace {

// Helper function that checks if a block is not hit in any interaction.
bool is_cold(cfg::Block* b) {
  const auto* sb = source_blocks::get_first_source_block(b);
  if (sb == nullptr) {
    return true;
  }

  bool may_be_hot = false;
  sb->foreach_val_early([&may_be_hot](const auto& val) {
    may_be_hot = (!val || val->val > 0.0f);
    return may_be_hot;
  });

  return !may_be_hot;
}

bool is_sparse(cfg::Block* switch_block) {
  instruction_lowering::CaseKeysExtentBuilder ckeb;
  for (auto* e : switch_block->succs()) {
    if (e->type() == cfg::EDGE_BRANCH) {
      ckeb.insert(*e->case_key());
    }
  }
  return ckeb->sufficiently_sparse();
}

bool never_compile_callcount_threshold_met(
    double call_count, int64_t never_compile_callcount_threshold) {
  return never_compile_callcount_threshold > -1 &&
         call_count <= static_cast<double>(never_compile_callcount_threshold);
}

bool never_compile_perf_threshold_met(DexMethod* method,
                                      int64_t never_compile_perf_threshold) {
  if (never_compile_perf_threshold <= -1) {
    return false;
  }

  int64_t sparse_switch_cases = 0;
  int64_t interpretation_cost = 20; // overhead of going into/out of interpreter
  for (auto* block : method->get_code()->cfg().blocks()) {
    if (is_cold(block)) {
      continue;
    }
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (opcode::is_an_internal(insn->opcode())) {
        continue;
      }
      // The interpreter uses expensive helper routines for a number of
      // instructions, which lead to an update of the hotness for JIT
      // purposes:
      // https://android.googlesource.com/platform/art/+/refs/heads/main/runtime/interpreter/mterp/nterp.cc
      // We assume that those instructions are more expensive than others
      // by an order of magnitude.
      interpretation_cost +=
          (insn->has_field() || insn->has_method() || insn->has_type() ||
           insn->has_string() || opcode::is_a_new(insn->opcode()))
              ? 10
              : 1;
      if (opcode::is_switch(insn->opcode()) && is_sparse(block)) {
        sparse_switch_cases += static_cast<int64_t>(block->succs().size());
      }
    }
  }

  if (sparse_switch_cases == 0) {
    return false;
  }

  // We want to compare
  //    interpretation_cost / sparse_switch_cases
  //                            (the average cost of code per switch case)
  // with
  //    never_compile_perf_threshold * sparse_switch_cases
  //                                     (cost of executing sparse switch)
  // to find a case where the cost of the executing sparse switch
  // excessively dominates the cost of code per switch case, which the
  // following achieves.
  if ((static_cast<double>(interpretation_cost) /
       std::pow(sparse_switch_cases, 2)) *
          100 >
      static_cast<double>(never_compile_perf_threshold)) {
    return false;
  }

  TRACE(APW, 5, "[%s] is within perf threshold: (%d / sqr(%d)) * 100 > %d\n%s",
        method->get_fully_deobfuscated_name().c_str(),
        (int32_t)interpretation_cost, (int32_t)sparse_switch_cases,
        (int32_t)never_compile_perf_threshold, SHOW(method->get_code()->cfg()));
  return true;
}

bool never_compile_called_coverage_threshold_met(
    DexMethod* method,
    double call_count,
    int64_t never_compile_called_coverage_threshold) {
  if (never_compile_called_coverage_threshold <= -1) {
    return false;
  }

  uint32_t covered_code_units = 0;
  uint32_t total_code_units = 0;
  for (auto* block : method->get_code()->cfg().blocks()) {
    auto ecu = block->estimate_code_units();
    total_code_units += ecu;
    if (!is_cold(block)) {
      covered_code_units += ecu;
    }
  }
  always_assert(total_code_units > 0);
  if (total_code_units < 24) {
    // Don't bother with small methods; adding annotation also creates
    // overhead. The chosen value is a bit larger than the 14-code units
    // inlining threshold of the AOT compiler.
    return false;
  }
  auto effective_call_count = std::max(1.0, call_count);
  if (effective_call_count * covered_code_units * 100 / total_code_units >=
      static_cast<double>(never_compile_called_coverage_threshold)) {
    return false;
  }
  TRACE(APW, 5,
        "[%s] is within coverage threshold: %f %u / %u > %d percent\n%s",
        method->get_fully_deobfuscated_name().c_str(), effective_call_count,
        covered_code_units, total_code_units,
        (int32_t)never_compile_called_coverage_threshold,
        SHOW(method->get_code()->cfg()));
  return true;
}

bool never_compile_string_lookup_method_matches(
    DexMethod* method, bool never_compile_strings_lookup_methods) {
  if (!never_compile_strings_lookup_methods) {
    return false;
  }
  auto* cls = type_class(method->get_class());
  if ((cls == nullptr) || !cls->rstate.is_generated() ||
      cls->get_perf_sensitive() != PerfSensitiveGroup::STRINGS_LOOKUP) {
    return false;
  }
  TRACE(APW, 5, "[%s] matches string-lookup method",
        method->get_fully_deobfuscated_name().c_str());
  return true;
}

} // namespace

UnorderedSet<std::string> excluded_interaction_ids(
    const baseline_profiles::BaselineProfileConfig& baseline_profile_config) {
  UnorderedSet<std::string> excluded_interaction_ids;
  const auto& harvest_config = baseline_profile_config.harvest_config;
  if (!harvest_config.never_compile_excluded_interaction_pattern.empty()) {
    boost::regex rx(harvest_config.never_compile_excluded_interaction_pattern);
    for (auto&& [interaction_id, interaction_name] :
         baseline_profile_config.interactions) {
      if (boost::regex_match(interaction_name, rx)) {
        excluded_interaction_ids.insert(interaction_id);
      }
    }
  }
  return excluded_interaction_ids;
}

std::optional<NeverCompileRules> select_never_compile(
    DexMethod* method,
    IRCode& code,
    const baseline_profiles::BaselineProfile& baseline_profile,
    const baseline_profiles::BaselineProfileConfig& baseline_profile_config,
    const UnorderedSet<std::string>& excluded_interaction_ids,
    const method_profiles::MethodProfiles& method_profiles) {
  const auto& harvest_config = baseline_profile_config.harvest_config;
  if (method::is_clinit(method)) {
    return std::nullopt;
  }
  auto it = baseline_profile.methods.find(method);
  if (!harvest_config.never_compile_ignore_hot) {
    if (it == baseline_profile.methods.end()) {
      return std::nullopt;
    }
    const auto& mf = it->second;
    if (!mf.hot) {
      return std::nullopt;
    }
  }
  double call_count = 0;
  for (auto&& [interaction_id, _] : baseline_profile_config.interactions) {
    auto method_stats = method_profiles.get_method_stat(interaction_id, method);
    if (!method_stats) {
      continue;
    }
    if ((excluded_interaction_ids.count(interaction_id) != 0u) &&
        method_stats->appear_percent >
            static_cast<double>(
                harvest_config.never_compile_excluded_appear100_threshold) &&
        method_stats->call_count >
            static_cast<double>(
                harvest_config.never_compile_excluded_call_count_threshold)) {
      return std::nullopt;
    }
    call_count = std::max(call_count, method_stats->call_count);
  }

  loop_impl::LoopInfo loop_info(code.cfg());
  if (loop_info.num_loops() > 0) {
    return std::nullopt;
  }

  NeverCompileRules rules;
  rules.callcount = never_compile_callcount_threshold_met(
      call_count, harvest_config.never_compile_callcount_threshold);
  rules.perf = never_compile_perf_threshold_met(
      method, harvest_config.never_compile_perf_threshold);
  rules.called_coverage = never_compile_called_coverage_threshold_met(
      method, call_count,
      harvest_config.never_compile_called_coverage_threshold);
  rules.strings_lookup = never_compile_string_lookup_method_matches(
      method, harvest_config.never_compile_strings_lookup_methods);
  return rules;
}

} // namespace never_compile_analysis
