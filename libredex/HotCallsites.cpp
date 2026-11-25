/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "HotCallsites.h"

#include <algorithm>
#include <atomic>

#include "BaselineProfile.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "MethodProfiles.h"
#include "Resolver.h"
#include "SourceBlocks.h"
#include "TypeInference.h"
#include "Walkers.h"

namespace never_inline_analysis {

CallerVerdict classify_caller(bool compiled,
                              size_t instructions,
                              size_t registers,
                              size_t max_caller_instructions,
                              size_t max_caller_registers) {
  if (!compiled) {
    return CallerVerdict::kNotCompiled;
  }
  switch (caller_inline_budget(instructions, registers, max_caller_instructions,
                               max_caller_registers)) {
  case CallerBudget::kTooManyInstructions:
    return CallerVerdict::kTooManyInstructions;
  case CallerBudget::kTooManyRegisters:
    return CallerVerdict::kTooManyRegisters;
  case CallerBudget::kWithin:
    return CallerVerdict::kRead;
  }
  not_reached();
}

CallsiteWalkCounts walk_callsites(const Scope& scope,
                                  const CallsiteWalk& walk,
                                  const CallsiteVisitor& visit) {
  auto consider_callee = [&](DexMethod* callee) {
    if (callee == nullptr || (callee->get_code() == nullptr)) {
      return false;
    }
    auto* cls = type_class(callee->get_class());
    if ((cls == nullptr) || cls->is_external()) {
      return false;
    }
    if (callee->is_virtual() && (!is_final(callee) && !is_final(cls))) {
      return false;
    }
    return true;
  };

  using ReceiverMap = UnorderedMap<const IRInstruction*, const DexType*>;
  InsertOnlyConcurrentMap<DexMethod*, ReceiverMap> receiver_types;
  auto get_callee = [&](DexMethod* caller,
                        IRInstruction* invoke_insn) -> DexMethod* {
    DexMethod* callee;
    do {
      callee = nullptr;
      auto caller_it = receiver_types.find(caller);
      if (caller_it != receiver_types.end()) {
        const auto& map = caller_it->second;
        auto map_it = map.find(invoke_insn);
        if (map_it != map.end()) {
          const auto* receiver_type = map_it->second;
          auto* receiver_cls = type_class(receiver_type);
          if ((receiver_cls != nullptr) && !is_interface(receiver_cls)) {
            auto* invoke_method = invoke_insn->get_method();
            callee = resolve_virtual_deprecated(receiver_cls,
                                                invoke_method->get_name(),
                                                invoke_method->get_proto());
          }
        }
      }
      if (callee == nullptr) {
        callee = resolve_invoke_method_deprecated(invoke_insn, caller);
      }
      if (!consider_callee(callee)) {
        return nullptr;
      }
      caller = callee;
      invoke_insn = nullptr;
    } while (is_simple(callee, &invoke_insn) && invoke_insn != nullptr &&
             walk.follow_forwarder(callee));
    return callee;
  };

  // Analyze caller/callee relationships
  std::atomic<size_t> callers_too_many_instructions{0};
  std::atomic<size_t> callers_too_many_registers{0};
  InsertOnlyConcurrentMap<DexMethod*, size_t> estimated_instructions;
  InsertOnlyConcurrentMap<DexMethod*, bool> has_catches;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    size_t instructions = code.count_opcodes();
    estimated_instructions.emplace(method, instructions);

    auto blocks = code.cfg().blocks();
    bool has_catch =
        std::any_of(blocks.begin(), blocks.end(),
                    [](cfg::Block* block) { return block->is_catch(); });
    has_catches.emplace(method, has_catch);

    type_inference::TypeInference ti(code.cfg());
    ti.run(method);
    const auto& type_envs = ti.get_type_environments();
    ReceiverMap map;
    for (auto& mie : InstructionIterable(code.cfg())) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (!opcode::is_invoke_virtual(op) && !opcode::is_invoke_interface(op)) {
        continue;
      }
      always_assert(type_envs.count(insn));
      const auto& env = type_envs.at(insn);
      auto dex_type = env.get_dex_type(insn->src(0));
      if (dex_type.has_value()) {
        map.emplace(insn, *dex_type);
      }
    }
    receiver_types.emplace(method, std::move(map));
  });
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    bool within_register_bound = true;
    switch (classify_caller(walk.caller_compiled(caller),
                            estimated_instructions.at(caller),
                            code.cfg().get_registers_size(),
                            walk.max_caller_instructions,
                            walk.max_caller_registers)) {
    case CallerVerdict::kNotCompiled:
      return;
    case CallerVerdict::kTooManyInstructions:
      callers_too_many_instructions.fetch_add(1);
      return;
    case CallerVerdict::kTooManyRegisters:
      callers_too_many_registers.fetch_add(1);
      if (!walk.visit_callers_over_register_bound) {
        return;
      }
      within_register_bound = false;
      break;
    case CallerVerdict::kRead:
      break;
    }
    for (auto* b : code.cfg().blocks()) {
      for_each_block_callsite(b, [&](IRInstruction* insn) {
        DexMethod* callee = get_callee(caller, insn);
        if (callee == nullptr) {
          return;
        }

        auto it = estimated_instructions.find(callee);
        if (it == estimated_instructions.end()) {
          return;
        }

        if (is_try_excluded(code.cfg(), b, has_catches.at(callee))) {
          return;
        }

        visit(b, callee, within_register_bound);
      });
    }
  });
  return CallsiteWalkCounts{
      .callers_too_many_instructions = callers_too_many_instructions.load(),
      .callers_too_many_registers = callers_too_many_registers.load(),
  };
}

HotCallsites::HotCallsites(
    const Scope& scope,
    const baseline_profiles::BaselineProfile& baseline_profile,
    const method_profiles::MethodProfiles& method_profiles,
    const HotCallsiteThresholds& thresholds) {
  using baseline_profiles::is_compiled;

  auto method_profile_appears = [&](DexMethod* method, float appear_threshold) {
    for (const auto& p : method_profiles.all_interactions()) {
      auto it = p.second.find(method);
      if (it != p.second.end() &&
          it->second.appear_percent >= appear_threshold) {
        return true;
      }
    }
    return false;
  };
  auto is_sufficiently_hot = [&](cfg::Block* block, DexMethod* callee) {
    if (!is_compiled(baseline_profile, callee)) {
      return false;
    }
    if (thresholds.hot_block_appear_threshold >= 0 &&
        !source_blocks::maybe_hot(block,
                                  thresholds.hot_block_appear_threshold)) {
      return false;
    }
    if (thresholds.hot_method_appear_threshold >= 0 &&
        !source_blocks::method_maybe_hot(
            callee, thresholds.hot_method_appear_threshold) &&
        !method_profile_appears(callee,
                                thresholds.hot_method_appear_threshold)) {
      return false;
    }
    return true;
  };
  const auto counts = walk_callsites(
      scope,
      CallsiteWalk{
          .caller_compiled =
              [&](DexMethod* caller) {
                return is_compiled(baseline_profile, caller);
              },
          .max_caller_instructions = thresholds.max_caller_instructions,
          .max_caller_registers = thresholds.max_caller_registers,
          .visit_callers_over_register_bound = false,
          .follow_forwarder = [](const DexMethod*) { return true; },
      },
      [&](cfg::Block* block, DexMethod* callee, bool) {
        if (is_sufficiently_hot(block, callee)) {
          hot_callsite_counts.fetch_add(callee, 1);
        } else {
          hot_cold_callees.insert(callee);
        }
      });
  callers_too_many_instructions = counts.callers_too_many_instructions;
  callers_too_many_registers = counts.callers_too_many_registers;
}

NeverInlineVerdict decide_never_inline(IRCode& code,
                                       bool already_never_inline,
                                       bool has_cold_callsite,
                                       size_t hot_callsites,
                                       const NeverInlineCriteria& criteria) {
  if (already_never_inline) {
    return {.decision = NeverInlineDecision::kAlreadyNeverInline};
  }

  bool min_hot_callsites_rule_met =
      hot_callsites >= criteria.min_hot_callsites &&
      code.estimate_code_units() >= criteria.min_hot_callsites_min_code_units;

  if (!has_cold_callsite && !min_hot_callsites_rule_met) {
    return {.decision = NeverInlineDecision::kNoCandidate};
  }

  if (hot_callsites != 0u && !min_hot_callsites_rule_met) {
    return {.decision = NeverInlineDecision::kTooHot};
  }

  const auto ineligibility = never_inline_eligibility(
      code, criteria.max_callee_code_units, criteria.min_callee_instructions);
  if (ineligibility != Ineligibility::kEligible) {
    return {.decision = NeverInlineDecision::kIneligible,
            .ineligibility = ineligibility};
  }
  return {.decision = NeverInlineDecision::kAnnotate,
          .min_hot_callsites_rule_met = min_hot_callsites_rule_met};
}

} // namespace never_inline_analysis
