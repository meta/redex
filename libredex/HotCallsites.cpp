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
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"
#include "Resolver.h"
#include "SourceBlocks.h"
#include "TypeInference.h"
#include "Walkers.h"

namespace never_inline_analysis {

HotCallsites::HotCallsites(
    const Scope& scope,
    const baseline_profiles::BaselineProfile& baseline_profile,
    const method_profiles::MethodProfiles& method_profiles,
    const HotCallsiteThresholds& thresholds) {
  using baseline_profiles::is_compiled;

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
    } while (is_simple(callee, &invoke_insn) && invoke_insn != nullptr);
    return callee;
  };

  // Analyze caller/callee relationships
  std::atomic<size_t> callers_too_many_instructions_count{0};
  std::atomic<size_t> callers_too_many_registers_count{0};
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
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    if (!is_compiled(baseline_profile, caller)) {
      return;
    }
    size_t caller_instructions = estimated_instructions.at(caller);
    if (caller_instructions > thresholds.max_caller_instructions) {
      callers_too_many_instructions_count.fetch_add(1);
      return;
    }
    size_t caller_registers = code.cfg().get_registers_size();
    if (caller_registers > thresholds.max_caller_registers) {
      callers_too_many_registers_count.fetch_add(1);
      return;
    }
    for (auto* b : code.cfg().blocks()) {
      bool callsite_has_catch =
          code.cfg().get_succ_edge_of_type(b, cfg::EDGE_THROW) != nullptr;
      bool has_throw = false;
      bool has_non_init_invoke = false;
      for (auto& mie : InstructionIterable(b).reversed()) {
        auto* insn = mie.insn;
        if (!opcode::is_an_invoke(insn->opcode())) {
          if (opcode::is_throw(insn->opcode())) {
            has_throw = true;
          }
          continue;
        }
        if (has_throw && !has_non_init_invoke) {
          if (!method::is_init(insn->get_method())) {
            has_non_init_invoke = true;
          }
          continue;
        }

        DexMethod* callee = get_callee(caller, insn);
        if (callee == nullptr) {
          continue;
        }

        auto it = estimated_instructions.find(callee);
        if (it == estimated_instructions.end()) {
          continue;
        }

        if (callsite_has_catch && has_catches.at(callee)) {
          continue;
        }

        if (is_sufficiently_hot(b, callee)) {
          hot_callsite_counts.fetch_add(callee, 1);
        } else {
          hot_cold_callees.insert(callee);
        }
      }
    }
  });
  callers_too_many_instructions = callers_too_many_instructions_count.load();
  callers_too_many_registers = callers_too_many_registers_count.load();
}

} // namespace never_inline_analysis
