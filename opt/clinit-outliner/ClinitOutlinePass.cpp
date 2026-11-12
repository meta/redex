/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ClinitOutlinePass.h"

#include <boost/regex.hpp>

#include "ApiLevelChecker.h"
#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "PassManager.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "Walkers.h"

void ClinitOutlinePass::bind_config() {
  bind("min_clinit_size", 16, m_min_clinit_size);
  bind("interaction_pattern", "", m_interaction_pattern);
  bind("interaction_threshold_override", -1, m_interaction_threshold_override);
  trait(Traits::Pass::unique, true);
}

void ClinitOutlinePass::run_pass(DexStoresVector& stores,
                                 ConfigFiles& conf,
                                 PassManager& mgr) {
  auto& method_profiles = conf.get_method_profiles();
  auto baseline_profile_config = conf.get_default_baseline_profile_config();
  if (!m_interaction_pattern.empty()) {
    boost::regex rx(m_interaction_pattern);
    unordered_erase_if(
        baseline_profile_config.interaction_configs,
        [&](auto& p) { return !boost::regex_match(p.first, rx); });
  }
  UnorderedMap<std::string, std::pair<int64_t, int64_t>> overridden_thresholds;
  if (m_interaction_threshold_override >= 0) {
    for (auto& [interaction_id, config] :
         UnorderedIterable(baseline_profile_config.interaction_configs)) {
      auto old_threshold = config.threshold;
      config.threshold = m_interaction_threshold_override;
      overridden_thresholds.emplace(
          interaction_id, std::make_pair(old_threshold, config.threshold));
    }
  }
  for (auto& [interaction_id, config] :
       UnorderedIterable(baseline_profile_config.interaction_configs)) {
    mgr.set_metric("interaction_" + interaction_id, config.threshold);
  }
  auto scope = build_class_scope(stores);
  baseline_profiles::BaselineProfileConfigMap bp_conf_map = {
      {baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME,
       baseline_profile_config}};
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, bp_conf_map, conf.get_method_profiles(),
      conf.get_coldstart_classes(),
      baseline_profiles::get_huge_method_max(conf));

  std::atomic<size_t> affected_final_fields{0};
  InsertOnlyConcurrentMap<DexMethod*, DexMethod*> outlined_clinits;

  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (!method::is_clinit(method) || method->rstate.no_optimizations() ||
        method->rstate.should_not_outline()) {
      return;
    }

    auto it = baseline_profile.methods.find(method);
    if (it == baseline_profile.methods.end()) {
      return;
    }
    if (!it->second.hot) {
      return;
    }

    if (code.estimate_code_units() < m_min_clinit_size) {
      // Probably not worth the overhead of another method.
      return;
    }

    UnorderedSet<DexField*> final_fields;
    for (auto& mie : InstructionIterable(code.cfg())) {
      auto* insn = mie.insn;
      if (opcode::is_an_sput(insn->opcode())) {
        auto* field = insn->get_field();
        auto* resolved_field = resolve_field(field, FieldSearch::Static);
        if ((resolved_field == nullptr) || !is_final(resolved_field)) {
          continue;
        }
        always_assert(field->get_class() == method->get_class());
        if (final_fields.insert(resolved_field).second) {
          resolved_field->set_access(resolved_field->get_access() & ~ACC_FINAL);
        }
      }
    }
    affected_final_fields.fetch_add(final_fields.size());
    auto* outlined_clinit =
        DexMethod::make_method(method->get_class(),
                               DexString::make_string("clinit$outlined"),
                               method->get_proto())
            ->make_concrete(ACC_STATIC | ACC_PUBLIC, method->release_code(),
                            /* is_virtual */ false);

    outlined_clinit->rstate.set_generated();
    outlined_clinit->rstate.set_dont_inline();
    int api_level = api::LevelChecker::get_method_level(method);
    outlined_clinit->rstate.set_api_level(api_level);
    outlined_clinit->set_deobfuscated_name(show_deobfuscated(outlined_clinit));

    method->set_code(std::make_unique<IRCode>());
    auto* new_code = method->get_code();
    auto* sb = source_blocks::get_first_source_block_of_method(outlined_clinit);
    if (sb != nullptr) {
      auto new_sb = source_blocks::clone_as_synthetic(sb);
      new_code->push_back(std::move(new_sb));
    }
    new_code->push_back(
        (new IRInstruction(OPCODE_INVOKE_STATIC))->set_method(outlined_clinit));
    new_code->push_back(new IRInstruction(OPCODE_RETURN_VOID));
    new_code->set_registers_size(0);
    new_code->build_cfg();

    outlined_clinits.emplace(method, outlined_clinit);
  });

  for (auto [method, outlined_clinit] : UnorderedIterable(outlined_clinits)) {
    type_class(method->get_class())->add_method(outlined_clinit);
    method_profiles.derive_stats(outlined_clinit, {method});
    // "Upgrade" appear_percent if configured threshold override applies, so
    // that ArtProfileWriter will consider outlined method as appropriate
    // considering threshold override.
    for (auto& [interaction_id, p] : UnorderedIterable(overridden_thresholds)) {
      auto [old_threshold, new_threshold] = p;
      auto stats =
          method_profiles.get_method_stat(interaction_id, outlined_clinit);
      if (stats &&
          stats->appear_percent >= static_cast<double>(new_threshold) &&
          stats->appear_percent < static_cast<double>(old_threshold)) {
        stats->appear_percent = static_cast<double>(old_threshold);
        method_profiles.set_method_stats(interaction_id, outlined_clinit,
                                         *stats);
      }
    }
  }

  mgr.set_metric("affected_clinits", outlined_clinits.size());
  mgr.set_metric("affected_final_fields", affected_final_fields.load());
  TRACE(CLINIT_OUTLINE, 1, "affected clinits: %zu, affected fields: %zu",
        outlined_clinits.size(), affected_final_fields.load());
}

static ClinitOutlinePass s_pass;
