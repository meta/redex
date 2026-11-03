/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>

#include "Pass.h"
#include "PassManager.h"

class ArtProfileWriterPass : public Pass {
 public:
  // Inlining replaces a call
  //
  //   invoke-static {...}, callee   // 3 code units
  //   move-result vX                // 1 code unit
  //
  // with a copy of the callee, so it adds code only when the callee is longer
  // than 4 code units. Therefore, 5 is the minimum callee size that can benefit
  // from not inlining.
  static constexpr uint32_t kDefaultNeverInlineMinHotCallsitesMinCodeUnits = 5;

  ArtProfileWriterPass() : Pass("ArtProfileWriterPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return redex_properties::simple::preserves_all();
  }

  void bind_config() override;
  void eval_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  bool m_never_inline_estimate;
  bool m_never_inline_attach_annotations;
  float m_never_inline_hot_block_appear_threshold;
  float m_never_inline_hot_method_appear_threshold;
  size_t m_never_inline_max_caller_instructions;
  size_t m_never_inline_max_caller_registers;
  uint32_t m_never_inline_max_callee_code_units;
  size_t m_never_inline_min_callee_instructions;
  size_t m_never_inline_min_hot_callsites;
  uint32_t m_never_inline_min_hot_callsites_min_code_units;
  bool m_include_strings_lookup_class;
  std::optional<ReserveRefsInfoHandle> m_reserved_refs_handle;
  std::optional<bool> m_override_strip_classes;
  uint32_t m_huge_method_max;
  size_t m_topoff_target_entries;
};
