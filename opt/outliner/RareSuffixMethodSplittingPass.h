/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "MethodSplittingConfig.h"
#include "Pass.h"

// Moves a rarely run suffix of a small method into a new static method of the
// same class, for methods small enough that ART inlines them into their
// compiled callers. Every inlined copy then holds a call instead of that code.
// Which suffixes count as rarely run is up to `RareSuffixSelection`.
class RareSuffixMethodSplittingPass : public Pass {
 public:
  RareSuffixMethodSplittingPass() : Pass("RareSuffixMethodSplittingPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {NoResolvablePureRefs, Preserves},
        {InitialRenameClass, Preserves},
    };
  }

  std::string get_config_doc() override {
    return trim(R"(
Moves a rarely run suffix of a small method into a new static method of the
same class, so that the copies ART inlines into compiled callers hold a call
instead of that code. A suffix that never returns, typically because it throws,
counts as rarely run. A method qualifies when it is small enough for ART to
inline, is called from compiled code, and the suffix makes several calls or
allocations.
    )");
  }

  void bind_config() override;
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  bool m_enabled{false};
  uint32_t m_art_inline_max_code_units;
  size_t m_max_caller_instructions;
  size_t m_min_compiled_call_sites;
  size_t m_min_suffix_runtime_calls;
  // The candidate evaluation and the net cost model MethodSplittingPass uses,
  // with this pass's live-in limit and code-unit costs.
  method_splitting_impl::Config m_config;
};
