/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "LocalPointersAnalysis.h"
#include "Pass.h"
#include "Trace.h"

class ObjectSensitiveDcePass final : public Pass {
 public:
  ObjectSensitiveDcePass() : Pass("ObjectSensitiveDcePass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
    };
  }

  void bind_config() override {
    bind("side_effect_summaries", {std::nullopt},
         m_external_side_effect_summaries_file, "TODO: Document me!",
         Configurable::bindflags::optionals::skip_empty_string);
    bind("escape_summaries", {std::nullopt}, m_external_escape_summaries_file,
         "TODO: Document me!",
         Configurable::bindflags::optionals::skip_empty_string);
    bind(
        "big_override_threshold",
        local_pointers::EscapeCallGraphStrategy::DEFAULT_BIG_OVERRIDE_THRESHOLD,
        m_big_override_threshold);

    if (!m_external_escape_summaries_file ||
        !m_external_side_effect_summaries_file) {
      TRACE(OSDCE, 1,
            "WARNING: External summary file missing; OSDCE will make "
            "conservative assumptions about system & third-party code.");
    }
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  std::optional<std::string> m_external_side_effect_summaries_file;
  std::optional<std::string> m_external_escape_summaries_file;
  uint32_t m_big_override_threshold;
};
