/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexClass.h"
#include "IRCode.h"
#include "Pass.h"

class StripDebugInfoPass : public Pass {
 public:
  StripDebugInfoPass() : Pass("StripDebugInfoPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {NoResolvablePureRefs, Preserves},
        {UltralightCodePatterns, Preserves},
    };
  }

  void bind_config() override {
    bind("drop_all_dbg_info", false, m_config.drop_all_dbg_info);
    bind("drop_local_variables", true, m_config.drop_local_variables);
    bind("drop_line_numbers", false, m_config.drop_line_nrs);
    bind("drop_src_files", true, m_config.drop_src_files);
    bind("drop_prologue_end", true, m_config.drop_prologue_end);
    bind("drop_epilogue_begin", true, m_config.drop_epilogue_begin);
    bind("drop_all_dbg_info_if_empty",
         true,
         m_config.drop_all_dbg_info_if_empty);
    bind("drop_synth_aggressive", false, m_config.drop_synth_aggressive);
    bind("drop_synth_conservative", false, m_config.drop_synth_conservative);
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

  void set_drop_prologue_end(bool b) { m_config.drop_prologue_end = b; }
  void set_drop_local_variables(bool b) { m_config.drop_local_variables = b; }
  void set_drop_epilogue_begin(bool b) { m_config.drop_epilogue_begin = b; }
  void set_drop_all_debug_info(bool b) { m_config.drop_all_dbg_info = b; }
  void set_drop_line_numbers(bool b) { m_config.drop_line_nrs = b; }

  struct Config {
    bool drop_all_dbg_info{false};
    bool drop_local_variables{false};
    bool drop_line_nrs{false};
    bool drop_src_files{false};
    bool drop_prologue_end{false};
    bool drop_epilogue_begin{false};
    bool drop_all_dbg_info_if_empty{false};
    bool drop_synth_aggressive{false};
    bool drop_synth_conservative{false};
  };

 private:
  Config m_config;
};

namespace strip_debug_info_impl {

struct Stats {
  int num_matches{0};
  int num_pos_dropped{0};
  int num_var_dropped{0};
  int num_prologue_dropped{0};
  int num_epilogue_dropped{0};
  int num_empty_dropped{0};
  int num_skipped_due_to_inlining{0};

  Stats& operator+=(const Stats& other);
};

class StripDebugInfo {
 public:
  explicit StripDebugInfo(const StripDebugInfoPass::Config& config)
      : m_config(config) {}

  Stats run(const Scope& scope);

  Stats run(IRCode&, bool should_drop_synth = false);

 private:
  bool drop_local_variables() const {
    return m_config.drop_local_variables || m_config.drop_all_dbg_info;
  }
  bool drop_prologue() const {
    return m_config.drop_prologue_end || m_config.drop_all_dbg_info;
  }
  bool drop_epilogue() const {
    return m_config.drop_epilogue_begin || m_config.drop_all_dbg_info;
  }
  bool drop_line_numbers() const {
    return m_config.drop_line_nrs || m_config.drop_all_dbg_info;
  }
  bool should_remove(const MethodItemEntry& mei, Stats& stats);
  bool should_drop_for_synth(const DexMethod*) const;

  const StripDebugInfoPass::Config& m_config;
};

} // namespace strip_debug_info_impl
