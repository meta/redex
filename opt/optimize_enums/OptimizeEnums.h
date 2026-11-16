/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "Pass.h"

namespace optimize_enums {

class OptimizeEnumsPass : public Pass {

 public:
  OptimizeEnumsPass() : Pass("OptimizeEnumsPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
    };
  }

  void bind_config() override;
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  int m_max_enum_size;
  uint32_t m_enum_utils_split_size;
  bool m_skip_sanity_check;
  bool m_support_kt_19_enum_entries;
  bool m_inline_enum_values;
  std::vector<const DexType*> m_enum_to_integer_allowlist;
};

} // namespace optimize_enums
