/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConstantPropagation.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
#include "Pass.h"

class ConstantPropagationPass : public Pass {
 public:
  ConstantPropagationPass() : Pass("ConstantPropagationPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NeedsAreEqualRefReservation, Establishes},
        {NoResolvablePureRefs, Preserves},
    };
  }

  void bind_config() override {
    bind("replace_moves_with_consts",
         true,
         m_config.transform.replace_moves_with_consts);
    bind("remove_dead_switch", true, m_config.transform.remove_dead_switch);
    bind("track_constructor_fields", false, m_config.track_constructor_fields,
         "In constructors, track the class's own fields from their zero "
         "initial values until `this` may escape, so that redundant stores to "
         "them are removed and reads of them become constants.");
  }

  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

 private:
  constant_propagation::Config m_config;
};
