/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "Pass.h"
#include "PassManager.h"

class UnreachableLoweringPass : public Pass {
 public:
  UnreachableLoweringPass() : Pass("UnreachableLoweringPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {NoInitClassInstructions, Preserves},
        {NoResolvablePureRefs, Preserves},
        {NoUnreachableInstructions, Establishes},
        {RenameClass, Preserves},
    };
  }

  void bind_config() override;

  void eval_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  std::optional<ReserveRefsInfoHandle> m_reserved_refs_handle;
  DexMethod* m_create_and_throw_method{nullptr};
  bool m_typed_nonreturning_methods{false};
};
