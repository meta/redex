/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "Pass.h"
#include "TypeInference.h"

class PackagePrivatePreprocessorPass : public Pass {
 public:
  PackagePrivatePreprocessorPass() : Pass("PackagePrivatePreprocessorPass") {}

  struct Stats {
    int unresolved_types{0};
    int external_inaccessible_types{0};
    int internal_inaccessible_types{0};

    int unresolved_fields{0};
    int external_inaccessible_private_fields{0};
    int external_inaccessible_fields{0};
    int internal_inaccessible_fields{0};

    int unresolved_methods{0};
    int external_inaccessible_private_methods{0};
    int external_inaccessible_methods{0};
    int internal_inaccessible_methods{0};

    int apparent_override_inaccessible_methods{0};
    int override_package_private_methods{0};

    int package_private_accessed_classes{0};
    int package_private_accessed_methods{0};
    int package_private_accessed_fields{0};
    int new_virtual_scope_roots{0};

    int renamed_methods{0};
    int updated_method_refs{0};
    int publicized_classes{0};
    int publicized_methods{0};
    int publicized_fields{0};
    int unsupported_unrenamable_methods{0};
    int unsupported_interface_implementations{0};
    int unsupported_multiple_package_private_overrides{0};
    int unsupported_non_public_interface_implementations{0};

    void report(PassManager& mgr);

    Stats& operator+=(const Stats& that);
  };

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {{DexLimitsObeyed, Preserves},
            {UltralightCodePatterns, Preserves},
            {NoInitClassInstructions, Preserves},
            {RenameClass, Preserves}};
  }

  void bind_config() override {
    bind("fail_if_illegal_internal_refs",
         false,
         m_fail_if_illegal_internal_refs);
    bind("fail_if_unsupported_refs", false, m_fail_if_unsupported_refs);
  }

  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

  const Stats& get_stats() const { return m_stats; }

 private:
  bool m_fail_if_illegal_internal_refs;
  bool m_fail_if_unsupported_refs;
  Stats m_stats;
};
