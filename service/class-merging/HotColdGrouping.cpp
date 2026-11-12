/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "HotColdGrouping.h"

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "MethodUtil.h"

namespace class_merging {

UnorderedSet<const DexMethod*> get_hot_methods(const Scope& scope,
                                               ConfigFiles& conf) {
  auto baseline_profile =
      baseline_profiles::get_default_baseline_profile(scope, conf);
  UnorderedSet<const DexMethod*> hot_methods;
  for (auto&& [method, flags] : UnorderedIterable(baseline_profile.methods)) {
    if (flags.hot) {
      hot_methods.insert(method);
    }
  }
  return hot_methods;
}

bool is_hot_mergeable(const DexClass* cls,
                      const virtual_scope::VirtualScopes& vscopes,
                      const UnorderedSet<const DexMethod*>& hot_methods) {
  const auto is_hot = [&hot_methods](const DexMethod* method) {
    return hot_methods.find(method) != hot_methods.end();
  };

  for (const auto* method : cls->get_dmethods()) {
    if (method::is_init(method) && is_hot(method)) {
      return true;
    }
  }

  UnorderedSet<const DexMethod*> relocated;
  for (const auto* scope : vscopes.at(cls->get_type())) {
    if (!scope->implements_interface() && scope->is_effectively_final()) {
      relocated.insert(scope->top_def());
    }
  }
  for (const auto* method : cls->get_vmethods()) {
    if (relocated.find(method) == relocated.end() && is_hot(method)) {
      return true;
    }
  }
  return false;
}

} // namespace class_merging
