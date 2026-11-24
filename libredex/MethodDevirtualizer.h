/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "Pass.h"

struct DevirtualizerConfigs {
  DevirtualizerConfigs(bool vmethods_not_using_this,
                       bool vmethods_using_this,
                       bool dmethods_not_using_this,
                       bool dmethods_using_this,
                       bool ignore_keep,
                       const UnorderedSet<DexType*>& do_not_devirt_anno)
      : vmethods_not_using_this(vmethods_not_using_this),
        vmethods_using_this(vmethods_using_this),
        dmethods_not_using_this(dmethods_not_using_this),
        dmethods_using_this(dmethods_using_this),
        ignore_keep(ignore_keep),
        do_not_devirt_anno(do_not_devirt_anno)

  {}

  bool vmethods_not_using_this = true;
  bool vmethods_using_this = false;
  bool dmethods_not_using_this = true;
  bool dmethods_using_this = false;
  bool ignore_keep = false;
  const UnorderedSet<DexType*>& do_not_devirt_anno;
};

struct DevirtualizerMetrics {
  uint32_t num_methods_not_using_this{0};
  uint32_t num_methods_using_this{0};
  uint32_t num_virtual_calls{0};
  uint32_t num_direct_calls{0};
  uint32_t num_super_calls{0};
};

class MethodDevirtualizer {
 public:
  explicit MethodDevirtualizer(DevirtualizerConfigs& config)
      : m_config(config) {}
  MethodDevirtualizer(bool vmethods_not_using_this,
                      bool vmethods_using_this,
                      bool dmethods_not_using_this,
                      bool dmethods_using_this,
                      bool ignore_keep,
                      const UnorderedSet<DexType*>& do_not_devirt_anno)

      : m_config(vmethods_not_using_this,
                 vmethods_using_this,
                 dmethods_not_using_this,
                 dmethods_using_this,
                 ignore_keep,
                 do_not_devirt_anno) {}

  DevirtualizerMetrics devirtualize_methods(const Scope& scope) {
    return devirtualize_methods(scope, scope);
  }

  DevirtualizerMetrics devirtualize_methods(
      const Scope& scope, const std::vector<DexClass*>& target_classes);

 private:
  DevirtualizerConfigs m_config;
  DevirtualizerMetrics m_metrics;

  void reset_metrics() { m_metrics = DevirtualizerMetrics(); }

  void staticize_methods_using_this(const std::vector<DexClass*>& scope,
                                    const UnorderedSet<DexMethod*>& methods);

  void staticize_methods_not_using_this(
      const std::vector<DexClass*>& scope,
      const UnorderedSet<DexMethod*>& methods);

  void verify_and_split(
      const std::vector<DexMethod*>& candidates,
      const InsertOnlyConcurrentSet<const DexMethod*>& method_handle_methods,
      UnorderedSet<DexMethod*>& using_this,
      UnorderedSet<DexMethod*>& not_using_this);
};
