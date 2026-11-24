/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <vector>

#include "ConcurrentContainers.h"
#include "DexClass.h"

class TypeTags;

// One object serves one operation on one scope: the methods that method
// handles name, which keep their prototypes, are gathered at the first
// `lift_constants_from` call that has methods to lift from, and reused by the
// later calls.
class ConstantLifting {

 public:
  ConstantLifting();

  bool is_applicable_to_constant_lifting(const DexMethod* method);

  // The potentially created constant value stub methods are returned.
  std::vector<DexMethod*> lift_constants_from(
      const Scope& scope,
      const TypeTags* type_tags,
      const std::vector<DexMethod*>& methods,
      const size_t stud_method_threshold);

  uint32_t get_num_const_lifted_methods() const {
    return m_num_const_lifted_methods;
  }

 private:
  const DexType* s_method_meta_anno;
  uint32_t m_num_const_lifted_methods;
  std::optional<InsertOnlyConcurrentSet<const DexMethod*>>
      m_methods_named_by_method_handles;
};
