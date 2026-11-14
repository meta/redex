/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <vector>

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

class DexMethod;
class DexStore;
using DexStoresVector = std::vector<DexStore>;

/**
 * Remove small identical virtual methods.
 * 1. Consider non-root and renamable methods without invoke-super. Remove the
 * child method if it overrides a method with the same implementation.
 *
 * Example:
 * class P {
 *   public int method() { return 0; }
 * }
 * class Child extends P {
 *   public int method() { return 0; }
 * }
 */
namespace dedup_vmethods {
uint32_t dedup(const DexStoresVector& stores,
               method_profiles::MethodProfiles* method_profiles = nullptr);

// Whether `method` may be removed in favor of an identical implementation in
// a superclass: small code without invoke-super, renamable, not a root, and
// not excluded from optimizations.
bool is_removable_copy(const DexMethod* method);
} // namespace dedup_vmethods
