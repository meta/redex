/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "MethodSplitter.h"

namespace method_splitting_test {

// A split environment without a min-sdk API file or class initialization
// instructions.
inline method_splitting_impl::SplitEnvironment split_environment(
    const DexStoresVector& stores,
    bool normal_primary_dex,
    int32_t min_sdk = 0,
    size_t reserved_mrefs = 0) {
  return method_splitting_impl::SplitEnvironment{
      min_sdk,
      method_splitting_impl::StoreRefCheckers(stores, normal_primary_dex,
                                              /* min_sdk_api */ nullptr),
      /* create_init_class_insns */ false, reserved_mrefs,
      /* reserved_trefs */ 0};
}

} // namespace method_splitting_test
