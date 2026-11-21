/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RegionPlan.h"

#include "Debug.h"

namespace method_splitting_impl {

RegionPlan RegionPlan::make(const std::vector<const Closure*>& members) {
  always_assert(members.size() == 1);
  always_assert(members.front() != nullptr &&
                members.front()->region.has_value());
  return RegionPlan(HostSwitchEdit::None);
}

} // namespace method_splitting_impl
