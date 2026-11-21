/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <vector>

#include "ControlFlow.h"
#include "MethodClosures.h"

namespace method_splitting_impl {

// The shape of one region split. It is decided once and read by the split's net
// saving and by the code that builds its call block.
class RegionPlan {
 public:
  // `members` are the candidate's closures, one per region. A plan takes
  // exactly one region: several would need the host's switch edited to take
  // each of their cases, which no plan here makes.
  static RegionPlan make(const std::vector<const Closure*>& members);

  HostSwitchEdit host_switch_edit() const { return m_host_switch_edit; }

 private:
  explicit RegionPlan(HostSwitchEdit host_switch_edit)
      : m_host_switch_edit(host_switch_edit) {}

  HostSwitchEdit m_host_switch_edit;
};

// The block the region of `member` hands control back to, read from the live
// CFG at emission.
cfg::Block* live_continuation(const Closure& member);

} // namespace method_splitting_impl
