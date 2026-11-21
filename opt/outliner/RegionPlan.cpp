/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RegionPlan.h"

#include "Debug.h"

namespace method_splitting_impl {

namespace {

// A continuation that reads the result of an instruction the split copied
// has nothing left to read.
void assert_region_boundary(const cfg::Block* exit) {
  always_assert_log(can_be_region_boundary(exit),
                    "region exit B%zu starts with move-result or "
                    "move-exception",
                    exit->id());
}

} // namespace

RegionPlan RegionPlan::make(const std::vector<const Closure*>& members) {
  always_assert(members.size() == 1);
  always_assert(members.front() != nullptr &&
                members.front()->region.has_value());
  return RegionPlan(HostSwitchEdit::None);
}

cfg::Block* live_continuation(const Closure& member) {
  // Read from the live CFG rather than from the block discovery recorded.
  // Emission is single-threaded and handles candidates one at a time, so an
  // EARLIER split in the same method may already have redirected the region's
  // out-edge, typically into that split's own call block. The continuation
  // discovery recorded is then orphaned but not deleted. Wiring this call block
  // to it would bring the orphan back to life: its body runs again and the move
  // out of the host it was split for is undone. Nothing asserts, because the
  // revived code is byte-identical. A single-block region leaves by its one
  // goto.
  auto* next = member.target->goes_to();
  always_assert_log(next != nullptr, "region at B%zu has no goto",
                    member.target->id());
  assert_region_boundary(next);
  return next;
}

} // namespace method_splitting_impl
