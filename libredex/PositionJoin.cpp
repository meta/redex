/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PositionJoin.h"

#include "RedexContext.h"

namespace positions {

FidelityChange mark_merged(DexPosition* survivor) {
  always_assert(survivor != nullptr);
  // An empty request reports a site nobody captured: the manager drops any set
  // the survivor carried, and leaves an already uncaptured survivor as it is.
  return g_redex->get_position_pattern_switch_manager()->record_candidates(
      survivor, {});
}

} // namespace positions
