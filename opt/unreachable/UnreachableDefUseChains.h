/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ControlFlow.h"
#include "IROpcode.h"
#include "LiveRange.h"

namespace unreachable {

// The uses of the values of the `unreachable` instructions in `cfg`, followed
// through moves.
inline live_range::DefUseChains get_def_use_chains(
    const cfg::ControlFlowGraph& cfg) {
  return live_range::MoveAwareChains(
             cfg, /* ignore_unreachable */ false,
             [](auto* insn) { return opcode::is_unreachable(insn->opcode()); })
      .get_def_use_chains();
}

} // namespace unreachable
