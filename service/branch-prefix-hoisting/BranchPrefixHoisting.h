/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConstantUses.h"
#include "Lazy.h"
#include "PositionJoin.h"

class IRCode;

namespace cfg {
class ControlFlowGraph;
} // namespace cfg

namespace branch_prefix_hoisting_impl {

// When non-null, `join_stats` counts fidelity changes and throwing instructions
// for which hoisting could not copy a governing position. Marking does not
// depend on whether stats are requested.
size_t process_code(IRCode*,
                    DexMethod*,
                    bool can_allocate_regs = true,
                    positions::JoinStats* join_stats = nullptr);
size_t process_cfg(cfg::ControlFlowGraph&,
                   Lazy<const constant_uses::ConstantUses>&,
                   bool can_allocate_regs = true,
                   positions::JoinStats* join_stats = nullptr);
} // namespace branch_prefix_hoisting_impl
