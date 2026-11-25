/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <vector>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "SplitNetSaving.h"

namespace method_splitting_test {

// A switch on v0 with cases 0 and 1 and a default, each one block. Case 0 and
// the default rejoin at one block, case 1 at another.
struct SwitchFixture {
  std::unique_ptr<IRCode> code;
  cfg::Block* sw{nullptr};
  cfg::Block* case0{nullptr};
  cfg::Block* case1{nullptr};
  cfg::Block* dflt{nullptr};

  SwitchFixture() {
    code = assembler::ircode_from_string(R"((
      (load-param v0)
      (switch v0 (:case0 :case1))
      (const v1 3)
      (goto :join)
      (:case0 0)
      (const v1 1)
      (goto :join)
      (:case1 1)
      (const v1 2)
      (goto :other)
      (:join)
      (return-void)
      (:other)
      (return-void)
    ))");
    code->build_cfg();
    for (auto* b : code->cfg().blocks()) {
      auto last = b->get_last_insn();
      if (last != b->end() && opcode::is_switch(last->insn->opcode())) {
        sw = b;
      }
    }
    always_assert(sw != nullptr);
    for (auto* e : sw->succs()) {
      if (!e->case_key()) {
        dflt = e->target();
      } else if (*e->case_key() == 0) {
        case0 = e->target();
      } else {
        case1 = e->target();
      }
    }
  }

  // The partition of the switch's edges by the heads `heads`.
  method_splitting_impl::SwitchPartition partition(
      const std::vector<cfg::Block*>& heads) const {
    UnorderedSet<cfg::BlockId> ids;
    for (auto* h : heads) {
      ids.insert(h->id());
    }
    return method_splitting_impl::partition_switch(sw, ids);
  }

  static cfg::Block* rejoin_of(cfg::Block* b) { return b->goes_to(); }
};

} // namespace method_splitting_test
