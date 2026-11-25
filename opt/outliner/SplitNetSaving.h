/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <variant>

#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "IROpcode.h"
#include "InstructionLowering.h"
#include "MethodClosures.h"
#include "MethodSplittingConfig.h"

namespace method_splitting_impl {

// The code units an instruction of `op` takes in the dex, at the widest form
// of an opcode with a literal, as `Block::estimate_code_units` counts it. The
// net cost model sizes every single instruction it adds by this, or a `const`
// of a known literal by `instruction_lowering::const_code_units`.
size_t opcode_code_units(IROpcode op);

// The code units `insn` takes in the dex: `IRInstruction::size`, except that a
// `const` or `const-wide` is sized at the narrowest form its literal fits
// instead of the widest (`instruction_lowering::const_code_units`). (The 4-bit
// `const/4` also needs a low register, which register allocation decides
// later.)
size_t dex_code_units(const IRInstruction* insn);

// `Block::estimate_code_units`, with each instruction sized by
// `dex_code_units`.
size_t dex_code_units(const cfg::Block* b);

// A switch's edges, split by whether their target is a head the split takes.
// Every key is inserted, including several keys that share one target.
struct SwitchPartition {
  instruction_lowering::CaseKeysExtentBuilder all;
  instruction_lowering::CaseKeysExtentBuilder grouped;
  instruction_lowering::CaseKeysExtentBuilder kept;
  bool default_grouped{false};
};

SwitchPartition partition_switch(
    const cfg::Block* sw, const UnorderedSet<cfg::BlockId>& grouped_heads);

// The code units of a switch over `keys`, as the dex holds it once ReduceGotos
// has run:
// - nothing for a switch left with no key;
// - `if-eqz` for a switch over key 0 alone;
// - `rsub-int/lit8; if-eqz` for a switch over one other key that fits 8 bits,
//   when no edge the switch keeps reads its selector (`selector_live` false);
// - otherwise the opcode and its payload.
// ReduceGotos also turns a switch over one key into `const; if-eq` in a method
// with fewer than 16 registers. A method worth splitting rarely has so few, so
// that form is not costed.
size_t switch_dispatch_code_units(
    const instruction_lowering::CaseKeysExtentBuilder& keys,
    bool selector_live);

// The code units of the host's dispatch once `edit` is applied to the
// partitioned switch, `selector_live` saying whether an edge the edited switch
// keeps reads its selector. The host keeps its default edge.
size_t host_dispatch_after(const SwitchPartition& partition,
                           HostSwitchEdit edit,
                           bool selector_live);

// Everything the net saving of one split depends on.
struct NetSavingInput {
  // A suffix: one launchpad invokes the split and returns its result,
  // `move-result` first when the host returns a value.
  struct Suffix {
    bool returns_value;
  };
  std::variant<Suffix> split;
  // The switch whose cases the split takes, for a split with several entries.
  struct Dispatch {
    const SwitchPartition& partition;
    // Whether a case the split's copy of the switch keeps reads its selector.
    bool selector_live_in_split;
    // Whether an edge of the host's switch reads its selector, before the edit
    // and after it. After the edit, the launchpad counts as such a reader where
    // it passes the selector as an argument.
    bool selector_live_in_host_before;
    bool selector_live_in_host_after;
  };
  std::optional<Dispatch> dispatch;
  // `evicted`: the code that leaves the host and is not hot, in the code units
  // the profile counts compiled code in (`Block::estimate_code_units`).
  // `duplicated`: the dex code units (`dex_code_units`) of the code the split
  // copies while the host keeps it.
  size_t evicted;
  size_t duplicated;
  // The arguments the launchpad passes, and the registers they take in the
  // invoke.
  size_t passed_args;
  size_t passed_arg_registers;
  // The dex code units of the constant definitions the split recreates at its
  // entry instead of taking them as arguments.
  size_t recreated_defs;
  // The copies of the host's code that run compiled: the host itself, or each
  // copy of a small host that ART inlines into its compiled callers. Every
  // copy loses the evicted code and gains the launchpad.
  size_t compiled_copies{1};
  // Set when the split changes how many compiled copies of the host there
  // are, because the smaller host is inlined at more call sites or fewer. A
  // copy that exists only before the split takes the whole host out of the
  // compiled code; one that exists only after it adds the host the split
  // leaves, launchpad included.
  struct CopiesAfter {
    // The compiled copies of the host after the split.
    size_t copies;
    // The compiled code units of the host before the split, and after it
    // without the launchpad.
    size_t host_before;
    size_t host_after;
  };
  std::optional<CopiesAfter> copies_after{std::nullopt};
  // Whether the split itself is compiled, as a Hot split is: the evicted code
  // then stays compiled once, in the split.
  bool split_compiled{false};
};

// The quantities of the net cost model, in code units:
// net = W * (saved - added_ccuc) - dex_added.
struct ClosureNetTerms {
  // Code that leaves the compiled copies of the host; 0 for an uncompiled
  // host.
  int64_t saved{0};
  // Code the launchpad adds back to the compiled copies of the host; 0 for an
  // uncompiled host.
  int64_t added_ccuc{0};
  // Dex growth: the launchpad, the split's metadata and body overhead, its
  // copy of a taken switch (with that copy's dummy default value), and the
  // duplicated code, less the dispatch the host's switch sheds.
  int64_t dex_added{0};
  double net{0.0};
};

ClosureNetTerms split_net_saving(const NetSavingInput& input,
                                 const Config& config,
                                 bool host_compiled);

} // namespace method_splitting_impl
