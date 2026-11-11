/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SplitNetSaving.h"

#include <algorithm>
#include <variant>

#include "Debug.h"
#include "IRInstruction.h"

namespace method_splitting_impl {

namespace {

// A non-range invoke names at most this many registers. Past it, the
// launchpad moves every argument into consecutive registers for the /range
// form, one move per register.
constexpr size_t kMaxNonRangeInvokeRegisters = 5;

} // namespace

size_t opcode_code_units(IROpcode op) { return IRInstruction(op).size(); }

size_t dex_code_units(const IRInstruction* insn) {
  const auto op = insn->opcode();
  if (op != OPCODE_CONST && op != OPCODE_CONST_WIDE) {
    return insn->size();
  }
  const auto units =
      instruction_lowering::const_code_units(op, insn->get_literal());
  redex_assert(units <= insn->size());
  return units;
}

size_t dex_code_units(const cfg::Block* b) {
  size_t units = b->estimate_code_units();
  for (const auto& mie : ir_list::ConstInstructionIterable(b)) {
    units -= mie.insn->size() - dex_code_units(mie.insn);
  }
  return units;
}

SwitchPartition partition_switch(
    const cfg::Block* sw, const UnorderedSet<cfg::BlockId>& grouped_heads) {
  SwitchPartition partition;
  bool saw_default = false;
  for (const auto* e : sw->succs()) {
    if (e->type() == cfg::EDGE_THROW) {
      continue;
    }
    const bool grouped = grouped_heads.contains(e->target()->id());
    if (e->type() == cfg::EDGE_BRANCH) {
      always_assert(e->case_key());
      partition.all.insert(*e->case_key());
      (grouped ? partition.grouped : partition.kept).insert(*e->case_key());
      continue;
    }
    always_assert(e->type() == cfg::EDGE_GOTO && !e->case_key());
    always_assert(!saw_default);
    saw_default = true;
    partition.default_grouped = grouped;
  }
  return partition;
}

size_t switch_dispatch_code_units(
    const instruction_lowering::CaseKeysExtentBuilder& keys,
    bool selector_live) {
  if (keys.empty()) {
    return 0;
  }
  if (keys.size() == 1) {
    const auto key = keys->first_key;
    if (key == 0) {
      // ReduceGotos turns a switch with one key, 0, into `if-eqz`.
      return opcode_code_units(OPCODE_IF_EQZ);
    }
    if (!selector_live && key == static_cast<int8_t>(key)) {
      // ...and one with another key it can subtract from a dead selector into
      // `rsub-int/lit8; if-eqz`.
      return opcode_code_units(OPCODE_RSUB_INT_LIT) +
             opcode_code_units(OPCODE_IF_EQZ);
    }
  }
  return opcode_code_units(OPCODE_SWITCH) +
         keys->estimate_switch_payload_code_units();
}

size_t host_dispatch_after(const SwitchPartition& partition,
                           HostSwitchEdit edit,
                           bool selector_live) {
  const bool deletes_grouped =
      host_switch_edge_edit(edit, /*into_taken_head=*/true,
                            /*is_default=*/false) == SwitchEdgeEdit::Delete;
  return switch_dispatch_code_units(
      deletes_grouped ? partition.kept : partition.all, selector_live);
}

ClosureNetTerms split_net_saving(const NetSavingInput& input,
                                 const Config& config,
                                 bool host_compiled) {
  // A suffix taking several cases deletes them from the host's switch, as it
  // takes the switch's edges into them.
  const auto edit =
      input.dispatch ? HostSwitchEdit::DeleteGrouped : HostSwitchEdit::None;
  // Code the launchpad adds to the host. It costs dex, and re-enters the
  // compiled code of a compiled host.
  size_t hot = 0;
  // Code that costs dex only: the split's metadata and the code its body
  // gains, the duplicated code, and the parts of a launchpad that are not
  // compiled code.
  const size_t return_units = opcode_code_units(OPCODE_RETURN);
  const size_t move_result = opcode_code_units(OPCODE_MOVE_RESULT);
  size_t dex_only = config.net_cu_method_metadata +
                    config.net_cu_load_param * input.passed_args +
                    input.recreated_defs + input.duplicated;
  const size_t spill =
      input.passed_arg_registers > kMaxNonRangeInvokeRegisters
          ? input.passed_arg_registers * config.net_cu_range_spill_per_reg
          : 0;
  hot += opcode_code_units(OPCODE_INVOKE_STATIC) + spill;
  hot +=
      return_units +
      (std::get<NetSavingInput::Suffix>(input.split).returns_value ? move_result
                                                                   : 0);
  // A split taking several cases of a switch starts with a copy of it over
  // the cases it takes. The host's switch sheds what the edit removes. It can
  // also grow, which counts as a negative shed: when the edit leaves the
  // selector live, a one-key switch cannot shrink to `rsub-int/lit8; if-eqz`.
  int64_t host_dispatch_shed = 0;
  if (input.dispatch) {
    const auto& partition = input.dispatch->partition;
    dex_only += switch_dispatch_code_units(
        partition.grouped, input.dispatch->selector_live_in_split);
    host_dispatch_shed =
        static_cast<int64_t>(
            host_dispatch_after(partition, HostSwitchEdit::None,
                                input.dispatch->selector_live_in_host_before)) -
        static_cast<int64_t>(host_dispatch_after(
            partition, edit, input.dispatch->selector_live_in_host_after));
  }
  // The shed counts as SAVED even though the host's switch is hot. It is
  // compiled code the host no longer holds, so the OAT shrinks by it, and no
  // code moves into the interpreter for it.
  const auto before = static_cast<int64_t>(input.compiled_copies);
  const auto after = input.copies_after
                         ? static_cast<int64_t>(input.copies_after->copies)
                         : before;
  const auto copies = std::min(before, after);
  // The copies the split removes, each of the whole host, and those it adds,
  // each of the host it leaves.
  int64_t removed = 0;
  int64_t added = 0;
  if (input.copies_after) {
    removed = (before - copies) *
              static_cast<int64_t>(input.copies_after->host_before);
    added = (after - copies) *
            static_cast<int64_t>(input.copies_after->host_after + hot);
  }
  const auto evicted = static_cast<int64_t>(input.evicted);
  const auto saved = host_compiled
                         ? copies * (evicted + host_dispatch_shed) + removed -
                               (input.split_compiled ? evicted : 0)
                         : int64_t{0};
  const auto added_ccuc =
      host_compiled ? copies * static_cast<int64_t>(hot) + added : int64_t{0};
  const auto dex_added =
      static_cast<int64_t>(hot + dex_only) - host_dispatch_shed;
  return ClosureNetTerms{.saved = saved,
                         .added_ccuc = added_ccuc,
                         .dex_added = dex_added,
                         .net = static_cast<double>(config.net_oat_weight) *
                                    static_cast<double>(saved - added_ccuc) -
                                static_cast<double>(dex_added)};
}

} // namespace method_splitting_impl
