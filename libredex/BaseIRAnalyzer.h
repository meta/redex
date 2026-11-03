/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <sparta/MonotonicFixpointIterator.h>

#include "ControlFlow.h"
#include "IRInstruction.h"

namespace ir_analyzer {

template <typename Domain>
class BaseIRAnalyzer
    : public sparta::MonotonicFixpointIterator<cfg::GraphInterface, Domain> {
 public:
  using NodeId = cfg::Block*;

  explicit BaseIRAnalyzer(const cfg::ControlFlowGraph& cfg)
      : sparta::MonotonicFixpointIterator<cfg::GraphInterface, Domain>(
            cfg, cfg.num_blocks()) {}

  void analyze_node(const NodeId& node, Domain* current_state) const override {
    for (auto& mie : ir_list::InstructionIterable(node)) {
      analyze_instruction(mie.insn, current_state);
    }
  }

  Domain analyze_edge(const cfg::GraphInterface::EdgeId&,
                      const Domain& exit_state_at_source) const override {
    return exit_state_at_source;
  }

  virtual void analyze_instruction(const IRInstruction* insn,
                                   Domain* current_state) const = 0;
};

template <typename Domain>
class BaseEdgeAwareIRAnalyzer
    : public sparta::MonotonicFixpointIterator<cfg::GraphInterface, Domain> {
 public:
  using NodeId = cfg::Block*;

  explicit BaseEdgeAwareIRAnalyzer(const cfg::ControlFlowGraph& cfg)
      : sparta::MonotonicFixpointIterator<cfg::GraphInterface, Domain>(
            cfg, cfg.num_blocks()) {}

  void analyze_node(const NodeId& node, Domain* state_at_entry) const override {
    auto last_insn = node->get_last_insn();
    for (auto& mie : ir_list::InstructionIterable(node)) {
      auto* insn = mie.insn;
      analyze_instruction(insn, state_at_entry, insn == last_insn->insn);
    }
  }

  Domain analyze_edge(const cfg::GraphInterface::EdgeId& edge,
                      const Domain& exit_state_at_source) const override {
    auto last_insn_it = edge->src()->get_last_insn();
    if (last_insn_it == edge->src()->end()) {
      return exit_state_at_source;
    }

    auto env = exit_state_at_source;
    auto* insn = last_insn_it->insn;
    auto op = insn->opcode();
    if (opcode::is_a_conditional_branch(op)) {
      analyze_if(insn, edge, &env);
    } else if (opcode::is_switch(op)) {
      analyze_switch(insn, edge, &env);
    } else if (edge->type() == cfg::EDGE_THROW) {
      analyze_throw(insn, edge, &env);
    } else {
      analyze_no_throw(insn, &env);
    }

    return env;
  }

  void analyze_instruction(const IRInstruction* insn,
                           Domain* current_state,
                           bool is_last) const {
    analyze_instruction_normal(insn, current_state);
    if (!is_last) {
      analyze_no_throw(insn, current_state);
    }
  }

 protected:
  // Analyze the "normal" aspect of an instruction (not knowing whether it will
  // throw or not).
  virtual void analyze_instruction_normal(const IRInstruction* insn,
                                          Domain* current_state) const = 0;

  // After the normal instruction analysis, if an execution path is taken where
  // the instruction will throw, analyze the throwing continuation of the
  // instruction.
  virtual void analyze_throw(const IRInstruction* /*insn*/,
                             const cfg::GraphInterface::EdgeId& /*edge*/,
                             Domain* /*current_state*/) const {}

  // After the normal instruction analysis, if an execution path is taken where
  // the instruction will not throw, analyze the not-throwing continuation of
  // the instruction.
  virtual void analyze_no_throw(const IRInstruction* /*insn*/,
                                Domain* /*current_state*/) const {}

  // When a block ends with an if-instruction, analyze the case where a
  // particular edge is taken.
  virtual void analyze_if(const IRInstruction* /*insn*/,
                          const cfg::GraphInterface::EdgeId& /*edge*/,
                          Domain* /*current_state*/) const {}

  // When a block ends with a switch-instruction, analyze the case where a
  // particular edge is taken.
  virtual void analyze_switch(const IRInstruction* /*insn*/,
                              const cfg::GraphInterface::EdgeId& /*edge*/,
                              Domain* /*current_state*/) const {}
};

// Base for backward IR dataflow analyses (e.g. liveness). The iteration is
// rooted at the method's EXIT, i.e. cfg.exit_block().
//
// PRECONDITION: the caller must have computed the exit block via
// cfg.calculate_exit_block() (the exit block is NOT computed on CFG
// construction — see ControlFlow.h). Constructing/running a backward analysis
// on a CFG whose exit block is null dereferences null and crashes. Most callers
// get this for free because an earlier transform already called
// calculate_exit_block(); a caller operating on a freshly built CFG must call
// it explicitly first.
template <typename Domain>
class BaseBackwardsIRAnalyzer
    : public sparta::MonotonicFixpointIterator<
          sparta::BackwardsFixpointIterationAdaptor<cfg::GraphInterface>,
          Domain> {
 public:
  using NodeId = cfg::Block*;

  explicit BaseBackwardsIRAnalyzer(const cfg::ControlFlowGraph& cfg)
      : sparta::MonotonicFixpointIterator<
            sparta::BackwardsFixpointIterationAdaptor<cfg::GraphInterface>,
            Domain>(cfg, cfg.num_blocks()) {}

  void analyze_node(const NodeId& node, Domain* current_state) const override {
    for (auto& mie : InstructionIterable(node).reversed()) {
      analyze_instruction(mie.insn, current_state);
    }
  }

  Domain analyze_edge(const cfg::GraphInterface::EdgeId&,
                      const Domain& exit_state_at_source) const override {
    return exit_state_at_source;
  }

  virtual void analyze_instruction(IRInstruction* insn,
                                   Domain* current_state) const = 0;
};

} // namespace ir_analyzer
