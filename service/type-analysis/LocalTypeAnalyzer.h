/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "BaseIRAnalyzer.h"
#include "DexTypeEnvironment.h"
#include "InstructionAnalyzer.h"

namespace type_analyzer {

namespace local {

using namespace ir_analyzer;

class LocalTypeAnalyzer final
    : public ir_analyzer::BaseIRAnalyzer<DexTypeEnvironment> {
 public:
  LocalTypeAnalyzer(const cfg::ControlFlowGraph& cfg,
                    InstructionAnalyzer<DexTypeEnvironment> insn_analyer)
      : ir_analyzer::BaseIRAnalyzer<DexTypeEnvironment>(cfg),
        m_insn_analyzer(std::move(insn_analyer)) {}

  void analyze_instruction(const IRInstruction* insn,
                           DexTypeEnvironment* env) const override;

 private:
  InstructionAnalyzer<DexTypeEnvironment> m_insn_analyzer;
};

class RegisterTypeAnalyzer final
    : public InstructionAnalyzerBase<RegisterTypeAnalyzer, DexTypeEnvironment> {
 public:
  static bool analyze_default(const IRInstruction* insn,
                              DexTypeEnvironment* env);

  static bool analyze_check_cast(const IRInstruction* insn,
                                 DexTypeEnvironment* env);

  static bool analyze_const(const IRInstruction* insn, DexTypeEnvironment* env);

  static bool analyze_const_string(const IRInstruction*,
                                   DexTypeEnvironment* env);

  static bool analyze_const_class(const IRInstruction*,
                                  DexTypeEnvironment* env);

  static bool analyze_aget(const IRInstruction* insn, DexTypeEnvironment* env);

  static bool analyze_move(const IRInstruction* insn, DexTypeEnvironment* env);

  static bool analyze_move_result(const IRInstruction* insn,
                                  DexTypeEnvironment* env);

  static bool analyze_move_exception(const IRInstruction* insn,
                                     DexTypeEnvironment* env);

  static bool analyze_new_instance(const IRInstruction* insn,
                                   DexTypeEnvironment* env);

  static bool analyze_new_array(const IRInstruction* insn,
                                DexTypeEnvironment* env);

  static bool analyze_filled_new_array(const IRInstruction* insn,
                                       DexTypeEnvironment* env);

  static bool analyze_invoke(const IRInstruction* insn,
                             DexTypeEnvironment* env);
};

/*
 * Similarly CtorFieldAnalyzer populates local FieldTypeEnvironment when
 * analyzing a ctor. We only do so for instance fields that belong to the class
 * the ctor is under. When collecting the WholeProgramState, we first collect
 * the end state of the FieldTypeEnvironment for all ctors. We use that as the
 * initial type mapping for all instance fields.
 *
 * Note that we only update Field type mapping for operations on `this` obj. We
 * do not want to collect field type update on another instance of the same
 * class. That's not correct. As a result, we might incorrectly initialize the
 * nullness of a field without the instance tracking.
 */
struct CtorFields {
  explicit CtorFields(const DexType* class_under_init)
      : class_under_init(class_under_init) {}

  // The class whose constructor is analyzed; null when not analyzing a
  // constructor.
  const DexType* class_under_init;
};

class CtorFieldAnalyzer final
    : public InstructionAnalyzerBase<CtorFieldAnalyzer,
                                     DexTypeEnvironment,
                                     CtorFields> {
 public:
  static bool analyze_default(const State& state,
                              const IRInstruction* insn,
                              DexTypeEnvironment* env);
  static bool analyze_load_param(const State& state,
                                 const IRInstruction* insn,
                                 DexTypeEnvironment* env);
  static bool analyze_iget(const State& state,
                           const IRInstruction* insn,
                           DexTypeEnvironment* env);

  static bool analyze_iput(const State& state,
                           const IRInstruction* insn,
                           DexTypeEnvironment* env);

  static bool analyze_move(const State& state,
                           const IRInstruction* insn,
                           DexTypeEnvironment* env);

  static bool analyze_move_result(const State& state,
                                  const IRInstruction* insn,
                                  DexTypeEnvironment* env);

  static bool analyze_invoke(const State& state,
                             const IRInstruction* insn,
                             DexTypeEnvironment* env);
};

} // namespace local

} // namespace type_analyzer
