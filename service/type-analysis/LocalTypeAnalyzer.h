/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "BaseIRAnalyzer.h"
#include "ConstructorAccesses.h"
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

// The state of CtorFieldAnalyzer.
struct CtorFields {
  CtorFields(const local_pointers::ConstructorAccesses* accesses,
             const UnorderedSet<const DexField*>& constructor_only_fields)
      : accesses(accesses), constructor_only_fields(&constructor_only_fields) {}

  // How the constructor uses `this`; null when not analyzing a constructor.
  const local_pointers::ConstructorAccesses* accesses;
  // Fields that only constructors of their class write, and only through
  // `this`.
  const UnorderedSet<const DexField*>* constructor_only_fields;
};

/*
 * Similarly CtorFieldAnalyzer populates local FieldTypeEnvironment when
 * analyzing a ctor. We only do so for instance fields that belong to the class
 * the ctor is under. When collecting the WholeProgramState, we first collect
 * the end state of the FieldTypeEnvironment for all ctors. We use that as the
 * initial type mapping for all instance fields.
 *
 * Only a store whose receiver is `this` sets a field's type, and a store that
 * may or may not target `this` widens it; a store to another instance of the
 * class leaves it alone. A read is answered from these stores only while
 * `this` cannot have escaped, since code that sees `this` may store to its
 * fields, unless no code but the class's constructors writes the field. A call
 * of another constructor of the class on `this` may store to them too, so it
 * forgets them.
 */
class CtorFieldAnalyzer final
    : public InstructionAnalyzerBase<CtorFieldAnalyzer,
                                     DexTypeEnvironment,
                                     CtorFields> {
 public:
  static bool analyze_iget(const State& state,
                           const IRInstruction* insn,
                           DexTypeEnvironment* env);

  static bool analyze_iput(const State& state,
                           const IRInstruction* insn,
                           DexTypeEnvironment* env);

  static bool analyze_invoke(const State& state,
                             const IRInstruction* insn,
                             DexTypeEnvironment* env);
};

} // namespace local

} // namespace type_analyzer
