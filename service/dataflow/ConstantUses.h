/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "TypeInference.h"
#include <functional>

namespace constant_uses {

enum TypeDemand : uint8_t {
  Error = 0x00,
  Int = 0x01,
  Float = 0x02,
  Long = 0x04,
  Double = 0x08,
  Object = 0x10,

  IntOrFloat = Int | Float,
  IntOrObject = Int | Object,
  LongOrDouble = Long | Double,
  None = (TypeDemand)(~0)
};

class ConstantUses {
 public:
  ConstantUses(const cfg::ControlFlowGraph& cfg,
               DexMethod* method,
               bool force_type_inference = false);
  ConstantUses(const cfg::ControlFlowGraph& cfg,
               bool is_static,
               DexType* declaring_type,
               DexType* rtype,
               DexTypeList* args,
               const std::function<std::string()>& method_describer,
               bool force_type_inference = false);

  // Given a const or const-wide instruction, retrieve all instructions that
  // use it.
  const std::vector<std::pair<IRInstruction*, size_t>>& get_constant_uses(
      IRInstruction*) const;

  // Given a const or const-wide instruction, compute the combination type
  // demand across all execution paths.
  TypeDemand get_constant_type_demand(IRInstruction*) const;

  // Given a const or const-wide instruction, whether every use would also
  // accept any other int value in its place, such as a parameter or the result
  // of an int computation. TypeDemand::Int alone does not say that: it
  // includes boolean, byte, char and short consumers, which a constant can
  // satisfy but an arbitrary int cannot, even when it holds the same value.
  bool accepts_any_int(IRInstruction*) const;

  // Whether type inference information was required to be computed.
  bool has_type_inference() const;

  // Whether type inference information was required to be computed.
  const type_inference::TypeInference* get_type_inference() const {
    return m_type_inference.get();
  }

 private:
  static TypeDemand get_type_demand(const DexType* type);
  TypeDemand get_type_demand(IRInstruction* insn, size_t src_index) const;
  // The type that `insn` declares for its operand `src_index`, such as a
  // parameter, field, return or array element type; nullptr if it declares
  // none.
  const DexType* get_declared_type(IRInstruction* insn, size_t src_index) const;

  mutable std::unique_ptr<type_inference::TypeInference> m_type_inference;
  UnorderedMap<IRInstruction*, std::vector<std::pair<IRInstruction*, size_t>>>
      m_constant_uses;
  std::vector<std::pair<IRInstruction*, size_t>> m_no_uses;
  DexType* m_rtype;
};

} // namespace constant_uses
