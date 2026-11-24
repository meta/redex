/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <array>

#include "DexClass.h"
#include "EnumUpcastAnalysis.h"
#include "Walkers.h"

namespace optimize_enums {

/**
 * We want to remove the generated static methods `SubEnum.valueOf()` and
 * `SubEnum.values()`. We cannot use `RemoveUnreachablePass` to remove them
 * because `Class.isEnum()` and `Class.getEnumConstants()` which use these
 * methods are commonly used in (de)serialization libraries so that we need
 * Proguard rule to keep these methods. There are two reasons why we wouldn't be
 * able to remove them.
 * 1. The method is called directly, e.g., `SubEnum.valueOf("ONE")`.
 * 2. The method is called reflectively, e.g., `Class.getDeclaredMethod("...")`
 *    and `Class.getEnumConstants()`.
 *
 * We can detect (2) by checking if the enum is ever upcasted to any type and if
 * it escapes a method so that it becomes hard to track. This could happen when
 * an upcasted enum is returned from a method, set to a class variable or array,
 * or passed as an argument to a method. We also need to check if the enum is
 * ever used as the type `java.lang.Class` by checking for
 * `Enum.getDeclaringClass()` and `const-class`.
 */
class EnumAnalyzeGeneratedMethods {
 public:
  EnumAnalyzeGeneratedMethods();

  /**
   * Adds the enum class and its generated methods to be considered for
   * optimization.
   */
  void consider_enum_type(DexType* type,
                          const DexMethod* valueof_method,
                          const DexMethod* values_method) {
    always_assert(!m_candidate_types.count(type));
    // TODO: Share `m_config` with `optimize_enums::replace_enum_with_int`
    m_config.candidate_enums.insert(type);
    m_candidate_methods.insert(valueof_method);
    m_candidate_methods.insert(values_method);
    m_candidate_types.insert(type);
  }

  /**
   * Returns the number of enum generated methods that are candidates for
   * deletion.
   */
  size_t num_candidate_enum_methods() { return m_candidate_methods.size(); }

  /**
   * Finds which of the generated methods of the considered enums are safe to
   * remove and removes them. Returns the number of methods that were removed.
   */
  size_t transform_code(const Scope& scope);

 private:
  Config m_config;
  // Method refs belong to one `RedexContext`, so each analysis makes its own.
  // They are made, not looked up, because the input need not reference them.
  const std::array<const DexMethodRef*, 7> m_allowlisted_methods;
  const DexMethodRef* m_get_declaring_class_method;
  const DexMethodRef* m_get_class_method;
  ConcurrentSet<const DexMethod*> m_candidate_methods;
  ConcurrentSet<const DexType*> m_candidate_types;

  void process_method(const EnumFixpointIterator& engine,
                      const cfg::ControlFlowGraph& cfg,
                      const DexMethod* method);

  void process_instruction(const IRInstruction* insn,
                           const EnumTypeEnvironment* env,
                           const DexMethod* method);

  void process_invocation(const IRInstruction* insn,
                          const EnumTypeEnvironment* env);

  // Keeps a generated method that is called, and with `valueOf` its whole
  // type.
  void keep_generated_method(const DexMethod* method);

  void keep_linked_generated_methods(const IRInstruction* insn);

  /**
   * Rejects an enum if it could be upcasted to some other type. Types in
   * `possible_types` could be upcasted to `expected_type`.
   */
  void reject_if_unsafe(const DexType* expected_type,
                        const EnumTypes& possible_types,
                        const IRInstruction* insn);
};
} // namespace optimize_enums
