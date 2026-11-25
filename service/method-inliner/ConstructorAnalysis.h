/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <vector>

#include "DeterministicContainers.h"

class DexField;
class DexMethod;
class DexType;
class DexClass;
class IRInstruction;

namespace constructor_analysis {

// Checks that...
// - there are no assignments to (non-inherited) instance fields before
//   a constructor call, and
// - the constructor refers to a method of the same class, and
// - there are no assignments to any final fields.
// Under these conditions, a constructor is universally inlinable.
bool can_inline_init(
    const DexMethod* init_method,
    const UnorderedSet<const DexField*>* finalizable_fields = nullptr,
    bool relaxed = false,
    UnorderedSet<DexField*>* written_final_fields = nullptr);

// Checks that the invocation of one constructor within another constructor
// of the same class can be inlined, either for a particular or for all
// callsites (when given callsite is nullptr).
// In particular, this checks that the relevant callsites invocations are
// with the this object as the receiver.
bool can_inline_inits_in_same_class(DexMethod* caller_method,
                                    const DexMethod* callee_method,
                                    IRInstruction* callsite_insn);

// A constructor invocation that initializes the object created by a
// new-instance instruction with a constructor that the instantiated type does
// not define. Relaxed init inlining (by Redex, or in the input dex of an
// application) produces them: after inlining `A.<init>` into its caller, the
// caller's `new-instance A` is initialized by `invoke-direct S.<init>`, where S
// is a super type of A.
struct RelaxedInit {
  IRInstruction* new_instance;
  IRInstruction* invoke;
  // The constructor the invocation resolves to; nullptr when it does not
  // resolve, for example when it names no constructor of its class.
  DexMethod* resolved_init;
};

// Finds the relaxed inits in the given method, which must have code with built
// CFG, whose new-instance type satisfies `is_relevant_type`, sorted by the CFG
// iteration order of the invocation, then of the new-instance.
std::vector<RelaxedInit> find_relaxed_inits(
    DexMethod* method,
    const std::function<bool(const DexType*)>& is_relevant_type);

} // namespace constructor_analysis
