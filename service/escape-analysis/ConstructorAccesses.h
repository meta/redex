/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "LocalPointersAnalysis.h"

namespace local_pointers {

// Whether an instruction's receiver is the object a constructor builds.
enum class Receiver : uint8_t {
  This,
  MaybeThis,
  Other,
};

struct FieldAccess {
  const DexField* field;
  Receiver receiver;
  // Whether `this` may have escaped before the access.
  bool after_escape;
};

// A call of a constructor of the class on `this`, as Java's this(...).
// It may store to any of the class's own fields, even when the callee keeps
// `this`. The class may not define the callee, which fails verification.
struct DelegatingCall {
  const DexMethodRef* callee;
  // `This` or `MaybeThis`.
  Receiver receiver;
  // Whether `this` may have escaped before the call.
  bool after_escape;
};

/*
 * How a constructor of `cls` uses the object it builds, `this`: which of its
 * accesses to the class's own instance fields have `this` as receiver, which
 * of its calls of a constructor of its class may receive `this`, and
 * where `this` may escape to code that can then change its fields at any later
 * point. Copies of `this` through moves and casts keep their
 * identity.
 *
 * Every call that receives `this` lets it escape, except a call of a
 * constructor that keeps its receiver: Object's constructor, and those in
 * `constructors_keeping_this`.
 *
 * The code of a constructor excluded from optimization may differ at runtime,
 * so no consumer credits it: it never keeps its receiver, and each of its
 * stores to a field of its class disqualifies that field as written only by
 * constructors.
 */
class ConstructorAccesses {
 public:
  ConstructorAccesses(
      const cfg::ControlFlowGraph& cfg,
      const DexClass* cls,
      const UnorderedSet<const DexMethod*>& constructors_keeping_this);

  // Field gets and puts, by instruction.
  const UnorderedMap<const IRInstruction*, FieldAccess>& field_accesses()
      const {
    return m_field_accesses;
  }

  // The call of a constructor of the class that `insn` makes and that may
  // receive `this`, or null.
  const DelegatingCall* get_delegating_call(const IRInstruction* insn) const {
    auto it = m_delegating_calls.find(insn);
    return it == m_delegating_calls.end() ? nullptr : &it->second;
  }

  // Whether `this` may have escaped once `insn` has run, but not before it on
  // the same block: `insn` lets `this` escape, or it starts a block that
  // `this` may enter already escaped, such as a loop whose body lets it
  // escape.
  bool is_escape(const IRInstruction* insn) const {
    return m_escapes.count(insn) != 0u;
  }

  // Whether the constructor keeps `this`: it lets `this` escape nowhere, and
  // through `this` it accesses only fields that its class declares or
  // inherits. A superclass constructor can reach a subclass's fields only by
  // casting `this` down. A field reference that does not resolve counts as
  // inherited when it names the class or one of its ancestors, since
  // resolution searches only upward from the class a reference names.
  bool keeps_this() const {
    return m_escapes.empty() && !m_accesses_other_fields;
  }

 private:
  UnorderedMap<const IRInstruction*, FieldAccess> m_field_accesses;
  UnorderedMap<const IRInstruction*, DelegatingCall> m_delegating_calls;
  UnorderedSet<const IRInstruction*> m_escapes;
  bool m_accesses_other_fields{false};
};

// How each constructor uses the object it builds, by constructor.
using ConstructorAccessesMap =
    UnorderedMap<const DexMethod*, std::unique_ptr<const ConstructorAccesses>>;

/*
 * Analyzes every constructor with code in `scope`, given the constructors that
 * keep their receiver. The constructors' CFGs must be built, as in a pass.
 */
ConstructorAccessesMap analyze_constructors(
    const Scope& scope,
    const UnorderedSet<const DexMethod*>& constructors_keeping_this);

/*
 * The constructors in `scope` that keep their receiver (see
 * `ConstructorAccesses::keeps_this`), given which of the constructors they
 * call keep it. Constructors outside `scope`, except Object's, and those
 * excluded from optimization do not.
 *
 * The whole-scope escape summaries of `analyze_scope` do not say which fields
 * a method accesses through a parameter, so they cannot answer this.
 *
 * TODO: Consider using the SummaryGenerator to analyze AOSP classes to find
 * other external constructors where this does not escape.
 */
UnorderedSet<const DexMethod*> get_constructors_keeping_this(
    const Scope& scope);

} // namespace local_pointers
