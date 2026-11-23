/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConstantPropagationWholeProgramState.h"
#include "ConstructorAccesses.h"

namespace constant_propagation {

// The instance fields that only constructors of their own class write, none
// of them excluded from optimization, whatever object they write them on.
// Static, external, volatile and kept fields are not included. A field's stores
// then all come from code that runs while some object of its class is under
// construction, which is what an aggregation of every store in the program
// needs.
UnorderedSet<const DexField*> gather_ifields_written_only_by_constructors(
    const Scope& scope);

// The fields of gather_ifields_written_only_by_constructors that those
// constructors write only through the object under construction. No other code
// can change them, so a constructor still knows their values after `this`
// escapes, and their values in a constructor are the values of the object it
// constructs.
// `constructor_accesses` holds every constructor with code in `scope`; only
// the receivers of its stores matter, which do not depend on which
// constructors keep `this`.
UnorderedSet<const DexField*> gather_constructor_only_ifields(
    const Scope& scope,
    const local_pointers::ConstructorAccessesMap& constructor_accesses);

// The fields of `candidate_ifields`, one of the sets above, whose values after
// construction may be inferred from the constructors and used wherever they are
// read: final fields, and non-final fields of classes with one constructor. Of
// the fields of a class with one constructor, it leaves out those that a method
// the constructor calls on `this` may read, and all of them if the constructor
// stores `this` into the heap.
EligibleIfields gather_safely_inferable_ifield_candidates(
    const Scope& scope,
    const UnorderedSet<const DexField*>& candidate_ifields,
    const UnorderedSet<std::string>& allowlist_method_names);

} // namespace constant_propagation
