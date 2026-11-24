/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "DexClass.h"

namespace method_fixup {

// Makes code, static field values and annotations stop referring to the
// vmethods that are keys of `removed_vmethods`, which the caller has deleted:
// invokes name the replacement that each maps to instead, and a method handle
// of a deleted vmethod names its descriptor through a new reference.
void fixup_references_to_removed_methods(
    const Scope& scope,
    UnorderedMap<DexMethodRef*, DexMethodRef*>& removed_vmethods);

} // namespace method_fixup
