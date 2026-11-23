/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "DexClass.h"

namespace constant_propagation {
namespace definitely_assigned_ifields {
// Computes the set of ifields which have are guaranteed to have been written to
// before they are ever read. This method assumes that cfgs have been
// build, and exit-blocks calculated.
UnorderedSet<const DexField*> get_definitely_assigned_ifields(
    const Scope& scope);
} // namespace definitely_assigned_ifields
} // namespace constant_propagation
