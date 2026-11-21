/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRInstruction.h"

namespace uninitialized_objects {

using UninitializedObjectDomain = sparta::ConstantAbstractDomain<bool>;

using UninitializedObjectEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t,
                                               UninitializedObjectDomain>;

using UninitializedObjectEnvironments =
    UnorderedMap<const IRInstruction*, UninitializedObjectEnvironment>;

// The objects whose initialization the analysis tracks. Untracked objects count
// as initialized.
enum class TrackedObjects {
  // Every object created by a `new-instance`, and a constructor's receiver.
  All,
  // Only a constructor's receiver.
  ConstructorReceiver,
};

// For each instruction, and each incoming register, determine if it may contain
// an uninitialized object, i.e. one that was created or passed in via the
// receiver argument of a constructor, and no invoke-direct to a constructor
// happened yet.
UninitializedObjectEnvironments get_uninitialized_object_environments(
    DexMethod* method, TrackedObjects tracked = TrackedObjects::All);

} // namespace uninitialized_objects
