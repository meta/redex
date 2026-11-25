/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "VirtualScopes.h"

struct ConfigFiles;

namespace class_merging {

/**
 * The methods the default baseline profile marks hot, identified the same way
 * as in MethodSplittingPass.
 */
UnorderedSet<const DexMethod*> get_hot_methods(const Scope& scope,
                                               ConfigFiles& conf);

/**
 * A mergeable is hot if any method that merging folds into a dispatch method
 * is in `hot_methods`: a constructor, or a virtual method other than the top
 * def of a non-interface, effectively final scope (those are relocated as they
 * are). A method that instantiates the mergeable through a relaxed init counts
 * like a constructor, as the inlined constructor body runs there.
 */
bool is_hot_mergeable(
    const DexClass* cls,
    const virtual_scope::VirtualScopes& vscopes,
    const UnorderedSet<const DexMethod*>& hot_methods,
    const std::vector<const DexMethod*>* relaxed_init_callers = nullptr);

} // namespace class_merging
