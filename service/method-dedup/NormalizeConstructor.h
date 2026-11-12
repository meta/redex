/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

#include "PositionJoin.h"

/**
 * A simple constructor only initializes some or all of the instance fields with
 * the arguments and calls the super constructor. Normalize these constructors
 * and deduplicate the ones that have the same normal form. Also, reorder the
 * arguments of these constructors by their associated instance fields
 * order.
 *
 * Example:
 * void <init>(E e, B b, A a, D d, C c) {
 *   this.f1 = a;
 *   this.f3 = c;
 *   this.f4 = e;
 *   const x 5
 *   const y 10
 *   super.<init>(this, b, y, d, x);
 * }
 *
 * is logically equal to
 *
 * void <init>(A a, B b, C c, D d, E e) {
 *   this.f3 = c;
 *   this.f4 = e;
 *   this.f1 = a;
 *   const x 5
 *   const y 10
 *   super.<init>(this, b, y, d, x);
 * }
 *
 * Summarize the logic of simple constructors and use the information to
 * help dedup the constructors. It's especially useful when merging anonymous
 * classes together to dedup as many constructors as possible.
 */

class DexClass;

namespace method_dedup {

/**
 * Return the estimated code size reduction from constructor deduplication.
 */
uint32_t estimate_deduplicatable_ctor_code_size(const DexClass* cls);

/**
 * Deduplicate non-root constructors for each class and fix all the callsites.
 */
size_t dedup_constructors(const std::vector<DexClass*>& classes,
                          const std::vector<DexClass*>& scope,
                          positions::JoinStats* join_stats = nullptr);
} // namespace method_dedup
