/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <limits>

#include "IRList.h"

class DexMethod;

namespace source_blocks {

// The smallest strictly-positive `val` the count pipeline manufactures or
// preserves: the smallest NORMAL float, so that arithmetic which keeps a value
// positive in exact math also keeps it positive in float. Deliberately not
// denorm_min(), which FTZ/DAZ builds may flush to zero and thus fail to guard.
//
// Two places need this bound, and each used to hard-code 1e-3 with the same
// rationale: SyntheticBlockCountsPass's `epsilon` (the floor for a covered
// block whose solved frequency underflowed) and the post-scaling guard in
// source_blocks::normalize. Sharing one constant is the point -- when the
// rationale changed, only one of the two copies would otherwise get updated.
//
// That rationale was "dominate every configured non-zero val threshold, so a
// synthesized or scaled count can never flip a supported block below one". It
// no longer binds: the only such threshold is
// PerfMethodInlinePass.min_block_hits (1e-8, facebook/config/fb4a.refig.inc),
// and that pass is disabled everywhere (facebook/config-lib/module_core.refig,
// "No DS support, on ice"); the other threshold it named, block_profiles_hits,
// is 0.0 in every config, which any positive val clears. Meanwhile 1e-3 is a
// large distortion once vals carry counts -- it fires on ordinary cold blocks
// and pins them orders of magnitude above their true count.
//
// If PerfMethodInlinePass is re-enabled with a non-zero min_block_hits, this
// bound must be revisited.
//
// The smallest positive normal float is what is wanted here, so `min()` is
// correct and `lowest()` -- what the lint rule assumes is meant -- would be the
// bug: it is the most negative float, and a negative floor would let a count go
// below zero.
// NOLINTNEXTLINE(facebook-hte-FloatingPointMin)
constexpr float kMinPositiveCount = std::numeric_limits<float>::min();

std::unique_ptr<SourceBlock> clone_as_synthetic(SourceBlock* sb,
                                                const DexMethod* ref,
                                                const SourceBlock::Val& val);

std::unique_ptr<SourceBlock> clone_as_synthetic(
    SourceBlock* sb,
    const DexMethod* ref = nullptr,
    const std::optional<SourceBlock::Val>& opt_val = std::nullopt);

std::unique_ptr<SourceBlock> clone_as_synthetic(
    SourceBlock* sb,
    const DexMethod* ref,
    const std::vector<SourceBlock*>& many);

// Like the `many` overload above, but SUMS the inputs' `val` instead of maxing
// (appear100 still maxes). Use for an N:1 OUTLINE where a body shared by N call
// sites runs about the sum of those sites' counts; use the `max` overload only
// when stamping a single representative onto many blocks (TEMPLATE-CLONE).
std::unique_ptr<SourceBlock> clone_as_synthetic_summing(
    SourceBlock* sb,
    const DexMethod* ref,
    const std::vector<SourceBlock*>& many);

// Gives `method`, a method created to serve several call sites, synthetic
// source blocks whose counts are the sum of the given call sites' source
// blocks: it runs once for each time one of those sites runs. Does nothing when
// `call_site_source_blocks` is empty.
void insert_source_blocks_summing_call_sites(
    DexMethod* method,
    const std::vector<SourceBlock*>& call_site_source_blocks);

} // namespace source_blocks
