/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

// Test-fixture helpers for MethodSplittingPass. Provides builders that produce
// canonical CFG shapes (hot-cold-hot, multi-block hammock, etc.) so individual
// tests don't re-spell long S-expression bodies, and a few utility
// functions for running the splitter and collecting results.
//
// Vocabulary:
//   - hot / cold -- block hotness per source-block weights
//   - hammock -- single-entry single-exit cold subgraph
//   - rejoin -- the post-dominator block where execution rejoins the
//     hot path after the region invoke; must contain at least one
//     non-return instruction or `normalize_cfg_for_splitting` will merge
//     it into the cold predecessor
//   - k -- number of live-out registers from the region body
//

// This header MUST NOT include `RedexTest.h` -- that header transitively
// defines a non-inline global which causes duplicate-symbol linker
// errors when two `.cpp` files in the same `redex_test` target both
// pull it in.

#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "DexClass.h"
#include "DexStore.h"
#include "MethodSplitter.h"
#include "MethodSplittingConfig.h"

namespace method_splitting_test {

// Source-block weight strings used by the builders. Hot blocks get
// `kHotWeights` in their `.src_block` directive; cold blocks get
// `kColdWeights`.
inline constexpr std::string_view kHotWeights = "(1.0 1.0)";
inline constexpr std::string_view kColdWeights = "(0.0 0.0)";

// A non-return instruction suitable for placing first in a rejoin
// block to keep `normalize_cfg_for_splitting` from merging the rejoin into
// the cold predecessor. Returns a single S-expression instruction.
std::string nonMergeableRejoin();

// Build a chain of `n_instrs` `sput` instructions to distinct static
// fields on `LFoo;`, each 2 code units. Block hotness comes from the
// enclosing `.src_block`, not from this chain, so the same primitive
// serves hot filler and cold bodies alike. `field_prefix` keeps two
// chains in one method writing distinct fields.
//
// Names are exactly `<field_prefix>_<i>`, with nothing else in the name, so
// `countFieldRefs` with that prefix counts this chain and no other.
std::string sputChain(size_t n_instrs, std::string_view field_prefix = "f");

// A `sput` to a static int field is 2 code units.
inline constexpr size_t kSputCodeUnits = 2;

// Build a hot-cold-hot CFG template: hot prefix -> if-eqz -> (cold body
// | hot rejoin) -> return-void. The cold body is exactly `cold_body`
// (an S-expression of instructions); the rejoin contains a
// `nonMergeableRejoin()` instruction before the return.
//
// `sig` is the method signature (e.g. `"(I)V"`); the cold body must
// be consistent with it (the default fixtures use `v0` as the
// if-eqz reg).
//
// The method reference inside each emitted `.src_block` is the fixed
// placeholder `LFoo;.bar:<sig>`, which does NOT name the class the method ends
// up on: `make_test_class` appends a uniquifying counter (`LFoo0;`, `LDetA1;`),
// so the two never match. That is sound only because nothing in the splitter
// reads `SourceBlock::src` -- it reads the vals. If a consumer ever keys on the
// method reference (grouping, dedup, profile derivation), these builders must
// take the resolved class name instead of hardcoding it.
std::string hotColdHotCfg(std::string_view cold_body,
                          std::string_view sig = "(I)V");

// Build a 3-block hammock: entry branches to one of two cold body
// blocks, both rejoin at a hot block.
std::string multiBlockHammockCfg(std::string_view body_a,
                                 std::string_view body_b,
                                 std::string_view body_c);

// Count instructions reachable from the entry of `m` that reference a field
// named `<marker>_<i>`, to tell which emitted method a `sputChain` body ended
// up in.
//
// `marker` must be exactly the `field_prefix` the chain was built with: the
// name must continue with `_`, so the marker `bd` does not count the chains
// `bd1` to `bd4`. A marker that names no chain counts 0, which an
// `EXPECT_EQ(count, 0u)` cannot tell from a correct placement, so pair such a
// check with a positive count of the same chain elsewhere. A chain built with
// the empty prefix is uncounted padding by convention: its names `_<i>` match
// only the empty marker.
//
// Only reachable instructions count: a split is built by deep-copying the
// host, so blocks outside the split survive in its CFG, unreachable, until a
// later `simplify()` drops them.
size_t countFieldRefs(DexMethod* m, std::string_view marker);

// Default Config for splitter unit tests: lowers the `min_*` size thresholds
// and raises `split_block_size` so test-sized CFGs aren't gated. Thresholds
// only; every capability stays at its C++ default.
method_splitting_impl::Config splitterTestConfig();

// `splitterTestConfig()` with region splitting enabled.
method_splitting_impl::Config regionTestConfig();

// One-call splitter invocation result; tests filter by `SplitKind`
// enum rather than by name substring (avoids the `$hot$` vs
// `$hot_cold$` overlap trap).
struct SplitResult {
  std::vector<DexMethod*> region_splits;
  std::vector<DexMethod*> suffix_splits;
  method_splitting_impl::StatsSnapshot stats;
};

// Construct a class with a single method `bar` from the given IR
// S-expression and signature, run `split_methods_in_stores` on it,
// and return the result by value.
SplitResult runSplitter(
    std::string_view sig,
    std::string_view code_sexpr,
    const method_splitting_impl::Config& cfg = splitterTestConfig(),
    std::string_view class_prefix = "LFoo");

// The field markers a split can reach, sorted. This is the part of
// `splitSignature` that discriminates WHERE a split landed.
std::vector<std::string> reachableFieldNames(DexMethod* m);

// Structural fingerprint of a run: kind, split name, and the sorted field
// markers each split can reach. Two runs that split the same shape in different
// PLACES differ here even when their split names match.
//
// Two limits a caller must know, because the comparison is only as strong as
// the signature it is given:
//  - a run that produced NO splits has the empty signature, so comparing two
//    such runs is trivially equal. A fixture that can legitimately split
//    nothing must assert that separately; equality here is not evidence.
//  - splits that reach no field markers contribute name-only entries, which is
//    no stronger than comparing split names. Fixtures should
//    carry per-index-distinct markers for the signature to discriminate
//    placement -- built with `sputChain` under a prefix of their own, NOT with
//    the empty prefix, whose names are padding `countFieldRefs` does not
//    count.
std::string splitSignature(const SplitResult& res);

// Same two runs as runTwiceAndCompare, but returns both signatures so a failing
// test can print WHICH split moved instead of just "false".
std::pair<std::string, std::string> runTwiceAndSignatures(
    const std::function<SplitResult(std::string_view class_prefix)>&
        builder_fn);

// Run `runSplitter` twice on equivalent fixtures and assert their
// `splitSignature`s match, so a run that splits the same shape in different
// PLACES is caught and not just one that renames a split. The test passes a
// builder that produces a run for a given class-name prefix, and the two
// prefixes must differ because the DexType registry is process-global.
//
// Returns true on match, false on divergence; the test should EXPECT_TRUE on
// the result with a message naming the suspect determinism subsystems
// (closure ordering, dedup-by-covered, name uniquifier). Use
// `runTwiceAndSignatures` instead when the failure message should say WHICH
// split moved.
bool runTwiceAndCompare(
    const std::function<SplitResult(std::string_view class_prefix)>&
        builder_fn);

} // namespace method_splitting_test
