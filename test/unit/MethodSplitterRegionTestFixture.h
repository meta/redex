/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

// Test-fixture helpers for the cold-region outlining feature in
// MethodSplittingPass. Provides builders that produce canonical CFG
// shapes (hot-cold-hot, multi-block hammock, etc.) so individual
// tests don't re-spell long S-expression bodies, and a few utility
// functions for running the splitter and collecting results.
//
// Vocabulary:
//   - hot / cold -- block hotness per source-block weights
//   - hammock -- single-entry single-exit cold subgraph
//   - rejoin -- the post-dominator block where execution rejoins the
//     hot path after the region invoke; must contain at least one
//     non-return instruction or `reduce_cfg` will merge it into the
//     cold predecessor
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

namespace method_splitting_region_test {

// Source-block weight strings used by the builders. Hot blocks get
// `kHotWeights` in their `.src_block` directive; cold blocks get
// `kColdWeights`.
inline constexpr std::string_view kHotWeights = "(1.0 1.0)";
inline constexpr std::string_view kColdWeights = "(0.0 0.0)";

// A non-return instruction suitable for placing first in a rejoin
// block to keep `reduce_cfg` from merging the rejoin into the cold
// predecessor. Returns a single S-expression instruction.
std::string nonMergeableRejoin();

// Build a cold-body S-expression of approximately `n_instrs`
// instructions using `sput` to distinct static fields on `LFoo;`.
// Each sput is 2 code units; tune `n_instrs` so the resulting cold
// body exceeds the net-model overhead floor (~35 code units) when net
// admission matters.
std::string coldBodySputs(size_t n_instrs);

// Build a single-block cold-body S-expression of approximately
// `n_instrs` instructions. Default kind is sput-chain.
enum class ColdBodyKind {
  kSputChain,
};
std::string coldBodyOfSize(size_t n_instrs,
                           ColdBodyKind kind = ColdBodyKind::kSputChain);

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

// Build a k-style cold body of `count` copies of `producer_sexpr`
// (a single instruction producing a value into `v0`). Used by k=1
// tests to vary the producer opcode (`add-int`, `move-object`, etc.).
std::string make_k_body(std::string_view producer_sexpr, size_t count);

// Default Config for region-splitter unit tests: enables region
// splitting and lowers `min_*_split_size` thresholds and raises
// `split_block_size` so test-sized CFGs aren't gated.
method_splitting_impl::Config regionTestConfig();

// One-call splitter invocation result; tests filter by `SplitKind`
// enum rather than by name substring (avoids the `$hot$` vs
// `$hot_cold$` overlap trap).
struct RegionResult {
  std::vector<DexMethod*> region_splits;
  std::vector<DexMethod*> suffix_splits;
  method_splitting_impl::StatsSnapshot stats;
};

// Construct a class with a single method `bar` from the given IR
// S-expression and signature, run `split_methods_in_stores` on it,
// and return the result by value.
RegionResult runRegionSplitter(
    std::string_view sig,
    std::string_view code_sexpr,
    const method_splitting_impl::Config& cfg = regionTestConfig(),
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
//    exactly as weak as the name comparison this replaced. Fixtures should
//    carry per-index-distinct markers (see `coldBodySputs`) for the signature
//    to discriminate placement.
std::string splitSignature(const RegionResult& res);

// Same two runs as runTwiceAndCompare, but returns both signatures so a failing
// test can print WHICH split moved instead of just "false".
std::pair<std::string, std::string> runTwiceAndSignatures(
    const std::function<RegionResult(std::string_view class_prefix)>&
        builder_fn);

// Run `runRegionSplitter` twice on equivalent fixtures and assert their
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
    const std::function<RegionResult(std::string_view class_prefix)>&
        builder_fn);

} // namespace method_splitting_region_test
