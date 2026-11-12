/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <stdint.h>

#include "BaselineProfileConfig.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "MethodProfiles.h"

struct ConfigFiles;

namespace baseline_profiles {

struct MethodFlags {
  bool hot{false};
  bool startup{false};
  bool post_startup{false};
};

struct BaselineProfile {
  UnorderedMap<const DexMethod*, MethodFlags> methods;
  UnorderedSet<const DexClass*> classes;

  // For output purposes. DO NOT USE DIRECTLY.
  UnorderedSet<std::string> unmatched_classes;
  size_t mark{0};

  void load_classes(const Scope& scope,
                    const ConfigFiles& config,
                    const std::string& bp_name);

  void transitively_close_classes(const Scope& scope);
};

// Only "hot" methods are AOT-compiled by dex2oat; a <clinit> never is.
bool is_compiled(const DexMethod* method, const MethodFlags& flags);

bool is_compiled(const BaselineProfile& baseline_profile,
                 const DexMethod* method);

// Applies every method's forced H/S bits to this materialized profile,
// inserting entries as needed and preserving other flags. These bits encode a
// single whole-program structural decision and therefore are not conditional
// on the profile's existing membership. Class bits are serialized and merged
// but do not affect profiles. Returns the number of individual H/S bits that
// changed.
size_t apply_forced_method_flags(const Scope& scope, BaselineProfile* profile);

// The huge-method limit the build models dex2oat with,
// `dex2oat.huge_method_max` in the global config.
uint32_t get_huge_method_max(const ConfigFiles& conf);

// ART's default inline_max_code_units_ (art/compiler/driver/compiler_options.h,
// kDefaultInlineMaxCodeUnits). The optimizing compiler does not inline a
// callee with more code units.
constexpr uint32_t DEFAULT_ART_INLINE_MAX_CODE_UNITS = 32;

// Why dex2oat can never turn a profile entry into compiled code.
//
// Mirrors the gates in the `quick_fn` lambda of `CompileMethodQuick`,
// art/dex2oat/driver/compiler_driver.cc (android17-release), plus the one size
// gate inside the optimizing compiler. All but kHugeMethod are evaluated
// BEFORE the profile is consulted:
//   :455 IsUncompilableMethod -- NOT modelled, see below
//   :459 native    -> dex2oat emits a JNI stub for this unconditionally,
//                     whether or not the profile mentions it, so the entry buys
//                     nothing
//   :482 abstract  -> "Abstract methods don't have code."
//   :484 @NeverCompile
//   :490 <clinit>  -> compiled only under kEverything; app builds use
//                     speed-profile
// and then HGraphBuilder::SkipCompilation
// (art/compiler/optimizing/builder.cc) drops a method larger than
// huge_method_threshold_.
//
// Deliberately NOT modelled: VerificationResults::IsUncompilableMethod, which
// fires when ART's verifier reported VERIFY_ERROR_RUNTIME_THROW or
// VERIFY_ERROR_LOCKING, and class-wide for any class left at
// kRetryVerificationAtRuntime. Reproducing it would mean reproducing ART's
// verifier. It has not been observed to reject any entry of a real profile.
enum class UncompilableReason {
  kNone,
  kNoCode, // abstract or native
  kClinit,
  kNeverCompile,
  kHugeMethod,
};

// Code units in the sense of ART's `InsnsSizeInCodeUnits()`, i.e. what the
// size gates compare against. The CFG contributes branch widening, so a caller
// outside a pass that has not built it gets the unadjusted estimate.
uint32_t dex2oat_code_units(DexMethod* method);

// The code units UnreachableLoweringPass adds per `unreachable` instruction,
// which it replaces with a call of `createAndThrow` and its move-result.
uint32_t lowered_unreachable_extra_code_units();

// `dex2oat_code_units` for code that UnreachableLoweringPass has not lowered
// yet: what dex2oat sees once every `unreachable` is lowered.
uint32_t dex2oat_code_units_before_unreachable_lowering(DexMethod* method);

UncompilableReason uncompilable_reason(DexMethod* method,
                                       uint32_t huge_method_max);

// Whether the profile flags ask dex2oat to compile this entry:
//   IsHotMethod() || (!IsLowMemoryMode() && IsStartupMethod())
// (compiler_driver.cc ShouldCompileBasedOnProfile, android17-release). We model
// the non-low-memory device, which is what these profiles target; on a low-RAM
// device the startup term drops out and the true count is lower.
bool flags_request_compilation(const MethodFlags& flags);

struct TopOffSelection {
  // Which methods to add. The SET is deterministic; the order within it is
  // not, so a caller that writes these out has to sort them itself.
  std::vector<DexMethod*> methods;
  // Eligible pool before truncation to the requested count, so a shortfall can
  // be told apart from an exhausted pool.
  size_t candidates{0};
  // How many of `candidates` and of `methods` have a void return TYPE, at any
  // body size -- not only the one-code-unit bodies the padding is drawn from.
  // `methods_returning_void` below `methods.size()` means the ranking ran out
  // of void candidates and fell back to value-returning padding.
  size_t candidates_returning_void{0};
  size_t methods_returning_void{0};
  // Methods the caller's exclusion set kept out of the candidate pool.
  size_t excluded_candidates{0};
};

// Pick up to `count` methods to pad a baseline profile with, smallest first.
//
// Candidates are ranked on, in order: code units, then a void return ahead of
// a value return, then the narrower frame. This is simply a cheap approximation
// for choosing methods that are likely identical (or a few buckets of many
// methods that are identical).
//
// What is left is broken on the deobfuscated name rather than on DexMethod
// order, because this may run after renaming and obfuscated names are
// sequential ids that move whenever unrelated code changes.
//
// `candidate_scope` bounds what may be picked, and the caller must restrict it
// to classes that ship alongside the profile -- for an app bundle, the root
// store. A padding entry naming a module class cannot be resolved when the
// profile is converted to its binary form, so those classes are not considered.
//
// `excluded`, when given, names methods that must never be padded with even
// though they pass every gate above. Redex can decide a method is not worth
// compiling and drop it from a profile without marking it -- padding it back
// in would silently undo that decision.
TopOffSelection select_smallest_topoff_methods(
    const Scope& candidate_scope,
    const BaselineProfile& baseline_profile,
    size_t count,
    uint32_t huge_method_max,
    const UnorderedSet<const DexMethod*>* excluded = nullptr);

// Returns a tuple of BaselineProfile and UnorderedMap<std::string,
// BaselineProfile> The first is the default profile that will be fed into the
// baseline profile driver as a manual input. The second is a mapping of config
// name to final baseline profile for every baseline profile that redex is
// generating. Forced method flags are applied unless explicitly deferred.
std::tuple<BaselineProfile, UnorderedMap<std::string, BaselineProfile>>
get_baseline_profiles(
    const Scope& scope,
    const UnorderedMap<std::string, BaselineProfileConfig>& configs,
    const method_profiles::MethodProfiles& method_profiles,
    UnorderedSet<const DexMethodRef*>* method_refs_without_def = nullptr,
    bool apply_forced_flags = true);

BaselineProfile get_default_baseline_profile(
    const Scope& scope,
    const UnorderedMap<std::string, BaselineProfileConfig>& configs,
    const method_profiles::MethodProfiles& method_profiles,
    UnorderedSet<const DexMethodRef*>* method_refs_without_def = nullptr,
    bool apply_forced_flags = true);

} // namespace baseline_profiles
