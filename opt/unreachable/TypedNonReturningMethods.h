/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>

#include "BaselineProfile.h"
#include "DexClass.h"
#include "DexStore.h"

/*
 * Types non-returning static methods in place.
 *
 * A call to a method that cannot return normally is followed by an
 * `unreachable` / `throw` pair, which lowering would otherwise turn into a
 * second call:
 *
 *   invoke-static {v0} LA;.fail:(I)V
 *   unreachable v1
 *   throw v1
 *
 * If the method has no return instruction, it verifies with any declared
 * return type. Its return type is changed in place to the exception type that
 * lowering throws for unreachable code, `com.redex.UnreachableException`,
 * leaving its body, name, class and access flags as they are, and the
 * `unreachable` becomes the result of the call it follows:
 *
 *   invoke-static {v0} LA;.fail:(I)Lcom/redex/UnreachableException;
 *   move-result-object v1
 *   throw v1
 *
 * The call still throws before it could return, so the result is never read
 * at runtime. Callers that ignore the result keep their instruction.
 *
 * ART cuts off the code after a call it knows always throws, but keeps a
 * `throw` that directly follows it, so in a compiled caller the typed site
 * costs more native code than the second call. A site is therefore only
 * converted if dex2oat does not compile its caller according to the baseline
 * profile, or if the call is covered by a handler, where ART keeps the code
 * after the call either way. Other call sites of a typed method ignore its
 * result and are lowered as before.
 *
 * A method qualifies if it is a static, non-native method with code returning
 * void that can be renamed and deleted, whose class is internal and neither
 * referenced by string nor serialized, and whose code has no return
 * instruction. All references to it must be instructions in methods without
 * `no_optimizations`; references from call sites, method handles, annotations
 * or static values reject it, as does a method or method reference with the
 * new signature on its class. It is selected only if the bytes its converted
 * call sites save outweigh the proto entries its new signature adds to the
 * dexes that reference it.
 *
 * Method references are assumed to be resolved to their definitions, as
 * `ResolveRefsPass` leaves them (`NoResolvablePureRefs`): a reference such as
 * `invoke-static Sub.fail()V` to a typed `Base.fail` would no longer resolve.
 * Nothing here enforces this. In configs that run `ResolveRefsPass`, every pass
 * from there up to UnreachableLoweringPass declares that it preserves the
 * property, so with `check_properties_deep`, its checker keeps asserting after
 * each pass that every method and field reference in an instruction is the
 * definition the resolver finds for it, where it finds one. Configs without
 * `ResolveRefsPass` must leave this option off.
 *
 * All decisions are made before anything is changed.
 */
namespace typed_nonreturning_methods {

struct Stats {
  size_t candidate_methods{0};
  size_t rejected_methods{0};
  size_t unprofitable_methods{0};
  size_t typed_methods{0};
  size_t typed_call_sites{0};
  // Matched call sites left alone because their caller is compiled and the
  // call is not covered by a handler.
  size_t compiled_call_sites{0};
};

// Types the qualifying methods referenced from `stores`, whose classes are
// `scope`, with `result_type` as their return type and rewrites their
// convertible call sites, where `baseline_profile` and `huge_method_max` tell
// which callers dex2oat compiles. `result_type` must be a throwable class. Must
// run after every pass that could change the matched call sites or cut off
// control flow after a call. ArtProfileWriterPass.topoff_target_entries, an
// option of that pass, can still pad the written profile with small methods,
// where a converted site costs native code.
Stats type_nonreturning_methods(
    const DexStoresVector& stores,
    const Scope& scope,
    DexType* result_type,
    const baseline_profiles::BaselineProfile& baseline_profile,
    uint32_t huge_method_max);

} // namespace typed_nonreturning_methods
