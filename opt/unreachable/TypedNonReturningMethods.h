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
#include "MethodProfiles.h"

/*
 * Types non-returning static methods.
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
 * instruction, and if its class has no method or method reference with the
 * new signature. It is selected only if the bytes its converted call sites
 * save outweigh the proto entries its new signature adds to the dexes that
 * reference it.
 *
 * Instructions in methods without `no_optimizations` reference the typed
 * method. Other references -- from annotations, static values, method handles
 * and call sites, or instructions in `no_optimizations` methods -- must keep
 * the original signature. If there are any, the body moves to a new method of
 * the same class with the same name and access flags and the new signature,
 * and the original becomes a stub that calls it:
 *
 *   LA;.fail:(I)V:
 *     invoke-static {p0} LA;.fail:(I)Lcom/redex/UnreachableException;
 *     return-void
 *
 * The stub's code and the second method reference, in the defining dex and in
 * each dex that references both signatures, are part of the cost, and each of
 * those dexes must have room for the reference.
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
  // Profitable methods left alone because a dex has no room for the method
  // reference that keeping the original signature adds.
  size_t no_method_ref_room_methods{0};
  size_t typed_methods{0};
  // Typed methods whose original signature stays as a stub.
  size_t stub_methods{0};
  size_t typed_call_sites{0};
  // Matched call sites left alone because their caller is compiled and the
  // call is not covered by a handler.
  size_t compiled_call_sites{0};
};

// Types the qualifying methods referenced from `stores`, whose classes are
// `scope`, with `result_type` as their return type and rewrites their
// convertible call sites, where `baseline_profile` and `huge_method_max` tell
// which callers dex2oat compiles. `result_type` must be a throwable class.
// `reserved_mrefs` method references stay free in every dex, and a typed
// method split off a stub gets the stub's `method_profiles` stats. Must run
// after every pass that could change the matched call sites or cut off control
// flow after a call. ArtProfileWriterPass.topoff_target_entries, an option of
// that pass, can still pad the written profile with small methods, where a
// converted site costs native code.
Stats type_nonreturning_methods(
    const DexStoresVector& stores,
    const Scope& scope,
    DexType* result_type,
    const baseline_profiles::BaselineProfile& baseline_profile,
    uint32_t huge_method_max,
    size_t reserved_mrefs,
    method_profiles::MethodProfiles& method_profiles);

// Moves the body of the static method `method` into a new method of its class
// with the same name and access flags and the signature `typed_proto`, and
// turns `method` into a stub that passes its arguments to the new method and
// returns. The new method keeps the rstate, the deobfuscated name and, through
// `profiles`, the profile stats of `method`; the stub is named `<name>$stub`
// and gets a synthetic copy of the body's entry source block, if any.
// References to `method` are left as they are. `method`'s class must not have
// a method or method reference with the new signature yet. Returns the new
// method.
DexMethod* split_off_typed_method(DexMethod* method,
                                  DexProto* typed_proto,
                                  method_profiles::MethodProfiles& profiles);

} // namespace typed_nonreturning_methods
