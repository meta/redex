/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "Pass.h"

namespace api {
class AndroidSDK;
} // namespace api

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

namespace lift_virtual_methods {

// Why a group of sibling methods was not lifted. For reporting only.
enum class Rejection : uint8_t {
  kFewerThanTwoIdentical,
  kTargetHasMethod,
  kUnknownAncestor,
  kAncestorDeclaresMethod,
  kApiLevel,
  kReceiverType,
  kRelocation,
  kCrossStore,
  kSubtreeConflict,
  kTooManyInheritors,
  kInterfaceDeclaresMethod,
  kSourceBlockMismatch,
  kCount,
};

const char* describe(Rejection rejection);

struct Stats {
  uint32_t lifted_methods{0};
  uint32_t removed_methods{0};
  uint32_t receiver_casts{0};
  size_t new_vtable_slots{0};
  std::array<size_t, static_cast<size_t>(Rejection::kCount)> rejections{};
};

/**
 * Lift the largest group of identical small sibling methods into their common
 * superclass when it does not declare the method yet, and remove the copies.
 * Siblings with different code keep their methods as overrides.
 *
 * Example (D8's desugaring of a default interface method for API < 24 gives
 * every implementing class its own forwarder):
 * interface I { default int m() { ... } }
 * class Base {}
 * class A extends Base implements I {
 *   public int m() { return I$-CC.$default$m(this); }
 * }
 * class B extends Base implements I {
 *   public int m() { return I$-CC.$default$m(this); }
 * }
 * becomes one `public int m()` in Base, which casts its receiver to I before
 * passing it on. A subclass of Base that does not implement I gains a method
 * that no existing call can reach.
 *
 * Folds the copies' source blocks and method profile stats into the lifted
 * method. A lift is skipped when it would add more than
 * `max_inheritors_per_copy` vtable slots (in the superclass and in the classes
 * that newly inherit the method) per removed copy, or when the superclass's
 * store or dex may not reference what the method references (external
 * references must exist at `min_sdk_api`; with none given, none may remain).
 */
Stats lift(const DexStoresVector& stores,
           method_profiles::MethodProfiles& method_profiles,
           bool normal_primary_dex,
           const api::AndroidSDK* min_sdk_api,
           double max_inheritors_per_copy);

} // namespace lift_virtual_methods

/**
 * Lifts identical small sibling methods into their common superclass and
 * removes the copies (see `lift_virtual_methods::lift`). Runs before InterDex,
 * so that the dex packing sees the smaller hierarchy and the inliner can still
 * inline what the lifted methods call.
 */
class LiftVirtualMethodsPass : public Pass {
 public:
  LiftVirtualMethodsPass() : Pass("LiftVirtualMethodsPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
    };
  }

  void bind_config() override;
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  double m_max_inheritors_per_copy{4};
};
