/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "DexAnnotation.h"
#include "DexClass.h"

namespace api {

/**
 * This class exists to check the required Android API level for a method.
 *
 * The api level information is backed by
 *   DexMethod.rstate.[get_api_level|set_api_level].
 * This state is initialized for all initially loaded classes, and computed
 * lazily on first access for all dynamically created method.
 * If desired at a point in time after annotations have been erased, this state
 * can be manually set by optimization passes that create methods.
 */
class LevelChecker {
 public:
  /**
   * Call `init` exactly once after the classes have been loaded from the dex
   * file. We have this initialization function (instead of a constructor)
   * because the static instance is created before the classes are loaded.
   *
   * `min_level` is the api level that un-annotated code should be assumed to
   * have.
   *
   * After this initialization, `get_method_level` can be called in parallel
   * safely.
   */
  static void init(int32_t min_level, const Scope& scope);

  /**
   * Get the "most specific" api level of this method. If the method is
   * annotated with Target/RequiresApi, return its level, if not, check the
   * containing class and return its level. If neither are annotated with
   * Target/RequiresApi, return s_min_level.
   * Annotations that have a value less than s_min_level are interpreted to mean
   * s_min_level.
   *
   * In an attempt to minimize restrictions on optimizations, this method groups
   * inner classes into the api level of their outer class. This isn't strictly
   * correct but it seems like most developers just forgot (or were too lazy) to
   * put the annotation on all the inner classes (especially anonymous ones).
   */
  static int8_t get_method_level(const DexMethod* method);

  /**
   * Return the minimum api level of the entire app. This is the lowest value
   * that `get_method_level` or `get_level` could return. Members with no
   * annotations have this api level.
   */
  static int32_t get_min_level();

  /**
   * Only Check the annotations of the given member, not any containing class
   * levels. If this member is not annotated, return -1.
   * Annotations that have a value less than s_min_level are interpreted to mean
   * s_min_level.
   */
  template <typename DexMember>
  static int32_t get_level(const DexMember* member) {
    if ((s_requires_api_old == nullptr && s_requires_api_new == nullptr &&
         s_target_api == nullptr) ||
        member->get_anno_set() == nullptr) {
      return -1;
    }
    for (const auto& anno : member->get_anno_set()->get_annotations()) {
      if (anno->type() != nullptr && (anno->type() == s_requires_api_old ||
                                      anno->type() == s_requires_api_new ||
                                      anno->type() == s_target_api)) {
        const auto& elems = anno->anno_elems();
        // xxx: @androidx.annotation.RequiresApi() can not be compiled by javac,
        // it should have argument. But we get such annotation after running R8.
        if (elems.empty()) {
          return -1;
        }
        const DexAnnotationElement& api_elem = only(elems);
        always_assert(api_elem.string == DexString::get_string("api") ||
                      api_elem.string == DexString::get_string("value"));
        const auto& value = api_elem.encoded_value;
        always_assert(value->evtype() == DEVT_INT);
        int32_t result = static_cast<int32_t>(value->value());
        if (result >= 100000) {
          // Possibly a value that corresponds to:
          // https://developer.android.com/reference/android/os/Build.VERSION_CODES_FULL
          // According to the docs "the current encoding scheme may change in
          // the future" but as a first step, try to munge an abnormally high
          // value that falls in the range of SDK_INT_FULL to what would likely
          // be the comparable SDK_INT value that would include it, for
          // compatibility purposes with the rest of our logic.
          auto inc = result % 100000 == 0 ? 0 : 1;
          result = result / 100000 + inc;
        }
        return std::max(result, s_min_level);
      }
    }
    return -1;
  }

 private:
  static DexClass* get_outer_class(const DexClass* cls);
  static void init_class(DexClass* clazz);
  static void init_method(DexMethod* method);
  static void propagate_levels(const Scope& scope);

  /**
   * These states are only meant to be edited during `init`. After
   * initialization, these are read-only and safe to use in parallel
   */
  static int32_t s_min_level;
  static const DexType* s_requires_api_old;
  static const DexType* s_requires_api_new;
  static const DexType* s_target_api;
  static bool s_has_been_init;
};

bool is_android_sdk_type(const DexType* type);

/*
 * Support library and Android X are designed to handle incompatibility and
 * discrepancies between different Android versions. It's riskier to change the
 * external method references in these libraries based on the one version of
 * external API we are building against.
 *
 * For instance, Landroid/os/BaseBundle; is added API level 21 as the base type
 * of Landroid/os/Bundle;. If we are building against an external library newer
 * than 21, we might rebind a method reference on Landroid/os/Bundle; to
 * Landroid/os/BaseBundle;. The output apk will not work on 4.x devices. In
 * theory, issues like this can be covered by the exclusion list. But in
 * practice is hard to enumerate the entire list of external classes that should
 * be excluded. Given that the support libraries are dedicated to handle this
 * kind of discrepancies. It's safer to not touch it.
 */
bool is_support_lib_type(const DexType* type);

} // namespace api
