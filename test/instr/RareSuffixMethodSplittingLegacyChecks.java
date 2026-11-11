/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package redex;

import kotlin.jvm.internal.Intrinsics;

/**
 * Java stand-in for a class compiled by Kotlin before 1.4, which checks its
 * parameters with the legacy checkParameterIsNotNull.
 */
class LegacyChecks {
  public int legacy(String a, String b) {
    Intrinsics.checkParameterIsNotNull(a, "a");
    Intrinsics.checkParameterIsNotNull(b, "b");
    return a.length() + b.length();
  }
}
