/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

enum EnumSafe {
  A("zero", 0),
  B(null, 1);

  String name;
  int value;
  boolean isUseful;

  EnumSafe(String str, int i) {
    this.name = str;
    this.value = i;
    this.isUseful = true;
  }
}

/**
 * Some corner cases where sparta might not be able to figure out the constants.
 * Move these cases to EnumSafe if we are able to handle them.
 */
enum EnumUnsafe1 {
  A("First"),
  B(A.name);

  String name;

  EnumUnsafe1(String str) {
    this.name = str;
  }
}

enum EnumUnsafe2 {
  A(new String(Character.toChars(0x1F3AE)));

  String name;

  EnumUnsafe2(String str) {
    this.name = str;
  }
}

/**
 * FAST's argument calls code that reads SLOW, which is still null then. Once
 * SLOW is boxed, `seen` would become true.
 */
enum EnumCalleeReadsLaterConstant {
  FAST(slowReady()),
  SLOW(true);

  static boolean seen;

  EnumCalleeReadsLaterConstant(boolean ready) {}

  static boolean slowReady() {
    seen = SLOW != null;
    return true;
  }
}

/**
 * The constructor body, not a constant's argument, reads SLOW while it is
 * still null. Once SLOW is boxed, `seen` would become true.
 */
enum EnumConstructorReadsLaterConstant {
  FAST(true),
  SLOW(false);

  static boolean seen;

  EnumConstructorReadsLaterConstant(boolean ready) {
    record();
  }

  static void record() {
    seen = SLOW != null;
  }
}
