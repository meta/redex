/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

public class DebugLocals {
  static class DropsLocal {
    static String drop() {
      return "local";
    }
  }

  static class KeepsLocal {
    static int keep(int n) {
      int local = n * 2;
      return local + 1;
    }
  }
}
