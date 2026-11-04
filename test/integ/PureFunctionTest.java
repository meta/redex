/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;
import java.util.Locale;
import java.lang.String;

class Base {
  int f;
  /* Pure in Base */
  int fn0 () { return 1;};
  int fn1(int i, int j) { return i+ j; }
  String fn2(String st, int i) { return st + i; }

  /* Modifies param in Base */
  String fn3(String st) { st.toUpperCase(Locale.ROOT); return st; }

  /* Pure in Base */
  int fn4(int i, int j) { return i+ j; }
  String fn5(String st, int i) { return st + i; }

  /* Modifies param in Base */
  String fn6(String st) { st.toUpperCase(Locale.ROOT); return st; }
}

class SubOne extends Base {
  /* Pure */
  int fn0 () { return 2;};
  int fn1(int i, int j) { return i+ j; }
  final String fn2(String st, int i) { return st + i; }

  /* Modifies param */
  String fn3 (String st) { st.toUpperCase(Locale.ROOT); return st; }

  /* Not Pure */
  int fn4(int i, int j) { f = 1; return i+ j; }
  String fn5(String st, int i) { f = -1; return st + i; }
  String fn6(String st) { f = 2; st.toUpperCase(Locale.ROOT); return st; }
}

class SubTwo extends Base {
  /* Pure */
  int fn0 () { return 3;};
  int fn1(int i, int j) { return i+ j; }
  final String fn2(String st, int i) { return st + i; }

  /* Modifies param */
  String fn3(String st) { st.toUpperCase(Locale.ROOT); return st; }

  /* Pure */
  int fn4(int i, int j) { return i+ j; }
  String fn5(String st, int i) { return st + i; }
  /* Modifies param */
  String fn6(String st) { st.toUpperCase(Locale.ROOT); return st; }
}
