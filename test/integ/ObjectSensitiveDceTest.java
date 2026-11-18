/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

class ObjectSensitiveDceTest {
  public static void basic() {
    Useless useless = new Useless();
    useless.foo();
  }

  public static void recursive() {
    Useless useless = new Useless();
    useless.recursive_foo(100);
  }

  public static void mutually_recursive() {
    Useless useless = new Useless();
    useless.mutually_recursive_foo(100);
  }

  public static void passed_to_no_optimizations_method() {
    Useless useless = new Useless();
    NoOptimizations.take(useless);
    useless.foo();
  }

  public static void invoke_super() {
    UselessDerived useless = new UselessDerived();
    useless.foo();
  }

  public static void invoke_virtual_with_overrides() {
    UselessBase useless = new UselessDerived();
    useless.bar();
  }

  public static void invoke_virtual_with_overrides_with_side_effect() {
    UselessBase useless = new UselessDerived();
    useless.bar_where_override_has_side_effect();
  }

  public static void invoke_virtual_with_too_many_overrides() {
    UselessBase useless = new UselessDerived();
    useless.bar_with_invoke_virtual_with_too_many_overrides();
  }

  public static void non_termination() {
    Useless useless = new Useless();
    useless.non_terminating_foo();
  }

  public static void clinit_with_side_effects() {
    UselessWithClInitWithSideEffects useless = new UselessWithClInitWithSideEffects();
    useless.foo();
  }

  public static void method_needing_init_class() {
    UselessWithMethodNeedingInitClass useless = new UselessWithMethodNeedingInitClass();
    useless.foo();
  }

  public static void pure_method_object() {
    Useless useless = new Useless();
    useless.getClass();
  }

  public static void array_clone() {
    int[] a = new int[1];
    a = a.clone();
    a.clone();
  }

  public static void do_not_reduce_finalize() {
    UselessWithFinalize useless = new UselessWithFinalize();
    useless.foo();
  }

  public static void do_not_reduce_finalize_field() {
    UselessWithFinalize useless = new UselessWithFinalize();
    useless.F = 42;
  }

  public static void do_not_reduce_finalize_derived() {
    UselessDerivedWithFinalize useless = new UselessDerivedWithFinalize();
    useless.bar();
  }
}

class Useless {
  int F;
  public Useless() {}
  public void foo() {
    F = 42;
  }
  public void non_terminating_foo() {
    while (true) {}
  }
  public void recursive_foo(int x) {
    if (x<=0) {
      F = 42;
    } else {
      recursive_foo(x-1);
    }
  }
  public void mutually_recursive_foo(int x) {
    if (x<=0) {
      F = 42;
    } else {
      mutually_recursive_bar(x-1);
    }
  }
  public void mutually_recursive_bar(int x) {
    if (x<=0) {
      F = 42;
    } else {
      mutually_recursive_foo(x-1);
    }
  }
}

class UselessBase {
  int F;
  public UselessBase() {}
  public void foo() {
    F = 42;
  }
  public void bar() {
    F = 42;
  }
  public void bar_where_override_has_side_effect() {
    F = 42;
  }
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived extends UselessBase {
  public UselessDerived() {}
  public void foo() {
    super.foo();
  }
  public void bar() {
    F = 42;
  }
  public void bar_where_override_has_side_effect() {
    try {
      System.loadLibrary("boo"); // side effect
    } catch (Throwable t) { }
  }
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived2 extends UselessBase {
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived3 extends UselessBase {
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived4 extends UselessBase {
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived5 extends UselessBase {
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessDerived6 extends UselessBase {
  public void bar_with_invoke_virtual_with_too_many_overrides() {
    F = 42;
  }
}

class UselessWithClInitWithSideEffects {
  int F;
  public UselessWithClInitWithSideEffects() {}
  static {
    try {
      System.loadLibrary("boo"); // side effect
    } catch (Throwable t) { }
  }
  public void foo() {
    F = 42;
  }
}

class UselessWithMethodNeedingInitClass {
  int F;
  public UselessWithMethodNeedingInitClass() {}
  public void foo() {
    F = new UselessWithClInitWithSideEffects().F;
  }
}

class UselessWithFinalize {
  int F;
  public UselessWithFinalize() {}
  public void foo() {
    F = 42;
  }
  protected void finalize() {}
}

class UselessDerivedWithFinalize extends UselessWithFinalize {
  public UselessDerivedWithFinalize() {}
  public void bar() {
    F = 37;
  }
}

class NoOptimizations {
  // The test marks this method `no_optimizations`: the code that runs may keep
  // its argument and read it later.
  public static void take(Object o) {}
}
