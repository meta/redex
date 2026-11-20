/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

// The only keep-rule entry point.
public class LiveReachabilityGraphTest {
  // Only this method calls make(), and marking walks a method's whole body
  // before it pushes the methods it calls, so Checked is not instantiable yet
  // when the walk reaches the instance-of. Keep the instance-of before the
  // call.
  static boolean checks(Object o) {
    boolean result = o instanceof Checked;
    make();
    return result;
  }

  static Object make() {
    return new CheckedImpl();
  }

  // As in checks(), Cast is not instantiable yet when the walk reaches the
  // check-cast, but entry() has already marked Cast.
  static Object casts(Object o) {
    Object result = (Cast) o;
    makeCast();
    return result;
  }

  static Object makeCast() {
    return new CastImpl();
  }

  public void entry() {
    Child.inherited();
    new Annotated().run();
    new Target().call();
    checks(null);
    // Marks Cast, without making it instantiable, before casts() is walked.
    Object casts = new Cast[0];
    casts(casts);
  }
}

class Parent {
  static void inherited() {}
}

// Child declares no method; the call above references Child.inherited(),
// which only Parent defines.
class Child extends Parent {}

// Nothing that is kept refers to Severity itself: the annotation value below
// refers to the field Severity.HIGH.
enum Severity {
  LOW,
  HIGH
}

@Retention(RetentionPolicy.RUNTIME)
@interface Level {
  Severity value();
}

@Level(Severity.HIGH)
class Annotated {
  void run() {}
}

// entry() calls call() directly, so call() is marked before the walk asks
// whether Target is instantiable.
class Target {
  void call() {}
}

// Besides CheckedImpl, only the instance-of in checks() names Checked.
interface Checked {}

class CheckedImpl implements Checked {}

interface Cast {}

class CastImpl implements Cast {}
