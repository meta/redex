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
  public void entry() {
    Child.inherited();
    new Annotated().run();
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
