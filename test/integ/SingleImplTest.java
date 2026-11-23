/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

interface Intf {
  public int get();
}

class Impl implements Intf{
  public int get() { return 42; }
}

class Helper {
// The following methods will be injected by the test. The reason
// is that javac doesn't compile the following code but it's type
// safe at bytecode level.
//
//   Object createIntf() {
//     return new Impl();
//   }

//   Intf retIntf() {
//     return createIntf();
//   }
}

// Overloads whose parameter type is a single-implementation interface. The
// test adds the default methods `Printer.print(GreetingImpl)` and
// `Sender.send(Message)`, which d8 would desugar for this test's min SDK.
interface Greeting {
  public String text();
}

class GreetingImpl implements Greeting {
  public String text() { return "hi"; }
}

interface Printer {}

class ConsolePrinter implements Printer {
  public String print(Greeting g) { return "console"; }
}

interface Message {
  public String body();
}

class MessageImpl implements Message {
  public String body() { return "message"; }
}

interface Sender {}

class EmailSender implements Sender {
  public String send(MessageImpl m) { return "email"; }
}

// `R` is the only implementation of both interfaces that declare it.
interface P {
  interface Q {
    class R implements P, Q {}
  }
}

// `Impl` is the only implementation of both interfaces that declare it.
// `AAA` makes SingleImpl remove `ZInner` in a later round than `AOuter`.
interface AOuter {
  void m(AOuter.ZInner x);

  interface AAA {
    void k(AOuter.ZInner z);
  }

  interface ZInner {
    class Impl implements AOuter, ZInner {
      public void m(ZInner x) {}
    }
  }
}

class AAAImpl implements AOuter.AAA {
  public void k(AOuter.ZInner z) {}
}

// `Impl3` is the only implementation of `Deep`, which declares it inside the
// class `Middle`.
interface Deep {
  class Middle {
    class Impl3 implements Deep {}
  }
}
