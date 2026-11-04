/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/**
 * This Java class is used as a simple container for dynamically generated
 * methods.
 */

package com.facebook.redextest;

import com.facebook.redex.annotations.MethodMeta;
import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

interface Interface {
  int magic();
}

abstract class Base implements Interface {
  public String str;
  Base(String s, int i) { str = s; }
  int realVirt() { return 100; }
  // Preventing Interface from being optimized away
  void whatCanISay(Interface i) {}
  boolean wasOverridden() { return false; }
  abstract boolean toBeImplemented();
}

class A extends Base {
  A(String s) {
    super(s, 0);
  }
  private A() { this("Oh A!"); }
  public static A createA() { return new A(); }
  public String getStr() { return str; }
  @Override
  int realVirt() { return 200; }
  public int magic() { return 42; }
  // non-ctor dmethod
  private int dmethod() { return 113; }
  public int callDMeth() { return dmethod(); }
  // non-virtual vmethod
  public int vmethod() { return 441; }
  public static int callVMeth(A a) { return a.vmethod(); }
  // dedup static method
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/A;")
  public static A fromObj(Object obj) {
    if (obj instanceof A) {
      return (A) obj;
    }
    A a = new A("Oh yes!");
    return a;
  }
  @Override
  boolean wasOverridden() { return true; }

  @Override
  boolean toBeImplemented() {
    return true;
  }
}

class B extends Base {
  B(String s) {
    super(s, 0);
  }
  private B() { this("Oh B!"); }
  public static B createB() { return new B(); }
  public String getStr() { return str; }
  @Override
  int realVirt() { return 300; }
  public int magic() { return 43; }
  // dedup static method
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/B;")
  public static B fromObj(Object obj) {
    if (obj instanceof B) {
      return (B) obj;
    }
    B b = new B("Oh yes!");
    return b;
  }
  @Override
  boolean wasOverridden() { return true; }

  @Override
  boolean toBeImplemented() {
    return true;
  }
}

class C extends Base {
  C(String s) {
    super(s, 1);
  }
  private C() { this("Oh C!"); }
  public static C createC() { return new C(); }
  public String getStr() { return str; }
  @Override
  int realVirt() { return 400; }
  public int magic() { return 44; }
  // dedup static method
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/C;")
  public static C fromObj(Object obj) {
    if (obj instanceof C) {
      return (C) obj;
    }
    C c = new C("Oh yes!");
    return c;
  }

  @Override
  boolean toBeImplemented() {
    return true;
  }
}

class D extends Base {
  D(String s) {
    super(s, 2);
  }
  private D() { this("Oh D!"); }
  public static D createD() { return new D(); }
  public String getStr() { return str; }
  @Override
  int realVirt() { return 500; }
  public int magic() { return 45; }
  // dedup static method
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/D;")
  public static D fromObj(Object obj) {
    if (obj instanceof D) {
      return (D) obj;
    }
    D d = new D("Oh yes!");
    return d;
  }

  @Override
  boolean toBeImplemented() {
    return true;
  }
}

abstract class SecondBase {
  abstract String foo();
}
class SecondA extends SecondBase {
  int getA() { return 1; }
  String foo() { return "A"; }
}
class SecondB extends SecondBase {
  int getB() { return 2; }
  String foo() { return "B"; }
}
class SecondC extends SecondBase {
  int getC() { return 3; }
  String foo() { return "C"; }
}

abstract class ThirdBase {
  abstract String foo();
}
abstract class ThirdMid extends ThirdBase {
  @Override
  String foo() { return "mid"; };
}
class ThirdA extends ThirdMid {
  int getA() { return 1; }
  @Override
  String foo() { return "A"; }
}
class ThirdB extends ThirdMid {
  int getB() { return 2; }
  @Override
  String foo() { return "B"; }
}
class ThirdC extends ThirdMid {
  int getC() { return 3; }
}

class ArrayBase {}
class ArrayA extends ArrayBase {}
class ArrayB extends ArrayBase {}
class ArrayC extends ArrayBase {}
class ArrayD extends ArrayBase {}

public class ClassMergingSimpleTest {

  static boolean isArrayA(Object o) { return o instanceof ArrayA[]; }
  static boolean isArrayB(Object o) { return o instanceof ArrayB[][]; }
  static boolean isArrayC(Object o) { return o instanceof ArrayC; }

  @Test
  public void testArrayInstanceOf() {
    assertThat(isArrayA(new ArrayA[1])).isTrue();
    assertThat(isArrayA(new ArrayA[0])).isTrue();
    assertThat(isArrayA(new ArrayB[1])).isFalse();
    assertThat(isArrayA(new ArrayA())).isFalse();
    assertThat(isArrayA(null)).isFalse();
  }

  @Test
  public void testMultiDimensionalArrayInstanceOf() {
    assertThat(isArrayB(new ArrayB[1][])).isTrue();
    assertThat(isArrayB(new ArrayB[0][])).isTrue();
    assertThat(isArrayB(new ArrayA[1][])).isFalse();
    assertThat(isArrayB(new ArrayB[1])).isFalse();
    assertThat(isArrayB(new ArrayB())).isFalse();
    assertThat(isArrayB(null)).isFalse();
  }

  @Test
  public void testPlainInstanceOfStillMerges() {
    assertThat(isArrayC(new ArrayC())).isTrue();
    assertThat(isArrayC(new ArrayD())).isFalse();
    assertThat(isArrayC(null)).isFalse();
  }

  @Test
  public void testMergingNonVirts() {
    A a = new A("Oh A!");
    B b = new B("Oh B!");
    C c = new C("Oh C!");
    D d = new D("Oh D!");
    assertThat(a.getStr()).isEqualTo("Oh A!");
    assertThat(b.getStr()).isEqualTo("Oh B!");
    assertThat(c.getStr()).isEqualTo("Oh C!");
    assertThat(d.getStr()).isEqualTo("Oh D!");
  }

  @Test
  public void testMultipleCtors() {
    A a = A.createA();
    B b = B.createB();
    C c = C.createC();
    D d = D.createD();
    assertThat(a.getStr()).isEqualTo("Oh A!");
    assertThat(b.getStr()).isEqualTo("Oh B!");
    assertThat(c.getStr()).isEqualTo("Oh C!");
    assertThat(d.getStr()).isEqualTo("Oh D!");
  }

  @Test
  public void testMergingRealVirts() {
    A a = new A("Oh A!");
    B b = new B("Oh B!");
    C c = new C("Oh C!");
    D d = new D("Oh D!");
    assertThat(a.realVirt()).isEqualTo(200);
    assertThat(b.realVirt()).isEqualTo(300);
    assertThat(c.realVirt()).isEqualTo(400);
    assertThat(d.realVirt()).isEqualTo(500);
  }

  @Test
  public void testMergingInterfaceImpl() {
    A a = new A("Oh A!");
    B b = new B("Oh B!");
    C c = new C("Oh C!");
    D d = new D("Oh D!");
    assertThat(a.magic()).isEqualTo(42);
    assertThat(b.magic()).isEqualTo(43);
    assertThat(c.magic()).isEqualTo(44);
    assertThat(d.magic()).isEqualTo(45);
  }

  @Test
  public void testFieldRefs() {
    A a = new A("Oh A!");
    B b = new B("Oh B!");
    C c = new C("Oh C!");
    D d = new D("Oh D!");
    assertThat(a.str).isEqualTo("Oh A!");
    assertThat(b.str).isEqualTo("Oh B!");
    assertThat(c.str).isEqualTo("Oh C!");
    assertThat(d.str).isEqualTo("Oh D!");
  }

  // Dummy for codegen reference.
  boolean instanceOf(Object o, int t) {
    if (!(o instanceof Base)) {
      return false;
    }
    return o.hashCode() == t;
  }

  @Test
  public void testInstanceOf() {
    A a = new A("Oh A!");
    B b = new B("Oh B!");
    C c = new C("Oh C!");
    D d = new D("Oh D!");
    assertThat(a instanceof A).isEqualTo(true);
    assertThat(b instanceof B).isEqualTo(true);
    assertThat(c instanceof C).isEqualTo(true);
    assertThat(d instanceof D).isEqualTo(true);
    assertThat(a instanceof Base).isEqualTo(true);
    assertThat(b instanceof Base).isEqualTo(true);
    assertThat(c instanceof Base).isEqualTo(true);
    assertThat(d instanceof Base).isEqualTo(true);
  }

  // Dummy for test
  static A fromObj(Object o) {
    if (o instanceof A) {
      return (A) o;
    }
    throw new IllegalStateException();
  }

  @Test
  public void testCheckCast() {
    A a = new A("Oh A!");
    Object o = a;
    assertThat(fromObj(o)).isEqualTo(a);
  }

  @Test
  public void testNewArray() {
    A[] aa = {new A("Oh A0!"), new A("Oh A1!"), new A("Oh A2!")};
    Object o = aa;
    A[] casted = (A[]) o;
    assertThat(casted.length).isEqualTo(3);
    assertThat(casted[0].str).isEqualTo("Oh A0!");
    assertThat(casted[1].str).isEqualTo("Oh A1!");
    assertThat(casted[2].str).isEqualTo("Oh A2!");

    Base[] ba = {new A("Oh A!"), new B("Oh B!")};
    assertThat(ba[0].str).isEqualTo("Oh A!");
    assertThat(ba[0].wasOverridden()).isEqualTo(true);
    assertThat(ba[1].str).isEqualTo("Oh B!");
    assertThat(ba[1].wasOverridden()).isEqualTo(true);
  }

  // Dummy for test
  public int testSwitch(int a) {
    switch (a) {
    case 1:
    case 2:
    case 3:
      a += 1;
      break;
    case 4:
      a += 4;
      break;
    default:
      a -= 1;
      break;
    }
    return a;
  }

  // Dummy for test
  class FieldReferencer {
    public A a;
    public FieldReferencer(A a) {
      this.a = a;
    }
    public A getA() { return this.a; }
  }

  @Test
  public void testFieldRefsTest() {
    A a = new A("Oh A!");
    FieldReferencer fr = new FieldReferencer(a);
    assertThat(fr.getA().str).isEqualTo("Oh A!");
  }

  @Test
  public void testNonCtor() {
    A a = new A("Oh A!");
    assertThat(a.callDMeth()).isEqualTo(113);
  }

  @Test
  public void testNonVirtual() {
    A a = new A("Oh A!");
    assertThat(A.callVMeth(a)).isEqualTo(441);
  }

  @Test
  public void testStaticDedup() {
    Object a = new A("Oh A!");
    A res = A.fromObj(a);
    assertThat(res.str).isEqualTo("Oh A!");
    Object o = new Object();
    res = A.fromObj(o);
    assertThat(res.str).isEqualTo("Oh yes!");
  }

  @Test
  public void testOverridenMethod() {
    A a = new A("Oh A!");
    C c = new C("Oh C!");

    assertThat(a.wasOverridden()).isEqualTo(true);
    assertThat(c.wasOverridden()).isEqualTo(false);
  }

  @Test
  public void testAllVirtualMethodsIdentical() {
    A a = new A("Oh A!");
    C c = new C("Oh C!");

    assertThat(a.toBeImplemented()).isEqualTo(true);
    assertThat(c.toBeImplemented()).isEqualTo(true);
  }

  @Test
  public void testSecondRoot() {
    SecondA a = new SecondA();
    SecondB b = new SecondB();
    SecondC c = new SecondC();
    assertThat(a.getA()).isEqualTo(1);
    assertThat(b.getB()).isEqualTo(2);
    assertThat(c.getC()).isEqualTo(3);
  }

  @Test
  public void testSecondRootAbstractOverridden() {
    SecondA a = new SecondA();
    SecondB b = new SecondB();
    SecondC c = new SecondC();
    assertThat(a.foo()).isEqualTo("A");
    assertThat(b.foo()).isEqualTo("B");
    assertThat(c.foo()).isEqualTo("C");
  }

  @Test
  public void testThirdRootAbstractPartialOverridden() {
    ThirdA a = new ThirdA();
    ThirdB b = new ThirdB();
    ThirdC c = new ThirdC();
    assertThat(a.foo()).isEqualTo("A");
    assertThat(b.foo()).isEqualTo("B");
    assertThat(c.foo()).isEqualTo("mid");
  }
}
