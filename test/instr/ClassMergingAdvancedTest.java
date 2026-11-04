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

import org.junit.Test;

import com.facebook.redex.annotations.ModelIdentity;
import com.facebook.redex.annotations.MethodMeta;
import static org.assertj.core.api.Assertions.assertThat;

@interface DoNotStrip {}

interface Interface1 {
  int magic1();
}
interface Interface2 {
  int magic2();
}
interface Interface3 {
  int magic3();
}
// True virtual with array return type
interface StringsGetter {
  String[] getStrings();
}

abstract class Base {
  int mTypeTag;
  Base(int typeTag) { this.mTypeTag = typeTag; }
  // Preventing Interface from being optimized away
  void whatCanISay(Interface1 i1, Interface2 i2, Interface3 i3) {}
  // Const-string based type references.
  public static Class<? extends Base> getClass(int typeTag)
      throws ClassNotFoundException {
    String name = null;
    switch (typeTag) {
    case 0x0:
      name = "com.facebook.redextest.Dummy";
      break;
    case 0x1:
      name = "com.facebook.redextest.A";
      break;
    case 0x2:
      name = "com.facebook.redextest.B";
      break;
    case 0x3:
      name = "com.facebook.redextest.C";
      break;
    case 0x4:
      name = "com.facebook.redextest.D";
      break;
    default:
      throw new IllegalArgumentException();
    }
    return (Class<? extends Base>) Class.forName(name);
  }
  // Default implementation with the interface method
  public int magic3() { return -1; }
  // To suppress constant folding.
  int passThrough(int arg) { return arg; }
  String passThrough(String s) { return s; }
  // Conflicting virtual method with constant lifted method.
  public final int getWithConstantA(int i) {
    int val = passThrough(i);
    return 100 + val;
  }
}

@ModelIdentity(typeTag = 0x1)
class A extends Base implements Interface1, Interface3, StringsGetter {
  volatile int a1;
  String a2;
  volatile long wide;
  volatile double mixed;
  final float immutable = 1.0f;

  A() { super(1); }
  void init(int a1, String a2) {
    this.a1 = a1;
    this.a2 = a2;
  }
  public int getA1() { return a1; }
  public String getA2() { return a2; }

  @Override
  public int magic1() {
    return 142;
  }

  @MethodMeta(constantTypes = "I", constantValues = "11")
  public int getWithConstantA() {
    int val = passThrough(11);
    return 100 + val;
  }
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/A;")
  public A
  getA() {
    return new A();
  }
  @MethodMeta(constantTypes = "S", constantValues = "SA")
  public String getStringA() {
    return passThrough("SA");
  }
  @MethodMeta(constantTypes = "SI", constantValues = "SA:11")
  public String getStringInt() {
    return passThrough("SA") + String.valueOf(11);
  }
  @MethodMeta(constantTypes = "IT",
              constantValues = "11:Lcom/facebook/redextest/A;")
  public int
  getIntTypeA() {
    new A();
    return 11;
  }
  @MethodMeta(constantTypes = "TS",
              constantValues = "Lcom/facebook/redextest/Invalid;:SA")
  public String
  getStringInvalidType() {
    new A();
    return passThrough("SA");
  }

  @MethodMeta(constantTypes = "III",
              constantValues = "1:1:42")
  public int multipleRepeatingConstants() {
    int val = passThrough(1);
    val += passThrough(1);
    val += passThrough(42);
    return val;
  }

  // Puting the array allocation here so the analysis will not exclude A as a
  // mergeable type.
  public static A[] getArray() {
    A[] ar = new A[1];
    ar[0] = new A();
    ar[0].init(1, "Oh A!");
    return ar;
  }
  public String[] getStrings() { return new String[] {"A"}; }
}

@ModelIdentity(typeTag = 0x2)
class B extends Base implements Interface1, Interface3, StringsGetter {
  String b1;
  int b2;
  volatile long wide;
  final double mixed = 2.0;
  final float immutable = 2.0f;

  B() { super(2); }
  void init(String b1, int b2) {
    this.b1 = b1;
    this.b2 = b2;
  }
  public String getB1() { return b1; }
  public int getB2() { return b2; }

  @Override
  public int magic1() {
    return 143;
  }

  @Override
  public int magic3() {
    return 3;
  }

  @MethodMeta(constantTypes = "I", constantValues = "12")
  public int getWithConstantB() {
    int val = passThrough(12);
    return 100 + val;
  }
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/B;")
  public B
  getB() {
    return new B();
  }
  @MethodMeta(constantTypes = "S", constantValues = "SB")
  public String getStringB() {
    return passThrough("SB");
  }
  @MethodMeta(constantTypes = "SI", constantValues = "SB:12")
  public String getStringInt() {
    return passThrough("SB") + String.valueOf(12);
  }
  @MethodMeta(constantTypes = "IT",
              constantValues = "12:Lcom/facebook/redextest/B;")
  public int
  getIntTypeB() {
    new B();
    return 12;
  }
  public String[] getStrings() { return new String[] {"B"}; }
}

@ModelIdentity(typeTag = 0x3)
class C extends Base implements Interface2, Interface3, StringsGetter {
  boolean c1;
  byte c2;
  char c3;
  short c4;
  int c5;
  String c6;

  C() { super(3); }
  void init(boolean c1, byte c2, char c3, short c4, int c5, String c6) {
    this.c1 = c1;
    this.c2 = c2;
    this.c3 = c3;
    this.c4 = c4;
    this.c5 = c5;
    this.c6 = c6;
  }

  public boolean getC1() { return c1; }
  public byte getC2() { return c2; }
  public char getC3() { return c3; }
  public short getC4() { return c4; }
  public int getC5() { return c5; }
  public String getC6() { return c6; }

  @Override
  public int magic2() {
    return 244;
  }

  @MethodMeta(constantTypes = "I", constantValues = "13")
  public int getWithConstantC() {
    int val = passThrough(13);
    return 100 + val;
  }
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/C;")
  public C
  getC() {
    return new C();
  }
  @MethodMeta(constantTypes = "S", constantValues = "SC")
  public String getStringC() {
    return passThrough("SC");
  }
  @MethodMeta(constantTypes = "TS",
              constantValues = "Lcom/facebook/redextest/C;:SC")
  public String
  getStringTypeC() {
    new C();
    return passThrough("SC");
  }
  public String[] getStrings() { return new String[] {"C"}; }
}

@ModelIdentity(typeTag = 0x4)
class D extends Base implements Interface2, Interface3, StringsGetter {
  static String static_field = "static_field";
  String d1;
  int d2;
  short d3;
  char d4;
  byte d5;
  boolean d6;

  D() { super(4); }
  void init(String d1, int d2, short d3, char d4, byte d5, boolean d6) {
    this.d1 = d1;
    this.d2 = d2;
    this.d3 = d3;
    this.d4 = d4;
    this.d5 = d5;
    this.d6 = d6;
  }

  public String getD1() { return d1; }
  public int getD2() { return d2; }
  public short getD3() { return d3; }
  public char getD4() { return d4; }
  public byte getD5() { return d5; }
  public boolean getD6() { return d6; }

  @Override
  public int magic2() {
    return 245;
  }

  @Override
  public int magic3() {
    return 5;
  }

  @MethodMeta(constantTypes = "I", constantValues = "14")
  public int getWithConstantD() {
    int val = passThrough(14);
    return 100 + val;
  }
  @MethodMeta(constantTypes = "T",
              constantValues = "Lcom/facebook/redextest/D;")
  public D
  getD() {
    return new D();
  }
  @MethodMeta(constantTypes = "S", constantValues = "SD")
  public String getStringD() {
    return passThrough("SD");
  }
  @MethodMeta(constantTypes = "TS",
              constantValues = "Lcom/facebook/redextest/D;:SD")
  public String
  getStringTypeD() {
    new D();
    return passThrough("SD");
  }
  public String[] getStrings() { return new String[] {"D"}; }
}

@ModelIdentity(typeTag = 0x5)
class E extends Base implements Interface1, Interface3, StringsGetter {
  String e1;
  int e2;
  volatile long wide;
  final double mixed = 3.0;
  final float immutable = 3.0f;

  E() { super(5); }
  void init(String e1, int e2) {
    this.e1 = e1;
    this.e2 = e2;
  }
  public String getE1() { return e1; }
  public int getE2() { return e2; }

  @Override
  public int magic1() {
    return 144;
  }

  @Override
  public int magic3() {
    return 6;
  }
  public String[] getStrings() { return new String[] {"E"}; }
}

class SignatureCollidingDummy {
  int f;
  public SignatureCollidingDummy(A a) { this.f = a.getA1(); }
  public SignatureCollidingDummy(B b) { this.f = b.getB2(); }
  public SignatureCollidingDummy(E e) { this.f = e.getE2(); }
  int getF() { return this.f; }
  @DoNotStrip
  public String[] protoUpdateWithArrayReturnType(A a) {
    String[] res = new String[1];
    res[0] = Integer.toString(this.f);
    return res;
  }
}

class FieldRefDummy {
  A[] as;
  public FieldRefDummy() { this.as = A.getArray(); }
  int getA1() { return as[0].getA1(); }
}

class ModelConverter {
  public static String convert(Class clazz) {
    return clazz.getName();
  }
}

public class ClassMergingAdvancedTest {

  @Test
  public void testShapeCreation() {
    A a = new A();
    a.init(1, "Oh A!");
    B b = new B();
    b.init("Oh B!", 2);
    assertThat(a.getA1()).isEqualTo(1);
    assertThat(a.getA2()).isEqualTo("Oh A!");
    assertThat(b.getB1()).isEqualTo("Oh B!");
    assertThat(b.getB2()).isEqualTo(2);
    assertThat(D.static_field).isEqualTo("static_field");

    C c = new C();
    c.init(false, (byte) 3, (char) 4, (short) 5, 6, "Oh C!");
    D d = new D();
    d.init("Oh D!", 7, (short) 8, (char) 9, (byte) 10, true);
    assertThat(c.getC1()).isEqualTo(false);
    assertThat(Boolean.valueOf(c.getC1())).isEqualTo(Boolean.valueOf(false));
    assertThat(c.getC2()).isEqualTo((byte) 3);
    assertThat(c.getC3()).isEqualTo((char) 4);
    assertThat(c.getC4()).isEqualTo((short) 5);
    assertThat(c.getC5()).isEqualTo(6);
    assertThat(c.getC6()).isEqualTo("Oh C!");
    assertThat(d.getD1()).isEqualTo("Oh D!");
    assertThat(d.getD2()).isEqualTo(7);
    assertThat(d.getD3()).isEqualTo((short) 8);
    assertThat(d.getD4()).isEqualTo((char) 9);
    assertThat(d.getD5()).isEqualTo((byte) 10);
    assertThat(d.getD6()).isEqualTo(true);
    assertThat(Boolean.valueOf(d.getD6())).isEqualTo(Boolean.valueOf(true));

    assertThat(a.magic1()).isEqualTo(142);
    assertThat(b.magic1()).isEqualTo(143);
    assertThat(c.magic2()).isEqualTo(244);
    assertThat(d.magic2()).isEqualTo(245);
  }

  @Test
  public void testConstStringTypeReferenceReplacement()
      throws ClassNotFoundException {
    Class<? extends Base> clazz = Base.getClass(0x1);
    assertThat(clazz).isNotNull();
    assertThat(clazz.getName()).isEqualTo("com.facebook.redextest.A");

    clazz = Base.getClass(0x2);
    assertThat(clazz).isNotNull();
    assertThat(clazz.getName()).isEqualTo("com.facebook.redextest.B");

    clazz = Base.getClass(0x3);
    assertThat(clazz).isNotNull();
    assertThat(clazz.getName()).isEqualTo("com.facebook.redextest.C");

    clazz = Base.getClass(0x4);
    assertThat(clazz).isNotNull();
    assertThat(clazz.getName()).isEqualTo("com.facebook.redextest.D");
  }

  @Test
  public void testSignatureUpdateCollision() {
    A a = new A();
    a.init(1, "Oh A!");
    SignatureCollidingDummy scd = new SignatureCollidingDummy(a);
    assertThat(scd.getF()).isEqualTo(1);

    B b = new B();
    b.init("Oh B!", 2);
    scd = new SignatureCollidingDummy(b);
    assertThat(scd.getF()).isEqualTo(2);

    scd = new SignatureCollidingDummy(a);
    String[] res = scd.protoUpdateWithArrayReturnType(a);
    assertThat(res).isEqualTo(new String[] {"1"});

    E e = new E();
    e.init("Oh E!", 3);
    scd = new SignatureCollidingDummy(e);
    assertThat(scd.getF()).isEqualTo(3);
  }

  @Test
  public void testInterfaceMethod() {
    A a = new A();
    a.init(1, "Oh A!");
    B b = new B();
    b.init("Oh B!", 2);
    assertThat(a.magic3()).isEqualTo(-1);
    assertThat(b.magic3()).isEqualTo(3);

    C c = new C();
    c.init(false, (byte) 3, (char) 4, (short) 5, 6, "Oh C!");
    D d = new D();
    d.init("Oh D!", 7, (short) 8, (char) 9, (byte) 10, true);
    assertThat(c.magic3()).isEqualTo(-1);
    assertThat(d.magic3()).isEqualTo(5);
  }

  @Test
  public void testConstantLifting() {
    A a = new A();
    a.init(1, "Oh A!");
    B b = new B();
    b.init("Oh B!", 2);
    assertThat(a.getWithConstantA()).isEqualTo(111);
    assertThat(b.getWithConstantB()).isEqualTo(112);
    assertThat(a.getStringInt()).isEqualTo("SA11");
    assertThat(b.getStringInt()).isEqualTo("SB12");
    assertThat(a.getIntTypeA()).isEqualTo(11);
    assertThat(b.getIntTypeB()).isEqualTo(12);
    assertThat(a.getStringInvalidType()).isEqualTo("SA");
    assertThat(a.multipleRepeatingConstants()).isEqualTo(44);

    C c = new C();
    c.init(false, (byte) 3, (char) 4, (short) 5, 6, "Oh C!");
    D d = new D();
    d.init("Oh D!", 7, (short) 8, (char) 9, (byte) 10, true);
    assertThat(c.getWithConstantC()).isEqualTo(113);
    assertThat(d.getWithConstantD()).isEqualTo(114);

    a = new A();
    a = a.getA();
    assertThat(a).isNotNull();
    b = new B();
    b = b.getB();
    assertThat(b).isNotNull();

    c = new C();
    c = c.getC();
    assertThat(c).isNotNull();
    d = new D();
    d = d.getD();
    assertThat(d).isNotNull();

    String s = a.getStringA();
    assertThat(s).isEqualTo("SA");
    s = b.getStringB();
    assertThat(s).isEqualTo("SB");
    s = c.getStringC();
    assertThat(s).isEqualTo("SC");
    s = d.getStringD();
    assertThat(s).isEqualTo("SD");
    assertThat(c.getStringTypeC()).isEqualTo("SC");
    assertThat(d.getStringTypeD()).isEqualTo("SD");
  }

  @Test
  public void testFieldArrayRef() {
    FieldRefDummy frd = new FieldRefDummy();
    assertThat(frd.getA1()).isEqualTo(1);
  }

  @Test
  public void testVirtualDispatch() {
    StringsGetter a = new A();
    assertThat(a.getStrings()).isEqualTo(new String[] {"A"});
    StringsGetter b = new B();
    assertThat(b.getStrings()).isEqualTo(new String[] {"B"});
    StringsGetter c = new C();
    assertThat(c.getStrings()).isEqualTo(new String[] {"C"});
    StringsGetter d = new D();
    assertThat(d.getStrings()).isEqualTo(new String[] {"D"});
    StringsGetter e = new E();
    assertThat(e.getStrings()).isEqualTo(new String[] {"E"});
  }

  @Test
  public void testSafeConstClass() {
    String s = ModelConverter.convert(A.class);
    assertThat(s).isNotEqualTo("");
    s = ModelConverter.convert(B.class);
    assertThat(s).isNotEqualTo("");
    s = ModelConverter.convert(C.class);
    assertThat(s).isNotEqualTo("");
  }
}
