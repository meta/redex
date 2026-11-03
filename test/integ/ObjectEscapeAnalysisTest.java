/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

public class ObjectEscapeAnalysisTest {
  public static String Foo;

  static class C {
    int x;
    int y;

    public C(int x, int y) {
      this.x = x;
      Foo = "inlinable side effect";
      this.y = y;
    }

    public int getX() {
      Foo = "another inlinable side effect";
      return this.x;
    }

    public int getY() {
      Foo = "yet another inlinable side effect";
      return this.y;
    }
  }

  static void does_not_leak(Object o) {}

  public static int reduceTo42A() {
    C c = new C(23, 19);
    does_not_leak(c);
    return c.getX() + c.getY();
  }

  static class D {
    int x;

    public D(int x) {
      this.x = x;
    }

    public static D allocator(int x) {
      return new D(x);
    }

    public int getX() {
      return this.x;
    }
  }

  public static int reduceTo42B() {
    D d = D.allocator(42);
    return d.getX();
  }

  static class E {
    int x;

    public E(int x) {
      this.x = x;
    }

    public int getX() {
      return this.x;
    }
  }

  static class F {
    int x;

    public F(int x) {
      this.x = x;
    }

    public int getX() {
      return this.x;
    }
  }

  public static int reduceTo42C() {
    E e = new E(21);
    F f = new F(21);
    return e.getX() + f.getX();
  }

  abstract static class Base {
    public Base() {}

    public int helper() {
      return getX();
    }

    public abstract int getX();

    public int getSomething() {
      return 1;
    }
  }

  static class Derived extends Base {
    int x;

    public Derived(int x) {
      this.x = x;
    }

    public /* override */ int getX() {
      return this.x;
    }

    public /* override */ int getSomething() {
      return 1 + super.getSomething();
    }
  }

  static class Derived2 extends Base {
    int x;

    public Derived2(int x) {
      this.x = x;
    }

    public /* override */ int getX() {
      return this.x - 2;
    }
  }

  public static int reduceTo42D() {
    Derived d = new Derived(42);
    return d.getX();
  }

  public static int reduceTo42WithOverrides() {
    Base b = new Derived(42);
    return b.getX();
  }

  public static int reduceTo42WithOverrides2() {
    Base b = new Derived(21);
    Base b2 = new Derived2(23);

    return b.helper() + b2.helper();
  }

  public static int reduceTo42WithInvokeSuper() {
    Derived d = new Derived(40);
    return d.getX() + d.getSomething();
  }

  static class G {
    static Object leak;
    static Object leak2;

    public G() {
      leak = this;
    }

    public G(H h) {
      leak = this;
      leak2 = h;
    }

    public int getX() {
      return 42;
    }
  }

  public static int doNotReduceTo42A() {
    G g = new G();
    return g.getX();
  }

  static class H {
    public H() {}

    public int getX() {
      return 42;
    }
  }

  public static int doNotReduceTo42B() {
    H h = new H();
    G g = new G(h);
    return h.getX();
  }

  static class I {
    int x;

    public I(int x) {
      this.x = x;
    }

    public static I allocator(int x) {
      return new I(x);
    }

    public int getX() {
      return this.x;
    }

    public I id() {
      return this;
    }
  }

  public static int optionalReduceTo42(boolean b) {
    I i = b ? I.allocator(42) : null;
    return b ? i.getX() : 0;
  }

  public static int optionalReduceTo42Alt(boolean b) {
    I i = b ? I.allocator(42) : null;
    return i == null ? 0 : i.getX();
  }

  private static I optionalAllocator(boolean b) {
    I i = I.allocator(42);
    if (b) {
      i = null;
    }
    return i;
  }

  public static int optionalReduceTo42Override(boolean b) {
    I i = optionalAllocator(b);
    return i == null ? 0 : i.getX();
  }

  public static int optionalReduceTo42CheckCast(boolean b) {
    Object o = optionalAllocator(b);
    return ((I)o) == null ? 0 : ((I)o).getX();
  }

  public static int optionalReduceTo42SuppressNPE(boolean b) {
    I i = b ? I.allocator(42) : null;
    return i.getX();
  }

  public static boolean optionalReduceToBC(boolean b, boolean c) {
    I i = b ? I.allocator(42) : null;
    I j = null;
    if (c) { j = i; }
    return j instanceof Object;
  }

  public static int optionalLoopyReduceTo42() {
    I i = null;
    int c = 0;
    while (true) {
      if (c != 0) {
        if (c == 2) {
          return i.getX();
        }
        i = I.allocator(42);
      }
      c++;
    }
  }

  static class LoopFieldObject {
    int x;

    LoopFieldObject(int x) {
      this.x = x;
    }
  }

  public static int loopFieldAliasing() {
    LoopFieldObject prev = null;
    int sum = 0;
    for (int i = 1; i <= 2; i++) {
      LoopFieldObject cur = new LoopFieldObject(i);
      if (i == 2) {
        sum = prev.x;
      }
      prev = cur;
    }
    return sum;
  }

  static class LoopNullObject {
    int x;

    LoopNullObject(int x) {
      this.x = x;
    }
  }

  public static int loopNullTracking() {
    LoopNullObject prev = null;
    int sum = 0;
    for (int i = 1; i <= 2; i++) {
      LoopNullObject cur = new LoopNullObject(i);
      if (prev != null) {
        sum = prev.x * 10 + cur.x;
      }
      prev = cur;
    }
    return sum;
  }

  public static int independentObjects(int x) {
    I a = new I(x);
    I b = new I(x + 1);
    I c = new I(x + 2);
    I d = new I(x + 3);
    return a.x + b.x + c.x + d.x;
  }

  public static int independentObjectWithMultipleReturns(boolean b, int x) {
    I a = new I(x);
    if (b) {
      return a.x;
    }
    return a.x + 1;
  }

  public static int loopFieldAliasingWithCast() {
    Object prev = null;
    int sum = 0;
    for (int i = 1; i <= 2; i++) {
      LoopFieldObject cur = new LoopFieldObject(i);
      if (i == 2) {
        sum = ((LoopFieldObject) prev).x;
      }
      prev = cur;
    }
    return sum;
  }

  public static boolean objectIsNotNull() {
    I i = I.allocator(42);
    return i == null;
  }

  public static int reduceTo42WithCheckCast() {
    Object i = I.allocator(42);
    return ((I)i).getX();
  }

  public static int reduceTo42WithReturnedArg() {
    I i = I.allocator(42);
    i = i.id();
    return i.getX();
  }

  static class J {
    public J() {}
  }

  static class DontOptimizeFinalInInit {
    final int x;
    int y;

    DontOptimizeFinalInInit() {
      J j = new J();
      int x = read_x(j);
      this.x = 42;
      this.y = this.x; // must not use previously read value of x (even though x is final)
    }

    int read_x(J j) {
      return this.x;
    }
  }

  static class K {
    int x;
    static int X;

    static class CyclicStaticInitDependency {
      static int Y;

      static {
        Y = X;
      }
    }

    static {
      // Static initialization order matters.
      X = CyclicStaticInitDependency.Y;
    }

    public K(int x) {
      this.x = x;
    }

    public int getX() {
      return this.x;
    }
  }

  public static int reduceTo42WithInitClass() {
    K k = new K(42);
    return k.getX();
  }

  static class L {
    int x;

    public L(int x) {
      this.x = x;
    }

    public synchronized int getX() {
      return this.x;
    }
  }

  public static int reduceTo42WithMonitors() {
    L l = new L(42);
    synchronized (l) {
      return l.getX();
    }
  }

  static class M {
    int x;

    public M(int x) {
      this.x = x;
    }

    public void add(int other) {
      this.x += this.x * other;
      this.x += this.x * other;
      this.x += this.x * other;
    }

    public int get() {
      return this.x;
    }
  }

  public static int reduceTo42WithMultiples1(int x) {
    M m = new M(x);
    m.add(1);
    m.add(2);
    m.add(3);
    return m.get();
  }

  public static int reduceTo42WithMultiples2(int x) {
    M m = new M(x);
    m.add(1);
    m.add(2);
    m.add(3);
    return m.get();
  }

  public static class N {
    int x;

    public N(Builder builder) {
      this.x = builder.x;
    }

    public static void onlyUseInstanceField(Builder builder) {
      System.out.println(builder.x);
    }

    public static class Builder {
      public int x;

      public Builder(int x) {
        this.x = x;
      }
    }

    public int get() {
      return this.x;
    }
  }

  public static N reduceTo42WithExpandedCtor() {
    return new N(new N.Builder(42));
  }

  public static void reduceTo42WithExpandedMethod() {
    N.onlyUseInstanceField(new N.Builder(42));
  }

  static class O {
    int x;
    public static O instance;

    static {
      // This prevents O from being completely inlinable (everywhere).
      instance = new O(23);
    }

    public O(int x) {
      this.x = x;
    }

    public int getX() {
      return this.x;
    }

    public int getX4(int dummy_a, int dummy_b, int dummy_c, int dummy_d) {
      return this.x;
    }
  }

  public static int reduceTo42IncompleteInlinableType() {
    O o = new O(42);
    return o.getX();
  }

  public static int reduceTo42IncompleteInlinableTypeB() {
    // This object creation can be reduced
    O o = new O(42);
    // This one not.
    O.instance = new O(16);
    return o.getX();
  }

  public static O helper(boolean b) {
    // This completely reducible class D makes the helper into a root.
    D d = D.allocator(42);
    d.getX();
    return b ? new O(42) : new O(23);
  }

  public static int reduceIncompleteInlinableType(boolean b) {
    O o = helper(b);
    return o.getX4(1, 2, 3, 4);
  }

  public static class P {
    int x;

    public P(int x) {
      this.x = x;
    }

    public int getX() {
      return this.x;
    }

    protected void finalize() {}
  }

  public static int doNotReduceTo42Finalize() {
    // This object creation can NOT be reduced
    P p = new P(42);
    return p.getX();
  }

  public static class PDerived extends P{

    public PDerived(int x) {
      super(x);
    }

    public int getX() {
      return this.x;
    }
  }

  public static int doNotReduceTo42FinalizeDerived() {
    // This object creation can NOT be reduced
    PDerived p = new PDerived(42);
    return p.getX();
  }

  static class Q {
    public Q() {}

    static class QQ {}

    public static Q allocator() {
      // Creating QQ here makes this method itself a root...
      new QQ();
      // ... a root that also allocates and returns ...
      Q q = new Q();
      Object x = null;
      x.getClass();
      // ... except that the return will get dce'd
      return q;
    }
  }

  public static void nothingToReduce() {
    Q.allocator();
  }

  interface R {}

  static class S implements R {
    int x;

    public S(int x) {
      this.x = x;
    }

    public static S allocator(int x) {
      return new S(x);
    }
  }

  // The allocated type implements the tested interface, so the instance-of
  // must fold to true, not false.
  public static boolean reduceInstanceOfInterface() {
    Object s = S.allocator(42);
    return s instanceof R;
  }
}
