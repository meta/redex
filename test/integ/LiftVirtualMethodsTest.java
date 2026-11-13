/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

// The shapes below mirror D8's desugaring of a default interface method:
// LiftI_CC stands in for the `LiftI$-CC` companion class, and every
// implementing class gets its own forwarder to it.
interface LiftI {
  int m(int x);
}

final class LiftI_CC {
  static int m(LiftI self, int x) {
    return x + 1;
  }
}

// Both forwarders move into UBase; UOther inherits a method nothing calls.
class UBase {}
class UA extends UBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class UB extends UBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class UOther extends UBase {}

// One subclass differs: the identical pair moves into MBase, and MC keeps its
// own method as an override.
class MBase {}
class MA extends MBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class MB extends MBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class MC extends MBase implements LiftI {
  public int m(int x) {
    return x + 2;
  }
}

// An ancestor already declares m: lifting into ABase would make AOther
// inherit a different method than AncestorTop.m.
class AncestorTop {
  public int m(int x) {
    return 7;
  }
}
class ABase extends AncestorTop {}
class AA extends ABase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class AB extends ABase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class AOther extends ABase {}

// A subclass has a static method with the same signature.
class SBase {}
class SA extends SBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class SB extends SBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class SC extends SBase {
  static int m(int x) {
    return 0;
  }
}

// Two levels: TBase gets the method from TA and TB, and the identical copies
// under TMid, which declares none, go with it.
class TBase {}
class TMid extends TBase {}
class TA extends TBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class TB extends TBase implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class TM1 extends TMid implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}
class TM2 extends TMid implements LiftI {
  public int m(int x) {
    return LiftI_CC.m(this, x);
  }
}

// RIter newly inherits remove() from RBase, but it implements Iterator, whose
// default remove() it reaches today through invoke-interface.
interface LiftR {
  void remove();
}

final class LiftR_CC {
  static void remove(LiftR self) {}
}

class RBase {}
class RA extends RBase implements LiftR {
  public void remove() {
    LiftR_CC.remove(this);
  }
}
class RB extends RBase implements LiftR {
  public void remove() {
    LiftR_CC.remove(this);
  }
}
class RIter extends RBase implements java.util.Iterator<Object> {
  public boolean hasNext() {
    return false;
  }

  public Object next() {
    return null;
  }
}

// EdgeBase gets m from EdgeA and EdgeB, and EdgeDeep's copy goes with it, since
// the path from EdgeBase to EdgeDeep holds only copies. EdgeShield's different
// m stays as an override and keeps the copies below it.
abstract class EdgeBase {}
class EdgeA extends EdgeBase implements LiftI {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class EdgeB extends EdgeBase implements LiftI {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class EdgeDeep extends EdgeA {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class EdgeInherited extends EdgeDeep {}
class EdgeShield extends EdgeA {
  public int m(int x) { return x + 2; }
}
class EdgeShieldDeep1 extends EdgeShield {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class EdgeShieldDeep2 extends EdgeShield {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class EdgeGap extends EdgeBase {}
class EdgeGap2 extends EdgeBase {}
class EdgeGap3 extends EdgeBase {}
abstract class EdgeGapLeaf extends EdgeGap {}
class EdgeCaller {
  static int call(EdgeB receiver, int x) { return receiver.m(x); }
}

// LBase gets m from LA and LB. LA's subclasses override m with code of their
// own, so after the lift their group targets LA, which no longer declares m.
class LBase {}
class LA extends LBase implements LiftI {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class LB extends LBase implements LiftI {
  public int m(int x) { return LiftI_CC.m(this, x); }
}
class LP extends LA {
  public int m(int x) { return x + 3; }
}
class LQ extends LA {
  public int m(int x) { return x + 3; }
}
class LCaller {
  static int call(LA receiver, int x) { return receiver.m(x); }
}
