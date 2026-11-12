/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

abstract class TypedCaptureBase {
  public abstract ClassMergingFieldTypesTest.CapturePayload read();
}

final class TypedCaptureA extends TypedCaptureBase {
  public ClassMergingFieldTypesTest.CapturePayload capture;
  public TypedCaptureA(ClassMergingFieldTypesTest.CapturePayload capture) {
    this.capture = capture;
  }
  public ClassMergingFieldTypesTest.CapturePayload read() { return capture; }
}

final class TypedCaptureB extends TypedCaptureBase {
  public ClassMergingFieldTypesTest.CapturePayload capture;
  public TypedCaptureB(ClassMergingFieldTypesTest.CapturePayload capture) {
    this.capture = capture;
  }
  public ClassMergingFieldTypesTest.CapturePayload read() { return capture; }
}

abstract class MixedCaptureBase {
  public abstract Object read();
}

final class MixedCaptureA extends MixedCaptureBase {
  public ClassMergingFieldTypesTest.CapturePayload capture;
  public MixedCaptureA(ClassMergingFieldTypesTest.CapturePayload capture) {
    this.capture = capture;
  }
  public Object read() { return capture; }
}

final class MixedCaptureB extends MixedCaptureBase {
  public Object capture;
  public MixedCaptureB(Object capture) { this.capture = capture; }
  public Object read() { return capture; }
}

abstract class ArrayCaptureBase {
  public abstract ClassMergingFieldTypesTest.CapturePayload[][] read();
}

final class ArrayCaptureA extends ArrayCaptureBase {
  public ClassMergingFieldTypesTest.CapturePayload[][] capture;
  public ArrayCaptureA(ClassMergingFieldTypesTest.CapturePayload[][] capture) {
    this.capture = capture;
  }
  public ClassMergingFieldTypesTest.CapturePayload[][] read() { return capture; }
}

final class ArrayCaptureB extends ArrayCaptureBase {
  public ClassMergingFieldTypesTest.CapturePayload[][] capture;
  public ArrayCaptureB(ClassMergingFieldTypesTest.CapturePayload[][] capture) {
    this.capture = capture;
  }
  public ClassMergingFieldTypesTest.CapturePayload[][] read() { return capture; }
}

public class ClassMergingFieldTypesTest {

  public static final class CapturePayload {
    public final int value;
    public CapturePayload(int value) { this.value = value; }
  }

  @Test
  public void testUnanimousCaptures() {
    CapturePayload first = new CapturePayload(7);
    CapturePayload second = new CapturePayload(9);
    TypedCaptureA a = new TypedCaptureA(first);
    TypedCaptureB b = new TypedCaptureB(second);
    assertThat(a.read()).isSameAs(first);
    assertThat(b.read()).isSameAs(second);
    a.capture = second;
    b.capture = null;
    assertThat(a.read()).isSameAs(second);
    assertThat(b.read()).isNull();
  }

  @Test
  public void testMixedCaptures() {
    CapturePayload payload = new CapturePayload(7);
    MixedCaptureA a = new MixedCaptureA(payload);
    MixedCaptureB b = new MixedCaptureB("opaque");
    assertThat(a.read()).isSameAs(payload);
    assertThat(b.read()).isEqualTo("opaque");
    b.capture = payload;
    assertThat(b.read()).isSameAs(payload);
  }

  @Test
  public void testUnanimousArrayCaptures() {
    CapturePayload[][] values = {{new CapturePayload(7)}, null};
    ArrayCaptureA a = new ArrayCaptureA(values);
    ArrayCaptureB b = new ArrayCaptureB(null);
    assertThat(a.read()).isSameAs(values);
    assertThat(a.read()[0][0].value).isEqualTo(7);
    assertThat(a.read()[1]).isNull();
    assertThat(b.read()).isNull();
    b.capture = values;
    assertThat(b.read()).isSameAs(values);
  }
}
