/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redex.test.instr;

import org.junit.Test;
import static org.assertj.core.api.Assertions.assertThat;

class Model {
  public int field;

  public static Builder newBuilder() {
    return new Builder();
  }

  public static class Builder {
    int field = 0;

    public void set_field(int f) {
      field = f;
    }

    public Model build() {
      Model obj = new Model();
      obj.field = field;
      return obj;
    }
  }
}

class LoopModel {
  public static class Builder {
    int field;
    long wide;
    Object reference;
  }
}

class PreviousModel {
  public static class Builder {
    int field;
  }
}

public class RemoveBuilderPatternTest {

  @Test
  public void testLoopBuilderStartsWithDefaultInt() {
    int sum = 0;
    for (int i = 0; i < 2; i++) {
      LoopModel.Builder builder = new LoopModel.Builder();
      if (i == 0) {
        builder.field = 5;
      }
      sum += builder.field;
    }
    assertThat(sum).isEqualTo(5);
  }

  @Test
  public void testLoopBuilderStartsWithDefaultWide() {
    long sum = 0;
    for (int i = 0; i < 2; i++) {
      LoopModel.Builder builder = new LoopModel.Builder();
      if (i == 0) {
        builder.wide = 7L;
      }
      sum += builder.wide;
    }
    assertThat(sum).isEqualTo(7L);
  }

  @Test
  public void testLoopBuilderStartsWithDefaultReference() {
    int nonNull = 0;
    for (int i = 0; i < 2; i++) {
      LoopModel.Builder builder = new LoopModel.Builder();
      if (i == 0) {
        builder.reference = new Object();
      }
      if (builder.reference != null) {
        nonNull++;
      }
    }
    assertThat(nonNull).isEqualTo(1);
  }

  @Test
  public void testConditionalLoopBuilderStartsWithDefaultFields() {
    int sum = 0;
    for (int i = 0; i < 3; i++) {
      LoopModel.Builder builder = null;
      if (i != 1) {
        builder = new LoopModel.Builder();
        if (i == 0) {
          builder.field = 5;
        }
      }
      if (builder != null) {
        sum += builder.field;
      }
    }
    assertThat(sum).isEqualTo(5);
  }

  @Test
  public void testPreviousLoopBuilderKeepsItsFields() {
    PreviousModel.Builder previous = null;
    int sum = 0;
    for (int i = 0; i < 2; i++) {
      PreviousModel.Builder builder = new PreviousModel.Builder();
      builder.field = i + 1;
      if (previous != null) {
        sum += previous.field * 10;
      }
      sum += builder.field;
      previous = builder;
    }
    assertThat(sum).isEqualTo(13);
  }

  @Test
  public void testRemoveSimpleBuilder() {
    Model.Builder builder = Model.newBuilder();
    int data = 1;
    builder.set_field(data);
    Model obj = builder.build();
    assertThat(obj.field).isEqualTo(1);
  }
}
