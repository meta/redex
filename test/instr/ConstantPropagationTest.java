/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package redex;

import java.util.Random;

import static org.assertj.core.api.Assertions.*;

import org.junit.Before;
import org.junit.Test;

import com.facebook.redexinline.ForceInline;

// A class with two constructors whose field initializers store the default
// values allocation already wrote.
class TwoCtors {
  int count = 0;
  Object last = null;

  // CHECK: method: direct redex.TwoCtors.<init>:()void
  // PRECHECK: iput {{.*}} redex.TwoCtors.count:int
  // POSTCHECK-NOT: iput
  // CHECK: return-void
  TwoCtors() {}

  TwoCtors(int start) {
    count = start;
  }
}

class InitCallingBase {
  InitCallingBase() {
    init();
  }

  void init() {}
}

// `InitCallingBase()` calls `init()` on `this`, which stores 5 into `x`
// before the initializer of `x` runs, so the initializer's store of 0 is not
// redundant.
class InitOverridingSub extends InitCallingBase {
  int x = 0;

  // CHECK: method: direct redex.InitOverridingSub.<init>:()void
  // CHECK: invoke-direct {{.*}} redex.InitCallingBase.<init>:()void
  // CHECK: iput {{.*}} redex.InitOverridingSub.x:int
  // CHECK: return-void
  InitOverridingSub() {}

  @Override
  void init() {
    x = 5;
  }
}

// `a`'s initializer reads `b` before `b`'s initializer stores 2 into it.
class ReadBeforeInit {
  int a = this.b + 1;
  int b = 2;

  // CHECK: method: direct redex.ReadBeforeInit.<init>:()void
  // PRECHECK: iget {{.*}} redex.ReadBeforeInit.b:int
  // POSTCHECK-NOT: iget
  // CHECK: iput {{.*}} redex.ReadBeforeInit.a:int
  // CHECK: iput {{.*}} redex.ReadBeforeInit.b:int
  // CHECK: return-void
  ReadBeforeInit() {}
}

public class ConstantPropagationTest {

  // use getRandom* if need to prevent constant folding. Use a fixed seed to
  // ensure test consistency.
  private final Random random = new Random(0L);
  private int getRandomInt() {
    return random.nextInt();
  }
  private long getRandomLong() {
    return random.nextLong();
  }

  // use MethodInline so redex sees these constants but `javac` and d8 do not
  @ForceInline
  long getLong() {
    return 0x0002000300040005L;
  }

  @ForceInline
  long getLong2() { return 0x0002000300040006L; }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_long
  @Test
  public void if_long() {
    long x = getLong();
    int y;
    // PRECHECK: cmp-long {{.*}}
    // PRECHECK: if-lez {{.*}}
    // POSTCHECK: cmp-long {{.*}}
    // POSTCHECK-NOT: if-lez {{.*}}
    if (x > 0x0001000200030004L) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  long getNegLong() {
    return 0x0000000fffffffffL;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_negative_long
  @Test
  public void if_negative_long() {
    long x = getNegLong();
    int y;
    // PRECHECK: cmp-long {{.*}}
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK: cmp-long {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == -1L) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(0);
    // CHECK: return-void
  }

  float getFloat1() {
    return 3.0f;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_float1
  @Test
  public void if_float1() {
    float x = getFloat1();
    int y;
    // PRECHECK: cmpg-float {{.*}}
    // PRECHECK: if-gtz {{.*}}
    // POSTCHECK: cmpg-float {{.*}}
    // POSTCHECK-NOT: if-gtz {{.*}}
    if (x <= 4.5f) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  float getFloat2() {
    return 2.25f;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_float2
  @Test
  public void if_float2() {
    float x = getFloat2();
    int y;
    // PRECHECK: cmpl-float {{.*}}
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK: cmpl-float {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == 2.25f) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  double getDouble1() {
    return 3.0;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_double1
  @Test
  public void if_double1() {
    double x = getDouble1();
    int y;
    // PRECHECK: cmpg-double {{.*}}
    // PRECHECK: if-gtz {{.*}}
    // POSTCHECK: cmpg-double {{.*}}
    // POSTCHECK-NOT: if-gtz {{.*}}
    if (x <= 4.5) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  double getDouble2() {
    return 2.26;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_double2
  @Test
  public void if_double2() {
    double x = getDouble2();
    int y;
    // PRECHECK: cmpl-double {{.*}}
    // PRECHECK: if-ltz {{.*}}
    // POSTCHECK: cmpl-double {{.*}}
    // POSTCHECK-NOT: if-ltz {{.*}}
    if (x >= 2.27) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(0);
    // CHECK: return-void
  }

  private int neg1() {
    return -1;
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_plus_one
  @Test
  public void if_plus_one() {
    int x = neg1();
    // PRECHECK: add-int/lit8 {{.*}}
    // POSTCHECK-NOT: add-int/lit8 {{.*}}
    x++;
    int y;
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == 0) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  private int one() {
    return 1;
  }

  private int two() {
    return 2;
  }

  private long two_long() { return 2; }

  private int three() { return 3; }

  private int nine() { return 9; }

  private int sixteen() {
    return 16;
  }

  private long sixteen_long() { return 16; }

  // This test intentionally does not use the same constant literal more than
  // once. The reason is that d8 will load that constant and re-use the
  // register rather than using a *-int/lit instruction.

  // CHECK: method: virtual redex.ConstantPropagationTest.if_plus_two
  @Test
  public void if_plus_two() {
    int x = one();
    // PRECHECK: add-int/lit8 {{.*}}
    // POSTCHECK-NOT: add-int/lit8 {{.*}}
    x += 2;
    int y;
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == 3) {
      y = 32;
    } else {
      y = 0;
    }
    assertThat(y).isEqualTo(32);
    // CHECK: return-void
  }

  private int max_val() { return Integer.MAX_VALUE; }

  // CHECK: method: virtual redex.ConstantPropagationTest.overflow
  @Test
  public void overflow() {
    int x = max_val();
    // PRECHECK: add-int/lit8 {{.*}}
    // POSTCHECK-NOT: add-int/lit8 {{.*}}
    x++;
    assertThat(x).isEqualTo(Integer.MIN_VALUE);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_lit_minus
  @Test
  public void if_lit_minus() {
    int x = one();
    // PRECHECK: rsub-int/lit8 {{.*}}
    // POSTCHECK-NOT: rsub-int/lit8 {{.*}}
    int y = 5 - x;
    int z;
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (y == 4) {
      z = 42;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(42);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_multiply_lit_const
  @Test
  public void if_multiply_lit_const() {
    int x = two();
    // PRECHECK: mul-int/lit8 {{.*}}
    // POSTCHECK-NOT: mul-int/lit8 {{.*}}
    int y = 42 * x;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 84) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual
  // redex.ConstantPropagationTest.if_multiply_large_lit_const
  @Test
  public void if_multiply_large_lit_const() {
    int x = two();
    // PRECHECK: mul-int/lit16 {{.*}}
    // POSTCHECK-NOT: mul-int/lit16 {{.*}}
    int y = 32767 * x;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 65534) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_shl_lit_const
  @Test
  public void if_shl_lit_const() {
    int x = two();
    // PRECHECK: shl-int/lit8 {{.*}}
    // POSTCHECK-NOT: shl-int/lit8 {{.*}}
    int y = x << 2;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 8) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_shr_lit_const
  @Test
  public void if_shr_lit_const() {
    int x = sixteen();
    // PRECHECK: shr-int/lit8 {{.*}}
    // POSTCHECK-NOT: shr-int/lit8 {{.*}}
    int y = x >> 2;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 4) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_ushr_lit_const
  @Test
  public void if_ushr_lit_const() {
    int x = neg1() * 16;
    // PRECHECK: ushr-int/lit8 {{.*}}
    // POSTCHECK-NOT: ushr-int/lit8 {{.*}}
    int y = x >>> 5;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 134217727) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_modulo_3
  @Test
  public void if_modulo_3() {
    int x = sixteen();
    // PRECHECK: rem-int/lit8 {{.*}}
    // POSTCHECK-NOT: rem-int/lit8 {{.*}}
    int y = x % 3;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (y == 1) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  private int blue_color_code() {
    return 0xFF0000FF;
  }

  // CHECK: method: virtual
  // redex.ConstantPropagationTest.if_truncating_left_shift
  @Test
  public void if_truncating_left_shift() {
    int x = blue_color_code();
    // PRECHECK: shl-int/lit8 {{.*}}
    // POSTCHECK-NOT: shl-int/lit8 {{.*}}
    int v = x << 8;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (v == 0x0000FF00) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_ushr_neg_val
  @Test
  public void if_ushr_neg_val() {
    int x = blue_color_code();
    // PRECHECK: ushr-int/lit8 {{.*}}
    // POSTCHECK-NOT: ushr-int/lit8 {{.*}}
    int v = x >>> 8;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    if (v == 0x00FF0000) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_div_by_zero
  @Test
  public void if_div_by_zero() {
    int x = one();
    int y = 0;
    int z = 3;
    try {
      if (x == 1) {
        // PRECHECK: div-int/2addr {{.*}}
        // POSTCHECK: div-int/2addr {{.*}}
        y = x / 0;
        z = 0;
      }
    } catch (Exception e) {
      z = 1;
    }
    assertThat(y).isEqualTo(0);
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_div_by_two
  @Test
  public void if_div_by_two() {
    int x = sixteen();
    // PRECHECK: div-int/lit8 {{.*}}
    // POSTCHECK-NOT: div-int/lit8 {{.*}}
    int y = x / 2;
    int z;
    if (y == 8) {
      z = 1;
    } else {
      z = 0;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.if_switch
  @Test
  public void if_switch() {
    int x = sixteen();
    // PRECHECK: div-int/lit8 {{.*}}
    // POSTCHECK-NOT: div-int/lit8 {{.*}}
    int y = x / 2;
    int z;
    // PRECHECK: if-{{.*}}
    // POSTCHECK-NOT: if-{{.*}}
    switch (y) {
    case 8:
      z = 1;
      break;
    default:
      z = 0;
      break;
    }
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_add
  @Test
  public void binop_add() {
    int x = sixteen();
    // PRECHECK: add-int{{.*}}
    // POSTCHECK-NOT: add-int{{.*}}
    int y = one();
    int z = x + y;
    assertThat(z).isEqualTo(17);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_sub
  @Test
  public void binop_sub() {
    int x = sixteen();
    // PRECHECK: sub-int{{.*}}
    // POSTCHECK-NOT: sub-int{{.*}}
    int y = one();
    int z = y - x;
    assertThat(z).isEqualTo(-15);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_mul
  @Test
  public void binop_mul() {
    int x = sixteen();
    // PRECHECK: mul-int{{.*}}
    // POSTCHECK-NOT: mul-int{{.*}}
    int y = two();
    int z = x * y;
    assertThat(z).isEqualTo(32);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_div
  @Test
  public void binop_div() {
    int x = sixteen();
    // PRECHECK: div-int{{.*}}
    // POSTCHECK-NOT: div-int{{.*}}
    int y = two();
    int z = x / y;
    assertThat(z).isEqualTo(8);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_rem
  @Test
  public void binop_rem() {
    int x = sixteen();
    // PRECHECK: rem-int{{.*}}
    // POSTCHECK-NOT: rem-int{{.*}}
    int y = three();
    int z = y % x;
    assertThat(z).isEqualTo(3);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_and
  @Test
  public void binop_and() {
    int x = nine();
    // PRECHECK: and-int{{.*}}
    // POSTCHECK-NOT: and-int{{.*}}
    int y = three();
    int z = x & y;
    assertThat(z).isEqualTo(1);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_or
  @Test
  public void binop_or() {
    int x = nine();
    // PRECHECK: or-int{{.*}}
    // POSTCHECK-NOT: or-int{{.*}}
    int y = three();
    int z = y | x;
    assertThat(z).isEqualTo(11);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_xor
  @Test
  public void binop_xor() {
    int x = nine();
    // PRECHECK: xor-int{{.*}}
    // POSTCHECK-NOT: xor-int{{.*}}
    int y = three();
    int z = x ^ y;
    assertThat(z).isEqualTo(10);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_and_non_const_lit
  @Test
  public void binop_and_non_const_lit() {
    int x = getRandomInt();
    // CHECK: and-int/lit{{.*}}
    x &= ~2;  // x's 2nd bit is 0
    int y = 6;  // 110
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_or_non_const_lit
  @Test
  public void binop_or_non_const_lit() {
    int x = getRandomInt();
    // CHECK: or-int/lit{{.*}}
    x |= 2;  // x's 2nd bit is 1
    int y = 4;  // 100
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_xor_non_const_lit
  @Test
  public void binop_xor_non_const_lit() {
    int x = getRandomInt();
    // CHECK: or-int/lit{{.*}}
    x |= 2;
    // CHECK: xor-int/lit{{.*}}
    x ^= 2;  // x's 2nd bit is 0
    int y = 6;  // 110
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_ushr_non_const_lit
  @Test
  public void binop_ushr_non_const_lit() {
    int x = getRandomInt() | 16;
    // CHECK: ushr-int/lit8{{.*}}
    int z = x >>> 2;  // 3rd bit is 1
    int y = getRandomInt() & ~4;  // 3rd bit is 0
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_shr_non_const_lit
  @Test
  public void binop_shr_non_const_lit() {
    int x = getRandomInt() | 16;
    // CHECK: shr-int/lit8{{.*}}
    int z = x >> 2;  // 3rd bit is 1
    int y = getRandomInt() & ~4;  // 3rd bit is 0
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);

    x = getRandomInt() | Integer.MIN_VALUE;
    // CHECK: shr-int/lit8{{.*}}
    z = x >> 1;
    y = getRandomInt() & Integer.MAX_VALUE;  // highest bit is 0
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_shl_non_const_lit
  @Test
  public void binop_shl_non_const_lit() {
    int x = getRandomInt() | 2;
    // CHECK: shl-int/lit8{{.*}}
    int z = x << 2;  // 4th bit is 1
    int y = getRandomInt() & ~8;  // 4th bit is 0
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_and_non_const
  @Test
  public void binop_and_non_const() {
    int x = getRandomInt();
    int z = getRandomInt() & ~2;
    // CHECK: and-int/2addr {{.*}}
    x &= z;  // x's 2nd bit is 0
    int y = 6;  // 110
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_or_non_const
  @Test
  public void binop_or_non_const() {
    int x = getRandomInt();
    int z = getRandomInt() | 2;
    // CHECK: or-int/2addr {{.*}}
    x |= z;  // x's 2nd bit is 1
    int y = 4;  // 100
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_xor_non_const
  @Test
  public void binop_xor_non_const() {
    int x = getRandomInt();
    int z = getRandomInt() | 2;
    // CHECK: or-int/lit8 {{.*}}
    x |= 2;
    // CHECK: xor-int/2addr {{.*}}
    x ^= z;  // x's 2nd bit is 0
    int y = 6;  // 110
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // Not adding unop_not_non_const here, because it seems like x = ~x is always
  // compiled to "xor-int/lit8 v0, v0, -1", which is not what we want to test.

  // Not adding binop_{ushr,shr,shl}_non_const here, because there's no easy way to
  // elicit the non-literals version of ushr-int, shr-int, and shl-int.

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_add_long
  @Test
  public void binop_add_long() {
    long x = getLong();
    // PRECHECK: add-long{{.*}}
    // POSTCHECK-NOT: add-long{{.*}}
    long y = getLong2();
    long z = x + y;
    assertThat(z).isEqualTo(1125925677170699L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_sub_long
  @Test
  public void binop_sub_long() {
    long x = getLong();
    // PRECHECK: sub-long{{.*}}
    // POSTCHECK-NOT: sub-long{{.*}}
    long y = two_long();
    long z = y - x;
    assertThat(z).isEqualTo(-0x0002000300040003L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_mul_long
  @Test
  public void binop_mul_long() {
    long x = sixteen_long();
    // PRECHECK: mul-long{{.*}}
    // POSTCHECK-NOT: mul-long{{.*}}
    long y = getLong();
    long z = y * x;
    assertThat(z).isEqualTo(9007405417365584L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_div_long
  @Test
  public void binop_div_long() {
    long x = getLong();
    // PRECHECK: div-long{{.*}}
    // POSTCHECK-NOT: div-long{{.*}}
    long y = two_long();
    long z = x / y;
    assertThat(z).isEqualTo(281481419292674L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_rem_long
  @Test
  public void binop_rem_long() {
    long x = getLong();
    // PRECHECK: rem-long{{.*}}
    // POSTCHECK-NOT: rem-long{{.*}}
    long y = sixteen_long();
    long z = x % y;
    assertThat(z).isEqualTo(5);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_rem_long2
  @Test
  public void binop_rem_long2() {
    long x = getLong();
    // PRECHECK: rem-long{{.*}}
    // POSTCHECK-NOT: rem-long{{.*}}
    long y = getLong2();
    long z = x % y;
    assertThat(z).isEqualTo(562962838585349L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_and_long
  @Test
  public void binop_and_long() {
    long x = getLong();
    // PRECHECK: and-long{{.*}}
    // POSTCHECK-NOT: and-long{{.*}}
    long y = getLong2();
    long z = x & y;
    assertThat(z).isEqualTo(562962838585348L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_or_long
  @Test
  public void binop_or_long() {
    long x = getLong();
    // PRECHECK: or-long{{.*}}
    // POSTCHECK-NOT: or-long{{.*}}
    long y = getLong2();
    long z = x | y;
    assertThat(z).isEqualTo(562962838585351L);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_xor_long
  @Test
  public void binop_xor_long() {
    long x = getLong();
    // PRECHECK: xor-long{{.*}}
    // POSTCHECK-NOT: xor-long{{.*}}
    long y = getLong2();
    long z = x ^ y;
    assertThat(z).isEqualTo(3L);
    // CHECK: return-void
  }

  long get_long_max() { return Long.MAX_VALUE; }

  long one_long() { return 1; }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_add_long_overflow
  @Test
  public void binop_add_long_overflow() {
    long x = get_long_max();
    long y = one_long();
    // PRECHECK: add-long{{.*}}
    // POSTCHECK-NOT: add-long{{.*}}
    long z = x + y;
    assertThat(z).isEqualTo(Long.MIN_VALUE);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_and_long_non_const
  @Test
  public void binop_and_long_non_const() {
    long x = getRandomLong();
    // CHECK: and-long{{.*}}
    x &= ~2L;  // x's 2nd bit is 0
    long y = 6L;  // 110
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_or_long_non_const
  @Test
  public void binop_or_long_non_const() {
    long x = getRandomLong();
    // CHECK: or-long{{.*}}
    x |= 2L;  // x's 2nd bit is 1
    long y = 4L;  // 100
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_xor_long_non_const
  @Test
  public void binop_xor_long_non_const() {
    long x = getRandomLong();
    // CHECK: or-long{{.*}}
    x |= 2L;
    // CHECK: xor-long{{.*}}
    x ^= 2L;  // x's 2nd bit is 0
    long y = 6L;  // 110
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == y) {
      System.out.println("Unreachable x == y");
    }
    assertThat(x).isNotEqualTo(y);
    // CHECK: return-void
  }

  // Not adding unop_not_long_non_const here, because it seems like x = ~x is
  // always compiled to "const-wide/16 v1 -1; xor-long/2addr v0, v1", which is
  // not what we want to test.

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_ushr_long_non_const
  @Test
  public void binop_ushr_long_non_const() {
    long x = getRandomLong() | 16L;
    // CHECK: ushr-long{{.*}}
    long z = x >>> 2;  // 3rd bit is 1
    long y = getRandomLong() & ~4L;  // 3rd bit is 0
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_shr_long_non_const
  @Test
  public void binop_shr_long_non_const() {
    long x = getRandomLong() | 16L;
    // CHECK: shr-long{{.*}}
    long z = x >> 2;  // 3rd bit is 1
    long y = getRandomLong() & ~4L;  // 3rd bit is 0
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);

    x = getRandomLong() | Long.MIN_VALUE;
    // CHECK: shr-long{{.*}}
    z = x >> 1;
    y = getRandomLong() & Long.MAX_VALUE;  // highest bit is 0
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.binop_shl_long_non_const
  @Test
  public void binop_shl_long_non_const() {
    long x = getRandomLong() | 2L;
    // CHECK: shl-long{{.*}}
    long z = x << 2;  // 4th bit is 1
    long y = getRandomLong() & ~8L;  // 4th bit is 0
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (z == y) {
      System.out.println("Unreachable z == y");
    }
    assertThat(z).isNotEqualTo(y);
    // CHECK: return-void
  }

  // CHECK: method: virtual redex.ConstantPropagationTest.low6bits_int
  @Test
  public void low6bits_int() {
    int x = 3;  // 0b11
    if (getRandomInt() > 0) {
      x = 76;  // 0b1001100
    }

    // x is known to be in the range of 3 to 76, and x's individual bits of the
    // lowest 4 bits are unknown.  But low6bits can tell x's lowest 4 bits are
    // either 0b0011 or 0b1100.
    // PRECHECK: if-ne {{.*}}
    // POSTCHECK-NOT: if-ne {{.*}}
    if (x == 4) {
      System.out.println("Unreachable x == 4");
    }
    assertThat(x).isNotEqualTo(4);

    // CHECK: if-ne {{.*}}
    if (x == 67) {  // 0b1000011
      System.out.println("Reachable x == 67");
    }
    assertThat(x).isNotEqualTo(4);
    // CHECK: return-void
  }
  // CHECK: method: virtual redex.ConstantPropagationTest.low6bits_long
  @Test
  public void low6bits_long() {
    long x = 3;  // 0b11
    if (getRandomInt() > 0) {
      x = 76;  // 0b1001100
    }

    // x is known to be in the range of 3 to 76, and x's individual bits of the
    // lowest 4 bits are unknown.  But low6bits can tell x's lowest 4 bits are
    // either 0b0011 or 0b1100.
    // PRECHECK: if-nez {{.*}}
    // POSTCHECK-NOT: if-nez {{.*}}
    if (x == 4) {
      System.out.println("Unreachable x == 4");
    }
    assertThat(x).isNotEqualTo(4);

    // CHECK: if-nez {{.*}}
    if (x == 67) {  // 0b1000011
      System.out.println("Reachable x == 67");
    }
    assertThat(x).isNotEqualTo(4);
    // CHECK: return-void
  }

  @Test
  public void constructorFieldsStartAtZero() {
    TwoCtors empty = new TwoCtors();
    assertThat(empty.count).isEqualTo(0);
    assertThat(empty.last).isNull();
    assertThat(new TwoCtors(3).count).isEqualTo(3);
  }

  @Test
  public void superclassConstructorMayStoreToSubclassField() {
    assertThat(new InitOverridingSub().x).isEqualTo(0);
  }

  @Test
  public void initializerReadsLaterFieldAsZero() {
    ReadBeforeInit r = new ReadBeforeInit();
    assertThat(r.a).isEqualTo(1);
    assertThat(r.b).isEqualTo(2);
  }
}
