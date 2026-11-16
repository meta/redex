/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package redex;

import static org.assertj.core.api.Assertions.assertThat;

import org.junit.Test;

// An input class already named redex.$EnumUtils makes OptimizeEnumsPass name its
// holders redex.$EnumUtils$u and redex.$EnumUtils$u$1.
// POSTCHECK-LABEL: class: redex.$EnumUtils$u //
// POSTCHECK: (PUBLIC, STATIC, FINAL) f0:java.lang.Integer
// POSTCHECK: (PUBLIC, STATIC, FINAL) f127:java.lang.Integer
// POSTCHECK-NOT: f128:java.lang.Integer
// POSTCHECK-LABEL: class: redex.$EnumUtils$u$1 //
// POSTCHECK: (PUBLIC, STATIC, FINAL) f128:java.lang.Integer
// POSTCHECK: (PUBLIC, STATIC, FINAL) f199:java.lang.Integer

class $EnumUtils {
  static int marker = 1;
}

// CHECK-LABEL: class: redex.WIDE
// CHECK-NEXT: Access flags:
// PRECHECK-NEXT: Superclass: java.lang.Enum
// POSTCHECK-NEXT: Superclass: java.lang.Object
enum WIDE {
  W0,
  W1,
  W2,
  W3,
  W4,
  W5,
  W6,
  W7,
  W8,
  W9,
  W10,
  W11,
  W12,
  W13,
  W14,
  W15,
  W16,
  W17,
  W18,
  W19,
  W20,
  W21,
  W22,
  W23,
  W24,
  W25,
  W26,
  W27,
  W28,
  W29,
  W30,
  W31,
  W32,
  W33,
  W34,
  W35,
  W36,
  W37,
  W38,
  W39,
  W40,
  W41,
  W42,
  W43,
  W44,
  W45,
  W46,
  W47,
  W48,
  W49,
  W50,
  W51,
  W52,
  W53,
  W54,
  W55,
  W56,
  W57,
  W58,
  W59,
  W60,
  W61,
  W62,
  W63,
  W64,
  W65,
  W66,
  W67,
  W68,
  W69,
  W70,
  W71,
  W72,
  W73,
  W74,
  W75,
  W76,
  W77,
  W78,
  W79,
  W80,
  W81,
  W82,
  W83,
  W84,
  W85,
  W86,
  W87,
  W88,
  W89,
  W90,
  W91,
  W92,
  W93,
  W94,
  W95,
  W96,
  W97,
  W98,
  W99,
  W100,
  W101,
  W102,
  W103,
  W104,
  W105,
  W106,
  W107,
  W108,
  W109,
  W110,
  W111,
  W112,
  W113,
  W114,
  W115,
  W116,
  W117,
  W118,
  W119,
  W120,
  W121,
  W122,
  W123,
  W124,
  W125,
  W126,
  W127,
  W128,
  W129,
  W130,
  W131,
  W132,
  W133,
  W134,
  W135,
  W136,
  W137,
  W138,
  W139,
  W140,
  W141,
  W142,
  W143,
  W144,
  W145,
  W146,
  W147,
  W148,
  W149,
  W150,
  W151,
  W152,
  W153,
  W154,
  W155,
  W156,
  W157,
  W158,
  W159,
  W160,
  W161,
  W162,
  W163,
  W164,
  W165,
  W166,
  W167,
  W168,
  W169,
  W170,
  W171,
  W172,
  W173,
  W174,
  W175,
  W176,
  W177,
  W178,
  W179,
  W180,
  W181,
  W182,
  W183,
  W184,
  W185,
  W186,
  W187,
  W188,
  W189,
  W190,
  W191,
  W192,
  W193,
  W194,
  W195,
  W196,
  W197,
  W198,
  W199;

  static boolean isLast(WIDE w) {
    return w == W199;
  }
}

public class EnumTransformSplitFallbackTest {
  @Test
  public void valuesAreTheSameObjectsAsTheConstants() {
    WIDE[] values = WIDE.values();
    assertThat(values.length).isEqualTo(200);
    assertThat(values[150] == WIDE.W150).isTrue();
    assertThat(WIDE.isLast(values[199])).isTrue();
    assertThat($EnumUtils.marker).isEqualTo(1);
  }
}
