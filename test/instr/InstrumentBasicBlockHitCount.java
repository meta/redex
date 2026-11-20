/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;


import static org.assertj.core.api.Assertions.assertThat;

import java.io.InputStream;
import java.util.Random;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.HashMap;
import org.junit.Test;
import org.junit.Before;

import com.facebook.proguard.annotations.DoNotStrip;

import com.facebook.redextest.InstrumentBasicBlockAnalysis;
import com.facebook.redextest.MetadataParser;

@DoNotStrip
public class InstrumentBasicBlockHitCount {
  // Information taken from source dictionary and metadata
  // Index: 0
  // Stats Array Info:
  // - Offset within Stats Array: 8
  // - Number of Vectors: 0
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc01(int foo) {
    return 42;
  }

  // Index: 1
  // Stats Array Info:
  // - Offset within Stats Array: 10
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc02(int a, int b) {
    if (a > 0) {
      return a / b;
    } else {
      return a * b;
    }
  }

  // Index: 2
  // Stats Array Info:
  // - Offset within Stats Array: 13
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc03(int a, int b) {
    if (a > 0) {
      a++;
    }
    return a;
  }

  // Index: 3
  // Stats Array Info:
  // - Offset within Stats Array: 16
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [5,4,2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  @SuppressWarnings({"EmptyCatchBlock", "CatchGeneralException"})
  public static int testFunc04(int a, int b) {
    try {
      int[] arr = new int[10];
      arr[10] = a;
    } catch (Exception e) {
       throw e;
    }
    return (b % 2);
  }

  // Index: 4
  // Stats Array Info:
  // - Offset within Stats Array: 19
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [4,3,5,2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc05(int flag, int temp_var) {
    int z = 0;
    if (flag != 0) {
      System.out.println("It's True!!");
      z += 1;
      if (temp_var > 4) {
        System.out.println("Greater than 4");
        z += 1;
      } else {
        System.out.println("Couldnt make it to 4!, early return");
        z -= 1;
        return z;
      }
    } else {
      System.out.println("Not True :(");
      z -= 1;
    }
    System.out.println("After Test: " + temp_var);
    return z;
  }

  // Index: 5
  // Stats Array Info:
  // - Offset within Stats Array: 22
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [4,3,2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc06(int a, int b) {
    try {
      return a / b;
    } catch (ArithmeticException e) {
      System.out.println("ArithmeticException");
      return 13;
    }
  }

  // Index: 6
  // Stats Array Info:
  // - Offset within Stats Array: 25
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [9,8,7,6,4,3,2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static int testFunc07(int a, int b) {
    if (a % 2 == 0) {
      try {
        return a / b;
      } catch (IllegalArgumentException e) {
        throw new IllegalArgumentException("Exception: " + a + ": " + e.getMessage());
      }
    } else {
      try {
        return b / a;
      } catch (IllegalArgumentException e) {
        throw new IllegalArgumentException("Exception: " + b + ": " + e.getMessage());
      }
    }
  }

  // Index: 7
  // Stats Array Info:
  // - Offset within Stats Array: 28
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [9,10,12,11,8,7,6,5,4,3,2,1]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  @SuppressWarnings("CatchGeneralException")
  public static int testFunc08(int size, int index, int num) {
    try {
      int[] arr = new int[size];
      arr[index] = num / index;
      if (index % 2 == 0) {
        index = index * 2020;
        return arr[index];
      }
    } catch (ArrayIndexOutOfBoundsException e) {
      System.out.println("ArrayIndexOutOfBoundsException");
      return 7;
    } catch (ArithmeticException e) {
      System.out.println("ArithmeticException");
      return 13;
    } catch (Exception e) {
      System.out.println("Exception");
      throw e;
    }
    return 9;
  }

  // Index: 8
  // Stats Array Info:
  // - Offset within Stats Array: 31
  // - Number of Bit-Vectors: 4
  // - Bit-Vector 0: [43,44,45,46,47,48,49,50,51,52,53,54,55,3,2,1]
  // - Bit-Vector 1: [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
  // - Bit-Vector 2: [11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
  // - Bit-Vector 3: [4,5,6,7,8,9,10]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static String testFunc09(int test_var) {
    if (test_var < 0) {
      test_var = test_var * -1;
    }
    switch (test_var) {
      case 1:
        return "apple";
      case 2:
        return "banana";
      case 3:
        return "cat";
      case 4:
        return "dog";
      case 5:
        return "eat";
      case 6:
        return "fat";
      case 7:
        return "go";
      case 8:
        return "hi";
      case 9:
        return "ice";
      case 10:
        return "juice";
      case 11:
        return "kim";
      case 12:
        return "love";
      case 13:
        return "mmm";
      case 14:
        return "ninja";
      case 15:
        return "orange";
      case 16:
        return "purge";
      case 17:
        return "qwerty";
      case 18:
        return "roll";
      case 19:
        return "star";
      case 20:
        return "tar";
      case 21:
        return "ufo";
      case 22:
        return "void";
      case 23:
        return "woman";
      case 24:
        return "x";
      case 25:
        return "yellow";
      case 26:
        return "zz";
      case 27:
        return "aapple";
      case 28:
        return "bbanana";
      case 29:
        return "ccat";
      case 30:
        return "ddog";
      case 31:
        return "eeat";
      case 32:
        return "ffat";
      case 33:
        return "ggo";
      case 34:
        return "hhi";
      case 35:
        return "iice";
      case 36:
        return "jjuice";
      case 37:
        return "kkim";
      case 38:
        return "llove";
      case 39:
        return "mmmm";
      case 40:
        return "nninja";
      case 41:
        return "oorange";
      case 42:
        return "ppurge";
      case 43:
        return "qqwerty";
      case 44:
        return "rroll";
      case 45:
        return "sstar";
      case 46:
        return "ttar";
      case 47:
        return "uufo";
      case 48:
        return "vvoid";
      case 49:
        return "wwoman";
      case 50:
        return "xx";
      case 51:
        return "yyellow";
      case 52:
        return "zzz";
    }
    return "...";
  }

  // Index: 9
  // Stats Array Info:
  // - Offset within Stats Array: 37
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [4,3,1,0]
  // Hits Array Info:
  // - No blocks within Loops
  @DoNotStrip
  public static boolean testFunc10() {
    try {
      Class.forName("com.facebook.Foo");
      return true;
    } catch (ClassNotFoundException e) {
      System.out.println("can't load it");
      return false;
    }
  }

  @DoNotStrip
  // Index: 10
  // Stats Array Info:
  // - Offset within Stats Array: 40
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [5,4,3,2,1]
  // Hits Array Info:
  // - Offset within Hits Array: 4
  // - Number of Loop Blocks: 4
  // - Array Order: [1,2,3,4]
  public static int testFunc11(int size) {
    int i;
    int sum = 0;
    for (i = 1; i < size; i++) {
      if (i % 10 == 0) {
        sum *= 10;
      }
      sum += i;
    }

    return sum;
  }

  @DoNotStrip
  // Index: 11
  // Stats Array Info:
  // - Offset within Stats Array: 43
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [5,4,3,2,1]
  // Hits Array Info:
  // - Offset within Hits Array: 8
  // - Number of Loop Blocks: 3
  // - Array Order: [1,2,4]
  public static int testFunc12(int[] array, int value) {
    int i;
    for (i = 0; i < array.length; i++)
    {
      if (array[i] == value) {
        return i;
      }
    }

    return -1;
  }

  @DoNotStrip
  // Index: 12
  // Stats Array Info:
  // - Offset within Stats Array: 46
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [10,12,11,9,7,6,5,4,3,2]
  // Hits Array Info:
  // - Offset within Hits Array: 11
  // - Number of Loop Blocks: 7
  // - Array Order: [2,3,4,5,6,7,9]
  public static int testFunc13(int[] array) {
    Random rand = new Random();
    int i;
    try {
      for(i = 0; i < array.length; i++) {
        array[i] = rand.nextInt() % array[i];
      }
    } catch (ArithmeticException e) {
      System.out.println("Just used left over sum");
      throw e;
    }
    return 7;
  }

  @DoNotStrip
  // Index: 13
  // Stats Array Info:
  // - Offset within Stats Array: 49
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [8,9,7,6,5,4,3,2]
  // Hits Array Info:
  // - Offset within Hits Array: 18
  // - Number of Loop Blocks: 6
  // - Array Order: [2,3,4,5,6,7]
  public static int testFunc14(int[] array, int[] array2) {
    int i;
    int sum = 0;
    try {
      for(i = 0; i < array.length; i++) {
        sum += array2[array[i]];
      }
    } catch (ArrayIndexOutOfBoundsException e) {
      System.out.println("Just used left over sum");
      return sum;
    }
    return sum;
  }

  @DoNotStrip
  // Index: 14
  // Stats Array Info:
  // - Offset within Stats Array: 52
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [5,4,3,2,1]
  // Hits Array Info:
  // - Offset within Hits Array: 24
  // - Number of Loop Blocks: 4
  // - Array Order: [1,2,3,4]
  public static int testFunc15(int size) {
    int i = 1;
    int sum = 0;
    while (i < size) {
      if (i % 10 == 0) {
        sum *= 10;
      }
      sum += i;
      i++;
    }

    return sum;
  }

  @DoNotStrip
  // Index: 15
  // Stats Array Info:
  // - Offset within Stats Array: 55
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [5,4,3,2,1]
  // Hits Array Info:
  // - Offset within Hits Array: 28
  // - Number of Loop Blocks: 3
  // - Array Order: [1,2,4]
  public static int testFunc16(int[] array, int value) {
    int i = 0;
    while (i < array.length) {
      if (array[i] == value) {
        return i;
      }
      i++;
    }

    return -1;
  }

  @DoNotStrip
  // Index: 16
  // Stats Array Info:
  // - Offset within Stats Array: 58
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [10,12,11,9,7,6,5,4,3,2]
  // Hits Array Info:
  // - Offset within Hits Array: 31
  // - Number of Loop Blocks: 7
  // - Array Order: [2,3,4,5,6,7,9]
  public static int testFunc17(int[] array) {
    Random rand = new Random();
    int i = 0;
    try {
      while(i < array.length) {
        array[i] = rand.nextInt() % array[i];
        i++;
      }
    } catch (ArithmeticException e) {
      System.out.println("Just used left over sum");
      throw e;
    }
    return 7;
  }

  @DoNotStrip
  // Index: 17
  // Stats Array Info:
  // - Offset within Stats Array: 61
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [8,9,7,6,5,4,3,2]
  // Hits Array Info:
  // - Offset within Hits Array: 38
  // - Number of Loop Blocks: 6
  // - Array Order: [2,3,4,5,6,7]
  public static int testFunc18(int[] array, int[] array2) {
    int i = 0;
    int sum = 0;
    try {
      while(i < array.length) {
        sum += array2[array[i]];
        i++;
      }
    } catch (ArrayIndexOutOfBoundsException e) {
      System.out.println("Just used left over sum");
      return sum;
    }
    return sum;
  }

  @DoNotStrip
  // Index: 18
  // Stats Array Info:
  // - Offset within Stats Array: 64
  // - Number of Bit-Vectors: 2
  // - Bit-Vector 0: [19,20,21,22,23,24,28,27,26,25,31,30,29,3,2,1]
  // - Bit-Vector 1: [32,6,5,4,8,7,9,10,11,12,13,14,15,16,17,18]
  // Hits Array Info:
  // - Offset within Hits Array: 44
  // - Number of Loop Blocks: 27
  // - Array Order: [1,2,29,30,31,25,26,27,28,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,4,5,6]
  public static String testFunc19(int[] arr) {
    int i = 0;
    String output = "";
    for (i = 0; i < arr.length; i++) {
      switch (arr[i]) {
        case 1:
          output = output + "apple";
          break;
        case 2:
          output = output + "banana";
          // fallthrough
        case 3:
          output = output + "cat";
          // fallthrough
        case 4:
          output = output + "dog";
          // fallthrough
        case 5:
          output = output + "eat";
          break;
        case 6:
          output = output + "fat";
          break;
        case 7:
          output = output + "go";
          // fallthrough
        case 8:
          // fallthrough
        case 9:
          // fallthrough
        case 10:
          continue;
        case 11:
          output = output + "kim";
          break;
        case 12:
          output = output + "love";
          break;
        case 13:
          output = output + "mmm";
          break;
        case 14:
          output = output + "ninja";
          break;
        case 15:
          output = output + "orange";
          break;
        case 16:
          output = output + "random";
          // fallthrough
        case 17:
          // fallthrough
        case 18:
          break;
        case 19:
          output = output + "star";
          break;
        case 20:
          output = output + "tar";
          break;
        case 21:
          output = output + "ufo";
          break;
        case 22:
          output = output + "void";
          break;
        case 23:
          output = output + "woman";
          break;
        case 24:
          // fallthrough
        case 25:
          // fallthrough
        case 26:
          // fallthrough
        case 27:
          // fallthrough
        case 28:
          output = output + "five";
          break;
        case 29:
          output = output + "ccat";
          break;
        case 30:
          return "ddog";
        case 31:
          output = output + "eeat";
          // fallthrough
        case 32:
          return "ffat";
        case 33:
          output = output + "ggo";
          // fallthrough
        case 34:
          output = output + "hhi";
          // fallthrough
        case 35:
          output = output + "iice";
          break;
        default:
          return output;
      }

      output = output + " ";
    }

    return output;
  }

  @DoNotStrip
  @SuppressWarnings({"EmptyCatchBlock", "CatchGeneralException"})
  // Index: 19
  // Stats Array Info:
  // - Offset within Stats Array: 68
  // - Number of Bit-Vectors: 3
  // - Bit-Vector 0: [17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]
  // - Bit-Vector 1: [19,32,31,30,29,35,34,33,43,41,39,38,37,36,26,18]
  // - Bit-Vector 2: [42,24,23,22,21,20]
  // Hits Array Info:
  // - Offset within Hits Array: 71
  // - Number of Loop Blocks: 35
  // - Array Order: [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,26,36,37,38,39,41,33,34,29,30,31,32,19,20,21,22,23,24]
  public static int testFunc20(int[][] arr, int[] arr2) {
    int i, j;
    int sum = 0;
    try {
      for (i = 0; i < arr.length; i++) {
          for (j = 0; j < arr[i].length; j++) {
            int val = 0;
            int size = arr[i].length;
            try {
              if (j % 2 == 0) {
                val = val + Math.max(arr[i][j], size % arr2[j]);
              }
              else {
                val = val +  Math.min(arr[i][j], size % arr2[j]);
              }

              if (val == 1031) {
                break;
              }
            } catch (ArrayIndexOutOfBoundsException e) {
              throw e;
            } catch (ArithmeticException e) {
              continue;
            } catch (Exception e) {
              System.out.println("Last Exception");
            }
            sum += val;
          }

          if(sum == 27023) {
            sum = sum / arr.length;
          }
      }
    } catch (ArrayIndexOutOfBoundsException e) {
      return 0;
    }

    return sum;
  }

  @DoNotStrip
  @SuppressWarnings({"EmptyCatchBlock", "CatchGeneralException"})
  // Index: 20
  // Stats Array Info:
  // - Offset within Stats Array: 73
  // - Number of Bit-Vectors: 2
  // - Bit-Vector 0: [18,17,15,11,10,9,8,6,5,4,25,24,23,3,2,1]
  // - Bit-Vector 1: [14,13,12,22,21,20,19]
  // Hits Array Info:
  // - Offset within Hits Array: 106
  // - Number of Loop Blocks: 14
  // - Array Order: [23,24,5,6,8,10,17,18,19,20,21,22,13,1]
  public static int testFunc21(int[] arr, int magic) {
    int i = 0;
    int sum = 0;
    switch (magic % 3) {
      case 0:
        for (i = 0; i < arr.length; i++) {
          sum = sum * arr[i];
        }

        // fallthrough
      case 1:
        try {
          for (i = 0; i < arr.length; i++) {
            sum = sum + (sum % arr[i]);
          }
        } catch (ArithmeticException e) {
          sum = 0;
        }

        break;

      case 2:

        for (i = 0; i < arr.length; i++) {
          sum = sum + arr[i];
          if(sum % 7 == 0) {
            break;
          }

          if(sum % 13 == 0) {
            return sum;
          }

          if(sum % 17 == 0) {
            continue;
          }
        }

        break;

      default:
        break;
    }

    for (i = 0; i < arr.length; i++) {
      sum -= arr[i];
    }

    return sum;
  }

  @DoNotStrip
  // Index: 21
  // Stats Array Info:
  // - Offset within Stats Array: 77
  // - Number of Bit-Vectors: 1
  // - Bit-Vector 0: [13,15,14,12,11,10,9,8,7,6,5,4,3,2,1]
  // Hits Array Info:
  // - Offset within Hits Array: 120
  // - Number of Loop Blocks: 7
  // - Array Order: [6,7,8,9,10,11,12]
  public synchronized int testFunc22(String id, HashMap<String, HashSet<Integer>> maps) {
    HashSet<Integer> intSet = maps.get(id);
    int total = 0;
    if (intSet != null) {
      for (int i : intSet) {
        total += i;
      }
    }
    return total;
  }

  @Before
  @DoNotStrip
  public void startUp() {
    InputStream iSourceBlock = getClass().getResourceAsStream("/assets/redex-source-block-method-dictionary.csv");
    InputStream iMetadata = getClass().getResourceAsStream("/assets/redex-instrument-metadata.txt");
    MetadataParser.startUp(iMetadata, iSourceBlock, false);
  }

  @Test
  @DoNotStrip
  public void test01() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc01(0)).isEqualTo(42);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc01")).isEqualTo(8);
    assertThat(MetadataParser.getHitOffset("testFunc01")).isEqualTo(-1);

    // TestFunc01 has no bitvector and no blocks within loops because
    // it only has one basicblock that always executes.
    assertThat(MetadataParser.getBlockHits("testFunc01", stats, hitStats)).isEqualTo("0[]");
  }

  @Test
  @DoNotStrip
  public void test02() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc02(21,7)).isEqualTo(3);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc02")).isEqualTo(10);
    assertThat(MetadataParser.getHitOffset("testFunc02")).isEqualTo(8);
    assertThat(MetadataParser.getBlockHits("testFunc02", stats, hitStats)).isEqualTo("2[1:1,2:0]");
  }

  @Test
  @DoNotStrip
  public void test03() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc03(8,9)).isEqualTo(9);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc03")).isEqualTo(13);
    assertThat(MetadataParser.getHitOffset("testFunc03")).isEqualTo(10);
    assertThat(MetadataParser.getBlockHits("testFunc03", stats, hitStats)).isEqualTo("2[1:1,2:1]");
  }

  @Test
  @DoNotStrip
  @SuppressWarnings("CatchGeneralException")
  public void test04() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    boolean thrown = false;
    try {
      testFunc04(10,16);
    } catch (Exception e) {
      System.out.println("Exeception Thrown");
      thrown = true;
    }
    assertThat(thrown).isTrue();
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc04")).isEqualTo(16);
    assertThat(MetadataParser.getHitOffset("testFunc04")).isEqualTo(-1);
    assertThat(MetadataParser.getBlockHits("testFunc04", stats, hitStats)).isEqualTo("0[]");
  }

  @Test
  @DoNotStrip
  public void test05() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc05(0,1)).isEqualTo(-1);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc05")).isEqualTo(18);
    assertThat(MetadataParser.getHitOffset("testFunc05")).isEqualTo(12);
    assertThat(MetadataParser.getBlockHits("testFunc05", stats, hitStats)).isEqualTo("5[1:0,2:0,3:1,4:1,5:0]");
  }

  @Test
  @DoNotStrip
  public void test06() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc06(9,1)).isEqualTo(9);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc06")).isEqualTo(21);
    assertThat(MetadataParser.getHitOffset("testFunc06")).isEqualTo(17);
    assertThat(MetadataParser.getBlockHits("testFunc06", stats, hitStats)).isEqualTo("3[1:1,2:1,4:0]");
  }

  @Test
  @DoNotStrip
  public void test07() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc07(8,2)).isEqualTo(4);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc07")).isEqualTo(24);
    assertThat(MetadataParser.getHitOffset("testFunc07")).isEqualTo(20);
    assertThat(MetadataParser.getBlockHits("testFunc07", stats, hitStats)).isEqualTo("6[1:1,2:1,4:0,6:0,7:0,9:0]");
  }

  @Test
  @DoNotStrip
  @SuppressWarnings("CatchGeneralException")
  public void test08() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    int value = 0;
    try {
      value = testFunc08(5,2,8);
    } catch (Exception e) {
      System.out.println("Exeception Thrown");
    }
    assertThat(value).isEqualTo(7);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc08")).isEqualTo(27);
    assertThat(MetadataParser.getHitOffset("testFunc08")).isEqualTo(26);
    assertThat(MetadataParser.getBlockHits("testFunc08", stats, hitStats)).isEqualTo("11[1:1,2:1,3:1,4:1,5:1,6:1,7:0,8:0,10:0,11:0,12:1]");
  }

  @Test
  @DoNotStrip
  public void test09() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc09(16)).isEqualTo("purge");
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc09")).isEqualTo(30);
    assertThat(MetadataParser.getHitOffset("testFunc09")).isEqualTo(37);
    assertThat(MetadataParser.getBlockHits("testFunc09", stats, hitStats)).isEqualTo("55[1:0,2:1,3:0,4:0,5:0,6:0,7:0,8:0,9:0,10:0,11:0,12:0,13:0,14:0,15:0,16:0,17:0,18:0,19:0,20:0,21:0,22:0,23:0,24:0,25:0,26:0,27:0,28:0,29:0,30:0,31:0,32:0,33:0,34:0,35:0,36:0,37:0,38:0,39:0,40:1,41:0,42:0,43:0,44:0,45:0,46:0,47:0,48:0,49:0,50:0,51:0,52:0,53:0,54:0,55:0]");
  }

  @Test
  @DoNotStrip
  public void test10() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc10()).isFalse();
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc10")).isEqualTo(36);
    assertThat(MetadataParser.getHitOffset("testFunc10")).isEqualTo(92);
    assertThat(MetadataParser.getBlockHits("testFunc10", stats, hitStats)).isEqualTo("4[0:1,1:1,2:0,4:1]");
  }

  @Test
  @DoNotStrip
  public void test11() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc11(15)).isEqualTo(510);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc11")).isEqualTo(39);
    assertThat(MetadataParser.getHitOffset("testFunc11")).isEqualTo(96);
    assertThat(MetadataParser.getBlockHits("testFunc11", stats, hitStats)).isEqualTo("5[1:15,2:14,3:1,4:14,5:1]");
  }

  @Test
  @DoNotStrip
  public void test12() {
    int []array = {5,1,3,8,9,0,4};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc12(array,4)).isEqualTo(6);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc12")).isEqualTo(42);
    assertThat(MetadataParser.getHitOffset("testFunc12")).isEqualTo(101);
    assertThat(MetadataParser.getBlockHits("testFunc12", stats, hitStats)).isEqualTo("5[1:7,2:7,3:1,4:6,5:0]");
  }

  @Test
  @DoNotStrip
  @SuppressWarnings("CatchGeneralException")
  public void test13() {
    int []array = {5,1,3,8,9,0,4};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    try {
      testFunc13(array);
    } catch (Exception e) {
      System.out.println("Exeception Thrown");
    }
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc13")).isEqualTo(45);
    assertThat(MetadataParser.getHitOffset("testFunc13")).isEqualTo(106);
    assertThat(MetadataParser.getBlockHits("testFunc13", stats, hitStats)).isEqualTo("9[2:6,3:6,4:6,5:6,6:6,7:5,8:5,9:0,11:1]");
  }

  @Test
  @DoNotStrip
  public void test14() {
    int []array = {5,1,3,8,9,0,4};
    int []array2 = {21,56,11};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc14(array, array2)).isEqualTo(0);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc14")).isEqualTo(48);
    assertThat(MetadataParser.getHitOffset("testFunc14")).isEqualTo(115);
    assertThat(MetadataParser.getBlockHits("testFunc14", stats, hitStats)).isEqualTo("7[2:1,3:1,4:1,5:1,6:0,7:0,9:1]");
  }

  @Test
  @DoNotStrip
  public void test15() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc15(15)).isEqualTo(510);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc15")).isEqualTo(51);
    assertThat(MetadataParser.getHitOffset("testFunc15")).isEqualTo(122);
    assertThat(MetadataParser.getBlockHits("testFunc15", stats, hitStats)).isEqualTo("5[1:15,2:14,3:1,4:14,5:1]");
  }

  @Test
  @DoNotStrip
  public void test16() {
    int []array = {5,1,3,8,9,0,4};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc16(array,4)).isEqualTo(6);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc16")).isEqualTo(54);
    assertThat(MetadataParser.getHitOffset("testFunc16")).isEqualTo(127);
    assertThat(MetadataParser.getBlockHits("testFunc16", stats, hitStats)).isEqualTo("5[1:7,2:7,3:1,4:6,5:0]");
  }

  @Test
  @DoNotStrip
  @SuppressWarnings("CatchGeneralException")
  public void test17() {
    int []array = {5,1,3,8,9,0,4};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    try {
      testFunc17(array);
    } catch (Exception e) {
      System.out.println("Exeception Thrown");
    }
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc17")).isEqualTo(57);
    assertThat(MetadataParser.getHitOffset("testFunc17")).isEqualTo(132);
    assertThat(MetadataParser.getBlockHits("testFunc17", stats, hitStats)).isEqualTo("9[2:6,3:6,4:6,5:6,6:6,7:5,8:5,9:0,11:1]");
  }

  @Test
  @DoNotStrip
  public void test18() {
    int []array = {5,1,3,8,9,0,4};
    int []array2 = {21,56,11};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc18(array, array2)).isEqualTo(0);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc18")).isEqualTo(60);
    assertThat(MetadataParser.getHitOffset("testFunc18")).isEqualTo(141);
    assertThat(MetadataParser.getBlockHits("testFunc18", stats, hitStats)).isEqualTo("7[2:1,3:1,4:1,5:1,6:0,7:0,9:1]");
  }

  @Test
  @DoNotStrip
  public void test19() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc15(9)).isEqualTo(testFunc11(9));
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    // Assert that TestFunc11 and TestFunc15's hit counts are the same
    // because they are equivalent codes
    assertThat(MetadataParser.getBlockHits("testFunc11", stats, hitStats)).isEqualTo(
      MetadataParser.getBlockHits("testFunc15", stats, hitStats)
    );
  }

  @Test
  @DoNotStrip
  public void test20() {
    int []array = {1,3};
    int []array2 = {21,56,11};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc18(array, array2)).isEqualTo(testFunc14(array, array2));
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    // Assert that testFunc14 is ran once like testFunc18
    assertThat(MetadataParser.getOffset("testFunc14")).isEqualTo(48);
    assertThat(MetadataParser.getOffset("testFunc18")).isEqualTo(60);
    assertThat(stats[60]).isEqualTo((short)1);
    assertThat(stats[60]).isEqualTo(stats[48]);

    // Assert that TestFunc18 and TestFunc14's hit counts are the same
    // because they are equivalent codes
    assertThat(MetadataParser.getBlockHits("testFunc18", stats, hitStats)).isEqualTo(
      MetadataParser.getBlockHits("testFunc14", stats, hitStats)
    );
  }

  @Test
  @DoNotStrip
  public void test21() {
    int []array = {1,3,21,16,11,15};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc19(array)).isEqualTo("apple catdogeat ufo random kim orange ");
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(63);
    assertThat(MetadataParser.getHitOffset("testFunc19")).isEqualTo(148);
    assertThat(MetadataParser.getBlockHits("testFunc18", stats, hitStats)).isEqualTo("7[2:0,3:0,4:0,5:0,6:0,7:0,9:0]");
  }

  @Test
  @DoNotStrip
  public void test22() {
    int []array = {22,13,16,9,5,55};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc19(array)).isEqualTo("void mmm random eat ");
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(63);
    assertThat(MetadataParser.getHitOffset("testFunc19")).isEqualTo(148);
    assertThat(MetadataParser.getBlockHits("testFunc19", stats, hitStats)).isEqualTo("30[1:6,2:6,3:1,4:0,5:0,6:0,7:0,8:0,9:0,10:1,11:0,12:0,13:0,14:1,15:0,16:0,17:1,18:0,19:0,20:0,21:0,22:0,23:0,24:0,25:1,26:0,27:4,28:5,29:0,30:0]");
  }

  @Test
  @DoNotStrip
  public void test23() {
    int []array = {31,16,12,7,28,21};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc19(array)).isEqualTo("ffat");
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(63);
    assertThat(MetadataParser.getHitOffset("testFunc19")).isEqualTo(148);
    assertThat(MetadataParser.getBlockHits("testFunc19", stats, hitStats)).isEqualTo("30[1:1,2:1,3:0,4:0,5:0,6:0,7:0,8:0,9:0,10:0,11:0,12:0,13:0,14:0,15:0,16:0,17:0,18:0,19:0,20:0,21:0,22:0,23:0,24:0,25:0,26:0,27:0,28:0,29:1,30:0]");
  }

  @Test
  @DoNotStrip
  public void test24() {
    int [][]array = {{5,10,15},{6,12,18},{7,14,21}};
    int []array2 = {21,56,11};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc20(array,array2)).isEqualTo(81);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc20(array,array2)).isEqualTo(81);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);
    assertThat(MetadataParser.getHitOffset("testFunc20")).isEqualTo(178);
    assertThat(MetadataParser.getBlockHits("testFunc20", stats, hitStats)).isEqualTo("35[2:4,3:4,4:3,5:12,6:12,7:12,8:9,9:9,10:9,11:9,12:6,13:6,14:6,15:6,16:6,17:3,18:3,19:3,20:3,21:3,24:0,25:0,26:0,28:9,29:3,31:0,32:9,33:9,35:0,36:0,37:0,38:3,39:0,40:1,42:0]");
  }

  @Test
  @DoNotStrip
  public void test25() {
    int [][]array = {{5,10,15},{6,12,18},{7,14,21}};
    int []array2 = {21};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc20(array,array2)).isEqualTo(0);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);
    assertThat(MetadataParser.getHitOffset("testFunc20")).isEqualTo(178);
    assertThat(MetadataParser.getBlockHits("testFunc20", stats, hitStats)).isEqualTo("35[2:1,3:1,4:1,5:2,6:2,7:2,8:2,9:2,10:2,11:2,12:1,13:1,14:1,15:1,16:1,17:1,18:1,19:0,20:0,21:0,24:0,25:0,26:0,28:1,29:0,31:0,32:1,33:1,35:0,36:0,37:0,38:0,39:1,40:0,42:1]");
  }

  @Test
  @DoNotStrip
  public void test26() {
    int [][]array = {{5,10,15},{6,12,18},{7,14,21}};
    int []array2 = {21,56,0};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc20(array,array2)).isEqualTo(27);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);
    assertThat(MetadataParser.getHitOffset("testFunc20")).isEqualTo(178);
    assertThat(MetadataParser.getBlockHits("testFunc20", stats, hitStats)).isEqualTo("35[2:4,3:4,4:3,5:12,6:12,7:12,8:9,9:9,10:9,11:9,12:6,13:6,14:6,15:3,16:3,17:3,18:3,19:3,20:3,21:3,24:0,25:0,26:0,28:6,29:3,31:0,32:6,33:9,35:0,36:0,37:0,38:3,39:0,40:1,42:0]");
  }

  @Test
  @DoNotStrip
  public void test27() {
    int []array = {21,56,0};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc21(array,0)).isEqualTo(-77);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);
    assertThat(MetadataParser.getHitOffset("testFunc21")).isEqualTo(213);
    assertThat(MetadataParser.getBlockHits("testFunc21", stats, hitStats)).isEqualTo("22[1:0,2:0,3:1,4:4,5:3,6:0,7:0,8:0,10:0,11:0,12:0,13:1,14:4,15:3,16:0,17:1,19:3,20:3,21:3,22:3,23:2,24:1]");
  }

  @Test
  @DoNotStrip
  public void test28() {
    int []array = {21,56,11,12};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc21(array,1)).isEqualTo(-100);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);
    assertThat(MetadataParser.getHitOffset("testFunc21")).isEqualTo(213);
    assertThat(MetadataParser.getBlockHits("testFunc21", stats, hitStats)).isEqualTo("22[1:1,2:0,3:0,4:5,5:4,6:0,7:0,8:0,10:0,11:0,12:0,13:0,14:0,15:0,16:1,17:1,19:5,20:5,21:4,22:4,23:4,24:1]");
  }

  @Test
  @DoNotStrip
  public void test29() {
    int []array = {55,13,97,111,213};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc21(array,2)).isEqualTo(0);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);
    assertThat(MetadataParser.getHitOffset("testFunc21")).isEqualTo(213);
    assertThat(MetadataParser.getBlockHits("testFunc21", stats, hitStats)).isEqualTo("22[1:1,2:1,3:0,4:6,5:5,6:1,7:6,8:5,10:5,11:0,12:5,13:0,14:0,15:0,16:0,17:0,19:0,20:0,21:0,22:0,23:0,24:1]");
  }

  @Test
  @DoNotStrip
  public void test30() {
    int i = 0;
    int j = 0;
    String inp = "";
    HashMap<String, HashSet<Integer>> maps = new HashMap<>();
    for(i = 0; i < 5; i++) {
      HashSet<Integer> intSet = new HashSet<>();
      for(j = 0; j < 10; j++) {
        intSet.add(j);
      }
      inp = inp + "a";
      maps.put(inp, intSet);
    }

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    testFunc22("aaa", maps);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc22")).isEqualTo(76);
    assertThat(MetadataParser.getHitOffset("testFunc22")).isEqualTo(235);
    assertThat(MetadataParser.getBlockHits("testFunc22", stats, hitStats)).isEqualTo("15[1:1,2:1,3:1,4:1,5:1,6:11,7:11,8:10,9:10,10:10,11:10,13:1,14:0,15:0,17:0]");
  }

  @Test
  @DoNotStrip
  public void test31() {
    int i = 0;
    int j = 0;
    String inp = "";
    HashMap<String, HashSet<Integer>> maps = new HashMap<>();
    for(i = 0; i < 5; i++) {
      HashSet<Integer> intSet = new HashSet<>();
      for(j = 0; j < 10; j++) {
        intSet.add(j);
      }
      inp = inp + "a";
      maps.put(inp, intSet);
    }

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    testFunc22("b", maps);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    assertThat(MetadataParser.getOffset("testFunc22")).isEqualTo(76);
    assertThat(MetadataParser.getHitOffset("testFunc22")).isEqualTo(235);
    assertThat(MetadataParser.getBlockHits("testFunc22", stats, hitStats)).isEqualTo("15[1:1,2:1,3:1,4:0,5:0,6:0,7:0,8:0,9:0,10:0,11:0,13:1,14:0,15:0,17:0]");
  }

  // More instrumented blocks than one onNonLoopBlockHit call can take
  // (InstrumentBasicBlockAnalysis has arity 3, i.e. 48 blocks), so the
  // non-loop hits are flushed with several calls, each starting further
  // into the hits array. The loop puts loop blocks into the last of them.
  @DoNotStrip
  public int testFunc23(int x) {
    int r = 0;
    if (x > 0) {
      r = r * 31 + 1;
    }
    if (x > 1) {
      r = r * 31 + 2;
    }
    if (x > 2) {
      r = r * 31 + 3;
    }
    if (x > 3) {
      r = r * 31 + 4;
    }
    if (x > 4) {
      r = r * 31 + 5;
    }
    if (x > 5) {
      r = r * 31 + 6;
    }
    if (x > 6) {
      r = r * 31 + 7;
    }
    if (x > 7) {
      r = r * 31 + 8;
    }
    if (x > 8) {
      r = r * 31 + 9;
    }
    if (x > 9) {
      r = r * 31 + 10;
    }
    if (x > 10) {
      r = r * 31 + 11;
    }
    if (x > 11) {
      r = r * 31 + 12;
    }
    if (x > 12) {
      r = r * 31 + 13;
    }
    if (x > 13) {
      r = r * 31 + 14;
    }
    if (x > 14) {
      r = r * 31 + 15;
    }
    if (x > 15) {
      r = r * 31 + 16;
    }
    if (x > 16) {
      r = r * 31 + 17;
    }
    if (x > 17) {
      r = r * 31 + 18;
    }
    if (x > 18) {
      r = r * 31 + 19;
    }
    if (x > 19) {
      r = r * 31 + 20;
    }
    if (x > 20) {
      r = r * 31 + 21;
    }
    if (x > 21) {
      r = r * 31 + 22;
    }
    if (x > 22) {
      r = r * 31 + 23;
    }
    if (x > 23) {
      r = r * 31 + 24;
    }
    if (x > 24) {
      r = r * 31 + 25;
    }
    if (x > 25) {
      r = r * 31 + 26;
    }
    if (x > 26) {
      r = r * 31 + 27;
    }
    if (x > 27) {
      r = r * 31 + 28;
    }
    if (x > 28) {
      r = r * 31 + 29;
    }
    if (x > 29) {
      r = r * 31 + 30;
    }
    if (x > 30) {
      r = r * 31 + 31;
    }
    if (x > 31) {
      r = r * 31 + 32;
    }
    if (x > 32) {
      r = r * 31 + 33;
    }
    if (x > 33) {
      r = r * 31 + 34;
    }
    if (x > 34) {
      r = r * 31 + 35;
    }
    if (x > 35) {
      r = r * 31 + 36;
    }
    if (x > 36) {
      r = r * 31 + 37;
    }
    if (x > 37) {
      r = r * 31 + 38;
    }
    if (x > 38) {
      r = r * 31 + 39;
    }
    if (x > 39) {
      r = r * 31 + 40;
    }
    if (x > 40) {
      r = r * 31 + 41;
    }
    if (x > 41) {
      r = r * 31 + 42;
    }
    if (x > 42) {
      r = r * 31 + 43;
    }
    if (x > 43) {
      r = r * 31 + 44;
    }
    if (x > 44) {
      r = r * 31 + 45;
    }
    if (x > 45) {
      r = r * 31 + 46;
    }
    if (x > 46) {
      r = r * 31 + 47;
    }
    if (x > 47) {
      r = r * 31 + 48;
    }
    if (x > 48) {
      r = r * 31 + 49;
    }
    if (x > 49) {
      r = r * 31 + 50;
    }
    if (x > 50) {
      r = r * 31 + 51;
    }
    if (x > 51) {
      r = r * 31 + 52;
    }
    if (x > 52) {
      r = r * 31 + 53;
    }
    if (x > 53) {
      r = r * 31 + 54;
    }
    if (x > 54) {
      r = r * 31 + 55;
    }
    if (x > 55) {
      r = r * 31 + 56;
    }
    if (x > 56) {
      r = r * 31 + 57;
    }
    if (x > 57) {
      r = r * 31 + 58;
    }
    if (x > 58) {
      r = r * 31 + 59;
    }
    if (x > 59) {
      r = r * 31 + 60;
    }
    for (int i = 0; i < 3; i++) {
      r = r * 31 + i;
    }
    return r;
  }

  @Test
  @DoNotStrip
  public void testLargeMethodHitCounts() {
    InstrumentBasicBlockAnalysis.startTracing();
    testFunc23(1000);
    InstrumentBasicBlockAnalysis.stopTracing();

    short[] stats = InstrumentBasicBlockAnalysis.getStats();
    short[] hitStats = InstrumentBasicBlockAnalysis.getHitStats();

    // Every branch is taken, so each block runs once, except the loop header
    // (4) and body (3). Block 122 reads 0 regardless of the hit offsets.
    StringBuilder expected = new StringBuilder("123[");
    for (int block = 1; block <= 119; block++) {
      expected.append(block).append(":1,");
    }
    expected.append("120:4,121:3,122:0,123:1]");
    assertThat(MetadataParser.getBlockHits("testFunc23", stats, hitStats))
        .isEqualTo(expected.toString());
  }
}
