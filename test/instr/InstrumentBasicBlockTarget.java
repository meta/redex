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
public class InstrumentBasicBlockTarget {
  // Information taken from source dictionary and metadata
  // Index: 0
  // Offset within Stats Array: 8
  @DoNotStrip
  public static int testFunc01(int foo) {
    return 42;
  }

  // Index: 1
  // Offset within Stats Array: 10
  // Bit-Vector 0: [2,1]
  @DoNotStrip
  public static int testFunc02(int a, int b) {
    if (a > 0) {
      return a / b;
    } else {
      return a * b;
    }
  }

  // Index: 2
  // Offset within Stats Array: 13
  // Bit-Vector 0: [2,1]
  @DoNotStrip
  public static int testFunc03(int a, int b) {
    if (a > 0) {
      a++;
    }
    return a;
  }

  // Index: 3
  // Offset within Stats Array: 16
  // Bit-Vector 0: [5,4,2,1]
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
  // Offset within Stats Array: 19
  // Bit-Vector 0: [4,3,5,2,1]
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
        System.out.println("Couldn't make it to 4!, early return");
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
  // Offset within Stats Array: 22
  // Bit-Vector 0: [4,3,2,1]
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
  // Offset within Stats Array: 25
  // Bit-Vector 0: [9,8,7,6,4,3,2,1]
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
  // Offset within Stats Array: 28
  // Bit-Vector 0: [9,10,12,11,8,7,6,5,4,3,2,1]
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
  // Offset within Stats Array: 31
  // Bit-Vector 0: [43,44,45,46,47,48,49,50,51,52,53,54,55,3,2,1]
  // Bit-Vector 1: [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
  // Bit-Vector 2: [11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
  // Bit-Vector 3: [4,5,6,7,8,9,10]
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
  // Offset within Stats Array: 37
  // Bit-Vector 0: [4,3,1,0]
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
  // Offset: 40
  // Vector 0: [5,4,3,2,1]
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
  // Offset: 43
  // Vector 0: [5,4,3,2,1]
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
  // Offset: 46
  // Vector 0: [10,12,11,9,7,6,5,4,3,2]
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
  // Offset: 49
  // Vector 0: [8,9,7,6,5,4,3,2]
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
  // Offset: 52
  // Vector 0: [5,4,3,2,1]
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
  // Offset: 55
  // Vector 0: [5,4,3,2,1]
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
  // Offset: 58
  // Vector 0: [10,12,11,9,7,6,5,4,3,2]
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
  // Offset: 61
  // Vector 0: [8,9,7,6,5,4,3,2]
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
  // Offset: 64
  // Vector 0: [19,20,21,22,23,24,28,27,26,25,31,30,29,3,2,1]
  // Vector 1: [32,6,5,4,8,7,9,10,11,12,13,14,15,16,17,18]
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
  // Offset: 68
  // Vector 0: [17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]
  // Vector 1: [19,32,31,30,29,35,34,33,43,41,39,38,37,36,26,18]
  // Vector 2: [42,24,23,22,21,20]
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
  // Offset: 73
  // Vector 0: [18,17,15,11,10,9,8,6,5,4,25,24,23,3,2,1]
  // Vector 1: [14,13,12,22,21,20,19]
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
  // Offset: 77
  // Vector 0: [13,15,14,12,11,10,9,8,7,6,5,4,3,2,1]
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
    MetadataParser.startUp(iMetadata, iSourceBlock, true);
  }

  @Test
  @DoNotStrip
  public void test01() {
    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc01(0)).isEqualTo(42);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Assert that the offset in the statsArray is 8
    assertThat(MetadataParser.getOffset("testFunc01")).isEqualTo(8);

    // TestFunc01 has no bitvector because it only has one basicblock
    // that always executes so we do not need to assert it
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

    // Assert that the offset in the statsArray is 10
    assertThat(MetadataParser.getOffset("testFunc02")).isEqualTo(10);

    // Assert that TestFunc02 executed only BasicBlocks (1) skipping
    // 2 which is [0,1] in the Bit-Vector form due to return in the if condition
    int[] blockList = {2,1};
    int[] blockHitList = {0,1};
    int i = 0;

    for(i = 0; i < blockList.length; i++) {
      int hitValue = MetadataParser.checkBlockHit("testFunc02", stats, blockList[i]);
      assertThat(hitValue).isEqualTo(blockHitList[i]);
    }
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

    // Assert that the offset in the statsArray is 13
    assertThat(MetadataParser.getOffset("testFunc03")).isEqualTo(13);

    // Assert that TestFunc03 executed all BasicBlocks
    // which is [1,1] in the Bit-Vector form
    int[] blockList = {2,1};
    int[] blockHitList = {1,1};
    int i = 0;

    for(i = 0; i < blockList.length; i++) {
      int hitValue = MetadataParser.checkBlockHit("testFunc03", stats, blockList[i]);
      assertThat(hitValue).isEqualTo(blockHitList[i]);
    }
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
      System.out.println("Exception Thrown");
      thrown = true;
    }
    assertThat(thrown).isTrue();
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();

    // Assert that the offset in the statsArray is 16
    assertThat(MetadataParser.getOffset("testFunc04")).isEqualTo(16);

    // Assert that TestFunc04 executed only some BasicBlocks skipping others due to ArrayOutOfBounds exception
    assertThat(MetadataParser.getBlockHits("testFunc04", stats)).isEqualTo("0[]");
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

    assertThat(MetadataParser.getOffset("testFunc05")).isEqualTo(18);

    // Assert that TestFunc05 executed only some BasicBlocks skipping others due to flag being zero
    assertThat(MetadataParser.getBlockHits("testFunc05", stats)).isEqualTo("5[1:0,2:0,3:1,4:1,5:0]");
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

    assertThat(MetadataParser.getOffset("testFunc06")).isEqualTo(21);

    // Assert that TestFunc06 executed only some BasicBlocks skipping others due to early return in exception
    assertThat(MetadataParser.getBlockHits("testFunc06", stats)).isEqualTo("3[1:1,2:1,4:0]");
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

    assertThat(MetadataParser.getOffset("testFunc07")).isEqualTo(24);

    // Assert that TestFunc07 executed only some BasicBlocks skipping others due 8 % 2 = 0 and
    // there was no exception handling needed so it returned early
    assertThat(MetadataParser.getBlockHits("testFunc07", stats)).isEqualTo("6[1:1,2:1,4:0,6:0,7:0,9:0]");
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
      System.out.println("Exception Thrown");
    }
    assertThat(value).isEqualTo(7);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();

    assertThat(MetadataParser.getOffset("testFunc08")).isEqualTo(27);

    // Assert that TestFunc08 executed only some BasicBlocks skipping others due to
    // index being 2 and 2 % 2 = 0 which causes an Array Index Out of Bounds Exception
    // before it returns early
    assertThat(MetadataParser.getBlockHits("testFunc08", stats)).isEqualTo("11[1:1,2:1,3:1,4:1,5:1,6:1,7:0,8:0,10:0,11:0,12:1]");
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

    assertThat(MetadataParser.getOffset("testFunc09")).isEqualTo(30);

    // Assert that TestFunc09 executed only some BasicBlocks skipping
    // everything else because it didn't have to go into the initial if condition
    // because test-flag > 0 and the switch statement made it jump to exact basicblock
    // of 16 and returning immediately.
    assertThat(MetadataParser.getBlockHits("testFunc09", stats)).isEqualTo("55[1:0,2:1,3:0,4:0,5:0,6:0,7:0,8:0,9:0,10:0,11:0,12:0,13:0,14:0,15:0,16:0,17:0,18:0,19:0,20:0,21:0,22:0,23:0,24:0,25:0,26:0,27:0,28:0,29:0,30:0,31:0,32:0,33:0,34:0,35:0,36:0,37:0,38:0,39:0,40:1,41:0,42:0,43:0,44:0,45:0,46:0,47:0,48:0,49:0,50:0,51:0,52:0,53:0,54:0,55:0]");
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

    assertThat(MetadataParser.getOffset("testFunc10")).isEqualTo(36);
    assertThat(MetadataParser.getBlockHits("testFunc10", stats)).isEqualTo("4[0:1,1:1,2:0,4:1]");
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

    assertThat(MetadataParser.getOffset("testFunc11")).isEqualTo(39);
    assertThat(MetadataParser.getBlockHits("testFunc11", stats)).isEqualTo("5[1:1,2:1,3:1,4:1,5:1]");
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

    assertThat(MetadataParser.getOffset("testFunc12")).isEqualTo(42);
    assertThat(MetadataParser.getBlockHits("testFunc12", stats)).isEqualTo("5[1:1,2:1,3:1,4:1,5:0]");
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
      System.out.println("Exception Thrown");
    }
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();

    assertThat(MetadataParser.getOffset("testFunc13")).isEqualTo(45);
    assertThat(MetadataParser.getBlockHits("testFunc13", stats)).isEqualTo("9[2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:0,11:1]");
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

    assertThat(MetadataParser.getOffset("testFunc14")).isEqualTo(48);
    assertThat(MetadataParser.getBlockHits("testFunc14", stats)).isEqualTo("7[2:1,3:1,4:1,5:1,6:0,7:0,9:1]");
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

    assertThat(MetadataParser.getOffset("testFunc15")).isEqualTo(51);
    assertThat(MetadataParser.getBlockHits("testFunc15", stats)).isEqualTo("5[1:1,2:1,3:1,4:1,5:1]");
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

    assertThat(MetadataParser.getOffset("testFunc16")).isEqualTo(54);
    assertThat(MetadataParser.getBlockHits("testFunc16", stats)).isEqualTo("5[1:1,2:1,3:1,4:1,5:0]");
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
      System.out.println("Exception Thrown");
    }
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();

    assertThat(MetadataParser.getOffset("testFunc17")).isEqualTo(57);
    assertThat(MetadataParser.getBlockHits("testFunc17", stats)).isEqualTo("9[2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:0,11:1]");
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

    assertThat(MetadataParser.getOffset("testFunc18")).isEqualTo(60);
    assertThat(MetadataParser.getBlockHits("testFunc18", stats)).isEqualTo("7[2:1,3:1,4:1,5:1,6:0,7:0,9:1]");
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

    // TestFunc15's bit-vector should be the same as testFunc11
    // because they are equivalent codes
    assertThat(MetadataParser.getBlockHits("testFunc15", stats)).isEqualTo(
      MetadataParser.getBlockHits("testFunc11", stats)
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

    // Assert that testFunc14 is ran once like testFunc18
    assertThat(MetadataParser.getOffset("testFunc14")).isEqualTo(48);
    assertThat(MetadataParser.getOffset("testFunc18")).isEqualTo(60);
    assertThat(stats[60]).isEqualTo((short)1);
    assertThat(stats[60]).isEqualTo(stats[48]);

    // TestFunc18's bit-vector should be the same as testFunc14
    // because they are equivalent codes
    assertThat(MetadataParser.getBlockHits("testFunc18", stats)).isEqualTo(
      MetadataParser.getBlockHits("testFunc14", stats)
    );
  }

  /*
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

    // Assert that the offset in the statsArray is 64
    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(64);

    // Assert that TestFunc19 executed only BasicBlocks (1,2,15,17,18,22,24,25,28,27,30,31,32) skipping
    // everything else because it only had to go to particular switch blocks.
    // As this test case has numerous basicblocks (32),
    // it needs two bitvectors so we need to make sure it is [0,0,0,1,0,0,1,1,1,0,1,1,1,0,1,1] in
    // Bit-Vector 1 and [1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1] in Bit-Vector 2
    int[][] blockList = {{19,20,21,22,23,24,28,27,26,25,31,30,29,3,2,1},
                         {32,6,5,4,8,7,9,10,11,12,13,14,15,16,17,18}};
    int[][] blockHitList = {{0,0,0,1,0,0,1,1,1,0,1,1,1,0,1,1},
                            {1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1}};
    int i = 0;
    int j = 0;

    for(i = 0; i < blockList.length; i++) {
      for(j = 0; j < blockList[i].length; j++) {
        int hitValue = MetadataParser.checkBlockHit("testFunc19", stats, blockList[i][j]);
        assertThat(hitValue).isEqualTo(blockHitList[i][j]);
      }
    }
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

    // Assert that the offset in the statsArray is 64
    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(64);

    // Assert that TestFunc19 executed only BasicBlocks (1,2,3,13,17,20,28,30,31) skipping
    // everything else because it only had to go to particular switch blocks.
    // As this test case has numerous basicblocks (32),
    // it needs two bitvectors so we need to make sure it is [0,1,0,0,0,0,1,0,0,0,1,1,0,1,1,1] in
    // Bit-Vector 1 and [0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0] in Bit-Vector 2
    int[][] blockList = {{19,20,21,22,23,24,28,27,26,25,31,30,29,3,2,1},
                       {32,6,5,4,8,7,9,10,11,12,13,14,15,16,17,18}};
    int[][] blockHitList = {{0,1,0,0,0,0,1,0,0,0,1,1,0,1,1,1},
                            {0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0}};
    int i = 0;
    int j = 0;

    for(i = 0; i < blockList.length; i++) {
      for(j = 0; j < blockList[i].length; j++) {
        int hitValue = MetadataParser.checkBlockHit("testFunc19", stats, blockList[i][j]);
        assertThat(hitValue).isEqualTo(blockHitList[i][j]);
      }
    }
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

    // Assert that the offset in the statsArray is 64
    assertThat(MetadataParser.getOffset("testFunc19")).isEqualTo(64);

    // Assert that TestFunc19 executed only BasicBlocks (1,2,7,8) skipping
    // everything else because it only had to go to particular switch blocks.
    // As this test case has numerous basicblocks (32),
    // it needs two bitvectors so we need to make sure it is [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1] in
    // Bit-Vector 1 and [0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0] in Bit-Vector 2
    int[][] blockList = {{19,20,21,22,23,24,28,27,26,25,31,30,29,3,2,1},
                       {32,6,5,4,8,7,9,10,11,12,13,14,15,16,17,18}};
    int[][] blockHitList = {{0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1},
                            {0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0}};
    int i = 0;
    int j = 0;

    for(i = 0; i < blockList.length; i++) {
      for(j = 0; j < blockList[i].length; j++) {
        int hitValue = MetadataParser.checkBlockHit("testFunc19", stats, blockList[i][j]);
        assertThat(hitValue).isEqualTo(blockHitList[i][j]);
      }
    }
  }
  */

  @Test
  @DoNotStrip
  public void test24() {
    int [][]array = {{5,10,15},{6,12,18},{7,14,21}};
    int []array2 = {21,56,11};

    // Start Tracing Information and run Function before stopping
    InstrumentBasicBlockAnalysis.startTracing();
    assertThat(testFunc20(array,array2)).isEqualTo(81);
    InstrumentBasicBlockAnalysis.stopTracing();

    // Get Stats from Instrument Analysis
    short[] stats = InstrumentBasicBlockAnalysis.getStats();

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);

    // Assert that TestFunc20 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc20", stats)).isEqualTo("35[2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:1,10:1,12:0,13:0,14:0,15:1,16:1,17:1,18:1,19:1,20:1,21:1,22:1,23:1,26:1,27:1,28:1,29:1,30:1,33:0,34:0,35:0,36:0,37:1,38:1,39:1,41:0,43:0]");
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

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);

    // Assert that TestFunc20 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc20", stats)).isEqualTo("35[2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:1,10:0,12:0,13:0,14:0,15:0,16:1,17:1,18:1,19:1,20:1,21:1,22:1,23:1,26:1,27:1,28:0,29:0,30:0,33:0,34:0,35:0,36:0,37:1,38:1,39:0,41:1,43:1]");
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

    assertThat(MetadataParser.getOffset("testFunc20")).isEqualTo(67);

    // Assert that TestFunc20 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc20", stats)).isEqualTo("35[2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:1,10:1,12:0,13:0,14:0,15:1,16:1,17:1,18:1,19:1,20:1,21:1,22:1,23:1,26:1,27:1,28:1,29:1,30:1,33:0,34:0,35:0,36:0,37:1,38:1,39:1,41:0,43:0]");
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

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);

    // Assert that TestFunc21 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc21", stats)).isEqualTo("22[1:0,2:0,3:1,4:1,5:1,6:0,7:0,8:0,10:0,11:0,12:0,13:1,14:1,15:1,16:0,17:1,19:1,20:1,21:1,22:1,23:1,24:1]");
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

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);

    // Assert that TestFunc21 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc21", stats)).isEqualTo("22[1:1,2:0,3:0,4:1,5:1,6:0,7:0,8:0,10:0,11:0,12:0,13:0,14:0,15:0,16:1,17:1,19:1,20:1,21:1,22:1,23:1,24:1]");
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

    assertThat(MetadataParser.getOffset("testFunc21")).isEqualTo(72);

    // Assert that TestFunc21 executed some BasicBlocks skipping
    // everything else because it only had to go to particular switch blocks.
    assertThat(MetadataParser.getBlockHits("testFunc21", stats)).isEqualTo("22[1:1,2:1,3:0,4:1,5:1,6:1,7:1,8:1,10:1,11:0,12:1,13:0,14:0,15:0,16:0,17:0,19:0,20:0,21:0,22:0,23:0,24:1]");
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

    assertThat(MetadataParser.getOffset("testFunc22")).isEqualTo(76);
    assertThat(MetadataParser.getBlockHits("testFunc22", stats)).isEqualTo("15[1:1,2:1,3:1,4:1,5:1,6:1,7:1,8:1,9:1,10:1,11:1,13:1,14:0,15:0,17:0]");
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

    assertThat(MetadataParser.getOffset("testFunc22")).isEqualTo(76);
    assertThat(MetadataParser.getBlockHits("testFunc22", stats)).isEqualTo("15[1:1,2:1,3:1,4:0,5:0,6:0,7:0,8:0,9:0,10:0,11:0,13:1,14:0,15:0,17:0]");
  }

  @Test
  @DoNotStrip
  public void testFuncNewInstanceOrder() {
    try {
      String input = "const";
      String output = new String(input);
      assertThat(output).isEqualTo(input);
    } catch (RuntimeException e) {
    }
  }
}
