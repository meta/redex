/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest;

import integ.TestIntDef;
import integ.TestIntDefNoBool;
import integ.TestStringDef;

@interface NotSafeAnno {}

interface I {
  int get();
}

class AccessGetClass {
	@TestIntDef public static int public_field = 0;

  public void takes_param(@TestIntDef int val) {
    public_field = val;
  }

	public void override_method() {}
}

@SuppressWarnings({"WrongIntDefValue", "WrongStringDefValue"})
abstract class AbstractClass{
  abstract @TestIntDef int pureVirtual(@TestIntDef int val);

  abstract int pureVirtualNoAnnoReturn(@TestIntDef int val);

  abstract @TestIntDef int pureVirtualInvalidParamAnno(@TestIntDef int val);

  abstract @TestStringDef int pureVirtualInvalidReturn(@TestIntDef int val);
}


@SuppressWarnings({"WrongIntDefValue", "WrongStringDefValue"})
class VirtualTest extends AbstractClass{
  @TestIntDef int pureVirtual(@TestIntDef int val) {
    return val;
  };

  int pureVirtualNoAnnoReturn(@TestIntDef int val) {
    return val;
  };

  @TestIntDef int pureVirtualInvalidParamAnno(@TestIntDef int val) {
    return val;
  }

  @TestStringDef int pureVirtualInvalidReturn(@TestIntDef int val) {
    return val;
  }
}

@SuppressWarnings({"WrongIntDefValue", "WrongStringDefValue"})
class WrongConstVirtualTest extends AbstractClass{
  @TestIntDef int pureVirtual(@TestIntDef int val) {
    return 6;
  };

  @TestIntDef int pureVirtualNoAnnoReturn(@TestIntDef int val) {
    return val;
  };

  @TestIntDef int pureVirtualInvalidParamAnno(@TestIntDef int val) {
    return val;
  }

  @TestStringDef int pureVirtualInvalidReturn(@TestIntDef int val) {
    return val;
  }
}

@SuppressWarnings({"WrongIntDefValue", "WrongStringDefValue"})
class NoAnnoVirtualTest extends AbstractClass{
  int pureVirtual(@TestIntDef int val) {
    return 2;
  };

  int pureVirtualNoAnnoReturn(@TestIntDef int val) {
    return val;
  };

  @TestIntDef int pureVirtualInvalidParamAnno(@TestStringDef int val) {
    return val;
  }

  @TestIntDef int pureVirtualInvalidReturn(@TestIntDef int val) {
    return val;
  }
}

@SuppressWarnings({"WrongIntDefValue", "WrongStringDefValue"})
public class TypedefAnnoCheckerTest {

  @TestIntDef int int_field = TestIntDef.ZERO;
  @TestIntDef private static int static_int_field = TestIntDef.ZERO;
  @TestStringDef int wrong_anno_field;
  @TestStringDef String str_field;
  int no_anno_field = 6;

  @TestIntDef public int testPureVirtualCall(@TestIntDef int val) {
    AbstractClass test_virtual = new VirtualTest();
    return test_virtual.pureVirtual(val);
  }

  @TestIntDef public int testWrongConstPureVirtualCall(@TestIntDef int val) {
    AbstractClass test_virtual = new WrongConstVirtualTest();
    return test_virtual.pureVirtual(val);
  }

  @TestIntDef public int testNoAnnoPureVirtualCall(@TestIntDef int val) {
    AbstractClass test_virtual = new NoAnnoVirtualTest();
    return test_virtual.pureVirtual(val);
  }

  @TestIntDef public int testPureVirtualCallNoAnno(@TestIntDef int val) {
    AbstractClass test_virtual = new VirtualTest();
    return test_virtual.pureVirtualNoAnnoReturn(val);
  }

  @TestIntDef public int testWrongConstPureVirtualCall2(@TestIntDef int val) {
    AbstractClass test_virtual = new WrongConstVirtualTest();
    return test_virtual.pureVirtualNoAnnoReturn(val);
  }

  @TestIntDef public int testPureVirtualInvalidParamAnno(@TestIntDef int val) {
    AbstractClass test_virtual = new NoAnnoVirtualTest();
    return test_virtual.pureVirtualInvalidParamAnno(val);
  }

  @TestIntDef public int testPureVirtualInvalidParamAnno2(@TestIntDef int val) {
    AbstractClass test_virtual = new WrongConstVirtualTest();
    return test_virtual.pureVirtualInvalidParamAnno(val);
  }

  @TestIntDef public int testPureVirtualInvalidReturn(@TestIntDef int val) {
    AbstractClass test_virtual = new WrongConstVirtualTest();
    return test_virtual.pureVirtualInvalidReturn(val);
  }

  void testIntField(@TestIntDef int val) {
    int_field = val;
  }

  @TestIntDef int testReturnIntField() {
    return int_field;
  }

  void testWrongIntField(@TestIntDef int val) {
    wrong_anno_field = val;
  }

  void testStringField(@TestStringDef String val) {
    str_field = val;
  }

  @TestIntDef int testNoAnnoField() {
    return testValidIntAnnoReturn(no_anno_field);
  }

  static @NotSafeAnno @TestIntDef int testValidIntAnnoReturn(@NotSafeAnno @TestIntDef int val) {
    return val;
  }

  static @NotSafeAnno @TestStringDef String testValidStrAnnoReturn(@NotSafeAnno @TestStringDef String val) {
    return val;
  }

  static @TestIntDef int testIntAnnoInvokeStatic(@TestIntDef int val) {
    return testValidIntAnnoReturn(val);
  }

  static @TestStringDef String testStringAnnoInvokeStatic(@TestStringDef String val) {
    return testValidStrAnnoReturn(val);
  }

  static @TestIntDef String testWrongAnnotationReturned(@TestStringDef String val) {
    return val;
  }

  static @TestIntDef int testWrongAnnoInvokeStatic(@TestStringDef int val) {
    return testValidIntAnnoReturn(val);
  }

  static @NotSafeAnno @TestIntDef int testIrrelevantAnnos(@TestIntDef int val) {
    return val;
  }

  static @TestIntDef int testConstReturn() {
    @TestIntDef int val = TestIntDef.FOUR;
    return val;
  }

  static @TestIntDef int testInvalidConstReturn() {
    int val = 5;
    return val;
  }

  static @TestIntDef int testInvalidConstReturn2() {
    @TestIntDef int val = 5;
    return val;
  }

  static @TestStringDef String testConstStrReturn() {
   String val = "one";
    return val;
  }

  static @TestStringDef String testInvalidConstStrReturn() {
    @TestStringDef String val = "five";
    return val;
  }

  static @TestIntDef int testInvalidConstInvokeStatic() {
    int val = 5;
    return testIntAnnoInvokeStatic(val);
  }

  static @TestIntDef int testInvalidConstInvokeStatic2() {
    @TestIntDef int val = 5;
    return testIntAnnoInvokeStatic(val);
  }

  static @TestIntDef int testMultipleBlocksInt(@TestIntDef int val) {
    if (val > TestIntDef.TWO) {
      return val;
    }
    return TestIntDef.FOUR;
  }

  static @TestStringDef String testMultipleBlocksString(@TestStringDef String val) {
    if (val.equals(TestStringDef.THREE)) {
      return val;
    }
    return TestStringDef.ONE;
  }

  static @TestStringDef String testInvalidMultipleBlocksString(@TestStringDef String val) {
    if (val.equals(TestStringDef.THREE)) {
      val = val.concat("five");
      return val;
    }
    return TestStringDef.ONE;
  }

  static @TestIntDef int testNonConstInt(@TestIntDef int val) {
    val += 2;
    return val;
  }

  static @TestIntDef I testInvalidType(@TestIntDef I val) {
    return val;
  }

  static @TestStringDef String testJoiningTwoAnnotations(@TestStringDef String val, @TestIntDef String val2) {
    int flag = 1;
    @TestStringDef String s = val;
    if (flag == 1) {
      s = val;
    } else {
      s = val2;
    }
    return s;
  }

  static @TestStringDef String testJoiningTwoAnnotations2(@TestStringDef String val, @TestStringDef String val2) {
    int flag = 1;
    @TestStringDef String s = val;
    if (flag == 1) {
      s = val;
    } else {
      s = val2;
    }
    return s;
  }

  static @TestIntDef int testReassigningInt(@TestStringDef int val, @TestIntDef int val2) {
    val = val2;
    return val;
  }

  static @TestIntDef int testIfElse() {
    boolean flag = true;
    int res = flag ? TestIntDef.ONE : TestIntDef.ZERO;
    return res;
  }

  static @TestIntDef int testIfElseParam(boolean flag) {
    int res = flag ? TestIntDef.ONE : TestIntDef.ZERO;
    return res;
  }

  static @TestStringDef String testIfElseString(boolean flag) {
    String res = flag ? TestStringDef.ONE : TestStringDef.TWO;
    return res;
  }

  static @TestIntDef int testXORIfElse(boolean flag) {
    int res = flag ? TestIntDef.ZERO : TestIntDef.ONE;
    return res;
  }

  static @TestIntDef int testXORIfElseZero() {
    boolean flag = false;
    int res = flag ? TestIntDef.ZERO : TestIntDef.ONE;
    return res;
  }

  static @TestStringDef String testAssignNullToString() {
    return null;
  }

  static boolean getBoolean() {
    return true;
  }

  static @TestIntDef int testConstFolding() {
    @TestIntDef int val = getBoolean() ? TestIntDef.ONE : TestIntDef.ZERO;
    return val;
  }

  @TestIntDef int testSGet() {
    @TestIntDef int val = static_int_field;
    return val;
  }

  public AccessGetClass testAccessGet() {
  	return new AccessGetClass() {
    	@Override
      public void override_method() {
        takes_param(static_int_field);
      }
    };
  }

  public AccessGetClass testAccessSet() {
  	return new AccessGetClass() {
    	@Override
      public void override_method() {
        takes_param(static_int_field);
        static_int_field = TestIntDef.ONE;
      }
    };
  }

  public AccessGetClass testSyntheticValField(@TestIntDef int param) {
  	return new AccessGetClass() {
      @Override
      public void override_method() {
        takes_param(param);
      }
    };
  }

  @TestStringDef public String testNullString() {
    return null;
  }

  // Simulates the ModelGen pattern: an untyped source (like Parcel.readInt())
  // passes a value to a typedef-annotated parameter. The checker should NOT
  // flag this if the source class is in do_not_check_list.
  static void testUntypedSourceToTypedSink() {
    int val = UntypedSource.readInt();
    testValidIntAnnoReturn(val);
  }

  // Test that a boolean parameter returned as an IntDef that does NOT contain
  // both 0 and 1 is flagged as an error. The compiler optimizes `flag ? 1 : 0`
  // to use the boolean value directly, producing an IOPCODE_LOAD_PARAM def.
  // TestIntDefNoBool has {0, 2, 3} but not 1, so this should fail.
  static @TestIntDefNoBool int testBoolParamInvalidIntDef(boolean flag) {
    int res = flag ? 1 : 0;
    return res;
  }

  // Test that an XOR-optimized ternary with an IntDef that does NOT contain
  // both 0 and 1 is flagged as an error. The compiler optimizes `flag ? 0 : 1`
  // to XOR. TestIntDefNoBool has {0, 2, 3} but not 1, so this should fail.
  static @TestIntDefNoBool int testXORInvalidIntDef(boolean flag) {
    int res = flag ? 0 : 1;
    return res;
  }

}

interface IntDefSource {
  @TestIntDef int value();
}

interface NoBoolSource {
  @TestIntDefNoBool int value();
}

// value() overrides two methods whose return typedefs conflict.
class ConflictingSource implements IntDefSource, NoBoolSource {
  public int value() {
    return TestIntDef.ONE;
  }
}

class ConflictingSourceUser {
  static @TestIntDefNoBool int noBoolValue(NoBoolSource source) {
    return source.value();
  }
}

interface OtherIntDefSource {
  @TestIntDef int value();
}

// value() overrides two methods that agree on the return typedef.
class AgreeingSource implements IntDefSource, OtherIntDefSource {
  public int value() {
    return TestIntDef.ONE;
  }
}
