/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package redex;

import java.util.Random;
import javax.annotation.Nullable;
import org.junit.Test;
import static org.assertj.core.api.Assertions.assertThat;

// POSTCHECK-LABEL: class: redex.$EnumUtils
// POSTCHECK-NEXT: Access flags: (PUBLIC, FINAL)
// POSTCHECK-NEXT: Superclass: java.lang.Object
// POSTCHECK: (PRIVATE, STATIC, FINAL) $VALUES:java.lang.Integer[]
// POSTCHECK: (PUBLIC, STATIC, FINAL) f0:java.lang.Integer
// POSTCHECK: (PUBLIC, STATIC, FINAL) f1:java.lang.Integer
// POSTCHECK: (PUBLIC, STATIC, FINAL) f2:java.lang.Integer
// POSTCHECK: (PUBLIC, STATIC, FINAL) f3:java.lang.Integer
// POSTCHECK-NOT: (PUBLIC, STATIC, FINAL) f4:java.lang.Integer

// This enum class contains some user defined static methods and it's never
// being casted to other types. It will be transformed to a class with only
// static methods by OptimizeEnumsPass.
// CHECK-LABEL: class: redex.SCORE
// CHECK-NEXT: Access flags:
// PRECHECK-NEXT: Superclass: java.lang.Enum
// POSTCHECK-NEXT: Superclass: java.lang.Object
enum SCORE {
  ONE(11, "UNO"),
  TWO(12, "DOS"),
  THREE(13, null);

  SCORE(int data, String str) {
    myOtherField = str;
    myField = data;
    scoreToWin = 101;
    constantString = "IDoNotChange";
  }

  static final SCORE DEFAULT = ONE;
  static final SCORE[] array = values();
  static int number = 0;

  // Primitive or String instance fields are (usually) safe.
  // POSTCHECK-DAG: method: direct redex.SCORE.redex$OE$get_myField:(java.lang.Integer)int
  int myField;
  // POSTCHECK-DAG: method: direct redex.SCORE.redex$OE$get_myOtherField:(java.lang.Integer)java.lang.String
  String myOtherField;
  int scoreToWin;
  String constantString;

  // POSTCHECK-DAG: method: direct redex.SCORE.increase$REDEX${{.*}}:(java.lang.Integer)java.lang.Integer
  public static @Nullable SCORE increase(@Nullable SCORE score) {
    if (score == null) {
      return null;
    }
    switch (score) {
    case ONE:
      return TWO;
    case TWO:
    case THREE:
      return THREE;
    }
    return null;
  }

  private SCORE instance_direct() { return this; }

  // Virtual methods are safe.
  // POSTCHECK-DAG: method: direct redex.SCORE.is_max$REDEX${{.*}}:(java.lang.Integer)boolean
  public boolean is_max() { return instance_direct() == THREE; }

  // POSTCHECK-DAG: method: direct redex.SCORE.toString$REDEX${{.*}}:(java.lang.Integer)java.lang.String
  public String toString() {
    return this.myOtherField;
  }

  // POSTCHECK-DAG: method: direct redex.SCORE.getString$REDEX${{.*}}:(java.lang.Integer)java.lang.String
  public String getString() {
    return this.myOtherField;
  }

  // POSTCHECK-DAG: method: direct redex.SCORE.cast_to_enum_array$REDEX${{.*}}:(java.lang.Integer)java.lang.Integer[]
  public SCORE[] cast_to_enum_array() {
    Object result = SCORE.values();
    return (SCORE[]) result;
  }
}

interface Intf {
  int make(SCORE score);
  int make(int i);
}

// Some usages of SCORE.
class A {
  // As parameter.
  // POSTCHECK: method: virtual redex.A.ha$REDEX${{.*}}:(java.lang.Integer)int
  public int ha(SCORE score) { return 1; }
}

abstract class B extends A implements Intf {
  // As return value.
  // POSTCHECK: method: virtual redex.B.haha$REDEX${{.*}}:()java.lang.Integer
  public SCORE haha() { return SCORE.THREE; }
  public int make(int i) { return i * 7; }
  int ha(int i) { return 11; }
}

// CHECK-LABEL: class: redex.C
class C extends B {
  static @Nullable SCORE s_score = SCORE.ONE;
  // PRECHECK: (STATIC) array:redex.SCORE[][]
  // POSTCHECK: (STATIC) array$REDEX${{.*}}:java.lang.Integer[][]
  static SCORE[][] array;
  @Nullable SCORE i_score = SCORE.ONE;
  @Nullable Object i_obj = null;

  public void set(SCORE score) { i_score = score; }
  public @Nullable SCORE get() { return i_score; }

  public int make(SCORE score) { return score.ordinal() * 5; }
}

// This enum class only contains several Enum objects.
// It will be optimized by OptimizeEnumsPass.
// PRECHECK: class: redex.PURE_SCORE
// PRECHECK-NEXT: Access flags:
// PRECHECK-NEXT: Superclass: java.lang.Enum
// POSTCHECK-NOT: class redex.PURE_SCORE
enum PURE_SCORE {
  ONE,
  TWO,
  THREE,
  FOUR,
  FIVE;
}

/* Some enums that are unsafe to be transformed. */
// CHECK: class: redex.USED_IN_UNSAFE_CONSTRUCTOR
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum USED_IN_UNSAFE_CONSTRUCTOR {
  ONE;
}
class HasUnsafeConstructor {
  HasUnsafeConstructor(USED_IN_UNSAFE_CONSTRUCTOR[] e) {}
  HasUnsafeConstructor(Integer[] e) {}
}
// CHECK: class: redex.MODIFIES_INSTANCE_FIELD
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum MODIFIES_INSTANCE_FIELD {
  ONE(1234);
  int myField;
  MODIFIES_INSTANCE_FIELD(int data) {
    myField = data;
  }
  public void modify() {
    myField++;
  }
}
// CHECK: class: redex.CAST_WHEN_RETURN
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_WHEN_RETURN {
  ONE;
  public static Enum[] method() {
    CAST_WHEN_RETURN[] array = new CAST_WHEN_RETURN[1];
    array[0] = ONE;
    return array;
  }
}
// CHECK: class: redex.CAST_THIS_POINTER
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_THIS_POINTER {
  ONE;
  public static void cast_this_method() {
    EnumHelper.inlined_method(CAST_THIS_POINTER.ONE);
  }
}
// CHECK: class: redex.CAST_THIS_POINTER_2
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_THIS_POINTER_2 {
  ONE;
  public String cast_this_method() {
    return super.toString();
  }
}
// CHECK: class: redex.CAST_PARAMETER
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_PARAMETER {
  ONE;
  public static <E extends Enum<E>> void method_accepts_enum_arg(
      @Nullable Enum<E> o) {}
  public static void method() { method_accepts_enum_arg(ONE); }
}
// CHECK: class: redex.USED_AS_CLASS_OBJECT
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum USED_AS_CLASS_OBJECT {
  ONE;
  public static <T> void method(Class<T> c) {}
  public static void method() { method(USED_AS_CLASS_OBJECT.class); }
}
// CHECK: class: redex.USED_IN_INSTANCE_OF
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum USED_IN_INSTANCE_OF {
  ONE;
  public static void method(boolean b) {}
  public static void method() { method(ONE instanceof USED_IN_INSTANCE_OF); }
}
// CHECK: class: redex.CAST_CHECK_CAST
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_CHECK_CAST { ONE; }
// CHECK: class: redex.CAST_ISPUT_OBJECT
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_ISPUT_OBJECT { ONE; }
// CHECK: class: redex.CAST_APUT_OBJECT
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_APUT_OBJECT { ONE; }
// CHECK: class: redex.ENUM_TYPE_1
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum ENUM_TYPE_1 { ONE; }
// CHECK: class: redex.ENUM_TYPE_2
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum ENUM_TYPE_2 {
  ONE,
  TWO;
  public static void test_join() {
    Enum obj = null;
    Random random = new Random();
    int pos_rand = random.nextInt() & Integer.MAX_VALUE;
    int selector = pos_rand % 2;
    if (selector == 0) {
      obj = ENUM_TYPE_1.ONE;
    } else if (selector == 1 || selector == -1) {
      obj = ENUM_TYPE_2.TWO;
    } else if (selector > 1) {
      obj = Enum.valueOf(ENUM_TYPE_1.class, "NotReach");
    }
    // obj may be Enum, ENUM_TYPE_1 or ENUM_TYPE_2
    int res = obj.ordinal();
    if (selector == 0) {
      assertThat(res).isEqualTo(0);
    } else if (selector == 1) {
      assertThat(res).isEqualTo(1);
    }
  }
}

// CHECK: class: redex.CAST_ENUM_ARRAY_TO_OBJECT
// CHECK-NEXT: Access flags:
// CHECK-NEXT: Superclass: java.lang.Enum
enum CAST_ENUM_ARRAY_TO_OBJECT {
  ONE;
  public static String method() {
    StringBuilder sb = new StringBuilder();
    sb.append(CAST_ENUM_ARRAY_TO_OBJECT.values());
    sb.append(String.valueOf(CAST_ENUM_ARRAY_TO_OBJECT.values()));
    return sb.toString();
  }
}

class EnumHelper {
  static void inlined_method(Enum e) { int a = e.hashCode(); }

  class Cache<T> {
    @Nullable T e = (T) null;
    public @Nullable T get() { return e; }
  }
  Cache<CAST_CHECK_CAST> mCache = new Cache();
  public CAST_CHECK_CAST check_cast_method() { return mCache.get(); }

  Object i_obj;
  static Enum s_obj;
  public void put_method() {
    i_obj = CAST_ISPUT_OBJECT.ONE;
    s_obj = CAST_ISPUT_OBJECT.ONE;
  }

  public void aput_method() {
    Object[] array = new Object[10];
    array[0] = CAST_APUT_OBJECT.ONE;
    s_obj = CAST_APUT_OBJECT.ONE;
  }

  public static int my_ordinal(SCORE score) { return score.ordinal(); }

  public static <T> T notEscape(T obj) { return obj; }
}

/* Test cases */
public class EnumTransformTest {
  @Test
  public void test_interface() {
    C c = new C();
    // Method with the same name but different type of argument.
    assertThat(c.make(SCORE.TWO)).isEqualTo(5);
    assertThat(c.make(1)).isEqualTo(7);
    assertThat(c.ha(0)).isEqualTo(11);
    assertThat(c.ha(null)).isEqualTo(1);
    assertThat(c.haha().ordinal()).isEqualTo(SCORE.THREE.ordinal());
  }

  // SCORE.ordinal() is transformed.
  @Test
  public void test_increase() {
    SCORE score = SCORE.ONE;
    assertThat(score.ordinal()).isEqualTo(SCORE.ONE.ordinal());
    assertThat(score.ordinal()).isEqualTo(0);
    score = SCORE.increase(score);
    assertThat(score.ordinal()).isEqualTo(1);
    score = SCORE.increase(score);
    assertThat(score.ordinal()).isEqualTo(2);
    score = SCORE.increase(score);
    assertThat(score.ordinal()).isEqualTo(2);
    score = SCORE.increase(null);
    if (score != null) {
      assertThat(true).isEqualTo(false);
    }
  }

  // SCORE.equals(SCORE) is transformed.
  @Test
  public void test_equals() {
    SCORE a = SCORE.ONE;
    assertThat(a.equals(SCORE.ONE)).isEqualTo(true);
    SCORE b = SCORE.increase(a);
    assertThat(a.equals(b)).isEqualTo(false);
  }

  // SCORE.compareTo(SCORE) is transformed.
  @Test
  public void test_compareTo() {
    SCORE a = SCORE.ONE;
    SCORE b = SCORE.increase(a);
    assertThat(a.compareTo(b)).isEqualTo(-1);
    assertThat(b.compareTo(a)).isEqualTo(1);
    assertThat(a.compareTo(a)).isEqualTo(0);
  }

  // SCORE.values() is transformed.
  @Test
  public void test_values() {
    SCORE[] values = SCORE.values();
    assertThat(values.length).isEqualTo(3);
    assertThat(SCORE.array.length).isEqualTo(3);
    for (int i = 0; i < 3; i++) {
      assertThat(values[i].ordinal()).isEqualTo(SCORE.array[i].ordinal());
    }
  }

  @Test
  public void test_string_valueof() {
    SCORE obj;
    int rand = new Random().nextInt();
    if (rand >= 0) {
      obj = SCORE.ONE;
    } else {
      obj = null;
    }
    if (rand >= 0) {
      assertThat(String.valueOf(obj)).isEqualTo(SCORE.ONE.toString());
    } else {
      assertThat(String.valueOf(obj)).isEqualTo("null");
    }
  }

  @Test
  public void toString_regression() {
    Enum e = SCORE.ONE;
    assertThat(e.toString()).isEqualTo("UNO");
  }

  // NullPointerException.
  @Test(expected = NullPointerException.class)
  public void test_npe() {
    int a = EnumHelper.my_ordinal(null);
  }

  // [isa]get_object, [isa]put_object and new_array instructions are
  // transformed.
  @Test
  public void test_get_put() {
    C.s_score = SCORE.ONE;
    assertThat(C.s_score.ordinal()).isEqualTo(0);

    C c = new C();
    c.set(SCORE.TWO);
    assertThat(c.get().ordinal()).isEqualTo(1);

    SCORE[] scores = new SCORE[1];
    scores[0] = SCORE.THREE;
    assertThat(scores[0].ordinal()).isEqualTo(SCORE.THREE.ordinal());
  }

  // PURE_SCORE class is deleted and PURE_SCORE objects are replaced with
  // Integer objects.
  @Test
  public void test_pure_score() {
    PURE_SCORE a = PURE_SCORE.ONE;
    assertThat(a.ordinal()).isEqualTo(PURE_SCORE.ONE.ordinal());
    PURE_SCORE five = PURE_SCORE.FIVE;
    PURE_SCORE five_2 = PURE_SCORE.FIVE;
    assertThat(five.ordinal()).isEqualTo(five_2.ordinal());
    // FIVE's ordinal is above max_enum_size, so it has no $EnumUtils field.
    assertThat(PURE_SCORE.valueOf("FIVE").ordinal()).isEqualTo(4);
    assertThat(PURE_SCORE.valueOf("TWO").ordinal()).isEqualTo(1);
    switch (five) {
      case FIVE:
        break;
      default:
        assertThat(true).isEqualTo(false);
    }
  }

  @Test
  public void test_if() {
    C c = new C();
    if (c.i_obj == c.i_score) {
      assertThat(true).isEqualTo(false);
    }
  }

  @Test
  public void test_toString() {
    C c = new C();
    StringBuilder sb = new StringBuilder();
    c.i_score = null;
    sb.append(c.i_score);
    sb.append(SCORE.ONE.toString());
    sb.append(SCORE.TWO);
    sb.append(SCORE.THREE);
    assertThat(sb.toString()).isEqualTo("nullUNODOSnull");
  }

  @Test(expected = NullPointerException.class)
  public void test_toString_throw() {
    C c = new C();
    c.i_score = null;
    c.i_score.toString();
  }

  enum COUNT { ONE, TWO };

  @Test
  public void test_hashCode() {
    SCORE.ONE.hashCode();
    SCORE.TWO.hashCode();
    SCORE.THREE.hashCode();
    // Test an enum that doesn't directly call `Enum.toString()`.
    COUNT.ONE.hashCode();
    COUNT.TWO.hashCode();
  }

  @Test
  public void test_valueOf() {
    String name = SCORE.ONE.name();
    SCORE s = SCORE.valueOf(name);
    assertThat(s.ordinal()).isEqualTo(SCORE.ONE.ordinal());
    s = SCORE.valueOf("TWO");
    assertThat(s.ordinal()).isEqualTo(SCORE.TWO.ordinal());
    s = SCORE.valueOf("THREE");
    assertThat(s.ordinal()).isEqualTo(SCORE.THREE.ordinal());
  }

  @Test(expected = IllegalArgumentException.class)
  public void test_valueOf_exception() {
    SCORE.valueOf("ZERO");
  }

  @Test
  public void test_join_with_multitypes() {
    ENUM_TYPE_2.test_join();
  }

  @Test
  public void test_non_escape_invocation() {
    SCORE one = SCORE.ONE;
    SCORE obj = EnumHelper.notEscape(one);
    assertThat(one.ordinal()).isEqualTo(obj.ordinal());
  }

  @Test
  public void virtual_method() {
    assertThat(SCORE.THREE.is_max()).isEqualTo(true);
  }

  @Test
  public void instance_fields() {
    assertThat(SCORE.ONE.myOtherField).isEqualTo("UNO");
    assertThat(SCORE.TWO.myOtherField).isEqualTo("DOS");
    assertThat(SCORE.THREE.myOtherField).isEqualTo(null);
    assertThat(SCORE.ONE.myField).isEqualTo(11);
    assertThat(SCORE.TWO.myField).isEqualTo(12);
    assertThat(SCORE.THREE.myField).isEqualTo(13);
  }

  @Test
  public void null_enum_value() {
    // PRECHECK:  check-cast {{.*}}, redex.SCORE
    // POSTCHECK: check-cast {{.*}}, java.lang.Integer
    SCORE score_obj = (SCORE) null;
    // CHECK: SCORE.increase
    SCORE.increase(null);
    // CHECK: sput-object {{.*}} redex.C.s_score
    C.s_score = null;
    C c_obj = new C();
    // CHECK: iput-object {{.*}} redex.C.i_score
    c_obj.i_score = null;
    // It's possible that a null value is used as Enum and candidate enum
    // type at the same time.
    SCORE null_ptr = null;
    SCORE.increase(null_ptr);
    CAST_PARAMETER.method_accepts_enum_arg(null_ptr);
  }
}
