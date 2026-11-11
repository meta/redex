/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package redex

import java.lang.reflect.InvocationTargetException
import org.assertj.core.api.Assertions.assertThat
import org.junit.Assert.assertThrows
import org.junit.Test

// Every method opens with the same three parameter checks, so the instruction
// sequence outliner moves the checks, with their wrapper calls, into one
// outlined method. It hosts that method in Intrinsics, the class of every
// method the sequence calls.
class OutlinedChecks {
  fun first(a: String, b: String, c: String): Int = a.length + b.length * c.length

  fun second(a: String, b: String, c: String): Int = a.length * b.length + c.length

  fun third(a: String, b: String, c: String): Int = a.length - b.length * c.length

  fun fourth(a: String, b: String, c: String): Int = a.length * b.length - c.length

  fun fifth(a: String, b: String, c: String): Int = a.length + b.length + c.length
}

class DirectChecks {
  fun eleven(
      a0: String,
      a1: String,
      a2: String,
      a3: String,
      a4: String,
      a5: String,
      a6: String,
      a7: String,
      a8: String,
      a9: String,
      a10: String,
  ): Int =
      a0.length +
          a1.length +
          a2.length +
          a3.length +
          a4.length +
          a5.length +
          a6.length +
          a7.length +
          a8.length +
          a9.length +
          a10.length
}

// Small methods whose failing check builds and throws an exception: the pass
// moves that code into a split method.
class ThrowingSuffixes {
  fun checked(value: Int): Int {
    check(value >= 0) { "negative value $value" }
    return value * 2
  }
}

// The constructor initializes the receiver before its check, so the check's
// throwing code can be split.
class CheckedInit(val value: Int) {
  init {
    require(value >= 0) { "negative value $value" }
  }
}

class RareSuffixMethodSplittingTest {
  private fun failure(target: Any, name: String, args: Array<String?>): Throwable {
    val method = target.javaClass.methods.single { it.name == name }
    try {
      method.invoke(target, *args)
    } catch (e: InvocationTargetException) {
      return e.cause!!
    }
    throw AssertionError("$name accepted a null argument")
  }

  // Kotlin names the first frame below the Intrinsics frames as the caller and
  // removes the Intrinsics frames from the trace.
  private fun assertNamesFirstFrame(e: Throwable, index: Int) {
    val caller = e.stackTrace[0]
    assertThat(e.message)
        .isEqualTo(
            "Parameter specified as non-null is null: method " +
                "${caller.className}.${caller.methodName}, parameter param at index = $index",
        )
    assertThat(e.stackTrace.map { it.className }).doesNotContain("kotlin.jvm.internal.Intrinsics")
  }

  @Test
  fun directCallSite() {
    val e = failure(DirectChecks(), "eleven", Array(11) { if (it == 10) null else "x" })
    assertThat(e).isInstanceOf(NullPointerException::class.java)
    assertNamesFirstFrame(e, 10)
    assertThat(e.stackTrace[0].className).isEqualTo("redex.DirectChecks")
    assertThat(e.stackTrace[0].methodName).isEqualTo("eleven")
  }

  @Test
  fun outlinedCallSite() {
    val e = failure(OutlinedChecks(), "second", arrayOf("a", null, "c"))
    assertThat(e).isInstanceOf(NullPointerException::class.java)
    assertNamesFirstFrame(e, 1)
    assertThat(e.stackTrace[0].className).isEqualTo("redex.OutlinedChecks")
    assertThat(e.stackTrace[0].methodName).isEqualTo("second")
  }

  // The exception is created in the split method (or in code outlined from
  // it), which the original method calls.
  private fun assertSplitFrame(
      e: Throwable,
      className: String,
      methodName: String,
      prefix: String,
  ) {
    val frames = e.stackTrace
    val split = frames.indexOfFirst { it.methodName.startsWith(prefix) }
    assertThat(split).isNotNegative()
    assertThat(frames[split + 1].className).isEqualTo(className)
    assertThat(frames[split + 1].methodName).isEqualTo(methodName)
  }

  @Test
  fun splitThrowingSuffix() {
    assertThat(ThrowingSuffixes().checked(3)).isEqualTo(6)
    val e = assertThrows(IllegalStateException::class.java) { ThrowingSuffixes().checked(-1) }
    assertThat(e.message).isEqualTo("negative value -1")
    assertSplitFrame(e, "redex.ThrowingSuffixes", "checked", "checked\$split\$")
  }

  @Test
  fun splitConstructorThrowingSuffix() {
    assertThat(CheckedInit(3).value).isEqualTo(3)
    val e = assertThrows(IllegalArgumentException::class.java) { CheckedInit(-1) }
    assertThat(e.message).isEqualTo("negative value -1")
    assertSplitFrame(e, "redex.CheckedInit", "<init>", "\$init\$\$split\$")
  }

  @Test
  fun legacyBuiltin() {
    val e = failure(LegacyChecks(), "legacy", arrayOf("a", null))
    assertThat(e).isInstanceOf(IllegalArgumentException::class.java)
    assertNamesFirstFrame(e, 1)
    assertThat(e.stackTrace[0].className).isEqualTo("redex.LegacyChecks")
    assertThat(e.stackTrace[0].methodName).isEqualTo("legacy")
  }
}
