/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redextest.objtest

// Basic companion object: the pass relocates getSomeStr (the auto-generated
// property accessor for someStr) from CompanionClass$Companion to CompanionClass
// as a static method.
class CompanionClass {
  companion object {
    var someStr: String = "Foo"
  }

  fun get(): String {
    return someStr
  }
}

// Second companion object with @JvmStatic: the pass relocates getSomeOtherStr
// and funX from AnotherCompanionClass$Companion to AnotherCompanionClass as
// static methods.
class AnotherCompanionClass {
  companion object {
    @JvmStatic var someOtherStr: String = "Bar"

    @JvmStatic
    fun funX(): String {
      return someOtherStr
    }
  }
}

class Foo {
  fun main() {
    val obj = CompanionClass()
    print(obj.get())
    print(CompanionClass.someStr)
    print(AnotherCompanionClass.someOtherStr)
    print(AnotherCompanionClass.funX())
  }
}

// Method name collision: both the outer class and the companion define get().
// When the pass relocates the companion's get() to the outer class, it must
// rename it to "get$CompanionWithMethodCollision$Companion" to avoid colliding
// with the outer class's existing get().
class CompanionWithMethodCollision {
  companion object {
    fun get(): String = "test2"
  }

  fun get(): String = "test1"
}

class CollisionTestCaller {
  fun main() {
    val obj = CompanionWithMethodCollision()
    print(obj.get())
    print(CompanionWithMethodCollision.get())
  }
}

// Named companion object: the pass should NOT relocate methods from
// NamedCompanionClass$Custom because it does not end with $Companion.
class NamedCompanionClass {
  companion object Custom {
    var someStr: String = "Baz"

    fun funY(): String {
      return someStr
    }
  }
}

class NamedCompanionCaller {
  fun main() {
    print(NamedCompanionClass.someStr)
    print(NamedCompanionClass.funY())
  }
}

// Companion methods calling each other: exercises rewrite_this_calls_to_static
// and two-pass relocation. methodA calls methodB via `this`, and methodB calls
// methodA via `this`. Both should be relocated as static methods.
class CompanionWithInterCalls {
  companion object {
    fun methodA(x: Int): Int {
      return if (x > 0) methodB(x - 1) else x
    }

    fun methodB(x: Int): Int {
      return if (x > 1) methodA(x - 2) else x
    }
  }
}

class InterCallsCaller {
  fun main() {
    print(CompanionWithInterCalls.methodA(5))
    print(CompanionWithInterCalls.methodB(3))
  }
}

// @JvmStatic bridge rename: the companion method compute() has @JvmStatic,
// which generates a static bridge on the outer class. After KeepThis::No
// drops the this parameter, the companion method's proto matches the bridge.
// The pass must rename the bridge to compute$companion_bridge to free the name.
class CompanionWithJvmStaticBridge {
  companion object {
    @JvmStatic fun compute(x: Int): Int = x * 2
  }
}

class JvmStaticBridgeCaller {
  fun main() {
    print(CompanionWithJvmStaticBridge.compute(42))
  }
}

// @JvmStatic bridge with a keep rule: the outer class bridge is kept by a
// proguard rule (simulating reflection via Class.getMethod("parseData", ...)).
// The pass must NOT rename the kept bridge.
class CompanionWithKeptBridge {
  companion object {
    @JvmStatic fun parseData(x: Int): String = "parsed:$x"
  }
}

class KeptBridgeCaller {
  fun main() {
    print(CompanionWithKeptBridge.parseData(42))
  }
}

// @JvmStatic on a private external fun: kotlinc places the actual native method
// on the outer class and a delegating wrapper on the companion. The pass must
// NOT rename the outer class's native method — JNI registration depends on the
// exact name. The companion's non-native methods should still be relocated.
class CompanionWithNativeMethod {
  companion object {
    @JvmStatic private external fun initNative(x: Int): Long

    fun helper(): String = "helper"
  }

  fun create(x: Int): Long = initNative(x)
}

class NativeMethodCaller {
  fun main() {
    val obj = CompanionWithNativeMethod()
    print(obj.create(42))
    print(CompanionWithNativeMethod.helper())
  }
}

// Abstract outer class with a companion object: the pass should still relocate
// the companion's methods to the abstract outer class as static methods.
// Abstract classes can have static methods, so this is valid.
abstract class AbstractOuterClass {
  companion object {
    fun helperFunc(): String = "abstract_helper"
  }

  abstract fun doWork(): String
}

class ConcreteSubclass : AbstractOuterClass() {
  override fun doWork(): String = helperFunc()
}

class AbstractOuterCaller {
  fun main() {
    print(AbstractOuterClass.helperFunc())
    print(ConcreteSubclass().doWork())
  }
}

// Interface outer class with a companion object: the pass relocates the
// companion's final helperFunc() to the interface, where methods must not be
// final.
interface InterfaceOuter {
  companion object {
    fun helperFunc(): String = "interface_helper"
  }
}

class InterfaceOuterCaller {
  fun main() {
    print(InterfaceOuter.helperFunc())
  }
}

// Companion with a const val property: the companion has a <clinit> that
// initializes $$INSTANCE, and the standard clinit pattern includes
// sget-object $$INSTANCE followed by sput-object OuterClass.Companion.
// This exercises the SPUT_OBJECT allowlist in is_def_trackable.
class CompanionWithConstVal {
  companion object {
    const val MAGIC = 42

    fun getMagic(): Int = MAGIC
  }
}

class ConstValCaller {
  fun main() {
    print(CompanionWithConstVal.getMagic())
  }
}

// Companion whose instance escapes: the companion is returned from a method,
// which is an untrackable usage that should prevent optimization.
class CompanionEscapes {
  companion object {
    fun doWork(): String = "work"
  }
}

fun getCompanion(): CompanionEscapes.Companion = CompanionEscapes.Companion

class EscapesCaller {
  fun main() {
    print(CompanionEscapes.doWork())
    print(getCompanion())
  }
}

// Companion with a pure function that takes a parameter but doesn't use `this`.
// After MethodDevirtualizationPass, this method becomes static with one param.
class CompanionWithPureFunction {
  companion object {
    fun double(x: Int): Int = x * 2
  }
}

class PureFunctionCaller {
  fun main() {
    print(CompanionWithPureFunction.double(21))
  }
}

// Companion with @Synchronized method: Kotlin generates MONITOR_ENTER on the
// companion instance.  After devirtualization, the companion instance becomes
// an explicit first parameter, but the MONITOR_ENTER still references it.
// This companion must NOT be relocated.
class CompanionWithSynchronized {
  var data = mutableListOf<String>()

  companion object {
    @Synchronized
    fun addItem(outer: CompanionWithSynchronized, item: String) {
      outer.data.add(item)
    }

    @Synchronized fun getSize(outer: CompanionWithSynchronized): Int = outer.data.size
  }
}

class SynchronizedCaller {
  fun main() {
    val obj = CompanionWithSynchronized()
    CompanionWithSynchronized.addItem(obj, "hello")
    print(CompanionWithSynchronized.getSize(obj))
  }
}

// Companion method with default arguments: Kotlin generates a static $default
// method on the companion class. This method takes the companion instance as
// its first parameter (it's already static), and the compiler reuses that
// register for the AND_INT_LIT bitmask check.  The pass must handle this
// without corrupting the $default method's CFG.
class CompanionWithDefaults {
  companion object {
    fun greet(name: String, greeting: String = "Hello"): String {
      return "$greeting, $name!"
    }
  }
}

class DefaultArgsCaller {
  fun main() {
    // Uses default value for greeting — generates call to greet$default
    print(CompanionWithDefaults.greet("World"))
    // Explicit value — direct call to greet
    print(CompanionWithDefaults.greet("World", "Hi"))
  }
}
