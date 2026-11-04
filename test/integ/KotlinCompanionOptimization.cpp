/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DexUtil.h"
#include "KotlinCompanionOptimizationPass.h"
#include "LocalDcePass.h"
#include "MethodDevirtualizationPass.h"
#include "RedexTest.h"
#include "Show.h"
#include "Trace.h"

class KotlinCompanionOptimizationTest : public RedexIntegrationTest {
 protected:
  void dump_cls(DexClass* cls) {
    TRACE(KOTLIN_COMPANION, 5, "Class %s", SHOW(cls));
    std::vector<DexMethod*> methods = cls->get_all_methods();
    std::vector<DexField*> fields = cls->get_all_fields();
    for (auto* v : fields) {
      TRACE(KOTLIN_COMPANION, 5, "Field %s", SHOW(v));
    }
    for (auto* v : methods) {
      TRACE(KOTLIN_COMPANION, 5, "Method %s", SHOW(v));
      TRACE(KOTLIN_COMPANION, 5, "%s", SHOW(v->get_code()));
    }
  }

  void set_root_method(const std::string& full_name) {
    auto* method = DexMethod::get_method(full_name)->as_def();
    ASSERT_NE(nullptr, method);
    method->rstate.set_root();
  }
};
namespace {

// Test basic companion optimization: companion object methods are relocated
// to the outer class as static methods and virtual calls are rewritten to
// static calls.
//
// Input (KotlinCompanionOptimization.kt):
//   CompanionClass has a companion with getSomeStr (property accessor)
//   AnotherCompanionClass has a companion with @JvmStatic
//     getSomeOtherStr and funX
//
// After optimization, Foo.main() should contain only static calls into
// the outer classes (no virtual calls through the companion instance).
TEST_F(KotlinCompanionOptimizationTest, CompanionMethodsRelocatedToStatic) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/Foo;.main:()V");
  auto* main_method =
      DexMethod::get_method("Lcom/facebook/redextest/objtest/Foo;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);
  DexType* main = DexType::get_type("Lcom/facebook/redextest/objtest/Foo;");
  DexType* outer1 =
      DexType::get_type("Lcom/facebook/redextest/objtest/CompanionClass;");
  DexType* outer2 = DexType::get_type(
      "Lcom/facebook/redextest/objtest/AnotherCompanionClass;");
  dump_cls(type_class(main));
  dump_cls(type_class(outer1));
  dump_cls(type_class(outer2));
  auto iterable = InstructionIterable(codex);
  unsigned static_calls = 0;
  std::unordered_set<DexType*> outer_classes;
  outer_classes.insert(outer1);
  outer_classes.insert(outer2);
  for (const auto& mie : iterable) {
    auto* insn = mie.insn;
    if (!opcode::is_an_invoke(insn->opcode())) {
      continue;
    }
    if (insn->opcode() == OPCODE_INVOKE_STATIC) {
      static_calls++;
      DexType* cls = insn->get_method()->get_class();
      ASSERT_EQ(outer_classes.count(cls), 1);
    }
  }
  // After optimization, there should be exactly 3 static calls in Foo.main():
  //   1. CompanionClass.getSomeStr (property accessor for someStr)
  //   2. AnotherCompanionClass.getSomeOtherStr (property accessor)
  //   3. AnotherCompanionClass.funX
  ASSERT_EQ(static_calls, 3);
}

// Test method name collision: when the outer class and its companion both
// define a method with the same name (get()), the pass must rename the
// relocated companion method to avoid a conflict.
//
// Input (KotlinCompanionOptimization.kt — CompanionWithMethodCollision):
//   CompanionWithMethodCollision.get() returns "test1"  (outer class method)
//   CompanionWithMethodCollision.Companion.get() returns "test2"  (companion)
//
// After optimization, the companion's get() is relocated to the outer class
// as a static method renamed to "get$CompanionWithMethodCollision$Companion"
// to avoid colliding with the outer class's existing get().
TEST_F(KotlinCompanionOptimizationTest, MethodNameCollisionRenaming) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/CollisionTestCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/CollisionTestCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);
  DexType* main =
      DexType::get_type("Lcom/facebook/redextest/objtest/CollisionTestCaller;");
  DexType* outer1 = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithMethodCollision;");
  dump_cls(type_class(main));
  dump_cls(type_class(outer1));
  auto iterable = InstructionIterable(codex);
  unsigned static_calls = 0;
  std::unordered_set<DexType*> outer_classes;
  outer_classes.insert(outer1);
  for (const auto& mie : iterable) {
    auto* insn = mie.insn;
    if (!opcode::is_an_invoke(insn->opcode())) {
      continue;
    }
    if (insn->opcode() == OPCODE_INVOKE_STATIC) {
      static_calls++;
      DexType* cls = insn->get_method()->get_class();
      // The relocated method is renamed to avoid colliding with the outer
      // class's own get() method.
      ASSERT_EQ(insn->get_method()->get_name()->str(),
                "get$CompanionWithMethodCollision$Companion");
      ASSERT_EQ(outer_classes.count(cls), 1);
    }
  }
  // Exactly one static call: the renamed companion get().
  // The outer class's own get() is called via invoke-virtual, not static.
  ASSERT_EQ(static_calls, 1);
}

// Test that named companion objects are not relocated.
// The pass only handles default-named $Companion inner classes.
//
// Input (KotlinCompanionOptimization.kt — NamedCompanionClass):
//   NamedCompanionClass has "companion object Custom" which compiles to
//   NamedCompanionClass$Custom — not $Companion.
//
// After running the pass, NamedCompanionCaller.main() should still contain
// virtual calls through the companion instance, not static calls into the
// outer class.
TEST_F(KotlinCompanionOptimizationTest, NamedCompanionNotRelocated) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/NamedCompanionCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/NamedCompanionCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  auto iterable = InstructionIterable(codex);
  unsigned static_calls_to_outer = 0;
  DexType* outer =
      DexType::get_type("Lcom/facebook/redextest/objtest/NamedCompanionClass;");
  for (const auto& mie : iterable) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_INVOKE_STATIC &&
        insn->get_method()->get_class() == outer) {
      static_calls_to_outer++;
    }
  }
  // Named companion (NamedCompanionClass$Custom) should NOT be relocated,
  // so there should be no static calls into NamedCompanionClass from the pass.
  ASSERT_EQ(static_calls_to_outer, 0);
}

// Test companion methods calling each other: exercises the simplified
// uses_this() check, rewrite_this_calls_to_static(), and two-pass relocation.
//
// Input: CompanionWithInterCalls has a companion with methodA and methodB
// that call each other via `this`.  The old uses_this() would reject these
// methods; the new one accepts them because the only uses of `this` are
// same-class invoke-virtual calls.
//
// After optimization:
//   - Both methodA and methodB are relocated to CompanionWithInterCalls
//     as static methods
//   - InterCallsCaller.main() calls them via invoke-static
//   - The intra-companion calls (methodA->methodB, methodB->methodA) are
//     also rewritten to invoke-static
TEST_F(KotlinCompanionOptimizationTest, CompanionInterCalls) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/InterCallsCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/InterCallsCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithInterCalls;");
  ASSERT_NE(nullptr, outer);
  dump_cls(type_class(outer));

  // Both methods should be relocated to the outer class as static methods.
  auto* methodA = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithInterCalls;.methodA:(I)I");
  auto* methodB = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithInterCalls;.methodB:(I)I");
  ASSERT_NE(nullptr, methodA);
  ASSERT_NE(nullptr, methodB);
  ASSERT_TRUE(methodA->is_def());
  ASSERT_TRUE(methodB->is_def());
  ASSERT_TRUE(is_static(methodA->as_def()));
  ASSERT_TRUE(is_static(methodB->as_def()));

  // The inter-calls inside methodA/methodB should now be invoke-static.
  auto check_internal_calls = [](DexMethodRef* m) {
    auto* code = m->as_def()->get_code();
    auto iterable = InstructionIterable(code);
    for (const auto& mie : iterable) {
      if (opcode::is_an_invoke(mie.insn->opcode())) {
        ASSERT_EQ(mie.insn->opcode(), OPCODE_INVOKE_STATIC)
            << "Expected invoke-static in " << show(m) << " but found "
            << show(mie.insn);
      }
    }
  };
  check_internal_calls(methodA);
  check_internal_calls(methodB);

  // InterCallsCaller.main() should have only static calls into the outer class.
  auto iterable = InstructionIterable(codex);
  unsigned static_calls = 0;
  for (const auto& mie : iterable) {
    auto* insn = mie.insn;
    if (!opcode::is_an_invoke(insn->opcode())) {
      continue;
    }
    if (insn->opcode() == OPCODE_INVOKE_STATIC) {
      static_calls++;
      ASSERT_EQ(insn->get_method()->get_class(), outer);
    }
  }
  // methodA and methodB
  ASSERT_EQ(static_calls, 2);
}

// Test @JvmStatic bridge rename: when KeepThis::No makes the companion
// method's proto match the existing @JvmStatic bridge on the outer class,
// the bridge is renamed to "$companion_bridge" to free the name for the
// relocated companion method.
//
// Input: CompanionWithJvmStaticBridge has a companion with @JvmStatic
// compute(Int):Int.  Kotlin generates a static bridge on the outer class
// with the same name/proto.
//
// After optimization:
//   - The bridge is renamed to "compute$companion_bridge"
//   - The companion method takes the name "compute" on the outer class
//   - JvmStaticBridgeCaller.main() calls via invoke-static "compute"
TEST_F(KotlinCompanionOptimizationTest, JvmStaticBridgeRename) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/JvmStaticBridgeCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/JvmStaticBridgeCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithJvmStaticBridge;");
  ASSERT_NE(nullptr, outer);
  dump_cls(type_class(outer));

  // The companion's compute() should now be on the outer class.
  auto* compute = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithJvmStaticBridge;"
      ".compute:(I)I");
  ASSERT_NE(nullptr, compute);
  ASSERT_TRUE(compute->is_def());
  ASSERT_TRUE(is_static(compute->as_def()));

  // The old @JvmStatic bridge should be renamed to $companion_bridge.
  auto* bridge = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithJvmStaticBridge;"
      ".compute$companion_bridge:(I)I");
  ASSERT_NE(nullptr, bridge);
  ASSERT_TRUE(bridge->is_def());
  ASSERT_TRUE(is_static(bridge->as_def()));

  // Callers of the renamed bridge must be redirected to the relocated method.
  // JvmStaticBridgeCaller.main() originally called the @JvmStatic bridge via
  // invoke-static; after the fix, it should call the relocated compute()
  // instead of the renamed compute$companion_bridge.
  auto iterable = InstructionIterable(codex);
  unsigned static_calls = 0;
  for (const auto& mie : iterable) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_INVOKE_STATIC &&
        insn->get_method()->get_class() == outer) {
      static_calls++;
      ASSERT_EQ(insn->get_method()->get_name()->str(), "compute")
          << "Caller should be redirected to relocated compute(), not the "
             "renamed bridge";
    }
  }
  ASSERT_EQ(static_calls, 1);
}

// Test @JvmStatic bridge with a keep rule (simulating reflection).
// When the bridge has can_rename() == false (e.g., kept by a proguard rule
// like `-keepclassmembers ... parseData`), the pass must NOT rename it.
// The companion method should be renamed on collision instead.
//
// This reproduces the bug in T262077911 where parseFromJson was renamed to
// parseFromJson$companion_bridge, breaking Class.getMethod("parseFromJson").
TEST_F(KotlinCompanionOptimizationTest, JvmStaticKeptBridgeNotRenamed) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/KeptBridgeCaller;.main:()V");

  // Mark the @JvmStatic bridge on the outer class as a root, simulating a
  // proguard `-keepclassmembers` rule that prevents renaming.
  auto* bridge = DexMethod::get_method(
                     "Lcom/facebook/redextest/objtest/CompanionWithKeptBridge;"
                     ".parseData:(I)Ljava/lang/String;")
                     ->as_def();
  ASSERT_NE(nullptr, bridge);
  bridge->rstate.set_keepnames();

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithKeptBridge;");
  ASSERT_NE(nullptr, outer);
  dump_cls(type_class(outer));

  // The bridge must keep its original name — reflection depends on it.
  auto* kept_bridge = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithKeptBridge;"
      ".parseData:(I)Ljava/lang/String;");
  ASSERT_NE(nullptr, kept_bridge) << "Kept bridge must not be renamed";
  ASSERT_TRUE(kept_bridge->is_def());
  ASSERT_TRUE(is_static(kept_bridge->as_def()));

  // The bridge must NOT be renamed to $companion_bridge.
  auto* renamed = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithKeptBridge;"
      ".parseData$companion_bridge:(I)Ljava/lang/String;");
  ASSERT_EQ(nullptr, renamed)
      << "Kept bridge must not be renamed to $companion_bridge";
}

// Test @JvmStatic on a private external fun in a companion.  kotlinc places
// the actual native method (initNative) on the outer class as a static native
// bridge with no code.  The pass must NOT rename this native method — JNI
// registration depends on the exact name.  The companion's non-native method
// (helper) should still be relocated.
//
// Input: CompanionWithNativeMethod has a companion with:
//   - @JvmStatic private external fun initNative(Int): Long  (native)
//   - fun helper(): String  (non-native)
//
// After optimization:
//   - The native initNative bridge on the outer class keeps its original name
//   - helper is relocated from companion to outer class
//   - The companion's initNative wrapper is renamed on collision
TEST_F(KotlinCompanionOptimizationTest, JvmStaticNativeMethodNotRenamed) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/NativeMethodCaller;.main:()V");

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithNativeMethod;");
  ASSERT_NE(nullptr, outer);
  dump_cls(type_class(outer));

  // The native initNative method on the outer class must keep its original
  // name — it must NOT be renamed to initNative$companion_bridge.
  auto* native_method = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithNativeMethod;"
      ".initNative:(I)J");
  ASSERT_NE(nullptr, native_method)
      << "Native method initNative must keep its original name";
  ASSERT_TRUE(native_method->is_def());
  ASSERT_TRUE(is_static(native_method->as_def()));
  // Native methods have no code.
  ASSERT_EQ(nullptr, native_method->as_def()->get_code());

  // There must NOT be a renamed native method.
  auto* renamed = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithNativeMethod;"
      ".initNative$companion_bridge:(I)J");
  ASSERT_EQ(nullptr, renamed)
      << "Native method must not be renamed to $companion_bridge";

  // helper() should be relocated from companion to outer class.
  auto* helper = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithNativeMethod;"
      ".helper:()Ljava/lang/String;");
  ASSERT_NE(nullptr, helper);
  ASSERT_TRUE(helper->is_def());
  ASSERT_TRUE(is_static(helper->as_def()));
}

// Test abstract outer class: the companion's methods should still be relocated
// to the abstract outer class as static methods.  Abstract classes can have
// static methods, so this is valid.
//
// Input: AbstractOuterClass is abstract and has a companion with helperFunc().
//
// After optimization:
//   - helperFunc is relocated to AbstractOuterClass as a static method
//   - AbstractOuterCaller.main() calls it via invoke-static
TEST_F(KotlinCompanionOptimizationTest, AbstractOuterClassCompanion) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/AbstractOuterCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/AbstractOuterCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer =
      DexType::get_type("Lcom/facebook/redextest/objtest/AbstractOuterClass;");
  ASSERT_NE(nullptr, outer);

  // The companion's helperFunc() should be relocated to the outer class.
  auto* helperFunc = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/AbstractOuterClass;"
      ".helperFunc:()Ljava/lang/String;");
  ASSERT_NE(nullptr, helperFunc);
  ASSERT_TRUE(helperFunc->is_def());
  ASSERT_TRUE(is_static(helperFunc->as_def()));
}

// Test interface outer class: interface methods must not be final, so the pass
// drops ACC_FINAL from the companion methods it relocates into an interface.
//
// Input: InterfaceOuter is an interface whose companion has the final method
// helperFunc().
//
// After optimization:
//   - helperFunc is relocated to InterfaceOuter as a static, non-final method
TEST_F(KotlinCompanionOptimizationTest, InterfaceOuterClassCompanion) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/InterfaceOuterCaller;.main:()V");

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  auto* helperFunc = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/InterfaceOuter;"
      ".helperFunc:()Ljava/lang/String;");
  ASSERT_NE(nullptr, helperFunc);
  ASSERT_TRUE(helperFunc->is_def());
  ASSERT_TRUE(is_interface(type_class(helperFunc->get_class())));
  ASSERT_TRUE(is_static(helperFunc->as_def()));
  ASSERT_FALSE(is_final(helperFunc->as_def()));
}

// Test companion with const val: the companion has a <clinit> that initializes
// $$INSTANCE, producing the sget-object/sput-object pattern that
// is_def_trackable must allowlist.
//
// Input: CompanionWithConstVal has a companion with `const val MAGIC = 42`
// and getMagic().  The companion has a clinit for $$INSTANCE.
//
// After optimization:
//   - getMagic is relocated to CompanionWithConstVal as a static method
//   - ConstValCaller.main() calls it via invoke-static
TEST_F(KotlinCompanionOptimizationTest, CompanionWithConstVal) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/ConstValCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/ConstValCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal;");
  ASSERT_NE(nullptr, outer);

  // The companion's getMagic() should be relocated to the outer class.
  auto* getMagic = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal;"
      ".getMagic:()I");
  ASSERT_NE(nullptr, getMagic);
  ASSERT_TRUE(getMagic->is_def());
  ASSERT_TRUE(is_static(getMagic->as_def()));
}

// Test non-final companion with no subclasses: strip ACC_FINAL from the
// companion class before running the pass.  The pass should still accept it
// via the class hierarchy check (no subclasses).
TEST_F(KotlinCompanionOptimizationTest, NonFinalCompanionNoSubclasses) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/InterCallsCaller;.main:()V");

  // Strip ACC_FINAL from CompanionWithInterCalls$Companion before running.
  auto* companion_cls = type_class(DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithInterCalls$Companion;"));
  ASSERT_NE(nullptr, companion_cls);
  ASSERT_TRUE(is_final(companion_cls));
  companion_cls->set_access(companion_cls->get_access() & ~ACC_FINAL);
  ASSERT_FALSE(is_final(companion_cls));

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // Despite not being final, the companion should still be relocated
  // because it has no subclasses.
  auto* methodA = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithInterCalls;.methodA:(I)I");
  ASSERT_NE(nullptr, methodA);
  ASSERT_TRUE(methodA->is_def());
  ASSERT_TRUE(is_static(methodA->as_def()));
}

// Test non-final companion with a parameterized method: strip ACC_FINAL from
// both the class and its virtual method.  The method-level is_final check
// is redundant when the class has no subclasses — the method should still
// be relocated.
TEST_F(KotlinCompanionOptimizationTest, NonFinalMethodNoSubclasses) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/JvmStaticBridgeCaller;.main:()V");

  // Strip ACC_FINAL from the companion class AND its compute method.
  auto* companion_cls =
      type_class(DexType::get_type("Lcom/facebook/redextest/objtest/"
                                   "CompanionWithJvmStaticBridge$Companion;"));
  ASSERT_NE(nullptr, companion_cls);
  companion_cls->set_access(companion_cls->get_access() & ~ACC_FINAL);

  for (auto* m : companion_cls->get_vmethods()) {
    if (m->get_name()->str() == "compute") {
      ASSERT_TRUE(is_final(m));
      m->set_access(m->get_access() & ~ACC_FINAL);
      ASSERT_FALSE(is_final(m));
    }
  }

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // compute should be relocated despite the class and method not being final.
  auto* outerCompute = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithJvmStaticBridge;"
      ".compute:(I)I");
  ASSERT_NE(nullptr, outerCompute)
      << "compute should be relocated even with non-final class and method";
  ASSERT_TRUE(outerCompute->is_def());
  ASSERT_TRUE(is_static(outerCompute->as_def()));
}

// Test @Synchronized companion method: the companion must NOT be relocated
// because @Synchronized generates MONITOR_ENTER on the companion instance.
TEST_F(KotlinCompanionOptimizationTest, SynchronizedCompanionNotRelocated) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/SynchronizedCaller;.main:()V");

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // addItem should NOT be relocated — @Synchronized uses companion as lock.
  auto* companion_addItem = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithSynchronized$Companion;"
      ".addItem:(Lcom/facebook/redextest/objtest/CompanionWithSynchronized;"
      "Ljava/lang/String;)V");
  ASSERT_NE(nullptr, companion_addItem)
      << "addItem should NOT be relocated (@Synchronized uses companion lock)";
  ASSERT_TRUE(companion_addItem->is_def());
  ASSERT_EQ(companion_addItem->as_def()->get_class(),
            DexType::get_type("Lcom/facebook/redextest/objtest/"
                              "CompanionWithSynchronized$Companion;"));
}

// Test cross-store rejection: move the companion to a secondary store while
// keeping the outer class in the root store.  The pass should reject the
// companion because relocating methods across stores is unsafe.
TEST_F(KotlinCompanionOptimizationTest, CrossStoreCompanionNotRelocated) {
  set_root_method("Lcom/facebook/redextest/objtest/ConstValCaller;.main:()V");

  // Move CompanionWithConstVal$Companion to a secondary store.
  auto* companion_cls = type_class(DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal$Companion;"));
  ASSERT_NE(nullptr, companion_cls);

  auto& root_store = stores.at(0);
  auto& root_dex_classes = root_store.get_dexen().at(0);
  root_dex_classes.erase(std::find(
      root_dex_classes.begin(), root_dex_classes.end(), companion_cls));

  DexMetadata secondary_metadata;
  secondary_metadata.set_id("SecondaryModule");
  DexStore secondary_store(secondary_metadata);
  secondary_store.add_classes(std::vector<DexClass*>{companion_cls});
  stores.emplace_back(secondary_store);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // getMagic should NOT be relocated — companion is in a different store.
  auto* companion_getMagic = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal$Companion;"
      ".getMagic:()I");
  ASSERT_NE(nullptr, companion_getMagic);
  ASSERT_TRUE(companion_getMagic->is_def());
  ASSERT_EQ(
      companion_getMagic->as_def()->get_class(),
      DexType::get_type(
          "Lcom/facebook/redextest/objtest/CompanionWithConstVal$Companion;"));
}

// Test companion method after MethodDevirtualizationPass: run devirtualization
// first, then the companion pass.  MethodDevirtualizationPass makes companion
// methods static (removing `this`) when they don't use `this`, but leaves them
// in vmethods.  The companion pass should still accept these devirtualized
// methods.
TEST_F(KotlinCompanionOptimizationTest, DevirtualizedCompanionMethod) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/ConstValCaller;.main:()V");

  // First, verify getMagic is virtual.
  auto* companion_cls = type_class(DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal$Companion;"));
  ASSERT_NE(nullptr, companion_cls);
  bool found_virtual = false;
  for (auto* m : companion_cls->get_vmethods()) {
    if (m->get_name()->str() == "getMagic") {
      found_virtual = true;
      ASSERT_FALSE(is_static(m));
    }
  }
  ASSERT_TRUE(found_virtual);

  // Run MethodDevirtualizationPass first — it will devirtualize getMagic
  // since it doesn't use `this`.
  auto devirt = std::make_unique<MethodDevirtualizationPass>();
  std::vector<Pass*> devirt_passes{devirt.get()};
  run_passes(devirt_passes);

  // Verify getMagic was actually devirtualized (made static).
  bool found_static = false;
  for (auto* m : companion_cls->get_vmethods()) {
    if (m->get_name()->str() == "getMagic") {
      found_static = is_static(m);
    }
  }
  // If devirt didn't touch it, check dmethods too.
  for (auto* m : companion_cls->get_dmethods()) {
    if (m->get_name()->str() == "getMagic") {
      found_static = is_static(m);
    }
  }
  ASSERT_TRUE(found_static)
      << "MethodDevirtualizationPass should have made getMagic static";

  // Now run the companion pass.
  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // getMagic should be relocated to the outer class.
  auto* outerGetMagic = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithConstVal;"
      ".getMagic:()I");
  ASSERT_NE(nullptr, outerGetMagic)
      << "getMagic should be relocated to outer class after devirtualization";
  ASSERT_TRUE(outerGetMagic->is_def());
  ASSERT_TRUE(is_static(outerGetMagic->as_def()));
}

// Test devirtualized companion method WITH parameters: run devirtualization
// first, then the companion pass.  `double(x: Int)` doesn't use `this`, so
// MethodDevirtualizationPass makes it static, removing `this` but keeping
// the `int` param.  The companion pass must not mistake the `int` param for
// `this` in its `uses_this` analysis.
TEST_F(KotlinCompanionOptimizationTest, DevirtualizedMethodWithParams) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/PureFunctionCaller;.main:()V");

  auto* companion_cls =
      type_class(DexType::get_type("Lcom/facebook/redextest/objtest/"
                                   "CompanionWithPureFunction$Companion;"));
  ASSERT_NE(nullptr, companion_cls);

  // Verify `double` is initially virtual.
  bool found_virtual = false;
  for (auto* m : companion_cls->get_vmethods()) {
    if (m->get_name()->str() == "double") {
      ASSERT_FALSE(is_static(m));
      found_virtual = true;
    }
  }
  ASSERT_TRUE(found_virtual);

  // Run MethodDevirtualizationPass — it will devirtualize `double` since
  // it doesn't use `this`.  The method becomes static with one int param.
  auto devirt = std::make_unique<MethodDevirtualizationPass>();
  std::vector<Pass*> devirt_passes{devirt.get()};
  run_passes(devirt_passes);

  // Verify `double` was devirtualized.
  bool is_now_static = false;
  for (auto* m : companion_cls->get_vmethods()) {
    if (m->get_name()->str() == "double") {
      is_now_static = is_static(m);
    }
  }
  for (auto* m : companion_cls->get_dmethods()) {
    if (m->get_name()->str() == "double") {
      is_now_static = is_static(m);
    }
  }
  ASSERT_TRUE(is_now_static)
      << "MethodDevirtualizationPass should have made double() static";

  // Now run the companion pass.
  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // double should be relocated to the outer class.
  auto* outerDouble = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithPureFunction;"
      ".double:(I)I");
  ASSERT_NE(nullptr, outerDouble) << "double(int) should be relocated to outer "
                                     "class after devirtualization";
  ASSERT_TRUE(outerDouble->is_def());
  ASSERT_TRUE(is_static(outerDouble->as_def()));
}

// Test companion whose instance escapes: a function returns the companion
// instance, which is an untrackable usage.  The companion should NOT be
// relocated.
TEST_F(KotlinCompanionOptimizationTest, CompanionEscapesNotRelocated) {
  auto scope = build_class_scope(stores);
  set_root_method("Lcom/facebook/redextest/objtest/EscapesCaller;.main:()V");

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  run_passes(passes);

  // doWork should NOT be relocated to the outer class because the companion
  // instance escapes via getCompanion().
  auto* companion_doWork = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionEscapes$Companion;"
      ".doWork:()Ljava/lang/String;");
  // doWork should still be on the companion class, not relocated.
  ASSERT_NE(nullptr, companion_doWork);
  ASSERT_TRUE(companion_doWork->is_def());
  ASSERT_EQ(companion_doWork->as_def()->get_class(),
            DexType::get_type(
                "Lcom/facebook/redextest/objtest/CompanionEscapes$Companion;"));
}

// Test companion method with default arguments: Kotlin generates a static
// $default method on the companion class whose first parameter is the
// companion instance (not VM-managed `this`).  The compiler reuses this
// register for the AND_INT_LIT bitmask check.
//
// This exercises the fix for CFG corruption: the old dead-instruction removal
// in rewrite_this_calls_to_static used raw register numbers and would
// incorrectly delete branch instructions that reused the first-param register,
// leaving a block with no successors.
//
// Input: CompanionWithDefaults has a companion with greet(String, String)
// where the second parameter has a default value.  Kotlin generates:
//   - greet(String, String):String              (virtual, on companion)
//   - greet$default(Companion, String, String, int, Object):String  (static)
//
// After optimization:
//   - Both greet and greet$default are relocated to CompanionWithDefaults
//   - DefaultArgsCaller.main() calls them via invoke-static
//   - The $default method's CFG remains valid (no crash)
TEST_F(KotlinCompanionOptimizationTest, CompanionWithDefaultArgs) {
  auto scope = build_class_scope(stores);
  set_root_method(
      "Lcom/facebook/redextest/objtest/DefaultArgsCaller;.main:()V");
  auto* main_method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/objtest/DefaultArgsCaller;.main:()V")
          ->as_def();
  auto* codex = main_method->get_code();
  ASSERT_NE(nullptr, codex);

  auto klr = std::make_unique<KotlinCompanionOptimizationPass>();
  auto dce = std::make_unique<LocalDcePass>();
  std::vector<Pass*> passes{klr.get(), dce.get()};
  // This would crash before the fix with:
  //   assertion 'num_succs > 0' failed in cfg::ControlFlowGraph::sanity_check()
  run_passes(passes);

  DexType* outer = DexType::get_type(
      "Lcom/facebook/redextest/objtest/CompanionWithDefaults;");
  ASSERT_NE(nullptr, outer);
  dump_cls(type_class(outer));

  // The companion's greet() should be relocated to the outer class.
  auto* greet = DexMethod::get_method(
      "Lcom/facebook/redextest/objtest/CompanionWithDefaults;"
      ".greet:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;");
  ASSERT_NE(nullptr, greet) << "greet not found on outer class";
  ASSERT_TRUE(greet->is_def());
  ASSERT_TRUE(is_static(greet->as_def()));

  // The $default method should also be relocated and its CFG should be valid.
  // We verify it exists on the outer class and has code (not corrupted).
  auto* outer_cls = type_class(outer);
  DexMethod* default_method = nullptr;
  for (auto* m : outer_cls->get_dmethods()) {
    if (m->get_name()->str().find("greet$default") != std::string::npos) {
      default_method = m;
      break;
    }
  }
  ASSERT_NE(nullptr, default_method)
      << "greet$default not found on outer class";
  ASSERT_TRUE(is_static(default_method));
  ASSERT_NE(nullptr, default_method->get_code()) << "greet$default has no code";
}
} // namespace
