/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ApiLevelChecker.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DexAsm.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "StaticReloV2.h"

namespace static_relo_v2 {

struct StaticReloV2Test : public RedexTest {
  DexProto* m_proto;

  StaticReloV2Test() {
    m_proto =
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  }

  DexClass* create_class(const char* class_name) {
    ClassCreator cc(DexType::make_type(class_name));
    cc.set_super(type::java_lang_Object());
    return cc.create();
  }

  DexMethod* create_method(DexClass* cls,
                           const char* method_name,
                           DexAccessFlags access) {
    DexMethod* method =
        DexMethod::make_method(cls->get_type(),
                               DexString::make_string(method_name), m_proto)
            ->make_concrete(access, false);
    method->set_code(std::make_unique<IRCode>(method, 1));
    method->get_code()->push_back(dex_asm::dasm(OPCODE_RETURN_VOID));
    method->get_code()->build_cfg();
    cls->add_method(method);
    return method;
  }

  void call(DexMethod* caller, DexMethod* callee) {
    IRInstruction* inst = new IRInstruction(OPCODE_INVOKE_STATIC);
    inst->set_method(callee);
    auto& cfg = caller->get_code()->cfg();
    auto ii = cfg::InstructionIterable(cfg);
    cfg.insert_before(ii.begin(), inst);
  }
};

/**
 * If public static methods are only referenced once, relocate them to the
 * caller class
 *
 * Input:
 * A.a -> B.b -> Other.c
 *
 * class A { public static void a() {}
 * }
 * class B {
 *   public static void b() {
 *     A.a();
 *   }
 * }
 * class Other {
 *   public void c() {
 *     B.b();
 *   }
 * }
 *
 * Output:
 * Other.a -> Other.b -> Other.c
 * class A {}
 * class B {}
 * class Other {
 *   public void c() {
 *     b();
 *   }
 *   public static a() {}
 *   public static b() {
 *     a();
 *   }
 * }
 */
TEST_F(StaticReloV2Test, staticMethodsOnlyRefedOnce) {
  DexClass* classA = create_class("A");
  DexMethod* method_a = create_method(classA, "a", ACC_PUBLIC | ACC_STATIC);
  DexClass* classB = create_class("B");
  DexMethod* method_b = create_method(classB, "b", ACC_PUBLIC | ACC_STATIC);
  DexClass* classOther = create_class("Other");
  DexMethod* method_c = create_method(classOther, "c", ACC_PUBLIC);

  call(method_b, method_a);
  call(method_c, method_b);

  Scope scope({classA, classB, classOther});
  api::LevelChecker::init(0, scope);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes.size(), 2);
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classA),
      candidate_classes.end());
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classB),
      candidate_classes.end());
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);
  EXPECT_EQ(relocated_methods, 2);
  EXPECT_EQ(method_a->get_class(), classOther->get_type());
  EXPECT_EQ(method_b->get_class(), classOther->get_type());
  EXPECT_EQ(method_c->get_class(), classOther->get_type());
}

/**
 * If public static methods are a cluster and only referenced by one other
 * class, relocate all of them into the caller class
 *
 * Input:
 * // A.a has higher api level.
 * A.a -> B.b -> Other.c
 * B.b -> A.a
 * A.a -> Other.c
 *
 * class A {
 *   public static void a() {
 *     B.b();
 *   }
 * }
 * class B {
 *   public static void b() {
 *     A.a();
 *   }
 * }
 * class Other {
 *   public void c() {
 *     B.b();
 *     A.a();
 *   }
 * }
 *
 * Output:
 * // Not relocate A.a because it has higher api level.
 * A.a -> Other.b -> Other.c
 * A.a -> Other.c
 * class A {
 *   public static void a() {}
 * }
 * class B {}
 * class Other {}
 *   public static void b() {
 *     A.a();
 *   }
 *   public void c() {
 *     b();
 *     A.a();
 *   }
 * }
 */
TEST_F(StaticReloV2Test, clusterRefedByOneClass) {
  DexClass* classA = create_class("A");
  DexMethod* method_a = create_method(classA, "a", ACC_PUBLIC | ACC_STATIC);
  DexClass* classB = create_class("B");
  DexMethod* method_b = create_method(classB, "b", ACC_PUBLIC | ACC_STATIC);
  DexClass* classOther = create_class("Other");
  DexMethod* method_c = create_method(classOther, "c", ACC_PUBLIC);

  call(method_a, method_b);
  call(method_b, method_a);
  call(method_c, method_b);
  call(method_c, method_a);

  Scope scope({classA, classB, classOther});
  api::LevelChecker::init(0, scope);
  method_a->rstate.set_api_level(1);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes.size(), 2);
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classA),
      candidate_classes.end());
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classB),
      candidate_classes.end());
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);
  EXPECT_EQ(relocated_methods, 1);
  EXPECT_EQ(method_a->get_class(), classA->get_type());
  EXPECT_EQ(method_b->get_class(), classOther->get_type());
  EXPECT_EQ(method_c->get_class(), classOther->get_type());
}

/**
 * If a static method referenced by multiple other classes, do not relocate.
 *
 * Input:
 * A.a -> Other1.b
 * A.a -> Other2.c
 * class A {
 *   public static void a() {}
 * }
 * class Other1 {
 *   public void b() {
 *     A.a();
 *   }
 * }
 * class Other2 {
 *   public void c() {
 *     A.a();
 *   }
 * }
 */
TEST_F(StaticReloV2Test, staticMethodRefedByMany) {
  DexClass* classA = create_class("A");
  DexMethod* method_a = create_method(classA, "a", ACC_PUBLIC | ACC_STATIC);
  DexClass* classOther1 = create_class("Other1");
  DexMethod* method_b = create_method(classOther1, "b", ACC_PUBLIC);
  DexClass* classOther2 = create_class("Other2");
  DexMethod* method_c = create_method(classOther2, "c", ACC_PUBLIC);

  call(method_b, method_a);
  call(method_c, method_a);

  Scope scope({classA, classOther1, classOther2});
  api::LevelChecker::init(0, scope);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes.size(), 1);
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classA),
      candidate_classes.end());
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);
  EXPECT_EQ(relocated_methods, 0);
}

/**
 * If a private static method is referenced by another class, its related method
 * within the same class should also be relocated properly
 *
 * Input:
 * Inner.a -> Inner.b
 * Inner.a -> Other.c
 *
 * class Outer {
 *   class Inner {
 *     private static void a() {}
 *     public static void b() { a(); }
 *     public static void c() {}
 *   }
 *   public void d() {
 *     Inner.a()
 *   }
 * }
 *
 * Output:
 * a and b are relocated to Outer, c keeps unchanged.
 */
TEST_F(StaticReloV2Test, relocatePrivateStaticMethod) {
  DexClass* classInner = create_class("Inner");
  DexMethod* method_private_a =
      create_method(classInner, "a", ACC_PRIVATE | ACC_STATIC);
  DexMethod* method_b = create_method(classInner, "b", ACC_PUBLIC | ACC_STATIC);
  DexMethod* method_c = create_method(classInner, "c", ACC_PUBLIC | ACC_STATIC);
  DexClass* classOuter = create_class("Outer");
  DexMethod* method_d = create_method(classOuter, "d", ACC_PUBLIC);

  call(method_b, method_private_a);
  call(method_d, method_private_a);

  Scope scope({classInner, classOuter});
  api::LevelChecker::init(0, scope);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes.size(), 1);
  EXPECT_NE(
      std::find(candidate_classes.begin(), candidate_classes.end(), classInner),
      candidate_classes.end());
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);

  EXPECT_EQ(relocated_methods, 2);
  EXPECT_EQ(method_private_a->get_class(), classOuter->get_type());
  EXPECT_EQ(method_b->get_class(), classOuter->get_type());
  EXPECT_EQ(method_c->get_class(), classInner->get_type());
}

/**
 * A static method that holds an invoke-direct method handle of a method that
 * is not private (tool-generated) stays in its class: ART runs the
 * implementation of the method that the holding class has, which `Screen`,
 * not a subclass of `Base`, does not have.
 *
 * class Base { public void log() {} }
 * class Logging extends Base {
 *   public static void logAsBase(Base b) {
 *     MethodHandle h = const-method-handle invoke-direct LBase;.log:()V;
 *     h.invokeExact(b);
 *   }
 * }
 * class Screen {
 *   public void show(Base b) { Logging.logAsBase(b); }
 * }
 */
TEST_F(StaticReloV2Test, keepMethodWithMethodHandleThatCallsLikeSuper) {
  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  auto* log = DexMethod::make_method("LBase;.log:()V")
                  ->make_concrete(ACC_PUBLIC,
                                  assembler::ircode_from_string(
                                      "((load-param-object v0) (return-void))"),
                                  /*is_virtual=*/true);
  base_creator.add_method(log);
  DexClass* class_base = base_creator.create();

  ClassCreator logging_creator(DexType::make_type("LLogging;"));
  logging_creator.set_super(class_base->get_type());
  auto* log_as_base = DexMethod::make_method("LLogging;.logAsBase:(LBase;)V")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                          assembler::ircode_from_string(R"((
                            (load-param-object v1)
                            (const-method-handle invoke-direct "LBase;.log:()V")
                            (move-result-pseudo-object v0)
                            (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LBase;)V")
                            (return-void)
                          ))"),
                                          /*is_virtual=*/false);
  logging_creator.add_method(log_as_base);
  DexClass* class_logging = logging_creator.create();

  DexClass* class_screen = create_class("LScreen;");
  auto* show = DexMethod::make_method("LScreen;.show:(LBase;)V")
                   ->make_concrete(ACC_PUBLIC,
                                   assembler::ircode_from_string(R"((
                            (load-param-object v0)
                            (load-param-object v1)
                            (invoke-static (v1) "LLogging;.logAsBase:(LBase;)V")
                            (return-void)
                          ))"),
                                   /*is_virtual=*/true);
  class_screen->add_method(show);

  Scope scope({class_base, class_logging, class_screen});
  for (auto* cls : scope) {
    for (auto* m : cls->get_all_methods()) {
      m->get_code()->build_cfg();
    }
  }
  api::LevelChecker::init(0, scope);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes, std::vector<DexClass*>{class_logging});
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);

  EXPECT_EQ(relocated_methods, 0);
  EXPECT_EQ(log_as_base->get_class(), class_logging->get_type());
}
/**
 * A static method that holds an invoke-custom stays in its class: the
 * bootstrap method receives a lookup in the class of the code that holds it.
 */
TEST_F(StaticReloV2Test, keepMethodWithInvokeCustom) {
  ClassCreator logging_creator(DexType::make_type("LLogging;"));
  logging_creator.set_super(type::java_lang_Object());
  auto log_code = assembler::ircode_from_string(R"((
    (invoke-static () "LLogging;.placeholder:()V")
    (return-void)
  ))");
  redex::make_invoke_custom(log_code.get(), "run", "()V");
  auto* log = DexMethod::make_method("LLogging;.log:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(log_code),
                                  /*is_virtual=*/false);
  logging_creator.add_method(log);
  DexClass* class_logging = logging_creator.create();

  DexClass* class_screen = create_class("LScreen;");
  auto* show = DexMethod::make_method("LScreen;.show:()V")
                   ->make_concrete(ACC_PUBLIC,
                                   assembler::ircode_from_string(R"((
                            (load-param-object v0)
                            (invoke-static () "LLogging;.log:()V")
                            (return-void)
                          ))"),
                                   /*is_virtual=*/true);
  class_screen->add_method(show);

  Scope scope({class_logging, class_screen});
  for (auto* cls : scope) {
    for (auto* m : cls->get_all_methods()) {
      m->get_code()->build_cfg();
    }
  }
  api::LevelChecker::init(0, scope);
  std::vector<DexClass*> candidate_classes =
      StaticReloPassV2::gen_candidates(scope);
  EXPECT_EQ(candidate_classes, std::vector<DexClass*>{class_logging});
  int relocated_methods =
      StaticReloPassV2::run_relocation(scope, candidate_classes);

  EXPECT_EQ(relocated_methods, 0);
  EXPECT_EQ(log->get_class(), class_logging->get_type());
}
} // namespace static_relo_v2
