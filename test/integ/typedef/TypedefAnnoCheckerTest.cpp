/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <string>

#include "Debug.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypedefAnnoCheckerPass.h"
#include "TypedefAnnoPatcher.h"
#include "Walkers.h"

struct TypedefAnnoCheckerTest : public RedexIntegrationTest {
  TypedefAnnoCheckerPass::Config get_config() {
    auto m_config = TypedefAnnoCheckerPass::Config();
    m_config.str_typedef =
        DexType::make_type("Lcom/facebook/redex/annotations/SafeStringDef;");
    m_config.int_typedef =
        DexType::make_type("Lcom/facebook/redex/annotations/SafeIntDef;");
    return m_config;
  }

  void build_cfg(Scope& scope) {
    for (auto* cls : scope) {
      always_assert(cls);
      for (auto* m : cls->get_dmethods()) {
        if ((m != nullptr) && (m->get_code() != nullptr)) {
          m->get_code()->build_cfg();
        }
      }
      for (auto* m : cls->get_vmethods()) {
        if ((m != nullptr) && (m->get_code() != nullptr)) {
          m->get_code()->build_cfg();
        }
      }
    }
  }

  void gather_typedef_values(TypedefAnnoCheckerPass pass,
                             DexClass* cls,
                             StrDefConstants& strdef_constants,
                             IntDefConstants& intdef_constants) {
    pass.gather_typedef_values(cls, strdef_constants, intdef_constants);
  }

  void collect_typedef_param_methods(
      const Scope& scope,
      const UnorderedSet<const DexType*>& typedef_annos,
      InsertOnlyConcurrentSet<const DexMethod*>& typedef_param_methods) {
    TypedefAnnoCheckerPass::collect_typedef_param_methods(
        scope, typedef_annos, typedef_param_methods);
  }

  bool has_typedef_sink(
      DexMethod* m,
      const InsertOnlyConcurrentSet<const DexMethod*>& typedef_param_methods,
      const UnorderedSet<const DexType*>& typedef_annos) {
    return TypedefAnnoCheckerPass::has_typedef_sink(m, typedef_param_methods,
                                                    typedef_annos);
  }

  void run_patcher(const Scope& scope,
                   const method_override_graph::Graph& method_override_graph) {
    auto config = get_config();
    TypedefAnnoPatcher patcher(config, method_override_graph);
    patcher.run(scope);
  }

  TypedefAnnoChecker run_checker(
      const Scope& scope,
      DexMethod* method,
      const method_override_graph::Graph& method_override_graph) {
    return run_checker_with_config(scope, method, method_override_graph,
                                   get_config());
  }

  TypedefAnnoChecker run_checker_with_config(
      const Scope& scope,
      DexMethod* method,
      const method_override_graph::Graph& method_override_graph,
      const TypedefAnnoCheckerPass::Config& config) {
    StrDefConstants strdef_constants;
    IntDefConstants intdef_constants;
    TypedefAnnoCheckerPass pass = TypedefAnnoCheckerPass(config);
    for (auto* cls : scope) {
      pass.gather_typedef_values(cls, strdef_constants, intdef_constants);
    }

    TypedefAnnoChecker checker = TypedefAnnoChecker(
        strdef_constants, intdef_constants, config, method_override_graph);
    checker.run(method);
    return checker;
  }
};

TEST_F(TypedefAnnoCheckerTest, TestValidIntAnnoReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testValidIntAnnoReturn:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestValidStrAnnoReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testValidStrAnnoReturn:(Ljava/lang/"
          "String;)Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestIntAnnoInvokeStatic) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testIntAnnoInvokeStatic:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestStringAnnoInvokeStatic) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testStringAnnoInvokeStatic:(Ljava/lang/"
          "String;)Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestWrongAnnotationReturned) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testWrongAnnotationReturned:(Ljava/lang/"
          "String;)Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testWrongAnnotationReturned:(Ljava/lang/String;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.java:180\n\
  has return annotation Linteg/TestIntDef; but the returned value has annotation  Linteg/TestStringDef; instead.\n\
  failed instruction: RETURN_OBJECT v0");
}

TEST_F(TypedefAnnoCheckerTest, TestWrongAnnoInvokeStatic) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testWrongAnnoInvokeStatic:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testWrongAnnoInvokeStatic:(I)I\n\
  at TypedefAnnoCheckerTest.java:184\n\
  while invoking Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testValidIntAnnoReturn:(I)I, parameter 0(val) has the annotation  Linteg/TestStringDef;\n\
  but the method expects the annotation to be Linteg/TestIntDef;.\n\
  failed instruction: INVOKE_STATIC v1, Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testValidIntAnnoReturn:(I)I");
}

TEST_F(TypedefAnnoCheckerTest, TestIntField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testIntField:(I)V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestWrongIntField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testWrongIntField:(I)V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testWrongIntField:(I)V\n\
  at TypedefAnnoCheckerTest.java:152\n\
  assigned field wrong_anno_field with annotation  Linteg/TestStringDef; to a value with annotation  Linteg/TestIntDef;.\n\
  failed instruction: IPUT v1, v0, Lcom/facebook/redextest/TypedefAnnoCheckerTest;.wrong_anno_field:I");
}

TEST_F(TypedefAnnoCheckerTest, TestStringField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testStringField:(Ljava/lang/"
                     "String;)V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);

  checker.run(method);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestConstReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testConstReturn:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidConstReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testInvalidConstReturn:()I")
                     ->as_def();
  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidConstReturn:()I\n\
  at TypedefAnnoCheckerTest.java:198\n\
  the int value 5 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 5\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidConstReturn2) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testInvalidConstReturn2:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidConstReturn2:()I\n\
  at TypedefAnnoCheckerTest.java:203\n\
  the int value 5 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 5\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidConstStrReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testInvalidConstStrReturn:()Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidConstStrReturn:()Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.java:213\n\
  the string value five does not have the typedef annotation  Linteg/TestStringDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST_STRING \"five\"\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidConstInvokeStatic) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testInvalidConstInvokeStatic:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidConstInvokeStatic:()I\n\
  at TypedefAnnoCheckerTest.java:218\n\
  the int value 5 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 5\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testIntAnnoInvokeStatic:(I)I\n\
  Incorrect parameter: index 0(val)");
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidConstInvokeStatic2) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testInvalidConstInvokeStatic2:()I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidConstInvokeStatic2:()I\n\
  at TypedefAnnoCheckerTest.java:223\n\
  the int value 5 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 5\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testIntAnnoInvokeStatic:(I)I\n\
  Incorrect parameter: index 0(val)");
}

TEST_F(TypedefAnnoCheckerTest, TestMultipleBlocksInt) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testMultipleBlocksInt:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestMultipleBlocksString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testMultipleBlocksString:(Ljava/lang/"
          "String;)Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidMultipleBlocksString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testInvalidMultipleBlocksString:(Ljava/lang/"
          "String;)Ljava/lang/"
          "String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidMultipleBlocksString:(Ljava/lang/String;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.java:243\n\
  the source of the value with annotation  Linteg/TestStringDef; is produced by invoking an unresolvable callee, so the value safety is not guaranteed.\n\
  failed instruction: INVOKE_VIRTUAL v1, v0, Ljava/lang/String;.concat:(Ljava/lang/String;)Ljava/lang/String;\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestNonConstInt) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testNonConstInt:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  auto err_str = checker.error();
  EXPECT_TRUE(err_str.find("TypedefAnnoCheckerPass: in method "
                           "Lcom/facebook/redextest/"
                           "TypedefAnnoCheckerTest;.testNonConstInt:(I)I") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("does not guarantee value safety for the value with "
                           "typedef annotation  Linteg/TestIntDef;") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("failed instruction: ADD_INT_LIT v0, v0, 2") !=
              std::string::npos);
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidType) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testInvalidType:(Lcom/facebook/"
                     "redextest/I;)Lcom/facebook/redextest/I;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, get_config(), *method_override_graph);
  checker.run(method);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testInvalidType:(Lcom/facebook/redextest/I;)Lcom/facebook/redextest/I;\n\
  at TypedefAnnoCheckerTest.java:254\n\
  annotation  Linteg/TestIntDef; annotates a value with an incompatible type or a non-constant value.\n\
  failed instruction: RETURN_OBJECT v0");
}

TEST_F(TypedefAnnoCheckerTest, TestJoiningTwoAnnotations) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testJoiningTwoAnnotations:(Ljava/lang/"
          "String;Ljava/lang/String;)Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testJoiningTwoAnnotations:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.java:265\n\
  one of the parameters needs to have the typedef annotation  Linteg/TestStringDef; attached to it. Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: IOPCODE_LOAD_PARAM_OBJECT v4\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestJoiningTwoAnnotations2) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testJoiningTwoAnnotations2:(Ljava/lang/"
          "String;Ljava/lang/String;)Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestReassigningInt) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testReassigningInt:(II)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestIfElse) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testIfElse:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestIfElseParam) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testIfElseParam:(Z)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestIfElseString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testIfElseString:(Z)Ljava/lang/"
                     "String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestXORIfElse) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testXORIfElse:(Z)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestXORIfElseZero) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testXORIfElseZero:()I")
                     ->as_def();

  IRCode* code = method->get_code();
  auto& cfg = code->cfg();

  type_inference::TypeInference inference(cfg);
  inference.run(method);

  auto* block = cfg.blocks().at(0);
  auto env = inference.get_entry_state_at(block);
  for (auto& mie : InstructionIterable(block)) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_XOR_INT_LIT) {
      EXPECT_EQ(env.get_type(insn->src(0)),
                type_inference::TypeDomain(IRType::ZERO));
    }
    inference.analyze_instruction(insn, &env);
  }

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestBoolParamInvalidIntDef) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testBoolParamInvalidIntDef:(Z)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  auto err_str = checker.error();
  EXPECT_TRUE(err_str.find("TypedefAnnoCheckerPass: in method ") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("testBoolParamInvalidIntDef") != std::string::npos);
  EXPECT_TRUE(err_str.find("assigns a int with typedef annotation") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("does not contain both the values 0 and 1") !=
              std::string::npos);
}

TEST_F(TypedefAnnoCheckerTest, TestXORInvalidIntDef) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testXORInvalidIntDef:(Z)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  auto err_str = checker.error();
  EXPECT_TRUE(err_str.find("TypedefAnnoCheckerPass: in method ") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("testXORInvalidIntDef") != std::string::npos);
  EXPECT_TRUE(err_str.find("assigns a int with typedef annotation") !=
              std::string::npos);
  EXPECT_TRUE(err_str.find("does not contain both the values 0 and 1") !=
              std::string::npos);
}

// Simulates the ModelGen pattern: an untyped source (like Parcel.readInt())
// returns a raw value that flows into a typedef-annotated parameter. Without
// do_not_check_list, the checker flags this. With the source class in
// do_not_check_list, the checker skips it — the same mechanism that makes
// is_model_gen redundant for real ModelGen code.
TEST_F(TypedefAnnoCheckerTest, TestUntypedSourceWithoutSkip) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testUntypedSourceToTypedSink:()V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // Without do_not_check_list, the checker should flag UntypedSource.readInt()
  // as not having the typedef annotation.
  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  auto err_str = checker.error();
  EXPECT_TRUE(err_str.find("UntypedSource") != std::string::npos);
}

TEST_F(TypedefAnnoCheckerTest, TestUntypedSourceWithSkip) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testUntypedSourceToTypedSink:()V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // With UntypedSource in do_not_check_list, the checker should pass.
  // This is the same mechanism that handles Parcel.readInt() for ModelGen.
  // Set deobfuscated names so do_not_check_list prefix matching works
  // (in production these are set by the obfuscation pipeline).
  auto* read_int = DexMethod::get_method(
                       "Lcom/facebook/redextest/UntypedSource;.readInt:()I")
                       ->as_def();
  ASSERT_NE(nullptr, read_int);
  read_int->set_deobfuscated_name(show(read_int));

  auto config = get_config();
  config.do_not_check_list.insert("Lcom/facebook/redextest/UntypedSource;");
  auto checker =
      run_checker_with_config(scope, method, *method_override_graph, config);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, testSynthAccessor) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* accessor = DexMethod::get_method(
                       "Lcom/facebook/redextest/"
                       "TypedefAnnoCheckerKtTest;.access$takesStrConst:(Lcom/"
                       "facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/"
                       "String;)Ljava/lang/String;")
                       ->as_def();
  EXPECT_TRUE(accessor != nullptr);
  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoCheckerPass pass = TypedefAnnoCheckerPass(get_config());
  for (auto* cls : scope) {
    gather_typedef_values(pass, cls, strdef_constants, intdef_constants);
  }

  auto config = get_config();
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker.run(accessor);

  // Without patching the accessor, the checker will fail.
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.access$takesStrConst:(Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/String;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:23\n\
  one of the parameters needs to have the typedef annotation  Linteg/TestStringDef; attached to it. Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: IOPCODE_LOAD_PARAM_OBJECT v2\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.takesStrConst:(Ljava/lang/String;)Ljava/lang/String;\n\
  Incorrect parameter: index 0(str)");

  TypedefAnnoPatcher patcher(config, *method_override_graph);
  patcher.run(scope);

  TypedefAnnoChecker checker2 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker2.run(accessor);
  // After patching the accessor, the checker should succeed.
  EXPECT_TRUE(checker2.complete());

  auto* accessor_caller =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest$testSynthAccessor$lmd$1;"
          ".invoke:()Ljava/lang/String;")
          ->as_def();
  EXPECT_TRUE(accessor_caller != nullptr);

  TypedefAnnoChecker checker3 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker3.run(accessor_caller);
  // The caller of the accessor has the actual violation.
  EXPECT_FALSE(checker3.complete());
  EXPECT_EQ(
      checker3.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest$testSynthAccessor$lmd$1;.invoke:()Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:43\n\
  the string value liu does not have the typedef annotation  Linteg/TestStringDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST_STRING \"liu\"\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.access$takesStrConst:(Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/String;)Ljava/lang/String;\n\
  Incorrect parameter: index 1(str)");
}

TEST_F(TypedefAnnoCheckerTest, testDefaultArg) {
  // Dex code example: https://fburl.com/dexbolt/o35r4sgv
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* wrong_default_arg =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.wrongDefaultArg$default:(Lcom/"
          "facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/"
          "String;ILjava/lang/Object;)Ljava/lang/String;")
          ->as_def();
  EXPECT_TRUE(wrong_default_arg != nullptr);

  auto* wrong_default_caller =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.wrongDefaultCaller:(Ljava/lang/"
          "String;)V")
          ->as_def();
  EXPECT_TRUE(wrong_default_caller != nullptr);

  auto* right_default_arg =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.rightDefaultArg$default:(Lcom/"
          "facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/"
          "String;ILjava/lang/Object;)Ljava/lang/String;")
          ->as_def();
  EXPECT_TRUE(right_default_arg != nullptr);

  auto* right_default_caller =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.rightDefaultCaller:(Ljava/lang/"
          "String;)V")
          ->as_def();
  EXPECT_TRUE(right_default_caller != nullptr);

  auto method_override_graph = mog::build_graph(scope);

  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoCheckerPass pass = TypedefAnnoCheckerPass(get_config());
  for (auto* cls : scope) {
    gather_typedef_values(pass, cls, strdef_constants, intdef_constants);
  }

  auto config = get_config();
  TypedefAnnoChecker checker = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker.run(wrong_default_arg);
  // Without patching the accessor, the checker will fail.
  // The default arg is not safe value. The param is not annotated.
  // We don't check the detailed error msg, since multiple errors are possible.
  EXPECT_FALSE(checker.complete());

  TypedefAnnoChecker checker1 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker1.run(wrong_default_caller);
  EXPECT_TRUE(checker1.complete());

  TypedefAnnoChecker checker2 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker2.run(right_default_arg);
  // Without patching the accessor, the checker will fail.
  // The default arg is a safe value, but the param is not annotated.
  EXPECT_FALSE(checker2.complete());
  EXPECT_EQ(
      checker2.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.rightDefaultArg$default:(Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/String;ILjava/lang/Object;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:65\n\
  one of the parameters needs to have the typedef annotation  Linteg/TestStringDef; attached to it. Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: IOPCODE_LOAD_PARAM_OBJECT v1\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.rightDefaultArg:(Ljava/lang/String;)Ljava/lang/String;\n\
  Incorrect parameter: index 0(str)");

  TypedefAnnoChecker checker3 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker3.run(right_default_caller);
  EXPECT_TRUE(checker3.complete());

  ///////////////////////////////////////////////////
  // Patch the default synth stub param !!!
  ///////////////////////////////////////////////////
  TypedefAnnoPatcher patcher(config, *method_override_graph);
  patcher.run(scope);

  TypedefAnnoChecker checker4 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker4.run(wrong_default_arg);
  // After patching the accessor, the param annotation is patched. But the wrong
  // constant error remains.
  EXPECT_FALSE(checker4.complete());
  EXPECT_EQ(
      checker4.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.wrongDefaultArg$default:(Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;Ljava/lang/String;ILjava/lang/Object;)Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:56\n\
  the string value default does not have the typedef annotation  Linteg/TestStringDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST_STRING \"default\"\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.wrongDefaultArg:(Ljava/lang/String;)Ljava/lang/String;\n\
  Incorrect parameter: index 0(str)");

  TypedefAnnoChecker checker5 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker5.run(wrong_default_caller);
  EXPECT_TRUE(checker5.complete());

  TypedefAnnoChecker checker6 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker6.run(right_default_arg);
  // After patching the accessor, the param annotation is patched. The default
  // arg is correct.
  EXPECT_TRUE(checker6.complete());

  TypedefAnnoChecker checker7 = TypedefAnnoChecker(
      strdef_constants, intdef_constants, config, *method_override_graph);
  checker7.run(right_default_caller);
  EXPECT_TRUE(checker7.complete());
}

TEST_F(TypedefAnnoCheckerTest, testAssignNullToString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testAssignNullToString:()Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestNoAnnoField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testNoAnnoField:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testNoAnnoField:()I\n\
  at TypedefAnnoCheckerTest.java:160\n\
  the field no_anno_field needs to have the annotation  Linteg/TestIntDef;.\n\
  failed instruction: IGET v1, Lcom/facebook/redextest/TypedefAnnoCheckerTest;.no_anno_field:I\n\
  Calling: Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testValidIntAnnoReturn:(I)I\n\
  Incorrect parameter: index 0(val)");
}

TEST_F(TypedefAnnoCheckerTest, TestPureVirtualCall) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testPureVirtualCall:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  // it should fail because NoAnnoVirtualTest;.pureVirtual does not have a
  // typedef annotation attached
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testPureVirtualCall:(I)I\n\
  at TypedefAnnoCheckerTest.java:105\n\
  the return value of Lcom/facebook/redextest/AbstractClass;.pureVirtual:(I)I\n\
  is used where annotation  Linteg/TestIntDef; is required,\n\
  but that method does not have the annotation in its return type.\n\
  To fix: use a constant from  Linteg/TestIntDef;, or validate the value before passing it.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtual:(I)I\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestWrongConstPureVirtualCall) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testWrongConstPureVirtualCall:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  // it should fail because NoAnnoVirtualTest;.pureVirtual does not have a
  // typedef annotation attached
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testWrongConstPureVirtualCall:(I)I\n\
  at TypedefAnnoCheckerTest.java:110\n\
  the return value of Lcom/facebook/redextest/AbstractClass;.pureVirtual:(I)I\n\
  is used where annotation  Linteg/TestIntDef; is required,\n\
  but that method does not have the annotation in its return type.\n\
  To fix: use a constant from  Linteg/TestIntDef;, or validate the value before passing it.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtual:(I)I\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestWrongConstPureVirtual) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "WrongConstVirtualTest;.pureVirtual:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/WrongConstVirtualTest;.pureVirtual:(I)I\n\
  at TypedefAnnoCheckerTest.java:61\n\
  the int value 6 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 6\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestPureVirtualCallNoAnno) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testPureVirtualCallNoAnno:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testPureVirtualCallNoAnno:(I)I\n\
  at TypedefAnnoCheckerTest.java:120\n\
  the return value of Lcom/facebook/redextest/AbstractClass;.pureVirtualNoAnnoReturn:(I)I\n\
  is used where annotation  Linteg/TestIntDef; is required,\n\
  but that method does not have the annotation in its return type.\n\
  To fix: use a constant from  Linteg/TestIntDef;, or validate the value before passing it.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtualNoAnnoReturn:(I)I\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestWrongConstPureVirtualCall2) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testWrongConstPureVirtualCall2:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testWrongConstPureVirtualCall2:(I)I\n\
  at TypedefAnnoCheckerTest.java:125\n\
  the return value of Lcom/facebook/redextest/AbstractClass;.pureVirtualNoAnnoReturn:(I)I\n\
  is used where annotation  Linteg/TestIntDef; is required,\n\
  but that method does not have the annotation in its return type.\n\
  To fix: use a constant from  Linteg/TestIntDef;, or validate the value before passing it.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtualNoAnnoReturn:(I)I\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestPureVirtualInvalidParamAnno) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testPureVirtualInvalidParamAnno:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testPureVirtualInvalidParamAnno:(I)I\n\
  at TypedefAnnoCheckerTest.java:130\n\
  while invoking Lcom/facebook/redextest/NoAnnoVirtualTest;.pureVirtualInvalidParamAnno:(I)I, parameter 0(val) has the annotation  Linteg/TestIntDef;\n\
  but the method expects the annotation to be Linteg/TestStringDef;.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtualInvalidParamAnno:(I)I");
}

TEST_F(TypedefAnnoCheckerTest, TestPureVirtualInvalidParamAnno2) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testPureVirtualInvalidParamAnno2:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testPureVirtualInvalidParamAnno2:(I)I\n\
  at TypedefAnnoCheckerTest.java:135\n\
  while invoking Lcom/facebook/redextest/NoAnnoVirtualTest;.pureVirtualInvalidParamAnno:(I)I, parameter 0(val) has the annotation  Linteg/TestIntDef;\n\
  but the method expects the annotation to be Linteg/TestStringDef;.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtualInvalidParamAnno:(I)I");
}

TEST_F(TypedefAnnoCheckerTest, TestPureVirtualInvalidReturn) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testPureVirtualInvalidReturn:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTest;.testPureVirtualInvalidReturn:(I)I\n\
  at TypedefAnnoCheckerTest.java:140\n\
  the return value of Lcom/facebook/redextest/AbstractClass;.pureVirtualInvalidReturn:(I)I\n\
  is used where annotation  Linteg/TestIntDef; is required,\n\
  but that method does not have the annotation in its return type.\n\
  To fix: use a constant from  Linteg/TestIntDef;, or validate the value before passing it.\n\
  failed instruction: INVOKE_VIRTUAL v0, v3, Lcom/facebook/redextest/AbstractClass;.pureVirtualInvalidReturn:(I)I\n\
 Error caught when returning the faulty value");
}

TEST_F(TypedefAnnoCheckerTest, TestReturnWhen) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testReturnWhen:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestKtField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testKtField:()Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestVarField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testVarField:()Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidVarField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testInvalidVarField:()Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.testInvalidVarField:()Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:105\n\
  the string value 5 does not have the typedef annotation  Linteg/TestStringDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST_STRING \"5\"\n\
 Error writing to field Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.var_field:Ljava/lang/String;in methodLcom/facebook/redextest/TypedefAnnoCheckerKtTest;.testInvalidVarField:()Ljava/lang/String;");
}

TEST_F(TypedefAnnoCheckerTest, TestReturnIntField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testReturnIntField:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestCompanionObject) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testCompanionObject:()Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestCompanionObjectGetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$Companion;."
                     "testCompanionObjectGetter:()Ljava/lang/String;")
                     ->as_def();

  auto* companion_class =
      type_class(DexType::make_type("Lcom/facebook/redextest/"
                                    "TypedefAnnoCheckerKtTest$Companion;"));
  companion_class->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$Companion;");
  auto* enclosing_class =
      type_class(DexType::make_type("Lcom/facebook/redextest/"
                                    "TypedefAnnoCheckerKtTest;"));
  enclosing_class->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest;");

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestCompanionVarSetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testCompanionVarSetter:()Ljava/"
                     "lang/String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestInvalidCompanionVarSetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testInvalidCompanionVarSetter:()Ljava/"
          "lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.testInvalidCompanionVarSetter:()Ljava/lang/String;\n\
  at TypedefAnnoCheckerTest.kt:88\n\
  the string value 5 does not have the typedef annotation  Linteg/TestStringDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST_STRING \"5\"\n\
 Error writing to field Lcom/facebook/redextest/TypedefAnnoCheckerKtTest;.companion_var:Ljava/lang/String;in methodLcom/facebook/redextest/TypedefAnnoCheckerKtTest;.testInvalidCompanionVarSetter:()Ljava/lang/String;");
}

TEST_F(TypedefAnnoCheckerTest, TestCompanionIntVarSetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testCompanionIntVarSetter:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestConstFolding) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testConstFolding:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCall) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$testLambdaCall$1;.invoke:()"
                     "Ljava/lang/String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestClassConstructorArgs) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testClassConstructorArgs:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, testSGet) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest;.testSGet:()I")
                     ->as_def();

  auto* code = method->get_code();
  code->build_cfg();
  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAccessGet) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest$1;.override_method:()V")
                     ->as_def();

  auto* code = method->get_code();
  code->build_cfg();
  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAccessSet) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest$2;.override_method:()V")
                     ->as_def();

  auto* code = method->get_code();
  code->build_cfg();
  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestSyntheticValField) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTest$3;.override_method:()V")
                     ->as_def();

  auto* code = method->get_code();
  code->build_cfg();
  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestNullString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTest;.testNullString:()Ljava/lang/String;")
          ->as_def();

  auto* code = method->get_code();
  code->build_cfg();
  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCallLocalVal) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest$testLambdaCallLocalVal$1;.invoke:()"
          "Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestClassConstructorDefaultArgs) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testClassConstructorDefaultArgs:(I)I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAnnotatedPropertyGetterPatching) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testAnnotatedPropertyGetterPatching:()"
          "Ljava/lang/String;")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAnnotatedPropertySetterPatching) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testAnnotatedPropertySetterPatching:()V")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAnnotatedCompanionPropertyAccessorGetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$Listener$Companion;.getOne:()"
                     "Ljava/lang/String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestAnnotatedCompanionPropertyAccessorSetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$Listener$Companion;.setOne:("
                     "Ljava/lang/String;)V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestClassPrivatePropertyGetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty$"
                     "returnInt$lmd$1;.invoke:()V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  auto* access_p = DexMethod::get_method(
                       "Lcom/facebook/redextest/"
                       "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;."
                       "access$getInt_field$p:(Lcom/facebook/redextest/"
                       "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;)I")
                       ->as_def();
  access_p->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;.access$getInt_field$"
      "p:(Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;)I");

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestClassPrivatePropertySetter) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty$"
                     "setInt$lmd$1;.invoke:()Ljava/lang/Object;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  auto* access_p = DexMethod::get_method(
                       "Lcom/facebook/redextest/"
                       "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;."
                       "access$setInt_field$p:(Lcom/facebook/redextest/"
                       "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;I)V")
                       ->as_def();
  access_p->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;.access$setInt_field$"
      "p:(Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$ClassWithPrivateProperty;I)");

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestSAM) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$sam_interface$1;."
                     "setString:(Ljava/lang/String;)V")
                     ->as_def();

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  method->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$sam_interface$1;."
      "setString:(Ljava/lang/String;)V");

  auto method_override_graph = mog::build_graph(scope);

  DexClass* synth_class = type_class(method->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCallLocalVarInt) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testLambdaCallLocalVarInt:()I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  auto* synth_init =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest$testLambdaCallLocalVarInt$1;.<init>:"
          "(Lcom/"
          "facebook/redextest/TypedefAnnoCheckerKtTest;Lkotlin/jvm/internal/"
          "Ref$IntRef;)V")
          ->as_def();
  synth_init->set_deobfuscated_name(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$testLambdaCallLocalVarInt$1;.<init>:("
      "Lcom/"
      "facebook/redextest/TypedefAnnoCheckerKtTest;Lkotlin/jvm/internal/"
      "Ref$IntRef;)V");

  DexClass* synth_class = type_class(synth_init->get_class());
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCallLocalVarIntDefault) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest;.testLambdaCallLocalVarIntDefault:()I")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  DexClass* synth_class = type_class(DexType::make_type(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$testLambdaCallLocalVarIntDefault$1;"));
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCallLocalVarString) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testLambdaCallLocalVarString:()"
                     "Ljava/lang/String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  DexClass* synth_class = type_class(DexType::make_type(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$testLambdaCallLocalVarString$1;"));
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestLambdaCallLocalVarStringDefault) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;."
                     "testLambdaCallLocalVarStringDefault:()Ljava/lang/String;")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests
  DexClass* synth_class = type_class(DexType::make_type(
      "Lcom/facebook/redextest/"
      "TypedefAnnoCheckerKtTest$testLambdaCallLocalVarStringDefault$1;"));
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

// Tests that the patcher propagates typedef annotations from an interface
// to a delegation class's forwarding method, so the checker passes.
TEST_F(TypedefAnnoCheckerTest, TestDelegatePatternWithPatcher) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);

  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "DelegateTestHelper;.callDelegate:(I)V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

// Tests the delegate forwarding method itself — the patcher propagates
// the typedef annotation from the interface, so the checker passes when
// verifying the return value of DelegatingClass.transform.
TEST_F(TypedefAnnoCheckerTest, TestDelegateMethodWithPatcher) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);

  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "DelegatingClass;.transform:(I)I")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestFunInterfaceSyntheticFields) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);

  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerKtTest$testFunInterface$1;.onListen:()V")
          ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests

  DexClass* synth_class = type_class(DexType::make_type(
      "Lcom/facebook/redextest/TypedefAnnoCheckerKtTest$testFunInterface$1;"));
  synth_class->set_deobfuscated_name(synth_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestKotlinEnumCtorValid) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);

  auto* clinit = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest$ShareType;.<clinit>:()V")
                     ->as_def();

  auto method_override_graph = mog::build_graph(scope);

  // set the deobfuscated name manually since it doesn't get set by default in
  // integ tests

  DexClass* enum_class = type_class(DexType::make_type(
      "Lcom/facebook/redextest/TypedefAnnoCheckerKtTest$ShareType;"));
  enum_class->set_deobfuscated_name(enum_class->get_name()->c_str());

  run_patcher(scope, *method_override_graph);

  auto checker = run_checker(scope, clinit, *method_override_graph);
  EXPECT_TRUE(checker.complete());

  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerKtTest;.testKotlinEnumCtor:()V")
                     ->as_def();
  auto checker2 = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker2.complete());
}

TEST_F(TypedefAnnoCheckerTest, TestMethodsWithoutSinksPass) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto method_override_graph = mog::build_graph(scope);
  run_patcher(scope, *method_override_graph);

  auto config = get_config();
  StrDefConstants strdef_constants;
  IntDefConstants intdef_constants;
  TypedefAnnoCheckerPass pass = TypedefAnnoCheckerPass(config);
  for (auto* cls : scope) {
    gather_typedef_values(pass, cls, strdef_constants, intdef_constants);
  }
  UnorderedSet<const DexType*> typedef_annos{config.int_typedef,
                                             config.str_typedef};
  InsertOnlyConcurrentSet<const DexMethod*> typedef_param_methods;
  collect_typedef_param_methods(scope, typedef_annos, typedef_param_methods);

  // Every method the checker fails must be one that run_pass checks, and some
  // methods must be skipped for this to test anything.
  size_t failing = 0;
  size_t skipped = 0;
  walk::methods(scope, [&](DexMethod* m) {
    bool has_sink = has_typedef_sink(m, typedef_param_methods, typedef_annos);
    if (!has_sink) {
      skipped++;
    }
    TypedefAnnoChecker checker = TypedefAnnoChecker(
        strdef_constants, intdef_constants, config, *method_override_graph);
    checker.run(m);
    if (!checker.complete()) {
      failing++;
      EXPECT_TRUE(has_sink) << show(m);
    }
  });
  EXPECT_GT(failing, 0u);
  EXPECT_GT(skipped, 0u);
}

TEST_F(TypedefAnnoCheckerTest, TestCallUnannotatedGenericMethod) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto method_override_graph = mog::build_graph(scope);
  run_patcher(scope, *method_override_graph);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTestKt;.testCallUnannotatedGenericMethod:"
          "(Lcom/facebook/redextest/Action3;I)V")
          ->as_def();

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete()) << checker.error();
}

TEST_F(TypedefAnnoCheckerTest, TestCallParamAnnotatedOnlyByOverride) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto method_override_graph = mog::build_graph(scope);
  run_patcher(scope, *method_override_graph);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTestKt;.testCallParamAnnotatedOnlyByOverride:"
          "(Lcom/facebook/redextest/Logger;Ljava/lang/String;)V")
          ->as_def();

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_TRUE(checker.complete()) << checker.error();
}

TEST_F(TypedefAnnoCheckerTest, TestCallInvalidParamAnnotatedByInterface) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto method_override_graph = mog::build_graph(scope);
  run_patcher(scope, *method_override_graph);
  auto* method =
      DexMethod::get_method(
          "Lcom/facebook/redextest/"
          "TypedefAnnoCheckerTestKt;.testCallInvalidParamAnnotatedByInterface:"
          "(Lcom/facebook/redextest/Logger;)V")
          ->as_def();

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTestKt;.testCallInvalidParamAnnotatedByInterface:(Lcom/facebook/redextest/Logger;)V\n\
  at TypedefAnnoCheckerTest.kt:480\n\
  the int value 6 does not have the typedef annotation  Linteg/TestIntDef; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 6\n\
  Calling: Lcom/facebook/redextest/Logger;.log:(ILjava/lang/String;)V\n\
  Incorrect parameter: index 0(level)");
}

TEST_F(TypedefAnnoCheckerTest, TestCallParamWithDifferentTypedefOnOverride) {
  auto scope = build_class_scope(stores);
  build_cfg(scope);
  auto method_override_graph = mog::build_graph(scope);
  run_patcher(scope, *method_override_graph);
  auto* method = DexMethod::get_method(
                     "Lcom/facebook/redextest/"
                     "TypedefAnnoCheckerTestKt;."
                     "testCallParamWithDifferentTypedefOnOverride:"
                     "(Lcom/facebook/redextest/Level;)V")
                     ->as_def();

  auto checker = run_checker(scope, method, *method_override_graph);
  EXPECT_FALSE(checker.complete());
  EXPECT_EQ(
      checker.error(),
      "TypedefAnnoCheckerPass: in method Lcom/facebook/redextest/TypedefAnnoCheckerTestKt;.testCallParamWithDifferentTypedefOnOverride:(Lcom/facebook/redextest/Level;)V\n\
  at TypedefAnnoCheckerTest.kt:494\n\
  the int value 1 does not have the typedef annotation  Linteg/TestIntDefNoBool; attached to it.\n\
  Check that the value is annotated and exists in the typedef annotation class.\n\
  failed instruction: CONST v0, 1\n\
  Calling: Lcom/facebook/redextest/NoBoolLevel;.set:(I)V\n\
  Incorrect parameter: index 0(level)");
}
