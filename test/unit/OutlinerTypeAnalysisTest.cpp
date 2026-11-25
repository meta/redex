/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "Debug.h"
#include "IRAssembler.h"
#include "OutlinerTypeAnalysis.h"
#include "PartialCandidateAdapter.h"
#include "RedexTest.h"

class OutlinerTypeAnalysisTest : public RedexTest {};

static IRInstruction* find_insn(
    DexMethod* method,
    const std::function<bool(IRInstruction*)>& predicate,
    size_t occurrence = 1) {
  always_assert(occurrence > 0);
  for (const auto& mie : InstructionIterable(method->get_code()->cfg())) {
    if (predicate(mie.insn) && --occurrence == 0) {
      return mie.insn;
    }
  }
  not_reached();
}

static IRInstruction* find_insn(DexMethod* method,
                                IROpcode opcode,
                                size_t occurrence = 1) {
  return find_insn(
      method,
      [opcode](IRInstruction* insn) { return insn->opcode() == opcode; },
      occurrence);
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_primitive) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(IZ)V" (
        (load-param v1)
        (load-param v2)
        (add-int v1 v1 v1)
        (move v1 v1)
        (or-int v1 v1 v1)
        (xor-int v2 v2 v2)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_ADD_INT);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of 'move' of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_MOVE);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of 'or-int' of 'move' of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_OR_INT);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of first 'load-param' is int due to method signature
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of second 'load-param' is boolean due to method signature
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // result type of 'xor-int' of boolean 'load-param' is boolean
    auto* insn = find_insn(foo_method, OPCODE_XOR_INT);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // the combined result type of int and boolean is int
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn1, insn2},
                            /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // the combined result type of boolean and the optional_extra_type int is
    // int
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    const auto* result_type = ota.get_result_type(
        nullptr, {insn}, /* optional_extra_type */ type::_int());
    EXPECT_EQ(result_type, type::_int());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_unreachable) {
  // Regression: a def fed by IOPCODE_UNREACHABLE (a synthetic undefined value
  // that the type analysis groups with consts) must not crash
  // get_const_insns_type_demand -- the constant-uses analysis only handles
  // OPCODE_CONST/OPCODE_CONST_WIDE. Its type is undeterminable -> nullptr.
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (const v0 0)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  auto& cfg = foo_method->get_code()->cfg();
  auto* unreachable = new IRInstruction(IOPCODE_UNREACHABLE);
  unreachable->set_dest(0);
  auto ii = InstructionIterable(cfg);
  cfg.insert_before(ii.begin(), unreachable);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  const auto* result_type =
      ota.get_result_type(nullptr, {unreachable}, /* optional_extra_type */
                          nullptr);
  EXPECT_EQ(result_type, nullptr);
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_object) {
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(Ljava/lang/Object;LBar;)V" (
        (load-param-object v1)
        (load-param-object v2)
        (load-param-object v3)
      )))");
  foo_method->get_code()->build_cfg();
  foo_creator.add_method(foo_method);
  object_creator.create();
  auto* foo_type = foo_creator.create()->get_type();
  auto* bar_type = bar_creator.create()->get_type();

  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of first 'load-param-object' is Foo
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn},
                            /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, foo_type);
  }

  {
    // result type of second 'load-param-object' is Object
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }

  {
    // result type of third 'load-param-object' is Bar
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 3);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, bar_type);
  }

  {
    // the combined result type of Foo and Object is Object
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn1, insn2},
                            /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }

  {
    // the combined result type of Foo and Bar is Object
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 3);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn1, insn2},
                            /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_object_with_interfaces) {
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  auto* i_type = i_creator.create()->get_type();
  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  auto* j_type = j_creator.create()->get_type();
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.add_interface(i_type);
  foo_creator.add_interface(j_type);
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  bar_creator.add_interface(i_type);
  bar_creator.add_interface(j_type);

  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(LBar;)V" (
        (load-param-object v1)
        (load-param-object v2)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  foo_creator.add_method(foo_method);
  object_creator.create();
  auto* foo_type = foo_creator.create()->get_type();
  auto* bar_type = bar_creator.create()->get_type();

  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of first 'load-param-object' is Foo
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, foo_type);
  }

  {
    // result type of second 'load-param-object' is Bar
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, bar_type);
  }

  {
    // the combined result type of Foo and Bar is nullptr, as the common base
    // type Object does not implement the common interfaces I and J
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        ota.get_result_type(nullptr, {insn1, insn2},
                            /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, nullptr);
  }
}

static std::shared_ptr<outliner_impl::PartialCandidateNode> create_node(
    std::vector<IRInstruction*> insns,
    std::vector<std::pair<cfg::Edge*,
                          std::shared_ptr<outliner_impl::PartialCandidateNode>>>
        succs = {}) {
  return std::make_shared<outliner_impl::PartialCandidateNode>(
      (outliner_impl::PartialCandidateNode){
          std::move(insns), {}, std::move(succs)});
}

static outliner_impl::PartialCandidateAdapter create_candidate(
    outliner_impl::OutlinerTypeAnalysis& ota,
    const std::shared_ptr<outliner_impl::PartialCandidateNode>& root) {
  outliner_impl::PartialCandidate pc{{}, *root};
  return outliner_impl::PartialCandidateAdapter(ota, std::move(pc));
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_primitive) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(IZ)Z" (
        (load-param v1)
        (load-param v2)
        (move v1 v1)
        (add-int v1 v1 v1)
        (or-int v1 v1 v1)
        (sub-int v1 v1 v1)
        (xor-int v2 v2 v2)
        (return v2)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // type demand of src(0) of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_ADD_INT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // type demand of src(0) of 'return' of foo is boolean
    auto* insn = find_insn(foo_method, OPCODE_RETURN);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // type demand of src(0) of 'xor' with boolean out is boolean
    auto* insn = find_insn(foo_method, OPCODE_XOR_INT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    candidate.set_result(insn->dest(), type::_boolean());
    const auto* result_type = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // type demand of src(0) of 'or' follows by 'sub' is int
    auto* insn1 = find_insn(foo_method, OPCODE_OR_INT);
    auto* insn2 = find_insn(foo_method, OPCODE_SUB_INT);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, type::_int());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_sputs_of_zero) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (const v0 0)
        (sput-object v0 "LFoo;.s1:LBar1;")
        (sput-object v0 "LFoo;.s2:LBar2;")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // there's no type that would fit untyped zero (null)
    auto* insn1 = find_insn(foo_method, OPCODE_SPUT_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, OPCODE_SPUT_OBJECT, 2);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, nullptr);
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_zero) {
  std::string src = R"(
      (
        (const v1 0)
        (const v2 0)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // type demand of if-eq src(0) is not something we can determine
    // with zero (could be object or int)
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, nullptr);
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_nonzero) {
  std::string src = R"(
      (
        (const v1 23)
        (const v2 42)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_int());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_large_constants) {
  std::string src = R"(
      (
        (const v1 -30000)
        (const v2 40000)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // the non-zero constants flowing into the if must be some kind of integer
    // type. The particular values here allow us to pick specific types.
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type0 = ota.get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type0, type::_short());
    const auto* result_type1 = ota.get_type_demand(candidate, insn->src(1));
    EXPECT_EQ(result_type1, type::_char());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_primitive_narrow) {
  std::string src = R"(
      (
        (const v0 42)
        (load-param-object v1)
        (iput-short v0 v1 "LFoo;.f:S")
        (iput-byte v0 v1 "LFoo;.g:B")
        (iput v0 v1 "LFoo;.h:I")
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method("LFoo;.foo:()V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // the narrowed type demand on the value across all the iputs is byte
    auto* insn1 = find_insn(foo_method, OPCODE_IPUT_SHORT);
    auto* insn2 = find_insn(foo_method, OPCODE_IPUT_BYTE);
    auto* insn3 = find_insn(foo_method, OPCODE_IPUT);
    auto root = create_node({insn1, insn2, insn3});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, type::_byte());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_aput_object) {
  std::string src = R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v2 42)
        (aput-object v0 v1 v2)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method(
                         "LFoo;.foo:(Ljava/lang/String;[Ljava/lang/String;)V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    auto* insn = find_insn(foo_method, OPCODE_APUT_OBJECT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* type0 = ota.get_type_demand(candidate, insn->src(0));
    const auto* type1 = ota.get_type_demand(candidate, insn->src(1));
    EXPECT_EQ(type0, type::java_lang_Object());
    EXPECT_EQ(type1, DexType::make_type("[Ljava/lang/Object;"));
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_inference) {
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  auto* i_type = i_creator.create()->get_type();
  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  auto* j_type = j_creator.create()->get_type();
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  bar_creator.add_interface(i_type);
  bar_creator.add_interface(j_type);
  auto* bar_type = bar_creator.create()->get_type();

  std::string src = R"(
      (
        (load-param-object v1)
        (load-param-object v2)
        (iput-object v2 v1 "LFoo;.i:LI;")
        (iput-object v2 v1 "LFoo;.j:LJ;")
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method("LFoo;.foo:(LBar;)V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // it's not clear what the narrowed type of {I, J} is; then type inference
    // will be used, which will determine that the incoming value is if type Bar
    // (which happens to implement the two interfaces)
    auto* insn1 = find_insn(foo_method, OPCODE_IPUT_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, OPCODE_IPUT_OBJECT, 2);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = ota.get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, bar_type);
  }
}
