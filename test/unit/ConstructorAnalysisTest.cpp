/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConstructorAnalysis.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "Show.h"

struct ConstructorAnalysisTest : public RedexTest {};

DexClass* create_a_class(const char* description, DexType* super) {
  ClassCreator cc(DexType::make_type(description));
  cc.set_super(super);
  return cc.create();
}

DexClass* create_a_class(const char* description) {
  return create_a_class(description, type::java_lang_Object());
}

/**
 * Create a method like
 * void <init>(object, ..(num_param_types many).., object) {
 *   load-param v0
 *   ...
 *   load-null v1
 *   iput f, v1, v0
 *   ...
 *   load-null v1
 *   invoke-direct v0, v1, ..(num_param_types many).., v1, {{init_to_call}}
 *   ret;
 * }
 */
DexMethod* create_an_init_method(
    DexClass* cls,
    DexMethodRef* init_to_call,
    size_t num_param_types,
    const std::vector<DexField*>& fields_to_assign_null = {},
    bool before_init_call = false,
    bool spurious_init_call = false) {
  DexTypeList::ContainerType param_types;
  auto* java_lang_Object = DexType::make_type("Ljava/lang/Object;");
  for (size_t i = 0; i < num_param_types; i++) {
    param_types.push_back(java_lang_Object);
  }
  auto* proto = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list(std::move(param_types)));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string("<init>"), proto);
  MethodCreator mc(ref, ACC_PUBLIC | ACC_CONSTRUCTOR);
  auto args = mc.get_reg_args();
  auto first_arg = *args.begin();
  auto* main_block = mc.get_main_block();
  if (before_init_call) {
    for (auto* f : fields_to_assign_null) {
      auto f_null_loc = mc.make_local(f->get_type());
      main_block->load_null(f_null_loc);
      main_block->iput(f, first_arg, f_null_loc);
    }
  }
  std::vector<Location> init_args{first_arg};
  auto p_null_loc = mc.make_local(java_lang_Object);
  main_block->load_null(p_null_loc);
  for (size_t i = 0; i < num_param_types; i++) {
    init_args.push_back(p_null_loc);
  }
  main_block->invoke(OPCODE_INVOKE_DIRECT, init_to_call, init_args);
  for (auto* f : fields_to_assign_null) {
    auto f_null_loc = mc.make_local(f->get_type());
    main_block->load_null(f_null_loc);
    main_block->iput(f, first_arg, f_null_loc);
  }
  if (spurious_init_call) {
    init_args[0] = mc.make_local(init_to_call->get_class());
    main_block->new_instance(init_to_call->get_class(), init_args[0]);
    main_block->invoke(OPCODE_INVOKE_DIRECT, init_to_call, init_args);
  }
  main_block->ret_void();
  auto* method = mc.create();
  cls->add_method(method);
  method->get_code()->build_cfg();
  return method;
}

TEST_F(ConstructorAnalysisTest, can_inline_init_simple) {
  auto* foo_cls = create_a_class("Lfoo;");
  auto* foo_init1 = create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});
  auto* foo_init2 = create_an_init_method(foo_cls, foo_init1, 1, {});

  EXPECT_FALSE(constructor_analysis::can_inline_init(foo_init1));
  EXPECT_TRUE(constructor_analysis::can_inline_init(foo_init2));
  EXPECT_TRUE(constructor_analysis::can_inline_inits_in_same_class(
      foo_init2, foo_init1, nullptr));
}

TEST_F(ConstructorAnalysisTest, can_inline_init_iput_before_init_call) {
  auto* foo_cls = create_a_class("Lfoo;");
  auto* f = DexField::make_field("Lfoo;.f:Ljava/lang/Object;")
                ->make_concrete(ACC_PUBLIC);
  auto* foo_init1 = create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});
  auto* foo_init2 = create_an_init_method(foo_cls, foo_init1, 1, {f},
                                          /* before_init_call */ true);

  EXPECT_FALSE(constructor_analysis::can_inline_init(foo_init2));
}

TEST_F(ConstructorAnalysisTest, can_inline_init_iput_after_init_call) {
  auto* foo_cls = create_a_class("Lfoo;");
  auto* f = DexField::make_field("Lsfoo;.f:Ljava/lang/Object;")
                ->make_concrete(ACC_PUBLIC);
  auto* foo_init1 = create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});
  auto* foo_init2 = create_an_init_method(foo_cls, foo_init1, 1, {f},
                                          /* before_init_call */ false);

  EXPECT_TRUE(constructor_analysis::can_inline_init(foo_init2));
}

TEST_F(ConstructorAnalysisTest,
       can_inline_inits_in_same_class_unsupported_init_call) {
  auto* foo_cls = create_a_class("Lfoo;");
  auto* foo_init1 = create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});
  auto* foo_init2 = create_an_init_method(foo_cls, foo_init1, 1, {}, false,
                                          /* spurious_init_call */ true);

  std::vector<IRInstruction*> callsite_insns;
  for (auto& mie : InstructionIterable(foo_init2->get_code()->cfg())) {
    IRInstruction* insn = mie.insn;
    if (insn->opcode() == OPCODE_INVOKE_DIRECT &&
        insn->get_method() == foo_init1) {
      callsite_insns.push_back(insn);
    }
  }
  EXPECT_EQ(callsite_insns.size(), 2);

  EXPECT_FALSE(constructor_analysis::can_inline_inits_in_same_class(
      foo_init2, foo_init1, nullptr));
  EXPECT_TRUE(constructor_analysis::can_inline_inits_in_same_class(
      foo_init2, foo_init1, callsite_insns[0]));
  EXPECT_FALSE(constructor_analysis::can_inline_inits_in_same_class(
      foo_init2, foo_init1, callsite_insns[1]));
}

TEST_F(ConstructorAnalysisTest, can_inline_init_supertype_relaxed) {
  auto* foo_cls = create_a_class("Lfoo;");
  auto* foo_init1 = create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});

  EXPECT_FALSE(constructor_analysis::can_inline_init(
      foo_init1, /* finalizable_fields */ nullptr, /* relaxed */ true));
}

TEST_F(ConstructorAnalysisTest, find_relaxed_inits) {
  // Set up a couple of classes, and usages of them (some of which will look
  // like its constructor was inlined).
  auto* foo_cls = create_a_class("Lfoo;");
  create_an_init_method(
      foo_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});

  auto* bar_cls = create_a_class("Lbar;");
  auto* bar_init = create_an_init_method(
      bar_cls, DexMethod::make_method("Ljava/lang/Object;.<init>:()V"), 0, {});

  auto* baz_cls = create_a_class("Lbaz;", bar_cls->get_type());
  create_an_init_method(baz_cls, bar_init, 0, {});

  auto* use_cls = assembler::class_from_string(R"(
    (class (public) "Luse;"
      (method (public static) "Luse;.a:(I)V"
        (
          ; relaxed, initialized by Object's constructor
          (new-instance "Lfoo;")
          (move-result-pseudo-object v1)
          (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")

          ; totally normal
          (new-instance "Lbar;")
          (move-result-pseudo-object v2)
          (invoke-direct (v2) "Lbar;.<init>:()V")

          ; relaxed, through a move
          (new-instance "Lbaz;")
          (move-result-pseudo-object v3)
          (move-object v4 v3)
          (invoke-direct (v4) "Lbar;.<init>:()V")

          ; does not resolve
          (new-instance "Lbar;")
          (move-result-pseudo-object v5)
          (invoke-direct (v5) "Lbar;.<init>:(I)V")
          (return-void)
        )
      )
    )
  )");

  Scope scope{foo_cls, bar_cls, baz_cls, use_cls};
  for (auto* cls : scope) {
    for (auto* m : cls->get_all_methods()) {
      auto* code = m->get_code();
      if (code != nullptr) {
        code->build_cfg();
      }
    }
  }
  auto* method = use_cls->get_dmethods().front();
  auto relaxed_inits = constructor_analysis::find_relaxed_inits(
      method, [](const DexType*) { return true; });
  ASSERT_EQ(relaxed_inits.size(), 3);
  EXPECT_EQ(relaxed_inits[0].new_instance->get_type(), foo_cls->get_type());
  // java.lang.Object is not defined in this test, so its constructor does not
  // resolve.
  EXPECT_EQ(relaxed_inits[0].resolved_init, nullptr);
  EXPECT_EQ(relaxed_inits[1].new_instance->get_type(), baz_cls->get_type());
  EXPECT_EQ(relaxed_inits[1].resolved_init, bar_init);
  EXPECT_EQ(show(relaxed_inits[1].invoke->get_method()), "Lbar;.<init>:()V");
  EXPECT_EQ(relaxed_inits[2].new_instance->get_type(), bar_cls->get_type());
  EXPECT_EQ(relaxed_inits[2].resolved_init, nullptr);

  auto baz_only = constructor_analysis::find_relaxed_inits(
      method, [&](const DexType* type) { return type == baz_cls->get_type(); });
  ASSERT_EQ(baz_only.size(), 1);
  EXPECT_EQ(baz_only[0].invoke, relaxed_inits[1].invoke);
}
