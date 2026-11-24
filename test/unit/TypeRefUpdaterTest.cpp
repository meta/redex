/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeReference.h"

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

using namespace type_reference;

class TypeRefUpdaterTest : public RedexTest {
 protected:
  // Defines `LFoo;` and a class `LUser;` with the static method `method`, then
  // updates `LFoo;` to `LBar;` everywhere.
  void update_foo_to_bar(DexMethod* method) {
    auto* foo = DexType::make_type("LFoo;");
    ClassCreator foo_creator(foo);
    foo_creator.set_super(type::java_lang_Object());
    auto* foo_cls = foo_creator.create();

    ClassCreator user_creator(DexType::make_type("LUser;"));
    user_creator.set_super(type::java_lang_Object());
    user_creator.add_method(method);
    auto* user_cls = user_creator.create();

    Scope scope{foo_cls, user_cls};
    UnorderedMap<DexType*, DexType*> mapping{
        {foo, DexType::make_type("LBar;")}};
    TypeRefUpdater(mapping).update_methods_fields(scope);
  }
};

TEST_F(TypeRefUpdaterTest, init_collision) {
  auto* foo = DexType::make_type("LFoo;");
  auto* bar = DexType::make_type("LBar;");
  ClassCreator cc(foo);
  cc.set_super(type::java_lang_Object());

  auto* ctor_takes_foo = DexMethod::make_method("LFoo;.<init>:(LFoo;)V")
                             ->make_concrete(ACC_PUBLIC, false);
  ctor_takes_foo->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (return-void)
    )
  )"));
  cc.add_method(ctor_takes_foo);

  auto* ctor_takes_bar = DexMethod::make_method("LFoo;.<init>:(LBar;)V")
                             ->make_concrete(ACC_PUBLIC, false);
  ctor_takes_bar->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (return-void)
    )
  )"));
  cc.add_method(ctor_takes_bar);

  auto* baz = DexMethod::make_method("LFoo;.baz:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  baz->set_code(assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:(LFoo;)V")

      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:(LBar;)V")

      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      ; No definition for the constructor.
      (invoke-direct (v0) "LFoo;.<init>:(LFoo;LFoo;)V")
      (return-void)
    )
  )"));
  cc.add_method(baz);

  auto* cls_foo = cc.create();

  Scope scope{cls_foo};

  UnorderedMap<DexType*, DexType*> mapping{{foo, bar}};
  TypeRefUpdater updater(mapping);
  updater.update_methods_fields(scope);

  EXPECT_NE(DexMethod::get_method("LFoo;.<init>:(LBar;I)V"), nullptr);
  auto expected_baz_code = assembler::ircode_from_string(R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (const v1 42)
      (invoke-direct (v0 v1) "LFoo;.<init>:(LBar;I)V")

      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo;.<init>:(LBar;)V")

      (new-instance "LFoo;")
      (move-result-pseudo-object v0)
      ; No definition for the constructor. We update its signature.
      (invoke-direct (v0) "LFoo;.<init>:(LBar;LBar;)V")
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(baz->get_code(), expected_baz_code.get());
}

TEST_F(TypeRefUpdaterTest, method_constant_and_method_handle_call_prototypes) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:(Ljava/lang/invoke/MethodHandle;Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (load-param-object v1)
      (const-method-type "(LFoo;)[LFoo;")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LFoo;)V")
      (return-void)
     )
    )
  )");
  update_foo_to_bar(method);

  auto expected = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (const-method-type "(LBar;)[LBar;")
      (move-result-pseudo-object v2)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LBar;)V")
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(method->get_code(), expected.get());
}

TEST_F(TypeRefUpdaterTest, call_site) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:(Ljava/lang/Object;)V"
     (
      (load-param-object v0)
      (invoke-static (v0) "LUser;.placeholder:(Ljava/lang/Object;)V")
      (return-void)
     )
    )
  )");
  // A tool-generated call site with an app-defined bootstrap method, whose
  // bootstrap arguments name `Foo` in a method type and a method handle.
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto("(LFoo;)V")));
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LUser;.take:(LFoo;)V")));
  auto* callsite =
      redex::make_invoke_custom(method->get_code(), "accept",
                                "(Ljava/lang/Object;)LFoo;", std::move(args));
  update_foo_to_bar(method);

  auto* new_callsite =
      std::next(InstructionIterable(method->get_code()).begin())
          ->insn->get_callsite();
  EXPECT_EQ(new_callsite->method_type(),
            DexProto::make_proto("(Ljava/lang/Object;)LBar;"));
  const auto& updated_args = new_callsite->args();
  ASSERT_EQ(updated_args.size(), 2);
  EXPECT_EQ(
      redex::encoded_value_as<DexEncodedValueMethodType>(updated_args[0].get())
          ->proto(),
      DexProto::make_proto("(LBar;)V"));
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                updated_args[1].get())
                ->methodhandle()
                ->methodref()
                ->get_proto(),
            DexProto::make_proto("(LBar;)V"));
  EXPECT_EQ(callsite->method_type(),
            DexProto::make_proto("(Ljava/lang/Object;)LFoo;"));
}

namespace {

// The call sites that the invoke-custom instructions of `method` hold.
std::vector<DexCallSite*> held_call_sites(DexMethod* method) {
  std::vector<DexCallSite*> callsites;
  for (const auto& mie : InstructionIterable(method->get_code())) {
    if (mie.insn->has_callsite()) {
      callsites.push_back(mie.insn->get_callsite());
    }
  }
  return callsites;
}

} // namespace

// Call sites are shared, also by code outside the updated scope, so a call
// site is replaced, not changed; ART links each call site once, so the
// instructions that shared it share its replacement.
TEST_F(TypeRefUpdaterTest, call_site_is_replaced) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:()V"
     (
      (invoke-static () "LUser;.placeholder:()V")
      (invoke-static () "LUser;.placeholder:()V")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto("(LFoo;)V")));
  auto* callsite = redex::make_invoke_custom(method->get_code(), "get",
                                             "()LFoo;", std::move(args));
  auto* outside = assembler::method_from_string(R"(
    (method (public static) "LOutside;.run:()V"
     (
      (invoke-static () "LOutside;.placeholder:()V")
      (return-void)
     )
    )
  )");
  InstructionIterable(outside->get_code())
      .begin()
      ->insn->set_opcode(OPCODE_INVOKE_CUSTOM)
      ->set_callsite(callsite);
  update_foo_to_bar(method);

  auto callsites = held_call_sites(method);
  ASSERT_EQ(callsites.size(), 2);
  EXPECT_EQ(callsites[0], callsites[1]);
  EXPECT_EQ(callsites[0]->method_type(), DexProto::make_proto("()LBar;"));
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodType>(
                callsites[0]->args().at(0).get())
                ->proto(),
            DexProto::make_proto("(LBar;)V"));
  EXPECT_EQ(held_call_sites(outside), std::vector<DexCallSite*>{callsite});
  EXPECT_EQ(callsite->method_type(), DexProto::make_proto("()LFoo;"));
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodType>(
                callsite->args().at(0).get())
                ->proto(),
            DexProto::make_proto("(LFoo;)V"));
}

TEST_F(TypeRefUpdaterTest, method_handle_members) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:()V"
     (
      (const-method-handle invoke-static "LUser;.take:(LFoo;)V")
      (move-result-pseudo-object v0)
      (const-method-handle static-get "LUser;.f:[LFoo;")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  auto ii = InstructionIterable(code);
  auto* take = ii.begin()->insn->get_methodhandle()->methodref();
  auto* field = std::next(ii.begin(), 2)->insn->get_methodhandle()->fieldref();
  update_foo_to_bar(method);

  EXPECT_EQ(take->get_proto(), DexProto::make_proto("(LBar;)V"));
  EXPECT_EQ(field->get_type(), DexType::make_type("[LBar;"));
}

// A method type that a static field value holds describes methods like a
// const-method-type does.
TEST_F(TypeRefUpdaterTest, method_type_of_static_field_value) {
  auto* foo = DexType::make_type("LFoo;");
  ClassCreator foo_creator(foo);
  foo_creator.set_super(type::java_lang_Object());
  auto* foo_cls = foo_creator.create();

  auto* field =
      DexField::make_field("LUser;.TYPE:Ljava/lang/invoke/MethodType;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::make_unique<DexEncodedValueMethodType>(
                              DexProto::make_proto("(LFoo;)[LFoo;")));
  ClassCreator user_creator(DexType::make_type("LUser;"));
  user_creator.set_super(type::java_lang_Object());
  user_creator.add_field(field);
  auto* user_cls = user_creator.create();

  Scope scope{foo_cls, user_cls};
  UnorderedMap<DexType*, DexType*> mapping{{foo, DexType::make_type("LBar;")}};
  TypeRefUpdater(mapping).update_methods_fields(scope);

  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodType>(
                field->get_static_value())
                ->proto(),
            DexProto::make_proto("(LBar;)[LBar;"));
}
