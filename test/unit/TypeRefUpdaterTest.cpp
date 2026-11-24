/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeReference.h"

#include "Creators.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "RedexTest.h"

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
