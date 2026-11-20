/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>

#include <gtest/gtest.h>

#include "Creators.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RemoveBuilders.h"
#include "Walkers.h"

class RemoveBuildersTest : public RedexTest {};

namespace {

// Runs RemoveBuildersPass on a `LUser;.make:()LFoo;` that creates a
// `LFoo$Builder;`, sets its field, makes `call` and builds a `LFoo;` with it.
// Returns whether `make` still creates the builder.
bool make_keeps_builder(const std::string& call) {
  ClassCreator object_creator(type::java_lang_Object());
  auto* object_init = dynamic_cast<DexMethod*>(
      DexMethod::make_method("Ljava/lang/Object;.<init>:()V"));
  object_init->set_access(ACC_PUBLIC | ACC_CONSTRUCTOR);
  object_init->set_external();
  object_creator.add_method(object_init);
  object_creator.create()->set_external();

  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
     )
    )
  )"));

  ClassCreator builder_creator(DexType::make_type("LFoo$Builder;"));
  builder_creator.set_super(type::java_lang_Object());
  builder_creator.add_field(
      DexField::make_field("LFoo$Builder;.x:I")->make_concrete(ACC_PUBLIC));
  builder_creator.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LFoo$Builder;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
     )
    )
  )"));
  builder_creator.add_method(assembler::method_from_string(R"(
    (method (public) "LFoo$Builder;.build:()LFoo;"
     (
      (load-param-object v0)
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LFoo;.<init>:()V")
      (return-object v1)
     )
    )
  )"));

  ClassCreator user_creator(DexType::make_type("LUser;"));
  user_creator.set_super(type::java_lang_Object());
  auto* make = assembler::method_from_string(R"(
    (method (public static) "LUser;.make:()LFoo;"
     (
      (new-instance "LFoo$Builder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LFoo$Builder;.<init>:()V")
      (const v1 1)
      (iput v1 v0 "LFoo$Builder;.x:I")
      )" + call + R"(
      (invoke-virtual (v0) "LFoo$Builder;.build:()LFoo;")
      (move-result-object v2)
      (return-object v2)
     )
    )
  )");
  user_creator.add_method(make);

  DexStore store("classes");
  store.add_classes(
      {foo_creator.create(), builder_creator.create(), user_creator.create()});
  DexStoresVector stores({std::move(store)});
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  ConfigFiles conf(Json::nullValue);
  conf.parse_global_config();
  RemoveBuildersPass pass;
  PassManager manager({&pass}, conf, RedexOptions{});
  manager.run_passes(stores, conf);

  // PassManager leaves the code in linear form.
  auto* code = make->get_code();
  always_assert(!code->cfg_built());
  auto ii = InstructionIterable(*code);
  return std::any_of(ii.begin(), ii.end(), [](const auto& mie) {
    return mie.insn->opcode() == OPCODE_NEW_INSTANCE &&
           mie.insn->get_type()->str() == "LFoo$Builder;";
  });
}

} // namespace

// A call whose target is not in the input runs code that is not known here:
//
//   Foo.Builder builder = new Foo.Builder();
//   builder.x = 1;
//   Missing.take(builder);  // `Missing` is not in the input
//   return builder.build();
TEST_F(RemoveBuildersTest, builderPassedToUnresolvedCallIsKept) {
  EXPECT_TRUE(make_keeps_builder(
      R"((invoke-static (v0) "LMissing;.take:(LFoo$Builder;)V"))"));
}

// An unresolved call that is not passed the builder does not keep it.
TEST_F(RemoveBuildersTest, builderNotPassedToUnresolvedCallIsRemoved) {
  EXPECT_FALSE(make_keeps_builder(R"((invoke-static () "LMissing;.run:()V"))"));
}
