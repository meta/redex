/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "Obfuscate.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Resolver.h"

namespace {

DexClass* make_class(std::string_view name, DexType* super) {
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(super);
  cc.set_access(ACC_PUBLIC);
  return cc.create();
}

void run_obfuscate(const std::vector<DexClass*>& classes) {
  ObfuscatePass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  DexStore store("classes");
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  manager.run_passes(stores, config);
}

// The method handles that the code of `method` loads with const-method-handle.
std::vector<DexMethodHandle*> loaded_method_handles(DexMethod* method) {
  std::vector<DexMethodHandle*> handles;
  for (const auto& mie : InstructionIterable(*method->get_code())) {
    if (mie.insn->has_methodhandle()) {
      handles.push_back(mie.insn->get_methodhandle());
    }
  }
  return handles;
}

} // namespace

class ObfuscateMethodHandleTest : public RedexTest {};

// Method handles (tool-generated here) that name a renamed field or static
// method through a subclass follow the rename, like a field instruction or an
// invoke of that member would.
TEST_F(ObfuscateMethodHandleTest, handles_of_inherited_members) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* f =
      DexField::make_field("LA;.f:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a->add_field(f);
  auto* g =
      DexMethod::make_method("LA;.g:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string("((return-void))"),
                          /* is_virtual */ false);
  a->add_method(g);
  auto* b = make_class("LB;", a->get_type());
  auto* c = make_class("LC;", type::java_lang_Object());
  auto* run = DexMethod::make_method("LC;.run:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(R"((
                                    (const-method-handle static-get "LB;.f:I")
                                    (move-result-pseudo-object v0)
                                    (const-method-handle invoke-static "LB;.g:()V")
                                    (move-result-pseudo-object v0)
                                    (return-void)
                                  ))"),
                                  /* is_virtual */ false);
  c->add_method(run);

  run_obfuscate({a, b, c});

  ASSERT_NE(f->get_name()->str(), "f");
  ASSERT_NE(g->get_name()->str(), "g");
  auto handles = loaded_method_handles(run);
  ASSERT_EQ(handles.size(), 2);
  EXPECT_EQ(handles[0]->fieldref(), f);
  EXPECT_EQ(handles[1]->methodref(), g);
}

// A static-get method handle of `LB;.x:I` resolves to the static field `LA;.x`,
// not to the instance field `LB;.x` that it names, so it still resolves to
// `LA;.x` after renaming. `LB;.w` makes the two fields get different names.
TEST_F(ObfuscateMethodHandleTest, field_handle_resolves_by_its_kind) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* a_x =
      DexField::make_field("LA;.x:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a->add_field(a_x);
  auto* b = make_class("LB;", a->get_type());
  auto* b_x = DexField::make_field("LB;.x:I")->make_concrete(ACC_PUBLIC);
  b->add_field(b_x);
  b->add_field(DexField::make_field("LB;.w:I")->make_concrete(ACC_PUBLIC));
  auto* c = make_class("LC;", type::java_lang_Object());
  auto* run = DexMethod::make_method("LC;.run:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(R"((
                                    (const-method-handle static-get "LB;.x:I")
                                    (move-result-pseudo-object v0)
                                    (return-void)
                                  ))"),
                                  /* is_virtual */ false);
  c->add_method(run);

  run_obfuscate({a, b, c});

  ASSERT_NE(a_x->get_name()->str(), "x");
  auto handles = loaded_method_handles(run);
  ASSERT_EQ(handles.size(), 1);
  EXPECT_EQ(handles[0]->type(), METHOD_HANDLE_TYPE_STATIC_GET);
  EXPECT_EQ(resolve_field_handle(handles[0]), a_x);
}

// A call site whose bootstrap argument is such a method handle is replaced by
// one with the fixed handle; the original, which other code may share, stays.
TEST_F(ObfuscateMethodHandleTest, call_site_handle_of_inherited_field) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* f =
      DexField::make_field("LA;.f:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a->add_field(f);
  auto* b = make_class("LB;", a->get_type());
  auto* c = make_class("LC;", type::java_lang_Object());
  auto* run = DexMethod::make_method("LC;.run:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(R"((
                                    (invoke-static () "LC;.placeholder:()V")
                                    (return-void)
                                  ))"),
                                  /* is_virtual */ false);
  c->add_method(run);
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  auto* handle =
      redex::make_method_handle(METHOD_HANDLE_TYPE_STATIC_GET, "LB;.f:I");
  args.push_back(std::make_unique<DexEncodedValueMethodHandle>(handle));
  auto* callsite =
      redex::make_invoke_custom(run->get_code(), "get", "()V", std::move(args));

  run_obfuscate({a, b, c});

  ASSERT_NE(f->get_name()->str(), "f");
  auto* insn = run->get_code()->begin()->insn;
  ASSERT_EQ(insn->opcode(), OPCODE_INVOKE_CUSTOM);
  auto* new_callsite = insn->get_callsite();
  ASSERT_NE(new_callsite, callsite);
  ASSERT_EQ(new_callsite->args().size(), 1);
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                new_callsite->args().front().get())
                ->methodhandle()
                ->fieldref(),
            f);
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                callsite->args().front().get())
                ->methodhandle(),
            handle);
}

namespace {

// The call sites that the invoke-custom instructions of `method` hold.
std::vector<DexCallSite*> held_call_sites(DexMethod* method) {
  std::vector<DexCallSite*> callsites;
  for (const auto& mie : InstructionIterable(*method->get_code())) {
    if (mie.insn->has_callsite()) {
      callsites.push_back(mie.insn->get_callsite());
    }
  }
  return callsites;
}

// A static method `name` of `cls` whose `n` invoke-custom instructions share
// one call site that passes a static-get handle of `LB;.f:I`.
DexMethod* add_user_of_inherited_field(DexClass* cls,
                                       const std::string& name,
                                       size_t n) {
  std::string code = "(";
  for (size_t i = 0; i < n; ++i) {
    code += R"((invoke-static () "LC;.placeholder:()V"))";
  }
  code += "(return-void))";
  auto* method = DexMethod::make_method("LC;." + name + ":()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                     assembler::ircode_from_string(code),
                                     /* is_virtual */ false);
  cls->add_method(method);
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodHandle>(
      redex::make_method_handle(METHOD_HANDLE_TYPE_STATIC_GET, "LB;.f:I")));
  redex::make_invoke_custom(method->get_code(), "get", "()V", std::move(args));
  return method;
}

} // namespace

// ART links each call site once, so instructions that share a call site must
// share its replacement, while another call site with the same values stays
// another call site.
TEST_F(ObfuscateMethodHandleTest, shared_call_site_stays_shared) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* f =
      DexField::make_field("LA;.f:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a->add_field(f);
  auto* b = make_class("LB;", a->get_type());
  auto* c = make_class("LC;", type::java_lang_Object());
  auto* run = add_user_of_inherited_field(c, "run", 2);
  auto* other = add_user_of_inherited_field(c, "other", 1);
  auto* callsite = held_call_sites(run).front();

  run_obfuscate({a, b, c});

  ASSERT_NE(f->get_name()->str(), "f");
  auto callsites = held_call_sites(run);
  ASSERT_EQ(callsites.size(), 2);
  EXPECT_NE(callsites[0], callsite);
  EXPECT_EQ(callsites[0], callsites[1]);
  auto other_callsites = held_call_sites(other);
  ASSERT_EQ(other_callsites.size(), 1);
  EXPECT_NE(other_callsites[0], callsites[0]);
}

// Method handles that static field values hold follow the rename too.
TEST_F(ObfuscateMethodHandleTest,
       static_field_value_handles_of_inherited_members) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* f =
      DexField::make_field("LA;.f:I")->make_concrete(ACC_PUBLIC | ACC_STATIC);
  a->add_field(f);
  auto* g =
      DexMethod::make_method("LA;.g:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string("((return-void))"),
                          /* is_virtual */ false);
  a->add_method(g);
  auto* b = make_class("LB;", a->get_type());
  auto* c = make_class("LC;", type::java_lang_Object());
  auto* getter =
      DexField::make_field("LC;.GETTER:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::make_unique<DexEncodedValueMethodHandle>(
                              redex::make_method_handle(
                                  METHOD_HANDLE_TYPE_STATIC_GET, "LB;.f:I")));
  c->add_field(getter);
  auto* invoker =
      DexField::make_field("LC;.INVOKER:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "LB;.g:()V")));
  c->add_field(invoker);

  run_obfuscate({a, b, c});

  ASSERT_NE(f->get_name()->str(), "f");
  ASSERT_NE(g->get_name()->str(), "g");
  auto handle_of = [](const DexField* field) {
    return redex::encoded_value_as<DexEncodedValueMethodHandle>(
               field->get_static_value())
        ->methodhandle();
  };
  EXPECT_EQ(handle_of(getter)->fieldref(), f);
  EXPECT_EQ(handle_of(invoker)->methodref(), g);
}
