/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "MethodReference.h"

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

class MethodReferenceTest : public RedexTest {};

namespace {

// The method handles that the code of `method` holds.
std::vector<DexMethodHandle*> held_method_handles(DexMethod* method) {
  std::vector<DexMethodHandle*> method_handles;
  for (const auto& mie : InstructionIterable(method->get_code())) {
    mie.insn->gather_methodhandles(method_handles);
  }
  return method_handles;
}

} // namespace

// Like an invoke of `LA;.b`, the method handles of `LA;.b` must call `LA;.a`
// once every call of `b` is redirected to `a`, as method deduplication does.
// The handles and the call site are shared, so they are replaced, not changed.
TEST_F(MethodReferenceTest, update_call_refs_simple_updates_method_handles) {
  auto* a = assembler::method_from_string(R"(
    (method (public static) "LA;.a:()V"
     (
      (return-void)
     )
    )
  )");
  auto* b = assembler::method_from_string(R"(
    (method (public static) "LA;.b:()V"
     (
      (return-void)
     )
    )
  )");
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LA;.user:()V"
     (
      (invoke-static () "LA;.placeholder:()V")
      (const-method-handle invoke-static "LA;.b:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");
  auto* handle_of_b =
      redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC, "LA;.b:()V");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodHandle>(handle_of_b));
  auto* callsite = redex::make_invoke_custom(user->get_code(), "run", "()V",
                                             std::move(args));
  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(a);
  creator.add_method(b);
  creator.add_method(user);
  Scope scope{creator.create()};

  method_reference::update_call_refs_simple(scope, {{b, a}});

  auto method_handles = held_method_handles(user);
  // The call site's bootstrap method, its argument and the constant.
  ASSERT_EQ(method_handles.size(), 3);
  for (auto* method_handle : {method_handles[1], method_handles[2]}) {
    EXPECT_EQ(method_handle->type(), METHOD_HANDLE_TYPE_INVOKE_STATIC);
    EXPECT_EQ(method_handle->methodref(), a);
  }
  EXPECT_EQ(handle_of_b->methodref(), b);
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                callsite->args()[0].get())
                ->methodhandle(),
            handle_of_b);
}

// An invoke-direct handle of a method that is not private calls that method
// itself when the holding class declares it, as ART resolves it.
TEST_F(MethodReferenceTest,
       update_call_refs_simple_updates_method_handle_of_own_virtual_method) {
  auto* m = assembler::method_from_string(R"(
    (method (public) "LA;.m:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  auto* n = assembler::method_from_string(R"(
    (method (public) "LA;.n:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LA;.user:()V"
     (
      (const-method-handle invoke-direct "LA;.m:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");
  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(m);
  creator.add_method(n);
  creator.add_method(user);
  Scope scope{creator.create()};

  method_reference::update_call_refs_simple(scope, {{m, n}});

  auto method_handles = held_method_handles(user);
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(method_handles[0]->type(), METHOD_HANDLE_TYPE_INVOKE_DIRECT);
  EXPECT_EQ(method_handles[0]->methodref(), n);
}

// ART links each call site once, so instructions that share a call site must
// share its replacement.
TEST_F(MethodReferenceTest, update_call_refs_simple_keeps_call_site_shared) {
  auto* a = assembler::method_from_string(R"(
    (method (public static) "LA;.a:()V"
     (
      (return-void)
     )
    )
  )");
  auto* b = assembler::method_from_string(R"(
    (method (public static) "LA;.b:()V"
     (
      (return-void)
     )
    )
  )");
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LA;.user:()V"
     (
      (invoke-static () "LA;.placeholder:()V")
      (invoke-static () "LA;.placeholder:()V")
      (return-void)
     )
    )
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LA;.b:()V")));
  auto* callsite = redex::make_invoke_custom(user->get_code(), "run", "()V",
                                             std::move(args));
  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(a);
  creator.add_method(b);
  creator.add_method(user);
  Scope scope{creator.create()};

  method_reference::update_call_refs_simple(scope, {{b, a}});

  std::vector<DexCallSite*> callsites;
  for (const auto& mie : InstructionIterable(user->get_code())) {
    if (mie.insn->has_callsite()) {
      callsites.push_back(mie.insn->get_callsite());
    }
  }
  ASSERT_EQ(callsites.size(), 2);
  EXPECT_NE(callsites[0], callsite);
  EXPECT_EQ(callsites[0], callsites[1]);
}

// A method handle that a static field value holds calls `LA;.a` too.
TEST_F(MethodReferenceTest,
       update_call_refs_simple_updates_method_handle_of_static_field_value) {
  auto* a = assembler::method_from_string(R"(
    (method (public static) "LA;.a:()V"
     (
      (return-void)
     )
    )
  )");
  auto* b = assembler::method_from_string(R"(
    (method (public static) "LA;.b:()V"
     (
      (return-void)
     )
    )
  )");
  auto* field =
      DexField::make_field("LA;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "LA;.b:()V")));
  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(a);
  creator.add_method(b);
  creator.add_field(field);
  Scope scope{creator.create()};

  method_reference::update_call_refs_simple(scope, {{b, a}});

  auto* method_handle = redex::encoded_value_as<DexEncodedValueMethodHandle>(
                            field->get_static_value())
                            ->methodhandle();
  EXPECT_EQ(method_handle->type(), METHOD_HANDLE_TYPE_INVOKE_STATIC);
  EXPECT_EQ(method_handle->methodref(), a);
}
