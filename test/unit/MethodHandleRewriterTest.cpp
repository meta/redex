/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodHandleRewriter.h"

#include <gtest/gtest.h>

#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRInstruction.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

class MethodHandleRewriterTest : public RedexTest {};

namespace {

// Maps every handle of `LFoo;.a:()V` to an invoke-static handle of
// `LFoo;.b:()V`.
MethodHandleRewriter::Mappings a_to_b() {
  return {.handle = [](const DexMethodHandle* method_handle,
                       const DexMethod*) -> std::optional<DexMethodHandle> {
    if (method_handle->methodref() != DexMethod::make_method("LFoo;.a:()V")) {
      return std::nullopt;
    }
    return DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                           DexMethod::make_method("LFoo;.b:()V"));
  }};
}

DexMethodHandle* handle_of_a() {
  return redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                   "LFoo;.a:()V");
}

// A call site that passes a new handle of `LFoo;.a:()V`, the Class of `LFoo;`
// and a string to its bootstrap method.
DexCallSite* make_callsite_of_a() {
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodHandle>(handle_of_a()));
  args.push_back(
      std::make_unique<DexEncodedValueType>(DexType::make_type("LFoo;")));
  args.push_back(
      std::make_unique<DexEncodedValueString>(DexString::make_string("name")));
  return redex::make_callsite("run", "()V", std::move(args));
}

DexMethodHandle* arg_method_handle(const DexCallSite* callsite, size_t i) {
  return redex::encoded_value_as<DexEncodedValueMethodHandle>(
             callsite->args().at(i).get())
      ->methodhandle();
}

std::unique_ptr<IRInstruction> make_const_method_handle(
    DexMethodHandle* method_handle) {
  auto insn = std::make_unique<IRInstruction>(OPCODE_CONST_METHOD_HANDLE);
  insn->set_methodhandle(method_handle);
  return insn;
}

std::unique_ptr<IRInstruction> make_invoke_custom(DexCallSite* callsite) {
  auto insn = std::make_unique<IRInstruction>(OPCODE_INVOKE_CUSTOM);
  insn->set_callsite(callsite);
  return insn;
}

} // namespace

TEST_F(MethodHandleRewriterTest, const_method_handle) {
  auto* original = handle_of_a();
  auto insn = make_const_method_handle(original);
  MethodHandleRewriter rewriter(a_to_b());

  EXPECT_TRUE(rewriter.rewrite(insn.get(), nullptr));
  auto* replacement = insn->get_methodhandle();
  EXPECT_EQ(replacement->type(), METHOD_HANDLE_TYPE_INVOKE_STATIC);
  EXPECT_EQ(replacement->methodref(), DexMethod::make_method("LFoo;.b:()V"));
  EXPECT_EQ(original->methodref(), DexMethod::make_method("LFoo;.a:()V"));

  EXPECT_FALSE(rewriter.rewrite(insn.get(), nullptr));
  EXPECT_EQ(insn->get_methodhandle(), replacement);
}

// The call site's other values carry over to its replacement, and the call
// site itself, which other instructions can hold, does not change.
TEST_F(MethodHandleRewriterTest, call_site_argument) {
  auto* original = make_callsite_of_a();
  auto insn = make_invoke_custom(original);
  MethodHandleRewriter rewriter(a_to_b());

  EXPECT_TRUE(rewriter.rewrite(insn.get(), nullptr));
  auto* replacement = insn->get_callsite();
  ASSERT_NE(replacement, original);
  EXPECT_EQ(replacement->method_handle(), original->method_handle());
  EXPECT_EQ(replacement->method_name(), original->method_name());
  EXPECT_EQ(replacement->method_type(), original->method_type());
  ASSERT_EQ(replacement->args().size(), 3);
  EXPECT_EQ(arg_method_handle(replacement, 0)->methodref(),
            DexMethod::make_method("LFoo;.b:()V"));
  EXPECT_EQ(replacement->args()[1]->show(), "LFoo;");
  EXPECT_EQ(replacement->args()[2]->show(), original->args()[2]->show());
  EXPECT_EQ(arg_method_handle(original, 0)->methodref(),
            DexMethod::make_method("LFoo;.a:()V"));

  EXPECT_FALSE(rewriter.rewrite(insn.get(), nullptr));
  EXPECT_EQ(insn->get_callsite(), replacement);
}

TEST_F(MethodHandleRewriterTest, call_site_bootstrap_method) {
  auto* original = redex::make_callsite("run", "()V");
  auto* bootstrap = original->method_handle();
  auto insn = make_invoke_custom(original);
  MethodHandleRewriter rewriter(
      {.handle = [&](const DexMethodHandle* method_handle,
                     const DexMethod*) -> std::optional<DexMethodHandle> {
        if (method_handle != bootstrap) {
          return std::nullopt;
        }
        return DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                               DexMethod::make_method("LBoot;.other:()V"));
      }});

  EXPECT_TRUE(rewriter.rewrite(insn.get(), nullptr));
  EXPECT_EQ(insn->get_callsite()->method_handle()->methodref(),
            DexMethod::make_method("LBoot;.other:()V"));
  EXPECT_EQ(original->method_handle(), bootstrap);
}

TEST_F(MethodHandleRewriterTest, call_site_class_argument) {
  auto* original = make_callsite_of_a();
  auto insn = make_invoke_custom(original);
  MethodHandleRewriter rewriter({.class_type = [](DexType* type) {
    return type == DexType::make_type("LFoo;") ? DexType::make_type("LBar;")
                                               : type;
  }});

  EXPECT_TRUE(rewriter.rewrite(insn.get(), nullptr));
  auto* replacement = insn->get_callsite();
  ASSERT_NE(replacement, original);
  EXPECT_EQ(arg_method_handle(replacement, 0), arg_method_handle(original, 0));
  EXPECT_EQ(replacement->args()[1]->show(), "LBar;");
  EXPECT_EQ(original->args()[1]->show(), "LFoo;");
}

TEST_F(MethodHandleRewriterTest, call_site_method_types) {
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto("(LFoo;)V")));
  auto* original = redex::make_callsite("run", "()LFoo;", std::move(args));
  auto insn = make_invoke_custom(original);
  MethodHandleRewriter rewriter({.method_type = [](DexProto* proto) {
    return proto == DexProto::make_proto("(LFoo;)V")
               ? DexProto::make_proto("(LBar;)V")
           : proto == DexProto::make_proto("()LFoo;")
               ? DexProto::make_proto("()LBar;")
               : proto;
  }});

  EXPECT_TRUE(rewriter.rewrite(insn.get(), nullptr));
  auto* replacement = insn->get_callsite();
  ASSERT_NE(replacement, original);
  EXPECT_EQ(replacement->method_type(), DexProto::make_proto("()LBar;"));
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodType>(
                replacement->args()[0].get())
                ->proto(),
            DexProto::make_proto("(LBar;)V"));
  EXPECT_EQ(original->method_type(), DexProto::make_proto("()LFoo;"));
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodType>(
                original->args()[0].get())
                ->proto(),
            DexProto::make_proto("(LFoo;)V"));
}

// A mapping that keeps everything keeps the call site.
TEST_F(MethodHandleRewriterTest, call_site_without_changes) {
  auto* original = redex::make_callsite("run", "()V");
  auto insn = make_invoke_custom(original);
  MethodHandleRewriter rewriter(
      {.handle = [](const DexMethodHandle* method_handle, const DexMethod*)
           -> std::optional<DexMethodHandle> { return *method_handle; },
       .class_type = [](DexType* type) { return type; },
       .method_type = [](DexProto* proto) { return proto; }});

  EXPECT_FALSE(rewriter.rewrite(insn.get(), nullptr));
  EXPECT_EQ(insn->get_callsite(), original);
}

// ART links each call site once, so instructions that share a call site keep
// sharing one, as do instructions that share a method handle.
TEST_F(MethodHandleRewriterTest, shared_originals_share_their_replacement) {
  auto* callsite = make_callsite_of_a();
  auto first_invoke = make_invoke_custom(callsite);
  auto second_invoke = make_invoke_custom(callsite);
  auto* method_handle = handle_of_a();
  auto first_const = make_const_method_handle(method_handle);
  auto second_const = make_const_method_handle(method_handle);
  MethodHandleRewriter rewriter(a_to_b());

  for (auto* insn : {first_invoke.get(), second_invoke.get(), first_const.get(),
                     second_const.get()}) {
    EXPECT_TRUE(rewriter.rewrite(insn, nullptr));
  }
  EXPECT_EQ(first_invoke->get_callsite(), second_invoke->get_callsite());
  EXPECT_EQ(first_const->get_methodhandle(), second_const->get_methodhandle());
}

// Call sites with equal values are still separate call sites, which ART links
// separately; so are their replacements.
TEST_F(MethodHandleRewriterTest, distinct_originals_stay_distinct) {
  auto first_invoke = make_invoke_custom(make_callsite_of_a());
  auto second_invoke = make_invoke_custom(make_callsite_of_a());
  auto first_const = make_const_method_handle(handle_of_a());
  auto second_const = make_const_method_handle(handle_of_a());
  MethodHandleRewriter rewriter(a_to_b());

  for (auto* insn : {first_invoke.get(), second_invoke.get(), first_const.get(),
                     second_const.get()}) {
    EXPECT_TRUE(rewriter.rewrite(insn, nullptr));
  }
  EXPECT_NE(first_invoke->get_callsite(), second_invoke->get_callsite());
  EXPECT_NE(first_const->get_methodhandle(), second_const->get_methodhandle());
}

// What a handle calls can depend on the class that holds it, so one handle can
// become different handles in different methods, and one call site different
// call sites.
TEST_F(MethodHandleRewriterTest, replacement_depends_on_holder) {
  auto* first_holder = DexMethod::make_method("LFirst;.m:()V")
                           ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  auto* second_holder = DexMethod::make_method("LSecond;.m:()V")
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  auto* callsite = make_callsite_of_a();
  auto first_invoke = make_invoke_custom(callsite);
  auto second_invoke = make_invoke_custom(callsite);
  auto third_invoke = make_invoke_custom(callsite);
  MethodHandleRewriter rewriter(
      {.handle = [](const DexMethodHandle* method_handle,
                    const DexMethod* holder) -> std::optional<DexMethodHandle> {
        if (method_handle->methodref() !=
            DexMethod::make_method("LFoo;.a:()V")) {
          return std::nullopt;
        }
        return DexMethodHandle(
            METHOD_HANDLE_TYPE_INVOKE_STATIC,
            DexMethod::make_method(holder->get_class(),
                                   DexString::make_string("a"),
                                   method_handle->methodref()->get_proto()));
      }});

  EXPECT_TRUE(rewriter.rewrite(first_invoke.get(), first_holder));
  EXPECT_TRUE(rewriter.rewrite(second_invoke.get(), second_holder));
  EXPECT_TRUE(rewriter.rewrite(third_invoke.get(), first_holder));
  EXPECT_EQ(arg_method_handle(first_invoke->get_callsite(), 0)->methodref(),
            DexMethod::make_method("LFirst;.a:()V"));
  EXPECT_EQ(arg_method_handle(second_invoke->get_callsite(), 0)->methodref(),
            DexMethod::make_method("LSecond;.a:()V"));
  EXPECT_EQ(first_invoke->get_callsite(), third_invoke->get_callsite());
}
