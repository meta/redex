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
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "RedexTest.h"
#include "Show.h"

class DexAnnotationTest : public RedexTest {};

TEST_F(DexAnnotationTest, DeobfuscateStrings) {
  auto* obj = DexType::make_type("Ljava/lang/Object;");
  auto* a = DexType::make_type("LX/a;");
  DexType::make_type("[LX/a;");
  DexType::make_type("[[LX/a;");
  {
    ClassCreator creator(a);
    creator.set_super(obj);
    auto* a_cls = creator.create();
    a_cls->set_deobfuscated_name(DexString::make_string("Lcom/fb/MyThing;"));
  }

  auto* other = DexType::make_type("Lother/thing;");
  {
    ClassCreator creator(other);
    creator.set_super(obj);
    auto* other_cls = creator.create();
    other_cls->set_deobfuscated_name(DexString::make_string("Lother/thing;"));
  }

  std::map<std::string, std::string> value_to_expected{
      {"LX/a;", "Lcom/fb/MyThing;"},
      {"LX/a<", "Lcom/fb/MyThing<"},
      {"Lother/thing;", "Lother/thing;"},
      {"[[LX/a;", "[[Lcom/fb/MyThing;"},
      {"no idea", "no idea"},
      {"", ""},
      {"[[[[[[[[[", "[[[[[[[[["}};

  for (auto&& [value, expected] : value_to_expected) {
    DexEncodedValueString ev(DexString::make_string(value));
    auto shown = ev.show_deobfuscated();
    EXPECT_STREQ(shown.c_str(), expected.c_str());
  }
}

TEST_F(DexAnnotationTest, EscapeStrings) {
  // Android's MUTF-8 encoding of "Hello, U+1F30E" (earth showing Americas).
  {
    std::vector<uint8_t> mutf8_bytes{0x48, 0x65, 0x6c, 0x6c, 0x6f,
                                     0x2c, 0x20, 0xed, 0xa0, 0xbc,
                                     0xed, 0xbc, 0x8e, 0x21, 0x0};
    const auto* dex_string = DexString::make_string((char*)mutf8_bytes.data());
    auto escaped = show_escaped(dex_string);
    std::u8string_view expected(u8"Hello, \U0001F30E!");
    std::string expected_str(expected.begin(), expected.end());
    EXPECT_STREQ(escaped.c_str(), expected_str.c_str());
  }
  // The overlong encoding for null zero inside a string.
  {
    std::vector<uint8_t> mutf8_bytes{0x79, 0x6f, 0xc0, 0x80,
                                     0x73, 0x75, 0x70, 0x0};
    const auto* dex_string = DexString::make_string((char*)mutf8_bytes.data());
    auto escaped = show_escaped(dex_string);
    std::string expected_str("yo\\u0000sup");
    EXPECT_STREQ(escaped.c_str(), expected_str.c_str());
  }
}

// Method handles and call sites print what they refer to, not where they are in
// memory, so equal ones print alike in any RedexContext.
TEST_F(DexAnnotationTest, ShowMethodHandleAndCallSiteByContent) {
  auto* bootstrap = DexMethodHandle::make_method_handle(
      METHOD_HANDLE_TYPE_INVOKE_STATIC,
      DexMethod::make_method(
          "LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;"
          "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
          "Ljava/lang/invoke/CallSite;"));
  auto* target = DexMethodHandle::make_method_handle(
      METHOD_HANDLE_TYPE_INVOKE_STATIC,
      DexMethod::make_method("LFoo;.run:()V"));
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.emplace_back(new DexEncodedValueMethodHandle(target));
  args.emplace_back(new DexEncodedValueMethodType(DexProto::make_proto("()V")));
  DexCallSite call_site(bootstrap, DexString::make_string("run"),
                        DexProto::make_proto("()Ljava/lang/Runnable;"),
                        std::move(args));

  EXPECT_EQ(show(target),
            "METHODHANDLE: TYPE=4 FIELD_OR_METHOD_ID=LFoo;.run:()V");

  EXPECT_EQ(show(&call_site),
            "CALLSITE: METHODHANDLE=" + show(bootstrap) +
                " METHODNAME=run METHODTYPE=()Ljava/lang/Runnable; ARGS=[" +
                show(target) + ", ()V]");

  // A handle to a field prints the field.
  auto* field_handle = DexMethodHandle::make_method_handle(
      METHOD_HANDLE_TYPE_STATIC_GET, DexField::make_field("LFoo;.bar:I"));
  DexOpcodeMethodHandle const_handle(DOPCODE_CONST_METHOD_HANDLE, field_handle);
  EXPECT_EQ(show(&const_handle), "const-method-handle LFoo;.bar:I v0");
}
