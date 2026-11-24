/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <algorithm>

#include "Creators.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexFileTestHelper.h"
#include "DexInstruction.h"
#include "DexLoader.h"
#include "IRAssembler.h"
#include "RedexContext.h"
#include "RedexTestUtils.h"
#include "Show.h"
#include "TypeUtil.h"

TEST(Dex039Test, ReadDex039) {
  // const-method-handle.dex is sourced from https://fburl.com/prikp912
  // ground truth dexdump is found at https://fburl.com/27ekisha

  const char* dexfile = std::getenv("dex");
  EXPECT_NE(nullptr, dexfile);

  g_redex = new RedexContext();

  // bare minium test to ensure the dex loads okay
  auto dl = DexLoader::create(DexLocation::make_location("", dexfile), 39,
                              DexLoader::Parallel::kYes);
  const auto& classes = dl.get_classes();
  auto* idx = dl.get_idx();

  // ensure that instructions can be shown
  std::ostringstream o;
  for (const auto& dex_class : classes) {
    o << show(dex_class);
    for (const auto& dex_method : dex_class->get_dmethods()) {
      o << show(dex_method);
      DexCode* code = dex_method->get_dex_code();
      for (const auto& dex_ins : code->get_instructions()) {
        o << show(dex_ins);
      }
    }
    for (const auto& dex_method : dex_class->get_vmethods()) {
      o << show(dex_method);
      DexCode* code = dex_method->get_dex_code();
      for (const auto& dex_ins : code->get_instructions()) {
        o << show(dex_ins);
      }
    }
  }
  auto parsed_code = o.str();

  EXPECT_NE(
      parsed_code.find("invoke-polymorphic "
                       "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
                       "lang/Object;)Ljava/lang/Object;, ([Ljava/lang/"
                       "String;)V v0, v5"),
      std::string::npos);
  EXPECT_NE(parsed_code.find("invoke-polymorphic "
                             "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/"
                             "lang/Object;)Ljava/lang/Object;, (Ljava/lang/"
                             "Object;)Ljava/lang/Class; v3, v2"),
            std::string::npos);
  EXPECT_NE(
      parsed_code.find("const-method-handle "
                       "Ljava/lang/Object;.getClass:()Ljava/lang/Class; v0"),
      std::string::npos);
  EXPECT_NE(
      parsed_code.find("const-method-type (CSIJFDLjava/lang/Object;)Z v0"),
      std::string::npos);
  EXPECT_EQ(idx->get_callsite_ids_size(), 0);
  EXPECT_EQ(idx->get_methodhandle_ids_size(), 1);
  EXPECT_EQ(idx->get_method_ids_size(), 23);
  EXPECT_EQ(idx->get_proto_ids_size(), 18);
  EXPECT_EQ(classes.size(), 2);
}

// `const-method-handle` and `const-method-type` are two code units long, and
// the prototype that `const-method-type` loads need not be the prototype of
// any method. Code that uses both reads back unchanged after it is written.
TEST(Dex039Test, ReadWriteConstMethodHandleAndType) {
  g_redex = new RedexContext();
  // `(CSJ)Z` is the prototype of no method here.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LConstants;.load:()V"
     (
      (const-method-type "(CSJ)Z")
      (move-result-pseudo-object v0)
      (const-method-handle invoke-instance "Ljava/lang/Object;.hashCode:()I")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");
  ClassCreator creator(DexType::make_type("LConstants;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(method);
  DexClasses classes{creator.create()};
  const auto before = redex::show_instructions_by_method(classes);

  auto tmpdir = redex::make_tmp_dir("dex039_test_%%%%%%%%");
  auto output = write_dex_file(std::move(classes), tmpdir.path, 39);

  delete g_redex;
  g_redex = new RedexContext();
  EXPECT_EQ(redex::show_instructions_by_method(load_dex_file(output, 39)),
            before);
  delete g_redex;
  g_redex = nullptr;
}

// `invoke-polymorphic` is four code units long: the method, the argument
// registers, and the prototype of the call site. All of it is read, and the
// next instruction starts after it.
TEST(Dex039Test, InvokePolymorphicKeepsCallSiteProto) {
  g_redex = new RedexContext();
  const char* dexfile = std::getenv("dex");
  ASSERT_NE(nullptr, dexfile);
  auto code = redex::show_instructions_by_method(load_dex_file(dexfile, 39));

  const auto& main = code.at("LMain;.main:([Ljava/lang/String;)V");
  auto it = std::find(main.begin(), main.end(),
                      "INVOKE_POLYMORPHIC v0, v5, "
                      "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
                      "lang/Object;)Ljava/lang/Object;, ([Ljava/lang/"
                      "String;)V");
  ASSERT_NE(it, main.end());
  ASSERT_NE(std::next(it), main.end());
  EXPECT_EQ(std::next(it)->rfind("RETURN_VOID", 0), 0u);

  const auto& display = code.at(
      "Lconstmethodhandle/ConstTest;.displayMethodHandle:(Ljava/lang/"
      "invoke/MethodHandle;)V");
  it = std::find(display.begin(), display.end(),
                 "INVOKE_POLYMORPHIC v3, v2, "
                 "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/"
                 "Object;)Ljava/lang/Object;, "
                 "(Ljava/lang/Object;)Ljava/lang/Class;");
  ASSERT_NE(it, display.end());
  ASSERT_NE(std::next(it), display.end());
  EXPECT_EQ(*std::next(it), "MOVE_RESULT_OBJECT v2");
  delete g_redex;
  g_redex = nullptr;
}

// Every method of the file reads back with the same code after it is written.
TEST(Dex039Test, ReadWriteDex039) {
  g_redex = new RedexContext();
  const char* dexfile = std::getenv("dex");
  ASSERT_NE(nullptr, dexfile);
  auto classes = load_dex_file(dexfile, 39);
  const auto before = redex::show_instructions_by_method(classes);

  auto tmpdir = redex::make_tmp_dir("dex039_test_%%%%%%%%");
  auto output = write_dex_file(std::move(classes), tmpdir.path, 39);

  delete g_redex;
  g_redex = new RedexContext();
  EXPECT_EQ(redex::show_instructions_by_method(load_dex_file(output, 39)),
            before);
  delete g_redex;
  g_redex = nullptr;
}
