/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DexClass.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "TypeStringRewriter.h"

class TypeStringRewriterTest : public RedexTest {};

TEST_F(TypeStringRewriterTest, maps_class_and_its_arrays) {
  rewriter::TypeStringMap mapping;
  mapping.add_type_name(DexString::make_string("Lcom/foo/Bar;"),
                        DexString::make_string("LX/a;"));

  EXPECT_EQ(mapping.get_new_type_name(DexString::make_string("Lcom/foo/Bar;")),
            DexString::make_string("LX/a;"));
  EXPECT_EQ(mapping.get_new_type_name(DexString::make_string("[Lcom/foo/Bar;")),
            DexString::make_string("[LX/a;"));
  EXPECT_EQ(
      mapping.get_new_type_name(DexString::make_string("[[Lcom/foo/Bar;")),
      DexString::make_string("[[LX/a;"));

  EXPECT_EQ(
      mapping.get_new_type_name(DexString::make_string("[Lcom/foo/Other;")),
      nullptr);
  EXPECT_EQ(mapping.get_new_type_name(DexString::make_string("[I")), nullptr);
}

TEST_F(TypeStringRewriterTest, array_mapping_also_maps_component) {
  rewriter::TypeStringMap mapping;
  mapping.add_type_name(DexString::make_string("[Lcom/foo/Baz;"),
                        DexString::make_string("[LX/b;"));

  EXPECT_EQ(mapping.get_new_type_name(DexString::make_string("[Lcom/foo/Baz;")),
            DexString::make_string("[LX/b;"));
  EXPECT_EQ(mapping.get_new_type_name(DexString::make_string("Lcom/foo/Baz;")),
            DexString::make_string("LX/b;"));
}

// Class.forName("[Lcom.foo.Bar;") names Bar[]; it must follow Bar's new name
// just like Class.forName("com.foo.Bar") does.
TEST_F(TypeStringRewriterTest, rewrites_array_class_name_literal) {
  DexType::make_type("Lcom/foo/Bar;");
  DexType::make_type("[Lcom/foo/Bar;");

  auto* method = assembler::class_with_method("LUser;",
                                              R"(
    (method (public static) "LUser;.load:()V"
      (
        (const-string "com.foo.Bar")
        (move-result-pseudo-object v0)
        (const-string "[Lcom.foo.Bar;")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  Scope scope{type_class(method->get_class())};

  rewriter::TypeStringMap mapping;
  mapping.add_type_name(DexString::make_string("Lcom/foo/Bar;"),
                        DexString::make_string("LX/a;"));
  EXPECT_EQ(rewriter::rewrite_string_literal_instructions(scope, mapping), 2u);

  code->clear_cfg();
  auto expected = assembler::ircode_from_string(R"(
    (
      (const-string "X.a")
      (move-result-pseudo-object v0)
      (const-string "[LX.a;")
      (move-result-pseudo-object v1)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code, expected.get());
}
