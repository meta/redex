/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexFileTestHelper.h"
#include "DexInstruction.h"
#include "DexLoader.h"
#include "IRAssembler.h"
#include "RedexContext.h"
#include "RedexTestUtils.h"
#include "RegAllocLoweringTestHelper.h"
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

namespace {

// What `classes` hold outside code: static field values and annotations.
std::vector<std::string> show_values_and_annotations(
    const DexClasses& classes) {
  std::vector<std::string> result;
  for (const auto* cls : classes) {
    if (cls->get_anno_set() != nullptr) {
      result.push_back(show(cls) + ": " + show(cls->get_anno_set()));
    }
    for (const auto* field : cls->get_sfields()) {
      result.push_back(show(field) + " = " + show(field->get_static_value()));
    }
    for (const auto* method : cls->get_all_methods()) {
      if (method->get_anno_set() != nullptr) {
        result.push_back(show(method) + ": " + show(method->get_anno_set()));
      }
    }
  }
  return result;
}

std::unique_ptr<DexAnnotationSet> make_annotation_set(
    const char* name, std::unique_ptr<DexEncodedValue> value) {
  auto anno = std::make_unique<DexAnnotation>(DexType::make_type("LAnno;"),
                                              DAV_RUNTIME);
  anno->add_element(name, std::move(value));
  auto set = std::make_unique<DexAnnotationSet>();
  set->add_annotation(std::move(anno));
  return set;
}

} // namespace

// A tool-generated dex file can hold method handles and method types outside
// code, as static field values and in annotations, here none of which code
// uses. They read back unchanged after they are written.
TEST(Dex039Test, ReadWriteMethodHandlesAndTypesOutsideCode) {
  g_redex = new RedexContext();
  ClassCreator creator(DexType::make_type("LConstants;"));
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  creator.add_field(
      DexField::make_field("LConstants;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "LTarget;.run:(LArg;)V"))));
  creator.add_field(
      DexField::make_field("LConstants;.TYPE:Ljava/lang/invoke/MethodType;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::make_unique<DexEncodedValueMethodType>(
                              DexProto::make_proto("(CSJ)Z"))));
  auto* method = DexMethod::make_method("LConstants;.annotated:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT | ACC_SYNTHETIC,
                                     /* is_virtual */ true);
  auto* types = new DexEncodedValueArray::Storage();
  types->push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto("(JJ)V")));
  ASSERT_TRUE(method->attach_annotation_set(make_annotation_set(
      "types", std::make_unique<DexEncodedValueArray>(types))));
  creator.add_method(method);
  auto* cls = creator.create();
  ASSERT_TRUE(cls->attach_annotation_set(make_annotation_set(
      "handle",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INSTANCE_GET, "LTarget;.f:LField;")))));
  DexClasses classes{cls};
  const auto before = show_values_and_annotations(classes);

  auto tmpdir = redex::make_tmp_dir("dex039_test_%%%%%%%%");
  auto output = write_dex_file(std::move(classes), tmpdir.path, 39);

  delete g_redex;
  g_redex = new RedexContext();
  EXPECT_EQ(show_values_and_annotations(load_dex_file(output, 39)), before);
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

// IRTypeChecker accepts every method, including the method constants and
// method handle calls, before and after register allocation, and the allocated
// code lowers to encodable instructions.
TEST(Dex039Test, TypeCheckAllocateAndLowerEveryMethod) {
  g_redex = new RedexContext();
  const char* dexfile = std::getenv("dex");
  ASSERT_NE(nullptr, dexfile);
  expect_type_correct_through_register_allocation_and_lowering(
      load_dex_file(dexfile, 39));
  delete g_redex;
  g_redex = nullptr;
}
