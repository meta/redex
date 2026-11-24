/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <string>

#include <boost/filesystem.hpp>

#include "DexCallSite.h"
#include "DexClass.h"
#include "DexFileTestHelper.h"
#include "DexIdx.h"
#include "DexLoader.h"
#include "DexMethodHandle.h"
#include "IRCode.h"
#include "RedexContext.h"
#include "RedexTestUtils.h"
#include "RegAllocLoweringTestHelper.h"
// NOLINTNEXTLINE(facebook-unused-include-check)
#include "SanitizersConfig.h"
#include "Show.h"

using CallSitePredicate = const std::function<bool(DexCallSite*)>&;
int ensureCallSite(DexIdx* idx, CallSitePredicate predicate) {
  for (int i = 0; i < idx->get_callsite_ids_size(); ++i) {
    auto* cs = idx->get_callsiteidx(i);
    if (predicate(cs)) {
      return i;
    }
  }
  return -1;
}

using MethodHandlePredicate = const std::function<bool(DexMethodHandle*)>&;
int ensureMethodHandle(DexIdx* idx, MethodHandlePredicate predicate) {
  for (int i = 0; i < idx->get_methodhandle_ids_size(); ++i) {
    auto* mh = idx->get_methodhandleidx(i);
    if (predicate(mh)) {
      return i;
    }
  }
  return -1;
}

static const char* DEX038_CLASS_NAME = "Lcom/facebook/redextest/Dex038;";
static const char* SUPPLIER_CLASS_NAME = "Ljava/util/function/Supplier;";
static const char* STRING_CLASS_NAME = "Ljava/lang/String;";
static const char* VOID_RETURN_OBJECT_PROTO = "()Ljava/lang/Object;";
static const char* VOID_RETURN_STRING_PROTO = "()Ljava/lang/String;";

void testReadDex(const char* dexfile) {
  auto dl = DexLoader::create(DexLocation::make_location("", dexfile), 38,
                              DexLoader::Parallel::kYes);
  auto* idx = dl.get_idx();

  EXPECT_EQ(idx->get_callsite_ids_size(), 7);
  EXPECT_EQ(idx->get_methodhandle_ids_size(), 8);

  // clang-format off

  // !!! N.B. !!! right now these tests assume a reliable ordering of
  // callsite/methodhandles by the dexer. it's definitely fragile.

  // verify lambda metafactory method handle shared by every callsite

  //   type        : invoke-static
  //   target      : Ljava/lang/invoke/LambdaMetafactory; metafactory
  //   target_type : (Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;
  int metafactoryMethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_STATIC &&
      (strcmp(mh->methodref()->get_name()->c_str(), "metafactory") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), "Ljava/lang/invoke/LambdaMetafactory;") == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;") == 0);
  });
  EXPECT_NE(metafactoryMethodHandleIdx, -1);
  DexMethodHandle* metafactoryMethodHandle = idx->get_methodhandleidx(metafactoryMethodHandleIdx);

  // verify all other method handles

  //   type        : invoke-static
  //   target      : Lcom/facebook/redextest/Dex038; lambda$run$0
  //   target_type : ()Ljava/lang/String;
  int lambdaRun0MethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_STATIC &&
      (strcmp(mh->methodref()->get_name()->c_str(), "lambda$run$0") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(lambdaRun0MethodHandleIdx, -1);
  DexMethodHandle* lambdaRun0MethodHandle = idx->get_methodhandleidx(lambdaRun0MethodHandleIdx);

  //   type        : invoke-static
  //   target      : Lcom/facebook/redextest/Dex038; lambda$run$1
  //   target_type : ()Ljava/lang/String;
  int lambdaRun1MethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_STATIC &&
      (strcmp(mh->methodref()->get_name()->c_str(), "lambda$run$1") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(lambdaRun1MethodHandleIdx, -1);
  DexMethodHandle* lambdaRun1MethodHandle = idx->get_methodhandleidx(lambdaRun1MethodHandleIdx);

  //   type        : invoke-static
  //   target      : Lcom/facebook/redextest/Dex038; lambda$run$2
  //   target_type : ()Ljava/lang/String;
  int lambdaRun2MethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_STATIC &&
      (strcmp(mh->methodref()->get_name()->c_str(), "lambda$run$2") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(lambdaRun2MethodHandleIdx, -1);
  DexMethodHandle* lambdaRun2MethodHandle = idx->get_methodhandleidx(lambdaRun2MethodHandleIdx);

  //   type        : invoke-static
  //   target      : Lcom/facebook/redextest/Dex038; staticStringSupplier
  //   target_type : ()Ljava/lang/String;
  int staticStringSupplierMethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_STATIC &&
      (strcmp(mh->methodref()->get_name()->c_str(), "staticStringSupplier") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(staticStringSupplierMethodHandleIdx, -1);
  DexMethodHandle* staticStringSupplierMethodHandle = idx->get_methodhandleidx(staticStringSupplierMethodHandleIdx);

  //   type        : invoke-instance
  //   target      : Lcom/facebook/redextest/Dex038; instanceStringSupplier
  //   target_type : (Lcom/facebook/redextest/Dex038;)Ljava/lang/String;
  int instanceStringSupplierMethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_INSTANCE &&
      (strcmp(mh->methodref()->get_name()->c_str(), "instanceStringSupplier") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(instanceStringSupplierMethodHandleIdx, -1);
  DexMethodHandle* instanceStringSupplierMethodHandle = idx->get_methodhandleidx(instanceStringSupplierMethodHandleIdx);

  //   type        : invoke-constructor
  //   target      : Ljava/lang/String; <init>
  //   target_type : (Ljava/lang/String;)V
  int constructorMethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR &&
      (strcmp(mh->methodref()->get_name()->c_str(), "<init>") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), STRING_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), "()V") == 0);
  });
  EXPECT_NE(constructorMethodHandleIdx, -1);
  DexMethodHandle* constructorMethodHandle = idx->get_methodhandleidx(constructorMethodHandleIdx);

  //   type        : invoke-direct
  //   target      : Lcom/facebook/redextest/Dex038; privateInstanceStringSupplier
  //   target_type : (Lcom/facebook/redextest/Dex038;)Ljava/lang/String;
  int directMethodHandleIdx = ensureMethodHandle(idx, [](DexMethodHandle* mh) {
    return
      mh->type() == METHOD_HANDLE_TYPE_INVOKE_DIRECT &&
      (strcmp(mh->methodref()->get_name()->c_str(), "privateInstanceStringSupplier") == 0) &&
      (strcmp(mh->methodref()->get_class()->get_name()->c_str(), DEX038_CLASS_NAME) == 0) &&
      (strcmp(SHOW(mh->methodref()->get_proto()), VOID_RETURN_STRING_PROTO) == 0);
  });
  EXPECT_NE(directMethodHandleIdx, -1);
  DexMethodHandle* directMethodHandle = idx->get_methodhandleidx(directMethodHandleIdx);

  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : (Lcom/facebook/redextest/Dex038;)Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), DEX038_CLASS_NAME) &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == instanceStringSupplierMethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #1 // offset 2179
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : (Lcom/facebook/redextest/Dex038;)Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), DEX038_CLASS_NAME) &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == directMethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #2 // offset 2192
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : ()Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), "") &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == constructorMethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #3 // offset 2205
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : ()Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), "") &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == staticStringSupplierMethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #4 // offset 2218
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : ()Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), "") &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == lambdaRun0MethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #5 // offset 2231
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : ()Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), "") &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == lambdaRun1MethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // Call Site #6 // offset 2244
  //   link_argument[0] : N (MethodHandle)
  //   link_argument[1] : get (String)
  //   link_argument[2] : ()Ljava/util/function/Supplier; (MethodType)
  //   link_argument[3] : ()Ljava/lang/Object; (MethodType)
  //   link_argument[4] : N (MethodHandle)
  //   link_argument[5] : ()Ljava/lang/String; (MethodType)
  EXPECT_NE(ensureCallSite(idx, [&](DexCallSite* cs) {
    return
      cs->method_handle() == metafactoryMethodHandle &&
      !strcmp(cs->method_name()->c_str(), "get") &&
      !strcmp(cs->method_type()->get_rtype()->get_name()->c_str(), SUPPLIER_CLASS_NAME) &&
      !strcmp(SHOW(cs->method_type()->get_args()), "") &&
      cs->args().size() == 3 &&
      !strcmp(SHOW(cs->args()[0]), VOID_RETURN_OBJECT_PROTO) &&
      ((DexEncodedValueMethodHandle*)cs->args()[1].get())->methodhandle() == lambdaRun2MethodHandle &&
      !strcmp(SHOW(cs->args()[2]), VOID_RETURN_STRING_PROTO);
  }), -1);

  // clang-format on
}

TEST(Dex038Test, ReadDex038) {
  g_redex = new RedexContext();

  const char* dexfile = std::getenv("dexfile");
  EXPECT_NE(nullptr, dexfile);

  testReadDex(dexfile);
}

TEST(Dex038Test, ReadWriteDex038) {
  g_redex = new RedexContext();

  const char* dexfile = std::getenv("dexfile");
  EXPECT_NE(nullptr, dexfile);

  auto classes = load_dex_file(dexfile, 38);
  const auto instructions_before = redex::show_instructions_by_method(classes);

  auto tmpdir = redex::make_tmp_dir("dex038_test_%%%%%%%%");
  auto output_dex = write_dex_file(std::move(classes), tmpdir.path, 38);

  delete g_redex;
  g_redex = new RedexContext();

  // Every method reads back with the code it was written with.
  EXPECT_EQ(redex::show_instructions_by_method(load_dex_file(output_dex, 38)),
            instructions_before);

  delete g_redex;
  g_redex = new RedexContext();

  testReadDex(output_dex.c_str());

  delete g_redex;
}

// `invoke-polymorphic` keeps the prototype of its call site, here `(J)J`,
// and the instruction after it is read from the right offset.
TEST(Dex038Test, InvokePolymorphicKeepsCallSiteProto) {
  g_redex = new RedexContext();

  const char* dexfile = std::getenv("dexfile");
  ASSERT_NE(nullptr, dexfile);
  load_dex_file(dexfile, 38);
  auto* method = DexMethod::get_method(
      "Lcom/facebook/redextest/Dex038;.addOneThroughMethodHandle:(J)J");
  ASSERT_NE(nullptr, method);
  auto* code = method->as_def()->get_code();
  auto ii = InstructionIterable(code);
  auto it = std::find_if(ii.begin(), ii.end(), [](const auto& mie) {
    return mie.insn->opcode() == OPCODE_INVOKE_POLYMORPHIC;
  });
  ASSERT_NE(it, ii.end());
  EXPECT_EQ(show(it->insn->get_signature_polymorphic()->method()),
            "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/"
            "Object;)Ljava/lang/Object;");
  EXPECT_EQ(show(it->insn->get_callsite_proto()), "(J)J");
  // The handle and `x`, whose register pair is one source in IR.
  EXPECT_EQ(it->insn->srcs_size(), 2u);
  EXPECT_TRUE(it->insn->src_is_wide(1));
  ++it;
  ASSERT_NE(it, ii.end());
  EXPECT_EQ(it->insn->opcode(), OPCODE_MOVE_RESULT_WIDE);

  delete g_redex;
}

// With more than five registers the call is an `invoke-polymorphic/range`,
// and its call-site prototype, `(IIIII)J`, is the prototype of no method.
TEST(Dex038Test, InvokePolymorphicRangeKeepsCallSiteProto) {
  g_redex = new RedexContext();

  const char* dexfile = std::getenv("dexfile");
  ASSERT_NE(nullptr, dexfile);
  load_dex_file(dexfile, 38);
  auto* method = DexMethod::get_method(
      "Lcom/facebook/redextest/Dex038;.sumThroughMethodHandle:"
      "(Ljava/lang/invoke/MethodHandle;IIIII)J");
  ASSERT_NE(nullptr, method);
  auto ii = InstructionIterable(method->as_def()->get_code());
  auto it = std::find_if(ii.begin(), ii.end(), [](const auto& mie) {
    return mie.insn->opcode() == OPCODE_INVOKE_POLYMORPHIC;
  });
  ASSERT_NE(it, ii.end());
  EXPECT_EQ(it->insn->srcs_size(), 6u);
  EXPECT_EQ(show(it->insn->get_callsite_proto()), "(IIIII)J");
  ++it;
  ASSERT_NE(it, ii.end());
  EXPECT_EQ(it->insn->opcode(), OPCODE_MOVE_RESULT_WIDE);

  delete g_redex;
}

// IRTypeChecker accepts every method, including the method handle calls and
// lambdas, before and after register allocation, and the allocated code lowers
// to encodable instructions.
TEST(Dex038Test, TypeCheckAllocateAndLowerEveryMethod) {
  g_redex = new RedexContext();
  const char* dexfile = std::getenv("dexfile");
  ASSERT_NE(nullptr, dexfile);
  expect_type_correct_through_register_allocation_and_lowering(
      load_dex_file(dexfile, 38));
  delete g_redex;
  g_redex = nullptr;
}
