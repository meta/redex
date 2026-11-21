/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "DexAnnotation.h"
#include "DexHasher.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

struct DexHasherTest : public RedexTest {};

TEST_F(DexHasherTest, DifferentRegistersMakeDifferentHash) {
  // Two methods differing only in register ID should have different hashes.
  auto* method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar1:()V"
      (
        (const v0 42)
        (return-void)
      )
    )
  )");

  auto* method2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar2:()V"
      (
        (const v1 42)
        (return-void)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  auto hash1 = hashing::DexMethodHasher(method1).run();
  auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_NE(hash1.registers_hash, hash2.registers_hash);
}

TEST_F(DexHasherTest, MethodHashIgnoresClassAndMethodName) {
  // The hash should be the same even if the class and method names differ,
  // as long as the code is identical.
  auto* method1 = assembler::method_from_string(R"(
    (method (public static) "LClass1;.method1:()I"
      (
        (const v0 100)
        (return v0)
      )
    )
  )");

  auto* method2 = assembler::method_from_string(R"(
    (method (public static) "LClass2;.method2:()I"
      (
        (const v0 100)
        (return v0)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  auto hash1 = hashing::DexMethodHasher(method1).run();
  auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_EQ(hash1.code_hash, hash2.code_hash);
}

TEST_F(DexHasherTest, MethodHashDiffersForDifferentOpcodes) {
  // Methods with different opcodes should have different hashes.
  auto* method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.add:(II)I"
      (
        (load-param v0)
        (load-param v1)
        (add-int v2 v0 v1)
        (return v2)
      )
    )
  )");

  auto* method2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.sub:(II)I"
      (
        (load-param v0)
        (load-param v1)
        (sub-int v2 v0 v1)
        (return v2)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  auto hash1 = hashing::DexMethodHasher(method1).run();
  auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_NE(hash1.code_hash, hash2.code_hash);
}

TEST_F(DexHasherTest, MethodHashDiffersForDifferentPrototypes) {
  // Methods with identical code but different prototypes should have different
  // code_hash values.
  auto* method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.noArg:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  auto* method2 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.oneArg:(I)I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  auto hash1 = hashing::DexMethodHasher(method1).run();
  auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_NE(hash1.code_hash, hash2.code_hash)
      << "Different prototypes should produce different code_hash";
}

TEST_F(DexHasherTest, MethodHashIgnoresAccessFlags) {
  // Methods with identical code and prototype but different access flags should
  // have the same code_hash.
  auto* method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.publicMethod:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  auto* method2 = assembler::method_from_string(R"(
    (method (private static) "LFoo;.privateMethod:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  auto hash1 = hashing::DexMethodHasher(method1).run();
  auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_EQ(hash1.code_hash, hash2.code_hash)
      << "Access flags should not affect code_hash";
}

TEST_F(DexHasherTest, MethodHashIgnoresDebugInfo) {
  // Methods with identical instructions but different debug info should have
  // the same code_hash.
  auto* const method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.withDebug:()I"
      (
        (.pos "LFoo;.withDebug:()I" "Foo.java" 10)
        (const v0 42)
        (.pos "LFoo;.withDebug:()I" "Foo.java" 11)
        (return v0)
      )
    )
  )");

  auto* const method2 = assembler::method_from_string(R"(
    (method (public static) "LBar;.noDebug:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  const auto hash1 = hashing::DexMethodHasher(method1).run();
  const auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_EQ(hash1.code_hash, hash2.code_hash)
      << "Debug info should not affect code_hash";
}

TEST_F(DexHasherTest, MethodHashIgnoresSourceBlocks) {
  // Methods with identical instructions but different source blocks should have
  // the same code_hash.
  auto* const method1 = assembler::method_from_string(R"(
    (method (public static) "LFoo;.withSourceBlock:()I"
      (
        (.src_block "LFoo;.withSourceBlock:()I" 0)
        (const v0 42)
        (.src_block "LFoo;.withSourceBlock:()I" 1)
        (return v0)
      )
    )
  )");

  auto* const method2 = assembler::method_from_string(R"(
    (method (public static) "LBar;.noSourceBlock:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )");

  method1->get_code()->build_cfg();
  method2->get_code()->build_cfg();

  const auto hash1 = hashing::DexMethodHasher(method1).run();
  const auto hash2 = hashing::DexMethodHasher(method2).run();

  EXPECT_EQ(hash1.code_hash, hash2.code_hash)
      << "Source blocks should not affect code_hash";
}

namespace {

// The code hash of a static method with `body`. When `method_type` is set,
// every `invoke-static` in `body` becomes an `invoke-custom` of a call site
// with that method type and `args` as its bootstrap arguments.
size_t code_hash_of(const std::string& body,
                    std::string_view method_type = "",
                    std::vector<std::unique_ptr<DexEncodedValue>> args = {}) {
  // The hash ignores the method's name, which only keeps the methods apart.
  static int count = 0;
  auto* method = assembler::method_from_string(
      R"((method (public static) "LFoo;.bar)" + std::to_string(count++) +
      R"(:()V" ()" + body + "))");
  if (!method_type.empty()) {
    redex::make_invoke_custom(method->get_code(), "run", method_type,
                              std::move(args));
  }
  method->get_code()->build_cfg();
  return hashing::DexMethodHasher(method).run().code_hash;
}

std::vector<std::unique_ptr<DexEncodedValue>> method_type_and_handle_args(
    std::string_view method_type, std::string_view method) {
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(std::make_unique<DexEncodedValueMethodType>(
      DexProto::make_proto(method_type)));
  args.push_back(std::make_unique<DexEncodedValueMethodHandle>(
      redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC, method)));
  return args;
}

} // namespace

// The hash covers what `const-method-type`, `const-method-handle` and
// `invoke-custom` refer to, not only that they refer to something.
TEST_F(DexHasherTest,
       MethodHashDiffersForDifferentMethodTypesHandlesAndCallSites) {
  EXPECT_NE(code_hash_of(R"(
    (const-method-type "(I)V")
    (move-result-pseudo-object v0)
    (return-void)
  )"),
            code_hash_of(R"(
    (const-method-type "(J)V")
    (move-result-pseudo-object v0)
    (return-void)
  )"));

  EXPECT_NE(code_hash_of(R"(
    (const-method-handle invoke-static "LFoo;.a:()V")
    (move-result-pseudo-object v0)
    (return-void)
  )"),
            code_hash_of(R"(
    (const-method-handle invoke-static "LFoo;.b:()V")
    (move-result-pseudo-object v0)
    (return-void)
  )"));

  const std::string call = R"(
    (invoke-static () "LFoo;.placeholder:()V")
    (return-void)
  )";
  EXPECT_NE(code_hash_of(call, "()V"),
            code_hash_of(call, "()V",
                         method_type_and_handle_args("(I)V", "LFoo;.a:(I)V")));
  EXPECT_NE(code_hash_of(call, "()V",
                         method_type_and_handle_args("(I)V", "LFoo;.a:(I)V")),
            code_hash_of(call, "()V",
                         method_type_and_handle_args("(J)V", "LFoo;.a:(J)V")));
}

// Method types and method handles among the bootstrap arguments of a call site
// are hashed by what they refer to, not by where they are in memory, so the
// hash is the same in every Redex run.
TEST_F(DexHasherTest, MethodHashOfCallSiteIsTheSameInEveryContext) {
  const std::string call = R"(
    (invoke-static () "LFoo;.placeholder:()V")
    (return-void)
  )";
  auto hash_in_this_context = [&]() {
    return code_hash_of(call, "()V",
                        method_type_and_handle_args("(I)V", "LFoo;.a:(I)V"));
  };
  auto first = hash_in_this_context();
  // While the first context lives, the second one allocates its method types
  // and method handles elsewhere.
  auto* first_context = g_redex;
  g_redex = new RedexContext();
  auto second = hash_in_this_context();
  delete g_redex;
  g_redex = first_context;
  EXPECT_EQ(first, second);
}
