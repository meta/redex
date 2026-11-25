/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PackagePrivatePreprocessor.h"

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "JarLoader.h"
#include "PassManager.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"

struct PackagePrivateProcessorTest : public RedexIntegrationTest {};

TEST_F(PackagePrivateProcessorTest, verify) {
  std::unordered_map<DexMethod*, const DexString*> vmethods;
  std::set<DexMethod*, dexmethods_comparator> ordered_vmethods;
  walk::methods(build_class_scope(stores), [&](DexMethod* method) {
    if (!method->is_virtual()) {
      return;
    }
    vmethods.emplace(method, method->get_name());
    ordered_vmethods.insert(method);
  });

  std::string sdk_jar = android_sdk_jar_path();
  ASSERT_TRUE(load_jar_file(DexLocation::make_location("", sdk_jar)));

  auto pass = std::make_unique<PackagePrivatePreprocessorPass>();
  std::vector<Pass*> passes = {pass.get()};

  run_passes(passes);

  std::string actual = "\n";
  for (auto* method : ordered_vmethods) {
    actual += show(method) + " <= " + show(vmethods.at(method)) + "\n";
  }

  std::string expected = R"(
LP/C;.interface_collision_not_okay:()V <= interface_collision_not_okay
LP/C;.package_private_collision1_okay:()V <= package_private_collision1_okay
LP/C;.package_private_collision2_okay:()V <= package_private_collision2_okay
LP/C;.package_private_collision3_not_okay:()V <= package_private_collision3_not_okay
LP/C;.package_private_collision3_okay:()V <= package_private_collision3_okay
LP/C;.simple_public_okay:()V <= simple_public_okay
LP/E;.package_private_collision3_not_okay:()V <= package_private_collision3_not_okay
LP/E;.package_private_collision3_okay:()V <= package_private_collision3_okay
LP/E;.simple_public_okay:()V <= simple_public_okay
LQ/D;.package_private_collision1_okay$REDEX$PPP$gBwUyFaWvqi:()V <= package_private_collision1_okay
LQ/D;.package_private_collision2_okay$REDEX$PPP$gBwUyFaWvqi:()V <= package_private_collision2_okay
LQ/D;.package_private_collision3_not_okay:()V <= package_private_collision3_not_okay
LQ/D;.package_private_collision3_okay$REDEX$PPP$gBwUyFaWvqi:()V <= package_private_collision3_okay
LQ/F;.interface_collision_not_okay:()V <= interface_collision_not_okay
LQ/F;.package_private_collision3_not_okay:()V <= package_private_collision3_not_okay
LQ/F;.package_private_collision3_okay$REDEX$PPP$gBwUyFaWvqi:()V <= package_private_collision3_okay
LQ/F;.simple_public_okay:()V <= simple_public_okay
LR/G;.package_private_collision3_okay$REDEX$PPP$c5q1BfR0O0k:()V <= package_private_collision3_okay
LR/G;.simple_public_okay:()V <= simple_public_okay
LR/I;.interface_collision_not_okay:()V <= interface_collision_not_okay
)";

  EXPECT_EQ(actual, expected);

  const auto& stats = pass->get_stats();

  EXPECT_EQ(stats.unresolved_types, 0);
  EXPECT_EQ(stats.external_inaccessible_types, 0);
  EXPECT_EQ(stats.internal_inaccessible_types, 0);

  EXPECT_EQ(stats.unresolved_fields, 0);
  EXPECT_EQ(stats.external_inaccessible_private_fields, 0);
  EXPECT_EQ(stats.external_inaccessible_fields, 0);
  EXPECT_EQ(stats.internal_inaccessible_fields, 0);

  EXPECT_EQ(stats.unresolved_methods, 0);
  EXPECT_EQ(stats.external_inaccessible_private_methods, 0);
  EXPECT_EQ(stats.external_inaccessible_methods, 0);
  EXPECT_EQ(stats.internal_inaccessible_methods, 0);

  EXPECT_EQ(stats.apparent_override_inaccessible_methods, 3);
  EXPECT_EQ(stats.override_package_private_methods, 3);

  EXPECT_EQ(stats.package_private_accessed_classes, 0);
  EXPECT_EQ(stats.package_private_accessed_methods, 0);
  EXPECT_EQ(stats.package_private_accessed_fields, 0);
  EXPECT_EQ(stats.new_virtual_scope_roots, 5);

  EXPECT_EQ(stats.renamed_methods, 5);
  EXPECT_EQ(stats.updated_method_refs, 0);
  EXPECT_EQ(stats.publicized_classes, 0);
  EXPECT_EQ(stats.publicized_methods, 6);
  EXPECT_EQ(stats.publicized_fields, 0);
  EXPECT_EQ(stats.unsupported_unrenamable_methods, 0);
  EXPECT_EQ(stats.unsupported_interface_implementations, 1);
  EXPECT_EQ(stats.unsupported_multiple_package_private_overrides, 1);
  EXPECT_EQ(stats.unsupported_non_public_interface_implementations, 0);
}

// javac rejects the shapes where `p.B` lists `I`, directly or through `p.A`, as
// `B.m` would weaken the access of `I.m`. It compiles the shape where `q.C`
// lists `I`, as `q.C` does not inherit the package-private `B.m`.
struct PackagePrivateProcessorGeneratedBytecodeTest : public RedexTest {
  // Creates `package p; public interface I { default void m() {} }`, a class
  // `p.A`, its subclass `p.B` with a package-private `m`, and `q.C`, a
  // subclass of `p.B`; `interfaces_of_a`, `interfaces_of_b` and
  // `interfaces_of_c` say which of them lists `I`.
  void create_classes(bool interfaces_of_a,
                      bool interfaces_of_b,
                      bool interfaces_of_c) {
    auto* i_type = DexType::make_type("Lp/I;");
    ClassCreator i_creator(i_type);
    i_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    i_creator.set_super(type::java_lang_Object());
    i_creator.add_method(assembler::method_from_string(R"(
      (method (public) "Lp/I;.m:()V" ((load-param-object v0) (return-void)))
    )"));

    auto* a_type = DexType::make_type("Lp/A;");
    ClassCreator a_creator(a_type);
    a_creator.set_access(ACC_PUBLIC);
    a_creator.set_super(type::java_lang_Object());
    if (interfaces_of_a) {
      a_creator.add_interface(i_type);
    }

    auto* b_type = DexType::make_type("Lp/B;");
    ClassCreator b_creator(b_type);
    b_creator.set_access(ACC_PUBLIC);
    b_creator.set_super(a_type);
    if (interfaces_of_b) {
      b_creator.add_interface(i_type);
    }
    b_creator.add_method(assembler::method_from_string(R"(
      (method () "Lp/B;.m:()V" ((load-param-object v0) (return-void)))
    )"));

    ClassCreator c_creator(DexType::make_type("Lq/C;"));
    c_creator.set_access(ACC_PUBLIC);
    c_creator.set_super(b_type);
    if (interfaces_of_c) {
      c_creator.add_interface(i_type);
    }

    DexStore store("classes");
    store.add_classes({i_creator.create(), a_creator.create(),
                       b_creator.create(), c_creator.create()});
    m_stores.emplace_back(std::move(store));
  }

  // Runs the pass with `fail_if_unsupported_refs` and returns its error.
  std::string run_pass() {
    Json::Value config;
    config["PackagePrivatePreprocessorPass"]["fail_if_unsupported_refs"] = true;
    ConfigFiles conf(config);
    conf.parse_global_config();
    PackagePrivatePreprocessorPass pass;
    PassManager manager({&pass}, conf);
    try {
      manager.run_passes(m_stores, conf);
    } catch (const RedexException& e) {
      return e.what();
    }
    return "";
  }

  DexStoresVector m_stores;
};

// package p; public class A implements I {}
// package p; public class B extends A { void m() {} }
//
// Android 12 and earlier refuse to link B; Android 13 and 14 link it, and B.m
// implements I.m. Once B.m is public, B links on Android 12 too.
TEST_F(PackagePrivateProcessorGeneratedBytecodeTest,
       nonPublicImplementationOfInheritedInterfaceIsUnsupported) {
  create_classes(/* interfaces_of_a */ true, /* interfaces_of_b */ false,
                 /* interfaces_of_c */ false);
  auto error = run_pass();
  EXPECT_NE(error.find("Redex limitation"), std::string::npos) << error;
  EXPECT_NE(error.find("Lp/B;.m:()V"), std::string::npos) << error;
}

// package p; public class A {}
// package p; public class B extends A implements I { void m() {} }
//
// Android 13 and earlier refuse to link B; Android 14 links it, and I.m runs
// for calls of I.m. Once B.m is public, B.m runs instead.
TEST_F(PackagePrivateProcessorGeneratedBytecodeTest,
       nonPublicImplementationOfAddedInterfaceIsUnsupported) {
  create_classes(/* interfaces_of_a */ false, /* interfaces_of_b */ true,
                 /* interfaces_of_c */ false);
  auto error = run_pass();
  EXPECT_NE(error.find("Redex limitation"), std::string::npos) << error;
  EXPECT_NE(error.find("Lp/B;.m:()V"), std::string::npos) << error;
}

// package q; public class C extends p.B implements p.I {}
//
// Android 13 and earlier refuse to link C, as ART matches B.m with I.m;
// Android 14 links it, and I.m runs for calls of I.m. Once B.m is public, B.m
// runs instead.
TEST_F(PackagePrivateProcessorGeneratedBytecodeTest,
       nonPublicImplementationInheritedBySubclassIsUnsupported) {
  create_classes(/* interfaces_of_a */ false, /* interfaces_of_b */ false,
                 /* interfaces_of_c */ true);
  auto error = run_pass();
  EXPECT_NE(error.find("Redex limitation"), std::string::npos) << error;
  EXPECT_NE(error.find("Lp/B;.m:()V"), std::string::npos) << error;
}
