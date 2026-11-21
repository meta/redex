/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdlib>
#include <cstring>
#include <vector>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "DexClass.h"
#include "DexLoader.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IRList.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"

class Dex037Test : public ::testing::Test {
 protected:
  void SetUp() override {
    g_redex = new RedexContext();
    const char* dexfile = std::getenv("dexfile");
    ASSERT_NE(nullptr, dexfile);

    std::vector<DexStore> stores;
    DexMetadata dm;
    dm.set_id("classes");
    DexStore root_store(dm);
    int input_dex_version = 0;
    root_store.add_classes(
        load_classes_from_dex(DexLocation::make_location("dex", dexfile),
                              nullptr,
                              &input_dex_version,
                              true,
                              true,
                              37));
    EXPECT_TRUE(input_dex_version == 37);
    classes = root_store.get_dexen()[0];
    // Apps always define java.lang.Object; a class chain without it is
    // incomplete.
    create_object_class();
  }

  void TearDown() override {
    delete g_redex;
    g_redex = nullptr;
  }

  DexClass* find_class(const char* name) {
    auto* type = DexType::get_type(name);
    if (type == nullptr) {
      return nullptr;
    }
    return type_class(type);
  }

  DexMethod* find_method(DexClass* cls, const char* name) {
    if (cls == nullptr) {
      return nullptr;
    }
    for (auto* method : cls->get_all_methods()) {
      if (strcmp(method->get_name()->c_str(), name) == 0) {
        return method;
      }
    }
    return nullptr;
  }

  void verify_TestIGreeterHasCorrectStructure(bool is_kotlin = false) {
    // Test that the Greeter interface is loaded and has default methods
    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);
    EXPECT_TRUE(is_interface(igreeter_cls));
    EXPECT_EQ(igreeter_cls->get_vmethods().size(), 5);
    // Kotlin has an additional clinit
    EXPECT_EQ(igreeter_cls->get_dmethods().size(), is_kotlin ? 3 : 2);

    auto* emptystring_method = find_method(igreeter_cls, "emptyString");
    ASSERT_NE(nullptr, emptystring_method);
    EXPECT_TRUE(is_private(emptystring_method));
    EXPECT_FALSE(is_static(emptystring_method));
    EXPECT_FALSE(is_abstract(emptystring_method));
    EXPECT_FALSE(emptystring_method->is_virtual());
    EXPECT_TRUE(emptystring_method->is_concrete());
    EXPECT_TRUE(emptystring_method->get_code() != nullptr);

    // Default interface methods are stored as virtual methods, they should be
    // public, non-static and non-abstract
    auto* greet_method = find_method(igreeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(greet_method->is_def());
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_FALSE(is_abstract(greet_method));
    // Default methods are concrete methods with implementation
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);

    for (auto& mie : InstructionIterable(greet_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "emptyString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_DIRECT);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }

    auto* farewell_method = find_method(igreeter_cls, "farewell");
    ASSERT_NE(nullptr, farewell_method);
    EXPECT_TRUE(is_public(farewell_method));
    EXPECT_FALSE(is_static(farewell_method));
    EXPECT_FALSE(is_abstract(farewell_method));
    EXPECT_TRUE(farewell_method->is_concrete());
    EXPECT_TRUE(farewell_method->get_code() != nullptr);

    auto* nested_greet_method = find_method(igreeter_cls, "nestedgreet");
    ASSERT_NE(nullptr, nested_greet_method);
    EXPECT_TRUE(nested_greet_method->is_def());
    EXPECT_TRUE(is_public(nested_greet_method));
    EXPECT_FALSE(is_static(nested_greet_method));
    EXPECT_FALSE(is_abstract(nested_greet_method));
    EXPECT_TRUE(nested_greet_method->is_concrete());
    EXPECT_TRUE(nested_greet_method->get_code() != nullptr);

    for (auto& mie : InstructionIterable(nested_greet_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
        ASSERT_NE(nullptr, resolved);
        EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
      }
    }

    auto* othermsg_method = find_method(igreeter_cls, "othermsg");
    ASSERT_NE(nullptr, othermsg_method);
    EXPECT_TRUE(is_public(othermsg_method));
    EXPECT_FALSE(is_static(othermsg_method));
    EXPECT_FALSE(is_abstract(othermsg_method));
    EXPECT_TRUE(othermsg_method->is_concrete());
    EXPECT_TRUE(othermsg_method->get_code() != nullptr);

    // Static interface method
    auto* static_greet_method = find_method(igreeter_cls, "staticGreet");
    ASSERT_NE(nullptr, static_greet_method);
    EXPECT_TRUE(is_static(static_greet_method));
    EXPECT_TRUE(is_public(static_greet_method));

    // Abstract interface method
    auto* non_default_method = find_method(igreeter_cls, "nonDefaultString");
    ASSERT_NE(nullptr, non_default_method);
    EXPECT_TRUE(is_abstract(non_default_method));
    EXPECT_TRUE(is_public(non_default_method));
    EXPECT_TRUE(non_default_method->is_concrete());
    EXPECT_EQ(non_default_method->get_code(), nullptr);
  }

  void verify_TestIFormalGreeterHasCorrectStructure() {
    auto* iformal_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$IFormalGreeter;");
    ASSERT_NE(nullptr, iformal_greeter_cls);
    EXPECT_TRUE(is_interface(iformal_greeter_cls));

    auto* greet_method = find_method(iformal_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(greet_method->is_def());
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_FALSE(is_abstract(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);
  }

  void verify_TestSimpleGreeterHasCorrectStructure() {
    auto* simple_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SimpleGreeter;");
    ASSERT_NE(nullptr, simple_greeter_cls);
    EXPECT_FALSE(is_interface(simple_greeter_cls));
    EXPECT_FALSE(is_abstract(simple_greeter_cls));
    EXPECT_EQ(simple_greeter_cls->get_vmethods().size(), 1);
    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    EXPECT_EQ(simple_greeter_cls->get_interfaces()->size(), 1);
    EXPECT_EQ(*(simple_greeter_cls->get_interfaces()->begin()),
              igreeter_cls->get_type());
  }

  void verify_TestComplexGreeterHasCorrectStructure() {
    auto* complex_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$ComplexGreeter;");
    ASSERT_NE(nullptr, complex_greeter_cls);
    EXPECT_FALSE(is_interface(complex_greeter_cls));
    auto* simple_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SimpleGreeter;");
    EXPECT_EQ(complex_greeter_cls->get_super_class(),
              simple_greeter_cls->get_type());
    EXPECT_EQ(complex_greeter_cls->get_interfaces()->size(), 0);

    EXPECT_EQ(complex_greeter_cls->get_vmethods().size(), 1);
    auto* greet_method = find_method(complex_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);
  }

  void verify_TestCustomGreeterHasCorrectStructure() {
    auto* custom_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$CustomGreeter;");
    ASSERT_NE(nullptr, custom_greeter_cls);
    EXPECT_FALSE(is_interface(custom_greeter_cls));

    EXPECT_EQ(custom_greeter_cls->get_vmethods().size(), 2);
    auto* greet_method = find_method(custom_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);
  }

  void verify_TestDoubleCustomGreeterHasCorrectStructure() {
    auto* double_custom_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$DoubleCustomGreeter;");
    ASSERT_NE(nullptr, double_custom_greeter_cls);
    EXPECT_FALSE(is_interface(double_custom_greeter_cls));
    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    auto* iformal_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$IFormalGreeter;");
    EXPECT_EQ(double_custom_greeter_cls->get_interfaces()->size(), 2);
    EXPECT_THAT(*(double_custom_greeter_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(
                    igreeter_cls->get_type(), iformal_greeter_cls->get_type()));

    EXPECT_EQ(double_custom_greeter_cls->get_vmethods().size(), 2);
    auto* greet_method = find_method(double_custom_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);
  }

  void verify_TestSuperCallingGreeterHasCorrectStructure() {
    auto* super_calling_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SuperCallingGreeter;");
    ASSERT_NE(nullptr, super_calling_greeter_cls);
    EXPECT_FALSE(is_interface(super_calling_greeter_cls));
    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    auto* iformal_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$IFormalGreeter;");
    auto* parent_cls = find_class("Lcom/facebook/redextest/Dex037$Parent;");
    EXPECT_EQ(super_calling_greeter_cls->get_interfaces()->size(), 2);
    EXPECT_EQ(super_calling_greeter_cls->get_super_class(),
              parent_cls->get_type());
    EXPECT_THAT(*(super_calling_greeter_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(
                    igreeter_cls->get_type(), iformal_greeter_cls->get_type()));

    EXPECT_EQ(super_calling_greeter_cls->get_vmethods().size(), 3);
    auto* greet_method = find_method(super_calling_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);
    for (auto& mie : InstructionIterable(greet_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), iformal_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
          resolved = resolve_super(iformal_greeter_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
          resolved = resolve_super(iformal_greeter_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "foo") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), parent_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_super(parent_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_super(parent_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
        }
      }
    }
    auto* wrap_greet_method =
        find_method(super_calling_greeter_cls, "wrapGreet");
    ASSERT_NE(nullptr, wrap_greet_method);
    EXPECT_TRUE(is_public(wrap_greet_method));
    EXPECT_FALSE(is_static(wrap_greet_method));
    EXPECT_TRUE(wrap_greet_method->is_concrete());
    EXPECT_TRUE(wrap_greet_method->get_code() != nullptr);
    for (auto& mie : InstructionIterable(wrap_greet_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          resolved = resolve_super(igreeter_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), wrap_greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          resolved = resolve_super(igreeter_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super,
                                    wrap_greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "foo") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), parent_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_super(parent_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), wrap_greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_super(parent_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super,
                                    wrap_greet_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), parent_cls->get_type());
        }
      }
    }
  }

  void verify_TestAbstractGreeterHasCorrectStructure() {
    auto* abstract_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$AbstractGreeter;");
    ASSERT_NE(nullptr, abstract_greeter_cls);
    EXPECT_FALSE(is_interface(abstract_greeter_cls));
    EXPECT_TRUE(is_abstract(abstract_greeter_cls));
    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    EXPECT_EQ(abstract_greeter_cls->get_interfaces()->size(), 1);
    EXPECT_EQ(*(abstract_greeter_cls->get_interfaces()->begin()),
              igreeter_cls->get_type());

    EXPECT_EQ(abstract_greeter_cls->get_vmethods().size(), 2);
    auto* greet_method = find_method(abstract_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(is_abstract(greet_method));

    auto* additional_greet_method =
        find_method(abstract_greeter_cls, "additionalGreet");
    ASSERT_NE(nullptr, additional_greet_method);
    EXPECT_TRUE(is_public(additional_greet_method));
    EXPECT_FALSE(is_static(additional_greet_method));
    EXPECT_TRUE(is_abstract(additional_greet_method));
  }

  void verify_TestConcreteGreeterHasCorrectStructure() {
    auto* concrete_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$ConcreteGreeter;");
    ASSERT_NE(nullptr, concrete_greeter_cls);
    EXPECT_FALSE(is_interface(concrete_greeter_cls));
    EXPECT_FALSE(is_abstract(concrete_greeter_cls));
    EXPECT_EQ(concrete_greeter_cls->get_interfaces()->size(), 0);
    auto* abstract_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$AbstractGreeter;");
    EXPECT_EQ(concrete_greeter_cls->get_super_class(),
              abstract_greeter_cls->get_type());

    EXPECT_EQ(concrete_greeter_cls->get_vmethods().size(), 4);
    auto* greet_method = find_method(concrete_greeter_cls, "greet");
    ASSERT_NE(nullptr, greet_method);
    EXPECT_TRUE(is_public(greet_method));
    EXPECT_FALSE(is_static(greet_method));
    EXPECT_TRUE(greet_method->is_concrete());
    EXPECT_TRUE(greet_method->get_code() != nullptr);

    auto* additional_greet_method =
        find_method(concrete_greeter_cls, "additionalGreet");
    ASSERT_NE(nullptr, additional_greet_method);
    EXPECT_TRUE(is_public(additional_greet_method));
    EXPECT_FALSE(is_static(additional_greet_method));
    EXPECT_TRUE(additional_greet_method->is_concrete());
    EXPECT_TRUE(additional_greet_method->get_code() != nullptr);

    auto* farewell_method = find_method(concrete_greeter_cls, "farewell");
    ASSERT_NE(nullptr, farewell_method);
    EXPECT_TRUE(is_public(farewell_method));
    EXPECT_FALSE(is_static(farewell_method));
    EXPECT_TRUE(farewell_method->is_concrete());
    EXPECT_TRUE(farewell_method->get_code() != nullptr);
  }

  void verify_TestILayerHasCorrectStructure() {
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_TRUE(is_interface(ilayer_cls));

    EXPECT_EQ(ilayer_cls->get_vmethods().size(), 1);
    auto* layer_method = find_method(ilayer_cls, "layer");
    ASSERT_NE(nullptr, layer_method);
    EXPECT_TRUE(is_public(layer_method));
    EXPECT_FALSE(is_abstract(layer_method));
    EXPECT_TRUE(layer_method->is_virtual());
    EXPECT_FALSE(is_static(layer_method));
    EXPECT_TRUE(layer_method->is_concrete());
    EXPECT_TRUE(layer_method->get_code() != nullptr);
  }

  void verify_TestILayerOverrideHasCorrectStructure() {
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_TRUE(is_interface(ilayer_override_cls));

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(ilayer_override_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_cls->get_type()));

    EXPECT_EQ(ilayer_override_cls->get_vmethods().size(), 1);
    auto* layer_method = find_method(ilayer_override_cls, "layer");
    ASSERT_NE(nullptr, layer_method);
    EXPECT_TRUE(is_public(layer_method));
    EXPECT_TRUE(layer_method->is_virtual());
    EXPECT_FALSE(is_abstract(layer_method));
    EXPECT_FALSE(is_static(layer_method));
    EXPECT_TRUE(layer_method->is_concrete());
    EXPECT_TRUE(layer_method->get_code() != nullptr);
  }

  void verify_TestILayerOverrideChildHasCorrectStructure() {
    auto* ilayer_override_child_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverrideChild;");
    ASSERT_NE(nullptr, ilayer_override_child_cls);
    EXPECT_TRUE(is_interface(ilayer_override_child_cls));

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_THAT(
        *(ilayer_override_child_cls->get_interfaces()),
        ::testing::UnorderedElementsAre(ilayer_override_cls->get_type()));

    EXPECT_EQ(ilayer_override_child_cls->get_vmethods().size(), 0);
  }

  void verify_TestILayerOverrideChild2HasCorrectStructure() {
    auto* ilayer_override_child_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverrideChild2;");
    ASSERT_NE(nullptr, ilayer_override_child_cls);
    EXPECT_TRUE(is_interface(ilayer_override_child_cls));

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_THAT(*(ilayer_override_child_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_cls->get_type(),
                                       ilayer_override_cls->get_type()));

    EXPECT_EQ(ilayer_override_child_cls->get_vmethods().size(), 0);
  }

  void verify_TestILayerNoOverrideHasCorrectStructure() {
    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    EXPECT_TRUE(is_interface(ilayer_no_override_cls));

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(ilayer_no_override_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_cls->get_type()));

    EXPECT_EQ(ilayer_no_override_cls->get_vmethods().size(), 0);
  }

  void verify_TestILayerConflictHasCorrectStructure() {
    auto* ilayer_conflict_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerConflict;");
    ASSERT_NE(nullptr, ilayer_conflict_cls);
    EXPECT_TRUE(is_interface(ilayer_conflict_cls));

    EXPECT_EQ(ilayer_conflict_cls->get_vmethods().size(), 1);
    auto* layer_method = find_method(ilayer_conflict_cls, "layer");
    ASSERT_NE(nullptr, layer_method);
    EXPECT_TRUE(is_public(layer_method));
    EXPECT_TRUE(layer_method->is_virtual());
    EXPECT_FALSE(is_abstract(layer_method));
    EXPECT_FALSE(is_static(layer_method));
    EXPECT_TRUE(layer_method->is_concrete());
    EXPECT_TRUE(layer_method->get_code() != nullptr);
  }

  void verify_TestILayerLast1HasCorrectStructure() {
    auto* ilayer_last1_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerLast1;");
    ASSERT_NE(nullptr, ilayer_last1_cls);
    EXPECT_TRUE(is_interface(ilayer_last1_cls));

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    EXPECT_THAT(*(ilayer_last1_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_override_cls->get_type(),
                                       ilayer_no_override_cls->get_type()));

    EXPECT_EQ(ilayer_last1_cls->get_vmethods().size(), 0);
  }

  void verify_TestILayerLast2HasCorrectStructure() {
    auto* ilayer_last2_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerLast2;");
    ASSERT_NE(nullptr, ilayer_last2_cls);
    EXPECT_TRUE(is_interface(ilayer_last2_cls));

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    EXPECT_THAT(*(ilayer_last2_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_no_override_cls->get_type(),
                                       ilayer_override_cls->get_type()));

    EXPECT_EQ(ilayer_last2_cls->get_vmethods().size(), 0);
  }

  void verify_TestLayer1HasCorrectStructure() {
    auto* layer1_cls = find_class("Lcom/facebook/redextest/Dex037$Layer1;");
    ASSERT_NE(nullptr, layer1_cls);
    EXPECT_FALSE(is_interface(layer1_cls));
    EXPECT_FALSE(is_abstract(layer1_cls));

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(layer1_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_override_cls->get_type(),
                                       ilayer_cls->get_type()));

    EXPECT_EQ(layer1_cls->get_vmethods().size(), 0);
  }

  void verify_TestLayer2HasCorrectStructure() {
    auto* layer2_cls = find_class("Lcom/facebook/redextest/Dex037$Layer2;");
    ASSERT_NE(nullptr, layer2_cls);
    EXPECT_FALSE(is_interface(layer2_cls));
    EXPECT_FALSE(is_abstract(layer2_cls));

    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(layer2_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_no_override_cls->get_type(),
                                       ilayer_cls->get_type()));

    EXPECT_EQ(layer2_cls->get_vmethods().size(), 0);
  }

  void verify_TestLayer3HasCorrectStructure() {
    auto* layer3_cls = find_class("Lcom/facebook/redextest/Dex037$Layer3;");
    ASSERT_NE(nullptr, layer3_cls);
    EXPECT_FALSE(is_interface(layer3_cls));
    EXPECT_FALSE(is_abstract(layer3_cls));

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_THAT(*(layer3_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_cls->get_type(),
                                       ilayer_override_cls->get_type()));

    EXPECT_EQ(layer3_cls->get_vmethods().size(), 0);
  }

  void verify_TestFinalLayer1HasCorrectStructure() {
    auto* finallayer1_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer1;");
    ASSERT_NE(nullptr, finallayer1_cls);
    EXPECT_FALSE(is_interface(finallayer1_cls));
    EXPECT_FALSE(is_abstract(finallayer1_cls));

    auto* layer1_cls = find_class("Lcom/facebook/redextest/Dex037$Layer1;");
    ASSERT_NE(nullptr, layer1_cls);
    EXPECT_EQ(finallayer1_cls->get_super_class(), layer1_cls->get_type());
    EXPECT_EQ(finallayer1_cls->get_interfaces()->size(), 0);

    EXPECT_EQ(finallayer1_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer1_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), layer1_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(layer1_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(layer1_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer2HasCorrectStructure() {
    auto* finallayer2_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer2;");
    ASSERT_NE(nullptr, finallayer2_cls);
    EXPECT_FALSE(is_interface(finallayer2_cls));
    EXPECT_FALSE(is_abstract(finallayer2_cls));

    auto* layer2_cls = find_class("Lcom/facebook/redextest/Dex037$Layer2;");
    ASSERT_NE(nullptr, layer2_cls);
    EXPECT_EQ(finallayer2_cls->get_super_class(), layer2_cls->get_type());
    EXPECT_EQ(finallayer2_cls->get_interfaces()->size(), 0);

    EXPECT_EQ(finallayer2_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer2_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), layer2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(layer2_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(layer2_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer3HasCorrectStructure() {
    auto* finallayer3_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer3;");
    ASSERT_NE(nullptr, finallayer3_cls);
    EXPECT_FALSE(is_interface(finallayer3_cls));
    EXPECT_FALSE(is_abstract(finallayer3_cls));

    auto* layer3_cls = find_class("Lcom/facebook/redextest/Dex037$Layer3;");
    ASSERT_NE(nullptr, layer3_cls);
    EXPECT_EQ(finallayer3_cls->get_super_class(), layer3_cls->get_type());
    EXPECT_EQ(finallayer3_cls->get_interfaces()->size(), 0);

    EXPECT_EQ(finallayer3_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer3_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), layer3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(layer3_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(layer3_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestMidLayerHasCorrectStructure() {
    auto* midlayer_cls = find_class("Lcom/facebook/redextest/Dex037$MidLayer;");
    ASSERT_NE(nullptr, midlayer_cls);
    EXPECT_FALSE(is_interface(midlayer_cls));
    EXPECT_FALSE(is_abstract(midlayer_cls));

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(midlayer_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_cls->get_type()));

    EXPECT_EQ(midlayer_cls->get_vmethods().size(), 0);
  }

  void verify_TestMidLayer2HasCorrectStructure() {
    auto* midlayer2_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer2;");
    ASSERT_NE(nullptr, midlayer2_cls);
    EXPECT_FALSE(is_interface(midlayer2_cls));
    EXPECT_FALSE(is_abstract(midlayer2_cls));

    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_last1_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerLast1;");
    ASSERT_NE(nullptr, ilayer_last1_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_THAT(*(midlayer2_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_no_override_cls->get_type(),
                                       ilayer_cls->get_type(),
                                       ilayer_last1_cls->get_type(),
                                       ilayer_override_cls->get_type()));

    EXPECT_EQ(midlayer2_cls->get_vmethods().size(), 0);
  }

  void verify_TestMidLayer3HasCorrectStructure() {
    auto* midlayer3_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer3;");
    ASSERT_NE(nullptr, midlayer3_cls);
    EXPECT_FALSE(is_interface(midlayer3_cls));
    EXPECT_FALSE(is_abstract(midlayer3_cls));

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(midlayer3_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_cls->get_type()));

    EXPECT_EQ(midlayer3_cls->get_vmethods().size(), 1);
    auto* layer_method = find_method(midlayer3_cls, "layer");
    ASSERT_NE(nullptr, layer_method);
    EXPECT_TRUE(is_public(layer_method));
    EXPECT_FALSE(is_static(layer_method));
    EXPECT_TRUE(layer_method->is_concrete());
    EXPECT_TRUE(layer_method->get_code() != nullptr);
  }

  void verify_TestFinalLayer4HasCorrectStructure() {
    auto* finallayer4_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4;");
    ASSERT_NE(nullptr, finallayer4_cls);
    EXPECT_FALSE(is_interface(finallayer4_cls));
    EXPECT_FALSE(is_abstract(finallayer4_cls));

    auto* midlayer_cls = find_class("Lcom/facebook/redextest/Dex037$MidLayer;");
    ASSERT_NE(nullptr, midlayer_cls);
    EXPECT_EQ(finallayer4_cls->get_super_class(), midlayer_cls->get_type());

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    EXPECT_THAT(
        *(finallayer4_cls->get_interfaces()),
        ::testing::UnorderedElementsAre(ilayer_override_cls->get_type()));

    EXPECT_EQ(finallayer4_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer4_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), midlayer_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(midlayer_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(midlayer_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer4_2HasCorrectStructure() {
    auto* finallayer4_2_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4_2;");
    ASSERT_NE(nullptr, finallayer4_2_cls);
    EXPECT_FALSE(is_interface(finallayer4_2_cls));
    EXPECT_FALSE(is_abstract(finallayer4_2_cls));

    auto* midlayer_cls = find_class("Lcom/facebook/redextest/Dex037$MidLayer;");
    ASSERT_NE(nullptr, midlayer_cls);
    EXPECT_EQ(finallayer4_2_cls->get_super_class(), midlayer_cls->get_type());

    auto* ilayer_override_child_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverrideChild;");
    ASSERT_NE(nullptr, ilayer_override_child_cls);
    EXPECT_THAT(
        *(finallayer4_2_cls->get_interfaces()),
        ::testing::UnorderedElementsAre(ilayer_override_child_cls->get_type()));

    EXPECT_EQ(finallayer4_2_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer4_2_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), midlayer_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(midlayer_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_super(midlayer_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestTopLayerHasCorrectStructure() {
    auto* toplayer_cls = find_class("Lcom/facebook/redextest/Dex037$TopLayer;");
    ASSERT_NE(nullptr, toplayer_cls);
    EXPECT_FALSE(is_interface(toplayer_cls));
    EXPECT_FALSE(is_abstract(toplayer_cls));

    EXPECT_EQ(toplayer_cls->get_vmethods().size(), 1);
    auto* layer_method = find_method(toplayer_cls, "layer");
    ASSERT_NE(nullptr, layer_method);
    EXPECT_TRUE(is_public(layer_method));
    EXPECT_FALSE(is_static(layer_method));
    EXPECT_TRUE(layer_method->is_concrete());
    EXPECT_TRUE(layer_method->get_code() != nullptr);
  }

  void verify_TestMidLayer4HasCorrectStructure(bool is_kotlin = false) {
    auto* midlayer4_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer4;");
    ASSERT_NE(nullptr, midlayer4_cls);
    EXPECT_FALSE(is_interface(midlayer4_cls));
    EXPECT_FALSE(is_abstract(midlayer4_cls));

    auto* toplayer_cls = find_class("Lcom/facebook/redextest/Dex037$TopLayer;");
    ASSERT_NE(nullptr, toplayer_cls);
    EXPECT_EQ(midlayer4_cls->get_super_class(), toplayer_cls->get_type());

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    EXPECT_THAT(*(midlayer4_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_cls->get_type()));
    if (is_kotlin) {
      // We need to add a layer override to fulfill kotlin compilation request
      EXPECT_EQ(midlayer4_cls->get_vmethods().size(), 1);
      auto* layer_method = find_method(midlayer4_cls, "layer");
      EXPECT_TRUE(is_public(layer_method));
      EXPECT_FALSE(is_static(layer_method));
      EXPECT_TRUE(layer_method->is_concrete());
      EXPECT_TRUE(layer_method->get_code() != nullptr);
      for (auto& mie : InstructionIterable(layer_method->get_code())) {
        auto* insn = mie.insn;
        if (insn->has_method()) {
          auto* callee_ref = insn->get_method();
          if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
            EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
            auto* resolved = resolve_invoke_method(insn);
            EXPECT_EQ(callee_ref->get_class(), toplayer_cls->get_type());
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
            resolved = resolve_super(toplayer_cls, callee_ref->get_name(),
                                     callee_ref->get_proto(), layer_method);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
            resolved = resolve_super(toplayer_cls, callee_ref->get_name(),
                                     callee_ref->get_proto(), nullptr);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
            resolved =
                resolve_method(callee_ref, MethodSearch::Super, layer_method);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
            resolved = resolve_method(callee_ref, MethodSearch::Super);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
          }
        }
      }
    } else {
      EXPECT_EQ(midlayer4_cls->get_vmethods().size(), 0);
    }
  }

  void verify_TestFinalLayer4_3HasCorrectStructure(bool is_kotlin = false) {
    auto* finallayer4_3_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4_3;");
    ASSERT_NE(nullptr, finallayer4_3_cls);
    EXPECT_FALSE(is_interface(finallayer4_3_cls));
    EXPECT_FALSE(is_abstract(finallayer4_3_cls));

    auto* midlayer4_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer4;");
    ASSERT_NE(nullptr, midlayer4_cls);
    EXPECT_EQ(finallayer4_3_cls->get_super_class(), midlayer4_cls->get_type());

    auto* ilayer_conflict_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerConflict;");
    ASSERT_NE(nullptr, ilayer_conflict_cls);
    EXPECT_THAT(
        *(finallayer4_3_cls->get_interfaces()),
        ::testing::UnorderedElementsAre(ilayer_conflict_cls->get_type()));

    if (is_kotlin) {
      // Need to override layer in FinalLayer4_3 in kotlin to compile
      EXPECT_EQ(finallayer4_3_cls->get_vmethods().size(), 2);
      auto* layer_method = find_method(finallayer4_3_cls, "layer");
      ASSERT_NE(nullptr, layer_method);
      EXPECT_TRUE(is_public(layer_method));
      EXPECT_FALSE(is_static(layer_method));
      EXPECT_TRUE(layer_method->is_concrete());
      EXPECT_TRUE(layer_method->get_code() != nullptr);
    } else {
      EXPECT_EQ(finallayer4_3_cls->get_vmethods().size(), 1);
    }
    auto* get_layer_method = find_method(finallayer4_3_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* toplayer_cls = find_class("Lcom/facebook/redextest/Dex037$TopLayer;");
    ASSERT_NE(nullptr, toplayer_cls);

    const auto expect_class_type = [is_kotlin, midlayer4_cls,
                                    toplayer_cls](const DexMethod* resolved) {
      if (is_kotlin) {
        // We also override layer in MidLayer4 to compile
        EXPECT_EQ(resolved->get_class(), midlayer4_cls->get_type());
      } else {
        EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
      }
    };
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), midlayer4_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          expect_class_type(resolved);
          resolved = resolve_super(midlayer4_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          expect_class_type(resolved);
          resolved = resolve_super(midlayer4_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          expect_class_type(resolved);
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          expect_class_type(resolved);
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          expect_class_type(resolved);
        }
      }
    }
  }

  void verify_TestFinalLayer5HasCorrectStructure() {
    auto* finallayer5_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer5;");
    ASSERT_NE(nullptr, finallayer5_cls);
    EXPECT_FALSE(is_interface(finallayer5_cls));
    EXPECT_FALSE(is_abstract(finallayer5_cls));

    auto* midlayer2_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer2;");
    ASSERT_NE(nullptr, midlayer2_cls);
    EXPECT_EQ(finallayer5_cls->get_super_class(), midlayer2_cls->get_type());
    EXPECT_EQ(finallayer5_cls->get_interfaces()->size(), 0);

    EXPECT_EQ(finallayer5_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer5_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), midlayer2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(midlayer2_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_super(midlayer2_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer6HasCorrectStructure(bool is_kotlin = false) {
    auto* finallayer6_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer6;");
    ASSERT_NE(nullptr, finallayer6_cls);
    EXPECT_FALSE(is_interface(finallayer6_cls));
    EXPECT_FALSE(is_abstract(finallayer6_cls));

    auto* midlayer3_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer3;");
    ASSERT_NE(nullptr, midlayer3_cls);
    EXPECT_EQ(finallayer6_cls->get_super_class(), midlayer3_cls->get_type());

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_conflict_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerConflict;");
    ASSERT_NE(nullptr, ilayer_conflict_cls);
    EXPECT_THAT(*(finallayer6_cls->get_interfaces()),
                ::testing::ElementsAre(ilayer_cls->get_type(),
                                       ilayer_conflict_cls->get_type()));
    if (is_kotlin) {
      // We need to override layer method to fulfill kotlin compilation
      // requirement
      EXPECT_EQ(finallayer6_cls->get_vmethods().size(), 2);
      auto* layer_method = find_method(finallayer6_cls, "layer");
      ASSERT_NE(nullptr, layer_method);
      EXPECT_TRUE(is_public(layer_method));
      EXPECT_FALSE(is_static(layer_method));
      EXPECT_TRUE(layer_method->is_concrete());
      EXPECT_TRUE(layer_method->get_code() != nullptr);
      for (auto& mie : InstructionIterable(layer_method->get_code())) {
        auto* insn = mie.insn;
        if (insn->has_method()) {
          auto* callee_ref = insn->get_method();
          if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
            EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
            auto* resolved = resolve_invoke_method(insn);
            EXPECT_EQ(callee_ref->get_class(), midlayer3_cls->get_type());
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
            resolved = resolve_super(midlayer3_cls, callee_ref->get_name(),
                                     callee_ref->get_proto(), layer_method);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
            resolved = resolve_super(midlayer3_cls, callee_ref->get_name(),
                                     callee_ref->get_proto(), nullptr);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
            resolved =
                resolve_method(callee_ref, MethodSearch::Super, layer_method);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
            resolved = resolve_method(callee_ref, MethodSearch::Super);
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          }
        }
      }
    } else {
      EXPECT_EQ(finallayer6_cls->get_vmethods().size(), 1);
    }
    auto* get_layer_method = find_method(finallayer6_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), midlayer3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          resolved = resolve_super(midlayer3_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          resolved = resolve_super(midlayer3_cls, callee_ref->get_name(),
                                   callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer7HasCorrectStructure() {
    auto* finallayer7_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer7;");
    ASSERT_NE(nullptr, finallayer7_cls);
    EXPECT_FALSE(is_interface(finallayer7_cls));
    EXPECT_FALSE(is_abstract(finallayer7_cls));

    auto* ilayer_last1_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerLast1;");
    ASSERT_NE(nullptr, ilayer_last1_cls);
    EXPECT_THAT(*(finallayer7_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_last1_cls->get_type()));

    EXPECT_EQ(finallayer7_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer7_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), finallayer7_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Virtual,
                                    get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Virtual);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer8HasCorrectStructure() {
    auto* finallayer8_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer8;");
    ASSERT_NE(nullptr, finallayer8_cls);
    EXPECT_FALSE(is_interface(finallayer8_cls));
    EXPECT_FALSE(is_abstract(finallayer8_cls));

    auto* ilayer_last2_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerLast2;");
    ASSERT_NE(nullptr, ilayer_last2_cls);
    EXPECT_THAT(*(finallayer8_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(ilayer_last2_cls->get_type()));

    EXPECT_EQ(finallayer8_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer8_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(), finallayer8_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Virtual,
                                    get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Virtual);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer9HasCorrectStructure() {
    auto* finallayer9_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer9;");
    ASSERT_NE(nullptr, finallayer9_cls);
    EXPECT_FALSE(is_interface(finallayer9_cls));
    EXPECT_FALSE(is_abstract(finallayer9_cls));

    auto* ilayer_no_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerNoOverride;");
    ASSERT_NE(nullptr, ilayer_no_override_cls);
    EXPECT_THAT(
        *(finallayer9_cls->get_interfaces()),
        ::testing::UnorderedElementsAre(ilayer_no_override_cls->get_type()));

    EXPECT_EQ(finallayer9_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer9_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(),
                    ilayer_no_override_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved =
              resolve_super(ilayer_no_override_cls, callee_ref->get_name(),
                            callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestFinalLayer10HasCorrectStructure() {
    auto* finallayer10_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer10;");
    ASSERT_NE(nullptr, finallayer10_cls);
    EXPECT_FALSE(is_interface(finallayer10_cls));
    EXPECT_FALSE(is_abstract(finallayer10_cls));

    auto* ilayer_override_child2_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverrideChild2;");
    ASSERT_NE(nullptr, ilayer_override_child2_cls);
    EXPECT_THAT(*(finallayer10_cls->get_interfaces()),
                ::testing::UnorderedElementsAre(
                    ilayer_override_child2_cls->get_type()));

    EXPECT_EQ(finallayer10_cls->get_vmethods().size(), 1);
    auto* get_layer_method = find_method(finallayer10_cls, "getLayer");
    ASSERT_NE(nullptr, get_layer_method);
    EXPECT_TRUE(is_public(get_layer_method));
    EXPECT_FALSE(is_static(get_layer_method));
    EXPECT_TRUE(get_layer_method->is_concrete());
    EXPECT_TRUE(get_layer_method->get_code() != nullptr);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);
    for (auto& mie : InstructionIterable(get_layer_method->get_code())) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_SUPER);
          auto* resolved = resolve_invoke_method(insn);
          EXPECT_EQ(callee_ref->get_class(),
                    ilayer_override_child2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved =
              resolve_super(ilayer_override_child2_cls, callee_ref->get_name(),
                            callee_ref->get_proto(), nullptr);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved =
              resolve_method(callee_ref, MethodSearch::Super, get_layer_method);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
          resolved = resolve_method(callee_ref, MethodSearch::Super);
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnClass() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(dex037_cls, "testInvokeVirtualOnClass");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* simple_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SimpleGreeter;");
    ASSERT_NE(nullptr, simple_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), simple_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnInterface() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnInterface");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnOverriddenMethod() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualOnOverriddenMethod");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* complex_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$ComplexGreeter;");
    ASSERT_NE(nullptr, complex_greeter_cls);

    auto* simple_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SimpleGreeter;");
    ASSERT_NE(nullptr, simple_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), complex_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), complex_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), complex_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), complex_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), complex_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), simple_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnParentClass() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualOnParentClass");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* simple_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SimpleGreeter;");
    ASSERT_NE(nullptr, simple_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), simple_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), simple_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnOverriddenMethod() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnOverriddenMethod");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualWithOverride() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualWithOverride");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* custom_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$CustomGreeter;");
    ASSERT_NE(nullptr, custom_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), custom_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), custom_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnMultipleInterfaces() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualOnMultipleInterfaces");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* double_custom_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$DoubleCustomGreeter;");
    ASSERT_NE(nullptr, double_custom_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    double_custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(),
                    double_custom_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    double_custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    double_custom_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(),
                    double_custom_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnMultipleInterfaces() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnMultipleInterfaces");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnMultipleInterfaces2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnMultipleInterfaces2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* iformal_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$IFormalGreeter;");
    ASSERT_NE(nullptr, iformal_greeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), iformal_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeSuperInterface() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(dex037_cls, "testInvokeSuperInterface");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* super_calling_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$SuperCallingGreeter;");
    ASSERT_NE(nullptr, super_calling_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    super_calling_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(),
                    super_calling_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    super_calling_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(),
                    super_calling_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(),
                    super_calling_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceInvokeSuperInterface() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceInvokeSuperInterface");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceInvokeSuperInterface2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceInvokeSuperInterface2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* iformal_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$IFormalGreeter;");
    ASSERT_NE(nullptr, iformal_greeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), iformal_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), iformal_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeStaticInterface(bool is_kotlin = false) {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(dex037_cls, "testInvokeStaticInterface");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (!is_kotlin) {
          // Kotlin generate invoke-virtual on companion method
          if (strcmp(callee_ref->get_name()->c_str(), "staticGreet") == 0) {
            EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_STATIC);
            EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
            ASSERT_NE(nullptr, resolved);
            EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          }
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnConcreteClass() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualOnConcreteClass");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* concrete_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$ConcreteGreeter;");
    ASSERT_NE(nullptr, concrete_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), concrete_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), concrete_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "additionalGreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), concrete_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), concrete_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), concrete_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), concrete_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), concrete_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), concrete_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), concrete_greeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeVirtualOnAbstractClass() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeVirtualOnAbstractClass");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* abstract_greeter_cls =
        find_class("Lcom/facebook/redextest/Dex037$AbstractGreeter;");
    ASSERT_NE(nullptr, abstract_greeter_cls);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), abstract_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "additionalGreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), abstract_greeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "othermsg") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), abstract_greeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnConcreteClass() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnConcreteClass");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "farewell") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "othermsg") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "nestedgreet") ==
                   0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(),
                          "nonDefaultString") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceOnReferences(
      bool is_kotlin = false) {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceOnReferences");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* igreeter_cls = find_class("Lcom/facebook/redextest/Dex037$IGreeter;");
    ASSERT_NE(nullptr, igreeter_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "greet") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), igreeter_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), igreeter_cls->get_type());
          if (is_kotlin) {
            // If kotlinc would generate invoke-interface IGreeter.greet or
            // invoke-virtual CustomGreeter/ComplexGreeter.greet for second and
            // third invoke site seems to be random-ish... So break after first
            // check.
            break;
          }
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeMultipleInterfaces1() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeMultipleInterfaces1");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer1_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer1;");
    ASSERT_NE(nullptr, finallayer1_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer1_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer1_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer1_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeMultipleInterfaces2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeMultipleInterfaces2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer2_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer2;");
    ASSERT_NE(nullptr, finallayer2_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer2_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeMultipleInterfaces3() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeMultipleInterfaces3");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer3_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer3;");
    ASSERT_NE(nullptr, finallayer3_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer3_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeClassAndInterface1() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeClassAndInterface1");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer4_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4;");
    ASSERT_NE(nullptr, finallayer4_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer4_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeClassAndInterface2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeClassAndInterface2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer4_2_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4_2;");
    ASSERT_NE(nullptr, finallayer4_2_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer4_2_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeClassAndInterface2_2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeClassAndInterface2_2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), ilayer_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeClassAndInterface3(
      bool is_kotlin = false) {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeClassAndInterface3");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer4_3_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer4_3;");
    ASSERT_NE(nullptr, finallayer4_3_cls);
    auto* toplayer_cls = find_class("Lcom/facebook/redextest/Dex037$TopLayer;");
    ASSERT_NE(nullptr, toplayer_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer4_3_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer4_3_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          if (is_kotlin) {
            // We override layer in FinalLayer4_3 in kotlin to compile
            EXPECT_EQ(resolved->get_class(), finallayer4_3_cls->get_type());
          } else {
            EXPECT_EQ(resolved->get_class(), toplayer_cls->get_type());
          }
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeClassAndInterface3_2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeClassAndInterface3_2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_conflict_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerConflict;");
    ASSERT_NE(nullptr, ilayer_conflict_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), ilayer_conflict_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_conflict_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeWithRedundantInterfaces() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeWithRedundantInterfaces");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer5_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer5;");
    ASSERT_NE(nullptr, finallayer5_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer5_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer5_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer5_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeWithClassMultipleInterface(
      bool is_kotlin = false) {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeWithClassMultipleInterface");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer6_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer6;");
    ASSERT_NE(nullptr, finallayer6_cls);
    auto* midlayer3_cls =
        find_class("Lcom/facebook/redextest/Dex037$MidLayer3;");
    ASSERT_NE(nullptr, midlayer3_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer6_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer6_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer6_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          if (is_kotlin) {
            // We override layer for FinalLayer6 in kotlin to compile
            EXPECT_EQ(resolved->get_class(), finallayer6_cls->get_type());
          } else {
            EXPECT_EQ(resolved->get_class(), midlayer3_cls->get_type());
          }
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeWithDiamondInterface1() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeWithDiamondInterface1");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer7_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer7;");
    ASSERT_NE(nullptr, finallayer7_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer7_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer7_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer7_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeWithDiamondInterface2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeWithDiamondInterface2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer8_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer8;");
    ASSERT_NE(nullptr, finallayer8_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer8_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer8_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer8_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeSuperWithInheritedDefault() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeSuperWithInheritedDefault");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer9_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer9;");
    ASSERT_NE(nullptr, finallayer9_cls);
    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer9_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer9_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer9_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeSuperWithInheritedDefault2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testLayeredInvokeSuperWithInheritedDefault2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* finallayer10_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer10;");
    ASSERT_NE(nullptr, finallayer10_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "getLayer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer10_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), finallayer10_cls->get_type());
        } else if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), finallayer10_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeSuperWithInheritedDefault2_2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(
        dex037_cls, "testLayeredInvokeSuperWithInheritedDefault2_2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    auto* ilayer_override_child2_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverrideChild2;");
    ASSERT_NE(nullptr, ilayer_override_child2_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(),
                    ilayer_override_child2_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeSuperWithInheritedDefault2_3() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(
        dex037_cls, "testLayeredInvokeSuperWithInheritedDefault2_3");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);
    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), ilayer_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodLayeredInvokeSuperWithInheritedDefault2_4() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method = find_method(
        dex037_cls, "testLayeredInvokeSuperWithInheritedDefault2_4");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), ilayer_override_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceVirtualDifference() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceVirtualDifference");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* final_layer11_cls =
        find_class("Lcom/facebook/redextest/Dex037$FinalLayer11;");
    ASSERT_NE(nullptr, final_layer11_cls);
    auto* ilayer_override_cls =
        find_class("Lcom/facebook/redextest/Dex037$ILayerOverride;");
    ASSERT_NE(nullptr, ilayer_override_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_VIRTUAL);
          EXPECT_EQ(callee_ref->get_class(), final_layer11_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_override_cls->get_type());
        }
      }
    }
  }

  void verify_TestResolveMethodInvokeInterfaceVirtualDifference2() {
    auto* dex037_cls = find_class("Lcom/facebook/redextest/Dex037;");
    ASSERT_NE(nullptr, dex037_cls);

    auto* test_method =
        find_method(dex037_cls, "testInvokeInterfaceVirtualDifference2");
    ASSERT_NE(nullptr, test_method);

    auto* code = test_method->get_code();
    ASSERT_NE(nullptr, code);

    auto* ilayer_cls = find_class("Lcom/facebook/redextest/Dex037$ILayer;");
    ASSERT_NE(nullptr, ilayer_cls);

    for (auto& mie : InstructionIterable(code)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        auto* callee_ref = insn->get_method();
        auto* resolved = resolve_invoke_method(insn);
        if (strcmp(callee_ref->get_name()->c_str(), "layer") == 0) {
          EXPECT_EQ(insn->opcode(), OPCODE_INVOKE_INTERFACE);
          EXPECT_EQ(callee_ref->get_class(), ilayer_cls->get_type());
          ASSERT_NE(nullptr, resolved);
          EXPECT_EQ(resolved->get_class(), ilayer_cls->get_type());
        }
      }
    }
  }

  DexClasses classes;
};
