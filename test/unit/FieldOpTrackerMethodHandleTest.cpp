/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "FieldOpTracker.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RemoveUnusedFields.h"
#include "Show.h"
#include "Walkers.h"

// The method handles in these tests are tool-generated: a bytecode tool with
// an app-defined bootstrap method.

namespace {

constexpr const char* kInvokeExact =
    "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/"
    "lang/Object;";

class FieldOpTrackerMethodHandleTest : public RedexTest {
 protected:
  FieldOpTrackerMethodHandleTest() {
    ClassCreator cc(DexType::make_type("LFoo;"));
    cc.set_super(type::java_lang_Object());
    cc.set_access(ACC_PUBLIC);
    m_field = DexField::make_field("LFoo;.f:I")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC);
    cc.add_field(m_field);
    m_cls = cc.create();
  }

  DexMethod* add_method(const std::string& spec, const std::string& code) {
    auto* m = DexMethod::make_method(spec)->make_concrete(
        ACC_PUBLIC | ACC_STATIC, assembler::ircode_from_string(code),
        /* is_virtual */ false);
    m_cls->add_method(m);
    return m;
  }

  // f = x, through a static-put method handle.
  void add_handle_put() {
    add_method("LFoo;.handle_put:(I)V", std::string(R"((
      (load-param v1)
      (const-method-handle static-put "LFoo;.f:I")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0 v1) ")") + kInvokeExact +
                                            R"(" "(I)V")
      (return-void)
    ))");
  }

  void run_remove_unused_fields() {
    remove_unused_fields::PassImpl pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    DexStore store("classes");
    store.add_classes({m_cls});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    manager.run_passes(stores, config);
  }

  // PassManager leaves the code without a CFG.
  static bool has_field_insn(DexMethod* method) {
    for (const auto& mie : InstructionIterable(*method->get_code())) {
      if (mie.insn->has_field()) {
        return true;
      }
    }
    return false;
  }

  DexClass* m_cls;
  DexField* m_field;
};

} // namespace

// A static-get method handle reads the field, so its writes stay.
TEST_F(FieldOpTrackerMethodHandleTest, read_only_through_handle) {
  auto* set = add_method("LFoo;.set:(I)V", R"((
    (load-param v0)
    (sput v0 "LFoo;.f:I")
    (return-void)
  ))");
  add_method("LFoo;.handle_get:()I", std::string(R"((
    (const-method-handle static-get "LFoo;.f:I")
    (move-result-pseudo-object v0)
    (invoke-polymorphic (v0) ")") + kInvokeExact +
                                         R"(" "()I")
    (move-result v1)
    (return v1)
  ))");

  run_remove_unused_fields();

  EXPECT_TRUE(has_field_insn(set));
}

// A static-put method handle writes the field, so its reads stay.
TEST_F(FieldOpTrackerMethodHandleTest, written_only_through_handle) {
  auto* get = add_method("LFoo;.get:()I", R"((
    (sget "LFoo;.f:I")
    (move-result-pseudo v0)
    (return v0)
  ))");
  add_handle_put();

  run_remove_unused_fields();

  EXPECT_TRUE(has_field_insn(get));
}

// A static-put method handle may write any value, not only the zero that the
// ordinary write stores, so the reads stay.
TEST_F(FieldOpTrackerMethodHandleTest, non_zero_written_only_through_handle) {
  add_method("LFoo;.clear:()V", R"((
    (const v0 0)
    (sput v0 "LFoo;.f:I")
    (return-void)
  ))");
  auto* get = add_method("LFoo;.get:()I", R"((
    (sget "LFoo;.f:I")
    (move-result-pseudo v0)
    (return v0)
  ))");
  add_handle_put();

  run_remove_unused_fields();

  EXPECT_TRUE(has_field_insn(get));
}

// A method handle can be called anywhere, so a write through one in the
// class initializer is not an initialization write.
TEST_F(FieldOpTrackerMethodHandleTest, handle_write_is_no_init_write) {
  m_cls->add_method(DexMethod::make_method("LFoo;.<clinit>:()V")
                        ->make_concrete(ACC_STATIC | ACC_CONSTRUCTOR,
                                        assembler::ircode_from_string(R"((
    (const-method-handle static-put "LFoo;.f:I")
    (move-result-pseudo-object v0)
    (sput-object v0 "LFoo;.h:Ljava/lang/invoke/MethodHandle;")
    (return-void)
  ))"),
                                        /* is_virtual */ false));
  Scope scope{m_cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto stats = field_op_tracker::analyze(scope);

  ASSERT_TRUE(stats.count(m_field));
  EXPECT_EQ(stats.at(m_field).writes, 1);
  EXPECT_EQ(stats.at(m_field).init_writes, 0);
}

// A static-get handle of `LChild;.f` reads the static `LFoo;.f`, as ART
// resolves it, not the instance field of that name that `LChild;` declares.
TEST_F(FieldOpTrackerMethodHandleTest, handle_read_counts_field_of_its_kind) {
  ClassCreator child(DexType::make_type("LChild;"));
  child.set_super(m_cls->get_type());
  auto* child_f =
      DexField::make_field("LChild;.f:I")->make_concrete(ACC_PUBLIC);
  child.add_field(child_f);
  auto* child_cls = child.create();
  add_method("LFoo;.handle_get:()V", R"((
    (const-method-handle static-get "LChild;.f:I")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  Scope scope{m_cls, child_cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto stats = field_op_tracker::analyze(scope);

  ASSERT_TRUE(stats.count(m_field));
  EXPECT_EQ(stats.at(m_field).reads, 1);
  EXPECT_FALSE(stats.count(child_f));
}
