/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "AccessMarking.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexTest.h"

namespace {

DexClass* make_class(std::string_view name) {
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(type::java_lang_Object());
  cc.set_access(ACC_PUBLIC);
  return cc.create();
}

DexMethod* add_method(DexClass* cls,
                      const std::string& spec,
                      DexAccessFlags access,
                      bool is_virtual,
                      const std::string& code) {
  auto* m = DexMethod::make_method(spec)->make_concrete(
      access, assembler::ircode_from_string(code), is_virtual);
  cls->add_method(m);
  return m;
}

void run_access_marking(const std::vector<DexClass*>& classes) {
  AccessMarkingPass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  DexStore store("classes");
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  manager.run_passes(stores, config);
}

// Holds `handle` and calls it with an instance of LA;.
std::string call_handle_code(const std::string& handle) {
  return R"((
    (load-param-object v1)
    (const-method-handle )" +
         handle + R"()
    (move-result-pseudo-object v0)
    (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LA;)V")
    (return-void)
  ))";
}

constexpr const char* kReturnVoid = "((load-param-object v0) (return-void))";

} // namespace

class AccessMarkingMethodHandleTest : public RedexTest {};

// A method handle (tool-generated here) in another class calls the method, so
// the method stays accessible to that class.
TEST_F(AccessMarkingMethodHandleTest, method_called_by_handle_in_other_class) {
  auto* a = make_class("LA;");
  auto* name = add_method(a, "LA;.name:()V", ACC_PUBLIC, true, kReturnVoid);
  auto* b = make_class("LB;");
  add_method(b, "LB;.run:(LA;)V", ACC_PUBLIC | ACC_STATIC, false,
             call_handle_code(R"(invoke-instance "LA;.name:()V")"));

  run_access_marking({a, b});

  EXPECT_TRUE(is_public(name));
  EXPECT_TRUE(name->is_virtual());
}

// A method handle in the method's own class keeps working once the method is
// private, so the method is still privatized.
TEST_F(AccessMarkingMethodHandleTest, method_called_by_handle_in_same_class) {
  auto* a = make_class("LA;");
  auto* name = add_method(a, "LA;.name:()V", ACC_PUBLIC, true, kReturnVoid);
  add_method(a, "LA;.run:(LA;)V", ACC_PUBLIC | ACC_STATIC, false,
             call_handle_code(R"(invoke-instance "LA;.name:()V")"));

  run_access_marking({a});

  EXPECT_TRUE(is_private(name));
}
