/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "DexClass.h"
#include "IRAssembler.h"
#include "IRTemplate.h"
#include "RedexTest.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"

// Shared setup for class merging unit tests. Include it from only one source
// file per test target: `RedexTest.h` defines a global.

namespace class_merging_test {

inline constexpr std::string_view kCtor = R"(
  (method (public constructor) "$CLS.<init>:()V"
   (
    (load-param-object v0)
    (invoke-direct (v0) "$SUPER.<init>:()V")
    (return-void)
   )
  )
)";

inline constexpr std::string_view kVirtual = R"(
  (method (public) "$CLS.$NAME:()V"
   (
    (load-param-object v0)
    (return-void)
   )
  )
)";

inline DexMethod* add_method(DexClass* cls, const std::string& code) {
  auto* method = assembler::method_from_string(code);
  method->get_code()->build_cfg();
  cls->add_method(method);
  return method;
}

inline DexMethod* add_ctor(DexClass* cls) {
  const auto cls_name = cls->get_type()->str_copy();
  const auto super_name = cls->get_super_class()->str_copy();
  return add_method(cls,
                    ir(kCtor, {{"$CLS", cls_name}, {"$SUPER", super_name}}));
}

inline DexMethod* add_virtual(DexClass* cls, const std::string& name) {
  const auto cls_name = cls->get_type()->str_copy();
  return add_method(cls, ir(kVirtual, {{"$CLS", cls_name}, {"$NAME", name}}));
}

class ClassMergingTest : public RedexTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("LBase;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
  }

  DexClass* make_class(const char* name, DexType* super) {
    auto* cls = create_internal_class(DexType::make_type(name), super, {});
    m_scope.push_back(cls);
    return cls;
  }

  // A subclass of Base with a ctor and an override of Base.run(), either of
  // which can be marked hot.
  DexClass* make_mergeable(const std::string& name,
                           bool hot_ctor = false,
                           bool hot_run = false) {
    auto* cls = make_class(name.c_str(), m_base->get_type());
    auto* ctor = add_ctor(cls);
    auto* run = add_virtual(cls, "run");
    if (hot_ctor) {
      m_hot_methods.push_back(ctor);
    }
    if (hot_run) {
      m_hot_methods.push_back(run);
    }
    return cls;
  }

  Scope m_scope;
  DexClass* m_base{nullptr};
  std::vector<DexMethod*> m_hot_methods;
};

} // namespace class_merging_test
