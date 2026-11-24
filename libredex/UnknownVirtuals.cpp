/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <array>
#include <string_view>

#include "UnknownVirtuals.h"

namespace {

// add any type on which an access is allowed and safe without accessibility
// issues
constexpr std::array<std::string_view, 10> safe_types_on_refs{
    "Ljava/lang/Object;",        "Ljava/lang/String;",  "Ljava/lang/Enum;",
    "Ljava/lang/StringBuilder;", "Ljava/lang/Boolean;", "Ljava/lang/Class;",
    "Ljava/lang/Long;",          "Ljava/lang/Integer;", "Landroid/os/Bundle;",
    "Ljava/nio/ByteBuffer;"};

// The checks below compare type names, not DexType pointers: a DexType belongs
// to one RedexContext, and a pointer kept from an earlier one no longer names
// the type it was kept for.

/**
 * If the type is a known final type or a well known type with no protected
 * methods the invocation is ok and can be optimized.
 * The problem here is that we don't have knowledge of all the types known
 * to the app and so we cannot determine whether the method was public or
 * protected. When public the optimization holds otherwise it's not always
 * possible to optimize and we conservatively give up.
 */
bool type_ok(const DexType* type) {
  if (type == nullptr) {
    return false;
  }
  return std::find(safe_types_on_refs.begin(), safe_types_on_refs.end(),
                   type->str()) != safe_types_on_refs.end();
}

/**
 * If the method is a known public method over a known public class
 * the optimization is safe.
 * Following is a short list of safe methods that are called with frequency
 * and are optimizable.
 */
bool is_method_known_to_be_public_helper(const DexType* type,
                                         DexMethodRef* meth) {
  if (type == nullptr) {
    return false;
  }
  auto type_name = type->str();
  auto meth_name = meth->get_name()->str();
  if (type_name == "Landroid/view/View;") {
    return meth_name == "getContext" || meth_name == "findViewById" ||
           meth_name == "setVisibility";
  }
  if (type_name == "Lcom/google/common/collect/ImmutableList;" ||
      type_name == "Ljava/util/ArrayList;") {
    return meth_name == "get" || meth_name == "isEmpty" ||
           meth_name == "size" || meth_name == "add";
  }
  if (type_name == "Landroid/content/Context;") {
    return meth_name == "getResources";
  }
  if (type_name == "Landroid/content/res/Resources;") {
    return meth_name == "getString";
  }
  if (type_name == "Landroid/view/LayoutInflater;") {
    return meth_name == "inflate";
  }
  if (type_name == "Landroid/view/ViewGroup;") {
    return meth_name == "getContext";
  }
  return false;
}

} // namespace

namespace unknown_virtuals {

bool is_method_known_to_be_public(DexMethodRef* method) {
  // if it's not known to redex but it's a common java/android API method
  if (is_method_known_to_be_public_helper(method->get_class(), method)) {
    return true;
  }
  const auto* type = method->get_class();
  if (type_ok(type)) {
    return true;
  }

  // the method ref is bound to a type known to redex but the method does
  // not exist in the hierarchy known to redex. Essentially the method
  // is from an external type i.e. A.equals(Object)
  auto* cls = type_class(type);
  while (cls != nullptr) {
    type = cls->get_super_class();
    cls = type_class(type);
  }
  return type_ok(type) || is_method_known_to_be_public_helper(type, method);
}

} // namespace unknown_virtuals
