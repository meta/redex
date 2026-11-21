/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexMethodHandle.h"
#include "Debug.h"
#include "DexAnnotation.h"

DexMethodHandle::DexMethodHandle(MethodHandleType type,
                                 DexMethodRef* methodref) {
  always_assert_log(isInvokeType(type),
                    "MethodHandleType %d invalid to use with methodref", type);
  m_type = type;
  m_methodref = methodref;
}

DexMethodHandle::DexMethodHandle(MethodHandleType type, DexFieldRef* fieldref) {
  always_assert_log(!isInvokeType(type),
                    "MethodHandleType %d invalid to use with fieldref", type);
  m_type = type;
  m_fieldref = fieldref;
}

DexMethodHandle* DexMethodHandle::make_method_handle(MethodHandleType type,
                                                     DexMethodRef* methodref) {
  auto* method_handle = new DexMethodHandle(type, methodref);
  g_redex->publish_methodhandle(method_handle);
  return method_handle;
}

DexMethodHandle* DexMethodHandle::make_method_handle(MethodHandleType type,
                                                     DexFieldRef* fieldref) {
  auto* method_handle = new DexMethodHandle(type, fieldref);
  g_redex->publish_methodhandle(method_handle);
  return method_handle;
}

DexMethodRef* DexMethodHandle::methodref() const {
  always_assert_log(isInvokeType(m_type),
                    "MethodHandleType %d invalid to use with methodref",
                    m_type);
  return m_methodref;
}

DexFieldRef* DexMethodHandle::fieldref() const {
  always_assert_log(!isInvokeType(m_type),
                    "MethodHandleType %d invalid to use with fieldref", m_type);
  return m_fieldref;
}

void DexMethodHandle::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  if (isInvokeType(m_type)) {
    lmethod.push_back(m_methodref);
  }
}

void DexMethodHandle::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  if (!isInvokeType(m_type)) {
    lfield.push_back(m_fieldref);
  }
}

bool DexMethodHandle::isInvokeType(MethodHandleType type) {
  switch (type) {
  case METHOD_HANDLE_TYPE_INVOKE_STATIC:
  case METHOD_HANDLE_TYPE_INVOKE_INSTANCE:
  case METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR:
  case METHOD_HANDLE_TYPE_INVOKE_DIRECT:
  case METHOD_HANDLE_TYPE_INVOKE_INTERFACE:
    return true;
  default:
    return false;
  }
}
