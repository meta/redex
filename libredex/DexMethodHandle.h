/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexDefs.h"
#include "RedexContext.h"

#include <string>
#include <vector>

class DexType;

class DexMethodHandle {
  friend struct RedexContext;

 public:
  DexMethodHandle(MethodHandleType type, DexMethodRef* methodref);
  DexMethodHandle(MethodHandleType type, DexFieldRef* fieldref);

  MethodHandleType type() const { return m_type; }
  DexMethodRef* methodref() const;
  DexFieldRef* fieldref() const;

  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const;

  static bool isInvokeType(MethodHandleType type);

  // A new handle of `type` to `methodref` or `fieldref`, owned by `g_redex`.
  static DexMethodHandle* make_method_handle(MethodHandleType type,
                                             DexMethodRef* methodref);
  static DexMethodHandle* make_method_handle(MethodHandleType type,
                                             DexFieldRef* fieldref);

 private:
  MethodHandleType m_type;
  union {
    DexFieldRef* m_fieldref;
    DexMethodRef* m_methodref;
  };
};
