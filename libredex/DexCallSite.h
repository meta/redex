/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <string>
#include <vector>

#include "DexAnnotation.h"

class DexEncodedValue;
class DexEncodedValueArray;
class DexFieldRef;
class DexIdx;
class DexMethod;
class DexMethodHandle;
class DexMethodRef;
class DexProto;
class DexString;
struct RedexContext;

class DexCallSite {
  friend struct RedexContext;

 public:
  DexCallSite(DexMethodHandle* linker_method_handle,
              const DexString* linker_method_name,
              DexProto* linker_method_type,
              std::vector<std::unique_ptr<DexEncodedValue>> linker_args)
      : m_linker_method_handle(linker_method_handle),
        m_linker_method_name(linker_method_name),
        m_linker_method_type(linker_method_type),
        m_linker_method_args(std::move(linker_args)) {}

  DexMethodHandle* method_handle() const { return m_linker_method_handle; }
  const DexString* method_name() const { return m_linker_method_name; }
  DexProto* method_type() const { return m_linker_method_type; }
  const std::vector<std::unique_ptr<DexEncodedValue>>& args() const {
    return m_linker_method_args;
  }

  void gather_strings(std::vector<const DexString*>& lstring) const;
  // The types the method type and the bootstrap arguments name, not those of
  // the methods and fields the method handles refer to.
  void gather_types(std::vector<const DexType*>& ltype) const;
  void gather_methodhandles(std::vector<DexMethodHandle*>& lmethodhandle) const;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const;

  DexEncodedValueArray as_encoded_value_array() const;

 private:
  DexMethodHandle* m_linker_method_handle;
  const DexString* m_linker_method_name;
  DexProto* m_linker_method_type;
  std::vector<std::unique_ptr<DexEncodedValue>> m_linker_method_args;
};
