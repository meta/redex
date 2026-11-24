/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexCallSite.h"

#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexMethodHandle.h"

void DexCallSite::gather_strings(std::vector<const DexString*>& lstring) const {
  lstring.emplace_back(m_linker_method_name);
  m_linker_method_type->gather_strings(lstring);
  for (const auto& ev : m_linker_method_args) {
    ev->gather_strings(lstring);
  }
}

void DexCallSite::gather_types(std::vector<const DexType*>& ltype) const {
  m_linker_method_type->gather_types(ltype);
  for (const auto& ev : m_linker_method_args) {
    ev->gather_types(ltype);
  }
}

void DexCallSite::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  lmethodhandle.push_back(m_linker_method_handle);
  for (const auto& ev : m_linker_method_args) {
    ev->gather_methodhandles(lmethodhandle);
  }
}

void DexCallSite::gather_methods(std::vector<DexMethodRef*>& lmethod) const {
  m_linker_method_handle->gather_methods(lmethod);
  for (const auto& ev : m_linker_method_args) {
    ev->gather_methods(lmethod);
  }
}

void DexCallSite::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  m_linker_method_handle->gather_fields(lfield);
  for (const auto& ev : m_linker_method_args) {
    ev->gather_fields(lfield);
  }
}

DexEncodedValueArray DexCallSite::as_encoded_value_array() const {
  auto aev = std::make_unique<std::vector<std::unique_ptr<DexEncodedValue>>>();
  aev->reserve(m_linker_method_args.size() + 3);

  aev->emplace_back(new DexEncodedValueMethodHandle(m_linker_method_handle));
  aev->emplace_back(new DexEncodedValueString(m_linker_method_name));
  aev->emplace_back(new DexEncodedValueMethodType(m_linker_method_type));
  for (const auto& arg : m_linker_method_args) {
    aev->emplace_back(arg->clone());
  }

  return DexEncodedValueArray(aev.release(), true);
}
