/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <list>
#include <vector>

class DexString;
class DexType;
class DexFieldRef;
class DexMethodRef;
class DexCallSite;
class DexProto;
class DexMethodHandle;

class Gatherable {
 protected:
  Gatherable() {}

  virtual ~Gatherable() {}

 public:
  virtual void gather_strings(
      std::vector<const DexString*>& /*lstring*/) const {}
  virtual void gather_types(std::vector<const DexType*>& /*ltype*/) const {}
  virtual void gather_fields(std::vector<DexFieldRef*>& /*lfield*/) const {}
  virtual void gather_methods(std::vector<DexMethodRef*>& /*lmethod*/) const {}
  virtual void gather_callsites(
      std::vector<DexCallSite*>& /*lcallsite*/) const {}
  virtual void gather_methodhandles(
      std::vector<DexMethodHandle*>& /*lmethodhandle*/) const {}
  // Protos referenced directly, not through a method, call site or method
  // handle.
  virtual void gather_protos(std::vector<DexProto*>& /*lproto*/) const {}
};
