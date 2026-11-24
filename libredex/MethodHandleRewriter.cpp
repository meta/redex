/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodHandleRewriter.h"

#include <boost/functional/hash.hpp>
#include <memory>

#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "IRInstruction.h"
#include "RedexContext.h"

namespace {

const void* member_of(const DexMethodHandle& handle) {
  if (DexMethodHandle::isInvokeType(handle.type())) {
    return handle.methodref();
  }
  return handle.fieldref();
}

// The value of `key` in `map`: the one already there, or else `candidate`,
// which is then published. Of threads racing for one key, one publishes.
template <typename Map, typename Key, typename T, typename Publish>
T* get_or_publish(Map& map,
                  const Key& key,
                  std::unique_ptr<T> candidate,
                  const Publish& publish) {
  auto [value, inserted] = map.emplace(key, candidate.get());
  if (inserted) {
    publish(candidate.release());
  }
  return *value;
}

} // namespace

size_t MethodHandleRewriter::HandleKeyHash::operator()(
    const HandleKey& key) const {
  size_t seed = 0;
  boost::hash_combine(seed, key.original);
  boost::hash_combine(seed, key.type);
  boost::hash_combine(seed, key.member);
  return seed;
}

size_t MethodHandleRewriter::CallSiteKeyHash::operator()(
    const CallSiteKey& key) const {
  size_t seed = 0;
  boost::hash_combine(seed, key.original);
  boost::hash_range(seed, key.values.begin(), key.values.end());
  return seed;
}

bool MethodHandleRewriter::rewrite(IRInstruction* insn,
                                   const DexMethod* holder) {
  if (insn->has_methodhandle()) {
    auto* handle = insn->get_methodhandle();
    auto* replacement = replace(handle, holder);
    insn->set_methodhandle(replacement);
    return replacement != handle;
  }
  if (insn->has_callsite()) {
    auto* callsite = insn->get_callsite();
    auto* replacement = replace(callsite, holder);
    insn->set_callsite(replacement);
    return replacement != callsite;
  }
  return false;
}

DexMethodHandle* MethodHandleRewriter::replace(DexMethodHandle* handle,
                                               const DexMethod* holder) {
  if (!m_mappings.handle) {
    return handle;
  }
  auto value = m_mappings.handle(handle, holder);
  if (!value) {
    return handle;
  }
  HandleKey key{handle, value->type(), member_of(*value)};
  if (key.type == handle->type() && key.member == member_of(*handle)) {
    return handle;
  }
  if (const auto* replacement = m_handles.get(key)) {
    return *replacement;
  }
  return get_or_publish(m_handles, key,
                        std::make_unique<DexMethodHandle>(*value),
                        [](DexMethodHandle* replacement) {
                          g_redex->publish_methodhandle(replacement);
                        });
}

DexType* MethodHandleRewriter::replace(DexType* type) const {
  return m_mappings.class_type ? m_mappings.class_type(type) : type;
}

DexProto* MethodHandleRewriter::replace(DexProto* proto) const {
  return m_mappings.method_type ? m_mappings.method_type(proto) : proto;
}

DexCallSite* MethodHandleRewriter::replace(DexCallSite* callsite,
                                           const DexMethod* holder) {
  const auto& args = callsite->args();
  CallSiteKey key{callsite, {}};
  key.values.reserve(2 + args.size());
  auto* bootstrap = replace(callsite->method_handle(), holder);
  auto* method_type = replace(callsite->method_type());
  bool changed = bootstrap != callsite->method_handle() ||
                 method_type != callsite->method_type();
  key.values.push_back(bootstrap);
  key.values.push_back(method_type);
  // Each argument that can change contributes what it becomes; others nullptr.
  for (const auto& arg : args) {
    if (const auto* handle_arg =
            dynamic_cast<const DexEncodedValueMethodHandle*>(arg.get())) {
      auto* handle = handle_arg->methodhandle();
      auto* replacement = replace(handle, holder);
      changed |= replacement != handle;
      key.values.push_back(replacement);
    } else if (const auto* type_arg =
                   dynamic_cast<const DexEncodedValueType*>(arg.get())) {
      auto* type = type_arg->type();
      auto* replacement = replace(type);
      changed |= replacement != type;
      key.values.push_back(replacement);
    } else if (const auto* proto_arg =
                   dynamic_cast<const DexEncodedValueMethodType*>(arg.get())) {
      auto* proto = proto_arg->proto();
      auto* replacement = replace(proto);
      changed |= replacement != proto;
      key.values.push_back(replacement);
    } else {
      key.values.push_back(nullptr);
    }
  }
  if (!changed) {
    return callsite;
  }
  if (const auto* replacement = m_callsites.get(key)) {
    return *replacement;
  }
  std::vector<std::unique_ptr<DexEncodedValue>> new_args;
  new_args.reserve(args.size());
  for (size_t i = 0; i < args.size(); ++i) {
    // The values pushed above, as their own types again.
    auto* value = const_cast<void*>(key.values[2 + i]);
    auto evtype = args[i]->evtype();
    if (evtype == DEVT_METHOD_HANDLE) {
      new_args.push_back(std::make_unique<DexEncodedValueMethodHandle>(
          static_cast<DexMethodHandle*>(value)));
    } else if (evtype == DEVT_TYPE) {
      new_args.push_back(
          std::make_unique<DexEncodedValueType>(static_cast<DexType*>(value)));
    } else if (evtype == DEVT_METHOD_TYPE) {
      new_args.push_back(std::make_unique<DexEncodedValueMethodType>(
          static_cast<DexProto*>(value)));
    } else {
      new_args.push_back(args[i]->clone());
    }
  }
  return get_or_publish(
      m_callsites, key,
      std::make_unique<DexCallSite>(bootstrap, callsite->method_name(),
                                    method_type, std::move(new_args)),
      [](DexCallSite* replacement) { g_redex->publish_callsite(replacement); });
}
