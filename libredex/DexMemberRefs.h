/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/functional/hash.hpp>
#include <string>
#include <string_view>
#include <vector>

class DexType;
class DexString;
class DexProto;

/**
 * A specification for a method in order to look it up in the global cache
 * or to create it. Also used to modify an existing method reference.
 */
struct DexMethodSpec {
  /* Method related members */
  DexType* cls = nullptr;
  const DexString* name = nullptr;
  DexProto* proto = nullptr;
  DexMethodSpec() = default;
  DexMethodSpec(DexType* c, const DexString* n, DexProto* p)
      : cls(c), name(n), proto(p) {}

  bool operator==(const DexMethodSpec& r) const {
    return cls == r.cls && name == r.name && proto == r.proto;
  }
};

/**
 * A specification for a field in order to look it up in the global cache
 * or to create it. Also used to modify an existing field reference.
 */
struct DexFieldSpec {
  /* Field related members */
  DexType* cls = nullptr;
  const DexString* name = nullptr;
  DexType* type = nullptr;

  DexFieldSpec() = default;
  DexFieldSpec(DexType* c, const DexString* n, DexType* t)
      : cls(c), name(n), type(t) {}

  bool operator==(const DexFieldSpec& r) const {
    return cls == r.cls && name == r.name && type == r.type;
  }
};

namespace dex_member_refs {

struct FieldDescriptorTokens {
  std::string_view cls;
  std::string_view name;
  std::string_view type;
  bool operator==(const FieldDescriptorTokens& fdt) const {
    return cls == fdt.cls && name == fdt.name && type == fdt.type;
  }
};

struct MethodDescriptorTokens {
  std::string_view cls;
  std::string_view name;
  std::vector<std::string_view> args;
  std::string_view rtype;
  bool operator==(const MethodDescriptorTokens& mdt) const {
    return cls == mdt.cls && name == mdt.name && args == mdt.args &&
           rtype == mdt.rtype;
  }
};

struct ProtoDescriptorTokens {
  std::vector<std::string_view> args;
  std::string_view rtype;
};

FieldDescriptorTokens parse_field(std::string_view);

// Parses a prototype such as "(I[Ljava/lang/String;)V".
ProtoDescriptorTokens parse_proto(std::string_view);

// When `kCheckFormat` = true, syntactical issues in the string
// will lead to asserts, i.e., throws.
template <bool kCheckFormat = false>
MethodDescriptorTokens parse_method(std::string_view);

} // namespace dex_member_refs

namespace std {

template <>
struct hash<DexMethodSpec> {
  size_t operator()(const DexMethodSpec& r) const {
    size_t seed = boost::hash<DexType*>()(r.cls);
    boost::hash_combine(seed, r.name);
    boost::hash_combine(seed, r.proto);
    return seed;
  }
};

template <>
struct hash<DexFieldSpec> {
  size_t operator()(const DexFieldSpec& r) const {
    size_t seed = boost::hash<DexType*>()(r.cls);
    boost::hash_combine(seed, r.name);
    boost::hash_combine(seed, r.type);
    return seed;
  }
};

template <>
struct hash<dex_member_refs::FieldDescriptorTokens> {
  size_t operator()(const dex_member_refs::FieldDescriptorTokens& fdt) const {
    size_t seed = boost::hash<std::string_view>()(fdt.cls);
    boost::hash_combine(seed, fdt.name);
    boost::hash_combine(seed, fdt.type);
    return seed;
  }
};

template <>
struct hash<dex_member_refs::MethodDescriptorTokens> {
  size_t operator()(const dex_member_refs::MethodDescriptorTokens& mdt) const {
    size_t seed = boost::hash<std::string_view>()(mdt.cls);
    boost::hash_combine(seed, mdt.name);
    boost::hash_combine(seed, mdt.args);
    boost::hash_combine(seed, mdt.rtype);
    return seed;
  }
};

} // namespace std
