/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexTypeEnvironment.h"

#include <ostream>
#include <vector>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "Show.h"

namespace dtv_impl {

bool implements(const DexClass* cls, const DexType* intf) {
  if (is_interface(cls)) {
    return false;
  }
  for (const auto* const interface : *cls->get_interfaces()) {
    if (interface == intf) {
      return true;
    }
  }

  auto* super_type = cls->get_super_class();
  auto* super_cls = type_class(cls->get_super_class());
  if ((super_cls != nullptr) && super_type != type::java_lang_Object()) {
    return implements(super_cls, intf);
  }
  return false;
}

/*
 * Every interface `type` implements: those its class declares, everything
 * those extend, and the same again for each super class. `implements` above
 * walks only the super class chain, so it cannot answer this.
 *
 * TypeSystem::get_implemented_interfaces computes the same thing, but building
 * a TypeSystem builds ClassScopes, which is far too expensive to do per join.
 */
void collect_interfaces(const DexType* type,
                        UnorderedSet<const DexType*>* out) {
  for (const auto* cls = type_class(type); cls != nullptr;
       cls = type_class(cls->get_super_class())) {
    for (const auto* const intf : *cls->get_interfaces()) {
      // Guard against re-walking a shared ancestor of a diamond.
      if (out->insert(intf).second) {
        collect_interfaces(intf, out);
      }
    }
  }
}

/*
 * The most specific interfaces both `l` and `r` implement. Empty means they
 * share none. More than one means they share several incomparable ones, so the
 * least upper bound is an intersection type that a single DexType cannot hold;
 * the caller must not collapse that case to Object.
 */
std::vector<const DexType*> find_common_interfaces(const DexType* l,
                                                   const DexType* r) {
  UnorderedSet<const DexType*> l_intfs;
  // An interface is castable to itself, and `collect_interfaces` reports only
  // what a type DECLARES. Without this the candidate set for an interface
  // operand is empty and the intersection below is silently one-sided.
  const auto* l_cls = type_class(l);
  if ((l_cls != nullptr) && is_interface(l_cls)) {
    l_intfs.insert(l);
  }
  collect_interfaces(l, &l_intfs);
  std::vector<const DexType*> shared;
  for (const auto* intf : UnorderedIterable(l_intfs)) {
    // check_cast walks r's super classes and its interface graph, so r's own
    // set does not need collecting.
    if (type::check_cast(r, intf)) {
      shared.push_back(intf);
    }
  }
  // Drop any candidate that a more specific candidate already implies, so that
  // e.g. sharing both Collection and Iterable still resolves, to Collection.
  std::vector<const DexType*> most_specific;
  for (const auto* intf : shared) {
    bool subsumed = false;
    for (const auto* other : shared) {
      if (other != intf && type::check_cast(other, intf)) {
        subsumed = true;
        break;
      }
    }
    if (!subsumed) {
      most_specific.push_back(intf);
    }
  }
  return most_specific;
}

/*
 * Try to find type on `l`'s parent chain that is also a parent of `r`.
 */
const DexType* find_common_super_class(const DexType* l, const DexType* r) {
  always_assert(l && r);
  if (l == r) {
    return l;
  }
  const auto* parent = l;
  while (parent != nullptr) {
    if (type::is_subclass(parent, r)) {
      return parent;
    }
    auto* parent_cls = type_class(parent);
    if (parent_cls == nullptr) {
      break;
    }
    parent = parent_cls->get_super_class();
  }
  return nullptr;
}

const DexType* find_common_type(const DexType* l, const DexType* r) {
  const DexClass* l_cls = type_class(l);
  const DexClass* r_cls = type_class(r);

  // One is interface, and the other implements it. This is answered from the
  // implementing class alone: it names the interface in its own interface
  // list, so the interface's own DexClass is not needed. Framework interfaces
  // often have none -- Lorg/apache/http/HttpEntity; left the Android SDK at
  // API 23 -- and bailing on that would send an answerable join to Top.
  if ((r_cls != nullptr) && !is_interface(r_cls) && implements(r_cls, l)) {
    return l;
  }
  if ((l_cls != nullptr) && !is_interface(l_cls) && implements(l_cls, r)) {
    return r;
  }

  if ((l_cls == nullptr) || (r_cls == nullptr)) {
    return nullptr;
  }

  const auto* parent = find_common_super_class(l, r);
  if ((parent == nullptr) || (type_class(parent) == nullptr)) {
    return nullptr;
  }
  if (parent != type::java_lang_Object()) {
    return parent;
  }

  // Reaching Object means the super class chain found nothing, but the chain
  // never looks at what the two operands both implement. That is often where
  // the real answer is: three classes that all implement HttpEntity and extend
  // Object share HttpEntity, not Object.
  auto shared = find_common_interfaces(l, r);
  if (shared.size() == 1) {
    return shared.front();
  }
  if (!shared.empty()) {
    // Several incomparable shared interfaces. The bound is an intersection
    // type, so there is no single answer and Top is the honest one.
    return nullptr;
  }

  // Nothing shared at all, so Object is genuinely the least upper bound.
  // Reporting it only in that case is load bearing: IRTypeChecker's
  // check_cast_helper treats Ljava/lang/Object; as an exact type and rejects
  // it against every other target, so handing it back for a merge we simply
  // failed to resolve turns a legal program into a type error.
  return parent;
}

/*
 * Only covers the simple cases here:
 * 1. Reference type arrays with the same depth level => common type array with
 * the same level
 * 2. If there's primitive array or the levels don't match => Top.
 */
const DexType* find_common_array_type(const DexType* l, const DexType* r) {
  uint32_t l_dim = type::get_array_level(l);
  uint32_t r_dim = type::get_array_level(r);

  bool has_primitive = false;
  auto* l_elem_type = type::make_array_element_type(l);
  auto* r_elem_type = type::make_array_element_type(r);
  if (type::is_primitive(l_elem_type) || type::is_primitive(r_elem_type)) {
    has_primitive = true;
  }
  if (!has_primitive && l_dim == r_dim) {
    const auto* common_element_type =
        find_common_type(l_elem_type, r_elem_type);
    return common_element_type != nullptr
               ? type::make_array_type(common_element_type, l_dim)
               : nullptr;
  }

  return nullptr;
}

/*
 * Partially mimicking the Dalvik bytecode structural verifier:
 * https://android.googlesource.com/platform/dalvik/+/android-cts-4.4_r4/vm/analysis/CodeVerify.cpp#2462
 */
sparta::AbstractValueKind DexTypeValue::join_with(const DexTypeValue& other) {
  if (equals(other)) {
    return kind();
  }
  if (is_none()) {
    m_dex_type = other.get_dex_type();
    return sparta::AbstractValueKind::Value;
  } else if (other.is_none()) {
    return sparta::AbstractValueKind::Value;
  }

  const auto* l = get_dex_type();
  const auto* r = other.get_dex_type();
  if (type::is_array(l) && type::is_array(r)) {
    const auto* common_array_type = find_common_array_type(l, r);
    if (common_array_type != nullptr) {
      m_dex_type = common_array_type;
      return sparta::AbstractValueKind::Value;
    }
  } else {
    const auto* common_type = find_common_type(l, r);
    if (common_type != nullptr) {
      m_dex_type = common_type;
      return sparta::AbstractValueKind::Value;
    }
  }

  // Give up. Rewrite to top.
  clear();
  return sparta::AbstractValueKind::Top;
}

} // namespace  dtv_impl

std::ostream& operator<<(std::ostream& output, const DexType* dex_type) {
  output << show(dex_type);
  return output;
}

bool SmallSetDexTypeDomain::leq(const SmallSetDexTypeDomain& other) const {
  if (is_bottom()) {
    return true;
  }
  if (other.is_bottom()) {
    return false;
  }
  if (other.is_top()) {
    return true;
  }
  if (is_top()) {
    return false;
  }
  return m_types.is_subset_of(other.m_types);
}

bool SmallSetDexTypeDomain::equals(const SmallSetDexTypeDomain& other) const {
  if (is_bottom()) {
    return other.is_bottom();
  }
  if (is_top()) {
    return other.is_top();
  }
  return m_types.equals(other.m_types);
}

void SmallSetDexTypeDomain::join_with(const SmallSetDexTypeDomain& other) {
  if (is_top() || other.is_bottom()) {
    return;
  }
  if (other.is_top()) {
    set_to_top();
    return;
  }
  if (is_bottom()) {
    m_kind = other.m_kind;
    m_types = other.m_types;
    return;
  }
  m_types.union_with(other.m_types);
  if (m_types.size() > MAX_SET_SIZE) {
    set_to_top();
  }
}

void SmallSetDexTypeDomain::widen_with(const SmallSetDexTypeDomain& other) {
  if (is_top() || other.is_bottom()) {
    return;
  }
  if (other.is_top()) {
    set_to_top();
    return;
  }
  if (is_bottom()) {
    m_kind = other.m_kind;
    m_types = other.m_types;
    return;
  }
  if (m_types.size() + other.m_types.size() > MAX_SET_SIZE) {
    set_to_top();
    return;
  }
  join_with(other);
}

std::ostream& operator<<(std::ostream& out, const SingletonDexTypeDomain& x) {
  using namespace sparta;
  switch (x.kind()) {
  case AbstractValueKind::Bottom: {
    out << "_|_";
    break;
  }
  case AbstractValueKind::Top: {
    out << "T";
    break;
  }
  case AbstractValueKind::Value: {
    auto type = x.get_dex_type();
    out << (type ? show(*type) : std::string("<NONE>"));
    break;
  }
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const SmallSetDexTypeDomain& x) {
  using namespace sparta;
  switch (x.kind()) {
  case sparta::AbstractValueKind::Bottom: {
    out << "_|_";
    break;
  }
  case sparta::AbstractValueKind::Top: {
    out << "T";
    break;
  }
  case sparta::AbstractValueKind::Value: {
    out << x.get_types();
    break;
  }
  }
  return out;
}
