/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <sstream>

#include <boost/variant.hpp>

#include <sparta/AbstractDomain.h>
#include <sparta/DisjointUnionAbstractDomain.h>

#include "Debug.h"
#include "ObjectWithImmutAttr.h"
#include "SignedConstantDomain.h"
#include "SingletonObject.h"

// Forward declarations.
template <class IsObject, typename... Domains>
class DisjointUnionWithSignedConstantDomain;

template <class IsObject, typename... Domains>
std::ostream& operator<<(
    std::ostream&,
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>&);

/*
 * This is similar to DisjointUnionAbstractDomain, with the addition of taking
 * into account the relationship between NEZ and non-null objects.
 */
template <class IsObject, typename... Domains>
class DisjointUnionWithSignedConstantDomain final
    : public sparta::AbstractDomain<
          DisjointUnionWithSignedConstantDomain<IsObject, Domains...>> {

 public:
  DisjointUnionWithSignedConstantDomain()
      : m_variant(SignedConstantDomain::top()) {}

  template <typename Domain>
  // NOLINTNEXTLINE(google-explicit-constructor)
  /* implicit */ DisjointUnionWithSignedConstantDomain(Domain d)
      : m_variant(d) {}

  static DisjointUnionWithSignedConstantDomain top() {
    return DisjointUnionWithSignedConstantDomain(SignedConstantDomain::top());
  }

  static DisjointUnionWithSignedConstantDomain bottom() {
    return DisjointUnionWithSignedConstantDomain(
        SignedConstantDomain::bottom());
  }

  bool is_top() const {
    return boost::apply_visitor([](const auto& dom) { return dom.is_top(); },
                                this->m_variant);
  }

  bool is_bottom() const {
    return boost::apply_visitor([](const auto& dom) { return dom.is_bottom(); },
                                this->m_variant);
  }

  bool is_nez() const {
    auto* dom = boost::get<SignedConstantDomain>(&m_variant);
    return dom && dom->interval() == sign_domain::Interval::NEZ;
  }

  // Is it nez only and nothing more?
  bool is_nez_only() const {
    auto* dom = boost::get<SignedConstantDomain>(&m_variant);
    return dom && dom->is_nez_only();
  }

  bool is_zero() const {
    auto* dom = boost::get<SignedConstantDomain>(&m_variant);
    return dom && dom->interval() == sign_domain::Interval::EQZ;
  }

  bool is_object() const;

  bool is_singleton_object() const {
    auto dom = boost::get<SingletonObjectDomain>(&m_variant);
    return dom && !dom->is_top() && !dom->is_bottom();
  }

  bool is_object_with_immutable_attr() const {
    auto dom = boost::get<ObjectWithImmutAttrDomain>(&m_variant);
    return dom && !dom->is_top() && !dom->is_bottom();
  }

  void set_to_top() {
    boost::apply_visitor([](auto& dom) { dom.set_to_top(); }, this->m_variant);
  }

  void set_to_bottom() {
    boost::apply_visitor([](auto& dom) { dom.set_to_bottom(); },
                         this->m_variant);
  }

  bool leq(const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>&
               other) const;

  bool equals(const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>&
                  other) const;

  void join_with(
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other);

  void widen_with(
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>&
          other) {
    this->join_with(other);
  }

  void meet_with(
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other);

  void narrow_with(
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>&
          other) {
    this->meet_with(other);
  }

  /*
   * This will throw if the domain contained in the union differs from the
   * requested Domain.
   */
  template <typename Domain>
  Domain get() const {
    if (is_top()) {
      return Domain::top();
    }
    if (is_bottom()) {
      return Domain::bottom();
    }
    return boost::get<Domain>(m_variant);
  }

  template <typename Domain>
  std::optional<Domain> maybe_get() const {
    if (is_top()) {
      return Domain::top();
    }
    if (is_bottom()) {
      return Domain::bottom();
    }
    auto* dom = boost::get<Domain>(&m_variant);
    if (dom == nullptr) {
      return std::nullopt;
    }
    return *dom;
  }

  template <typename Domain>
  void apply(std::function<void(Domain*)> operation) {
    auto* dom = boost::get<Domain>(&m_variant);
    if (dom) {
      operation(dom);
    }
  }

  /*
   * Return a numeric index representing the current type, if any.
   */
  std::optional<int> which() const {
    if (is_top() || is_bottom()) {
      return std::nullopt;
    }
    return m_variant.which();
  }

  template <typename Visitor>
  static typename Visitor::result_type apply_visitor(
      const Visitor& visitor,
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& dom) {
    return boost::apply_visitor(visitor, dom.m_variant);
  }

  template <typename Visitor>
  static typename Visitor::result_type apply_visitor(
      const Visitor& visitor,
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& d1,
      const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& d2) {
    return boost::apply_visitor(visitor, d1.m_variant, d2.m_variant);
  }

  const boost::variant<SignedConstantDomain, Domains...>& variant() const {
    return m_variant;
  }

 private:
  // Check if all template parameters are true (see
  // https://stackoverflow.com/questions/28253399/check-traits-for-all-variadic-template-arguments/28253503#28253503)
  template <bool...>
  struct bool_pack;

  template <bool... v>
  using all_true = std::is_same<bool_pack<true, v...>, bool_pack<v..., true>>;

  static_assert(
      std::is_base_of<sparta::AbstractDomain<SignedConstantDomain>,
                      SignedConstantDomain>::value,
      "All members of the disjoint union must inherit from AbstractDomain");
  static_assert(
      all_true<(std::is_base_of<sparta::AbstractDomain<Domains>,
                                Domains>::value)...>::value,
      "All members of the disjoint union must inherit from AbstractDomain");

  boost::variant<SignedConstantDomain, Domains...> m_variant;
};

template <class IsObject, typename... Domains>
std::ostream& operator<<(
    std::ostream& o,
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& du) {
  o << "[SU] ";
  boost::apply_visitor([&o](const auto& dom) { o << dom; }, du.variant());
  return o;
}

template <class IsObject, typename... Domains>
void DisjointUnionWithSignedConstantDomain<IsObject, Domains...>::join_with(
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other) {
  if (this->is_bottom()) {
    this->m_variant = other.m_variant;
    return;
  }
  if (other.is_bottom()) {
    return;
  }
  auto nez = (this->is_nez() || this->is_object()) &&
             (other.is_nez() || other.is_object());
  boost::apply_visitor(sparta::duad_impl::join_visitor(), this->m_variant,
                       other.m_variant);
  if (this->is_top() && nez) {
    this->m_variant = SignedConstantDomain(sign_domain::Interval::NEZ);
  }
}

template <class IsObject, typename... Domains>
void DisjointUnionWithSignedConstantDomain<IsObject, Domains...>::meet_with(
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other) {
  if (this->is_top()) {
    this->m_variant = other.m_variant;
    return;
  }
  if (other.is_top()) {
    return;
  }
  // Non-null objects of custom object domains are compatible with NEZ, and
  // more specific.
  if (this->is_nez_only() && other.is_object()) {
    this->m_variant = other.m_variant;
    return;
  }
  if (other.is_nez_only() && this->is_object()) {
    return;
  }
  // SingletonObjectDomain and ObjectWithImmutAttrDomain both represent object
  // references and they have intersection.
  // Handle their meet operator specially.
  if ((this->is_singleton_object() && other.is_object_with_immutable_attr()) ||
      (other.is_singleton_object() && this->is_object_with_immutable_attr())) {
    this->m_variant = SignedConstantDomain(sign_domain::Interval::NEZ);
    return;
  }

  // Non-null objects of different custom object domains can never alias, so
  // they meet at bottom, which is the default meet implementation for
  // disjoint domains.
  boost::apply_visitor(sparta::duad_impl::meet_visitor(), this->m_variant,
                       other.m_variant);
}

template <class IsObject, typename... Domains>
bool DisjointUnionWithSignedConstantDomain<IsObject, Domains...>::leq(
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other)
    const {
  // A non-null object represents fewer possible values than the more general
  // NEZ
  if (other.is_nez_only() && this->is_object()) {
    return true;
  }
  return boost::apply_visitor(sparta::duad_impl::leq_visitor(), this->m_variant,
                              other.m_variant);
}

template <class IsObject, typename... Domains>
bool DisjointUnionWithSignedConstantDomain<IsObject, Domains...>::equals(
    const DisjointUnionWithSignedConstantDomain<IsObject, Domains...>& other)
    const {
  return boost::apply_visitor(sparta::duad_impl::equals_visitor(),
                              this->m_variant, other.m_variant);
}

template <class IsObject, typename... Domains>
bool DisjointUnionWithSignedConstantDomain<IsObject, Domains...>::is_object()
    const {
  return !this->is_top() && !this->is_bottom() &&
         boost::apply_visitor(IsObject(), this->m_variant);
}
