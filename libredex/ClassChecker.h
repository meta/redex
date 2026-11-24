/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConcurrentContainers.h"
#include "DexClass.h"

class ClassChecker {
 public:
  explicit ClassChecker();

  ClassChecker(const ClassChecker&) = delete;
  ClassChecker(ClassChecker&& other) = default;

  ClassChecker& operator=(const ClassChecker&) = delete;
  ClassChecker& operator=(ClassChecker&& other) = default;

  void init_setting(
      bool definition_check,
      const UnorderedSet<std::string>& definition_check_allowlist,
      const UnorderedSet<std::string>& definition_check_allowlist_prefixes,
      bool external_check,
      const UnorderedSet<std::string>& external_check_allowlist,
      const UnorderedSet<std::string>& external_check_allowlist_prefixes);

  void run(const Scope& scope);

  bool fail() const { return !m_good; }

  std::ostringstream print_failed_classes();

 private:
  bool m_good;
  bool m_external_check{false};
  bool m_definition_check{false};
  UnorderedSet<const DexType*> m_external_check_allowlist;
  UnorderedSet<const DexType*> m_definition_check_allowlist;
  UnorderedSet<std::string> m_external_check_allowlist_prefixes;
  UnorderedSet<std::string> m_definition_check_allowlist_prefixes;
  ConcurrentSet<const DexClass*> m_failed_classes_abstract_check;
  ConcurrentMap<const DexClass*, InsertOnlyConcurrentSet<const DexType*>>
      m_failed_classes_external_check;
  ConcurrentMap<const DexClass*, InsertOnlyConcurrentSet<const DexType*>>
      m_failed_classes_definition_check;
  // Methods which are incorrectly overriding final methods on a super.
  ConcurrentSet<const DexMethod*> m_failed_methods;
};
