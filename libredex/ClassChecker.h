/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <string>

#include "ConcurrentContainers.h"
#include "DexClass.h"

/**
 * Describes the classes in `scope`, and the external classes, whose supertypes
 * the runtime refuses to link, or returns std::nullopt when there are none:
 *
 * - a superclass defined as an interface, or an implemented interface defined
 *   as a class (IncompatibleClassChangeError);
 * - an interface whose superclass is not java.lang.Object (ClassFormatError);
 * - a cycle of superclasses and superinterfaces (ClassCircularityError);
 * - a superclass declared final (VerifyError).
 *
 * Apart from an interface's superclass, which must be java.lang.Object, a
 * supertype without a definition is not an error: types missing from the
 * input are legitimate, and analyses handle them.
 *
 * These are the structural properties of the class hierarchy; ART checks more
 * when it links a class (access to the supertypes, for example).
 *
 * redex-all and the tools that load through Tool::init reject an input for
 * which this reports anything, so that analyses can rely on these properties
 * instead of each tolerating their violation.
 */
std::optional<std::string> check_class_hierarchy(const Scope& scope);

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
  std::optional<std::string> m_class_hierarchy_errors;
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
