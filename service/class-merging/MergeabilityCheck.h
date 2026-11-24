/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexClass.h"

class DexMethodHandle;
class RefChecker;

namespace class_merging {

using TypeSet = std::set<const DexType*, dextypes_comparator>;

struct ModelSpec;

class MergeabilityChecker {
 public:
  MergeabilityChecker(const Scope& scope,
                      const ModelSpec& spec,
                      const RefChecker& ref_checker,
                      const TypeSet& generated);
  /**
   * Try to identify types referenced by operations that Class Merging does not
   * support. Such operations include reflections, instanceof checks on
   * no-type-tag shapes.
   * Ideally, part of the checks we perform below should be enforced at Java
   * source level. That is we should restrict such use cases on the generated
   * Java classes. As a result, we can make those generated classes easier to
   * optimize by Class Merging.
   */
  TypeSet get_non_mergeables();

 private:
  const Scope& m_scope;
  const ModelSpec& m_spec;
  const RefChecker& m_ref_checker;
  const TypeSet& m_generated;
  const UnorderedSet<DexType*>& m_const_class_safe_types;
  bool m_track_use_of_reflection;

  void exclude_unsupported_cls_property(TypeSet& non_mergeables);
  void exclude_unsupported_bytecode(TypeSet& non_mergeables);
  void exclude_method_handle_refs(TypeSet& non_mergeables);
  void exclude_unsupported_static_value_method_handles(TypeSet& non_mergeables);
  void exclude_static_fields(TypeSet& non_mergeables);
  void exclude_unsafe_sdk_and_store_refs(TypeSet& non_mergeables);
  void exclude_unhandled_anno_refs(TypeSet& non_mergeables);
  void collect_referenced_mergeable_types(const DexEncodedValue* ev,
                                          TypeSet& non_mergeables,
                                          const DexType* anno_type,
                                          const char* context);

  TypeSet exclude_unsupported_bytecode_refs_for(DexMethod* method);
  // `holder` is the method whose code holds `method_handle`, or nullptr when
  // a static field value holds it.
  void exclude_unsupported_method_handle_refs(
      const DexMethodHandle* method_handle,
      const DexMethod* holder,
      TypeSet& non_mergeables);
};

} // namespace class_merging
