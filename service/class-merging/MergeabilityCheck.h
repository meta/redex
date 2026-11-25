/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <map>
#include <vector>

#include "ConcurrentContainers.h"
#include "DexClass.h"

class DexMethodHandle;
class RefChecker;

namespace class_merging {

using TypeSet = std::set<const DexType*, dextypes_comparator>;

struct ModelSpec;

// A forwarding constructor `A.<init>(P) { super_ctor(this, P); }` that class
// merging gives a merged type A, for the super-type constructor `super_ctor`
// that relaxed inits of A invoke (see `constructor_analysis::RelaxedInit`).
struct RelaxedInitForwarder {
  DexMethod* super_ctor;
  // A's constructor with proto P, which is already such a forwarder, if any.
  DexMethod* existing_ctor;
};

// How relaxed inits instantiate a type.
struct RelaxedInits {
  // The forwarding constructors that merging the type requires, sorted by
  // super-type constructor.
  std::vector<RelaxedInitForwarder> forwarders;
  // The methods with such relaxed inits, sorted. The inlined constructor
  // bodies run there.
  std::vector<const DexMethod*> callers;
};

using RelaxedInitsByType =
    std::map<const DexType*, RelaxedInits, dextypes_comparator>;

// Number of types with a relaxed init that class merging cannot handle, by
// reason. Such a type is not merged.
struct RelaxedInitExclusions {
  // Redex does not generate the type tags, so the merged constructors do not
  // store the tag that a forwarding constructor passes.
  uint32_t type_tag_not_generated{0};
  // The invoked constructor does not resolve to a constructor of a super type,
  // or one constructor call initializes objects of different types.
  uint32_t unsupported{0};
  // The invoked constructor is external and neither public nor protected.
  uint32_t inaccessible{0};
  // The invoked constructor fails the RefChecker.
  uint32_t unsafe_refs{0};
  // Two invoked constructors share a proto, or the type already has a
  // constructor with that proto that is not their forwarder.
  uint32_t ctor_conflict{0};

  RelaxedInitExclusions& operator+=(const RelaxedInitExclusions& other) {
    type_tag_not_generated += other.type_tag_not_generated;
    unsupported += other.unsupported;
    inaccessible += other.inaccessible;
    unsafe_refs += other.unsafe_refs;
    ctor_conflict += other.ctor_conflict;
    return *this;
  }
};

struct Mergeability {
  TypeSet non_mergeables;
  RelaxedInitsByType relaxed_inits;
  RelaxedInitExclusions relaxed_init_exclusions;
};

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
  Mergeability get_mergeability();

 private:
  const Scope& m_scope;
  const ModelSpec& m_spec;
  const RefChecker& m_ref_checker;
  const TypeSet& m_generated;
  const UnorderedSet<DexType*>& m_const_class_safe_types;
  bool m_track_use_of_reflection;

  // Relaxed inits found in the scope, by instantiated type.
  struct RelaxedInitCalls {
    // nullptr stands for an invoked constructor that does not resolve.
    UnorderedSet<DexMethod*> super_ctors;
    UnorderedSet<const DexMethod*> callers;
    // A constructor call that initializes an object of this type also
    // initializes one of another type.
    bool shares_invoke{false};
  };
  ConcurrentMap<const DexType*, RelaxedInitCalls> m_relaxed_init_calls;

  void exclude_unsupported_cls_property(const RelaxedInitsByType& relaxed_inits,
                                        TypeSet& non_mergeables);
  void classify_relaxed_inits(Mergeability& mergeability);
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
