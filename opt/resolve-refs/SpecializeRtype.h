/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <utility>

#include "DexClass.h"
#include "DexStore.h"
#include "FrameworkApi.h"
#include "Resolver.h"

class PassManager;
struct SubtypeMaps;
class DexTypeDomain;
class XStoreRefs;

namespace method_override_graph {
class Graph;
} // namespace method_override_graph

namespace resolve_refs {

using MethodToInferredReturnType =
    std::map<DexMethod*, const DexType*, dexmethods_comparator>;

struct RtypeStats {
  std::atomic<size_t> num_rtype_specialized = 0;
  std::atomic<size_t> num_rtype_specialized_direct = 0;
  std::atomic<size_t> num_rtype_specialized_virtual_1 = 0;
  std::atomic<size_t> num_rtype_specialized_virtual_1p = 0;
  std::atomic<size_t> num_rtype_specialized_virtual_10p = 0;
  std::atomic<size_t> num_rtype_specialized_virtual_100p = 0;
  std::atomic<size_t> num_rtype_specialized_virtual_more_override = 0;
  size_t num_virtual_candidates = 0;

  void print(PassManager* mgr) const;
};

class RtypeCandidates final {
 public:
  void collect_inferred_rtype(const DexMethod* meth,
                              const DexTypeDomain& inferred_rtype,
                              DexTypeDomain& curr_rtype);
  void collect_specializable_rtype(const api::AndroidSDK* min_sdk_api,
                                   const XStoreRefs& xstores,
                                   const SubtypeMaps& subtype_maps,
                                   DexMethod* meth,
                                   const DexTypeDomain& rtype_domain);
  const MethodToInferredReturnType& get_candidates() {
    return m_rtype_candidates;
  }
  RtypeCandidates& operator+=(const RtypeCandidates& that) {
    m_rtype_candidates.insert(that.m_rtype_candidates.begin(),
                              that.m_rtype_candidates.end());
    return *this;
  }

 private:
  MethodToInferredReturnType m_rtype_candidates;
};

class RtypeSpecialization final {
 public:
  explicit RtypeSpecialization(MethodToInferredReturnType candidates,
                               XStoreRefs xstores)
      : m_candidates(std::move(candidates)), m_xstores(std::move(xstores)) {}

  void specialize_rtypes(const Scope& scope, const SubtypeMaps& subtype_maps);
  void print_stats(PassManager* mgr) const { m_stats.print(mgr); }

 private:
  const MethodToInferredReturnType m_candidates;
  const XStoreRefs m_xstores;
  RtypeStats m_stats;

  void specialize_non_true_virtuals(
      const method_override_graph::Graph& override_graph,
      DexMethod* meth,
      const DexType* better_rtype,
      InsertOnlyConcurrentMap<DexMethod*, const DexType*>& virtual_roots,
      RtypeStats& stats) const;

  void specialize_true_virtuals(
      const SubtypeMaps& subtype_maps,
      const method_override_graph::Graph& override_graph,
      DexMethod* meth,
      const DexType* better_rtype,
      InsertOnlyConcurrentMap<DexMethod*, const DexType*>& virtual_roots,
      RtypeStats& stats) const;
  bool shares_identical_rtype_candidate(DexMethod* meth,
                                        const DexType* better_rtype) const;
  bool share_common_rtype_candidate(
      const MethodToInferredReturnType& rtype_candidates,
      const UnorderedBag<const DexMethod*>& meths,
      const DexType* better_rtype) const;
};

} // namespace resolve_refs
