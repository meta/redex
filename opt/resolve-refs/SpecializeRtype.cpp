/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SpecializeRtype.h"

#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DexTypeEnvironment.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "Show.h"
#include "Trace.h"
#include "WorkQueue.h"

namespace mog = method_override_graph;

namespace resolve_refs {

void RtypeStats::print(PassManager* mgr) const {
  if (num_rtype_specialized == 0) {
    return;
  }
  TRACE(RESO, 1, "[ref reso] rtype specialized %zu",
        num_rtype_specialized.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized direct %zu",
        num_rtype_specialized_direct.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized virtual 1 %zu",
        num_rtype_specialized_virtual_1.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized virtual 1+ %zu",
        num_rtype_specialized_virtual_1p.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized virtual 10+ %zu",
        num_rtype_specialized_virtual_10p.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized virtual 100+ %zu",
        num_rtype_specialized_virtual_100p.load());
  TRACE(RESO, 1, "[ref reso] rtype specialized more override %zu",
        num_rtype_specialized_virtual_more_override.load());
  TRACE(RESO, 1, "[ref reso] rtype specialize virtual candidates %zu",
        num_virtual_candidates);
  mgr->incr_metric("num_rtype_specialized", num_rtype_specialized);
  mgr->incr_metric("num_rtype_specialized_direct",
                   num_rtype_specialized_direct);
  mgr->incr_metric("num_rtype_specialized_virtual_1",
                   num_rtype_specialized_virtual_1);
  mgr->incr_metric("num_rtype_specialized_virtual_1+",
                   num_rtype_specialized_virtual_1p);
  mgr->incr_metric("num_rtype_specialized_virtual_10+",
                   num_rtype_specialized_virtual_10p);
  mgr->incr_metric("num_rtype_specialized_virtual_100+",
                   num_rtype_specialized_virtual_100p);
  mgr->incr_metric("num_rtype_specialized_virtual_more_override+",
                   num_rtype_specialized_virtual_more_override);
  mgr->incr_metric("num_virtual_candidates", num_virtual_candidates);
}

namespace {

/*
 * Mirroring the similar checks we have in RemoveUnusedArgsPass.
 */
bool is_safe_to_specialize(const DexMethod* meth) {
  return can_delete(meth) && can_rename(meth) && !is_native(meth);
}

bool can_update_rtype_for(const SubtypeMaps& subtype_maps,
                          DexMethod* meth,
                          const DexProto* new_proto) {
  if (!is_safe_to_specialize(meth)) {
    return false;
  }
  if (has_signature_collision(subtype_maps, meth, new_proto)) {
    // Bail on collision.
    TRACE(RESO, 4, "specialize bail on proto collision w/ %s -> %s", SHOW(meth),
          SHOW(new_proto));
    return false;
  }
  return true;
}

bool can_update_rtype_for(const SubtypeMaps& subtype_maps,
                          DexMethod* meth,
                          const DexType* new_rtype) {
  DexProto* updated_proto =
      DexProto::make_proto(new_rtype, meth->get_proto()->get_args());
  return can_update_rtype_for(subtype_maps, meth, updated_proto);
}

bool can_update_rtype_for_list(const SubtypeMaps& subtype_maps,
                               const UnorderedBag<const DexMethod*>& meths,
                               const DexProto* new_proto) {
  for (const auto* m : UnorderedIterable(meths)) {
    auto* meth = const_cast<DexMethod*>(m);
    if (!can_update_rtype_for(subtype_maps, meth, new_proto)) {
      return false;
    }
  }
  return true;
}

/*
 * We want to make sure that all the global overrides share the same set of
 * common overriddens. If it's not the case, one of the candidate here might
 * have been rejected due to having too many overriddens.
 */
bool share_common_overriddens_size(
    const method_override_graph::Graph& override_graph,
    const UnorderedBag<const DexMethod*>& meths) {
  std::optional<size_t> num_overriddens;
  for (const auto* meth : UnorderedIterable(meths)) {
    auto overriddens = method_override_graph::get_overridden_methods(
        override_graph, meth, true);
    if (!num_overriddens) {
      num_overriddens = overriddens.size();
    } else if (*num_overriddens != overriddens.size()) {
      return false;
    }
  }
  return true;
}

void update_rtype_for(const SubtypeMaps& subtype_maps,
                      DexMethod* meth,
                      const DexType* new_rtype,
                      RtypeStats& stats,
                      bool rename_on_collision = false) {
  DexProto* updated_proto =
      DexProto::make_proto(new_rtype, meth->get_proto()->get_args());
  if (!can_update_rtype_for(subtype_maps, meth, updated_proto)) {
    return;
  }

  DexMethodSpec spec(nullptr, nullptr, updated_proto);
  meth->change(spec, rename_on_collision);
  TRACE(RESO, 4, "rtype specialized -> %s", SHOW(meth));
  stats.num_rtype_specialized++;
}

void update_rtype_unsafe_for(DexMethod* meth,
                             const DexType* new_rtype,
                             RtypeStats& stats) {
  DexProto* updated_proto =
      DexProto::make_proto(new_rtype, meth->get_proto()->get_args());
  DexMethodSpec spec(nullptr, nullptr, updated_proto);
  meth->change(spec, false);
  TRACE(RESO, 4, "rtype specialized -> %s", SHOW(meth));
  stats.num_rtype_specialized++;
}

bool update_rtype_for_list(const SubtypeMaps& subtype_maps,
                           const UnorderedBag<const DexMethod*>& meths,
                           const DexType* new_rtype,
                           RtypeStats& stats) {
  if (meths.empty()) {
    return true;
  }
  DexProto* updated_proto = DexProto::make_proto(
      new_rtype, (*unordered_any(meths))->get_proto()->get_args());

  for (const auto* m : UnorderedIterable(meths)) {
    auto* meth = const_cast<DexMethod*>(m);
    if (!can_update_rtype_for(subtype_maps, meth, updated_proto)) {
      return false;
    }
  }

  for (const auto* m : UnorderedIterable(meths)) {
    auto* meth = const_cast<DexMethod*>(m);
    update_rtype_unsafe_for(meth, new_rtype, stats);
  }

  return true;
}

} // namespace

void RtypeCandidates::collect_inferred_rtype(
    const DexMethod* meth,
    const DexTypeDomain& inferred_rtype,
    DexTypeDomain& curr_rtype) {
  // Method itself is not qualified for proto rtype update
  if (!is_safe_to_specialize(meth)) {
    return;
  }

  curr_rtype.join_with(inferred_rtype);
}

void RtypeCandidates::collect_specializable_rtype(
    const api::AndroidSDK* min_sdk_api,
    const XStoreRefs& xstores,
    const SubtypeMaps& subtype_maps,
    DexMethod* meth,
    const DexTypeDomain& rtype_domain) {
  if (rtype_domain.is_bottom() || rtype_domain.is_top()) {
    return;
  }
  DexType* rtype = meth->get_proto()->get_rtype();
  const auto better_rtype = rtype_domain.get_dex_type();
  if (!better_rtype || *better_rtype == type::java_lang_Object()) {
    return;
  }
  redex_assert(type::is_object(rtype));
  redex_assert(better_rtype);
  if (*better_rtype == rtype || type::is_array(rtype)) {
    return;
  }

  TRACE(RESO, 3, "collect rtype for %s inferred %s", SHOW(meth),
        SHOW(*better_rtype));
  auto* better_rtype_cls = type_class(*better_rtype);
  if ((better_rtype_cls != nullptr) && better_rtype_cls->is_external() &&
      !min_sdk_api->has_type(*better_rtype)) {
    return;
  }
  // Drop cross dex store ref from the current method. Make sure that all
  // collected candidates are free of illegal refs.
  if (xstores.illegal_ref(meth->get_class(), *better_rtype)) {
    return;
  }
  // `better_rtype` is a subtype of the exsting `rtype`.
  if (type::check_cast(*better_rtype, rtype) &&
      can_update_rtype_for(subtype_maps, meth, *better_rtype)) {
    m_rtype_candidates.emplace(meth, *better_rtype);
  }
}

bool RtypeSpecialization::shares_identical_rtype_candidate(
    DexMethod* meth, const DexType* better_rtype) const {
  if (type_class_internal(meth->get_class()) == nullptr) {
    // Cannot modify external method.
    return false;
  }
  if (meth->get_code() == nullptr) {
    // Interface methods w/ no code are not in the rtype_candidates map. Cross
    // dex store refs check was not done earlier.
    bool is_illegal_ref =
        m_xstores.illegal_ref(meth->get_class(), better_rtype);
    return !is_illegal_ref;
  }

  if (m_candidates.count(meth) == 0) {
    return false;
  }
  const auto* candidate_rtype = m_candidates.at(meth);
  return candidate_rtype == better_rtype;
}

bool RtypeSpecialization::share_common_rtype_candidate(
    const MethodToInferredReturnType& rtype_candidates,
    const UnorderedBag<const DexMethod*>& meths,
    const DexType* better_rtype) const {
  for (const auto* m : UnorderedIterable(meths)) {
    if (type_class_internal(m->get_class()) == nullptr) {
      // Cannot modify external method.
      return false;
    }
    if (m->get_code() == nullptr) {
      // Interface methods w/ no code are not in the rtype_candidates map. Cross
      // dex store refs check was not done earlier.
      if (m_xstores.illegal_ref(m->get_class(), better_rtype)) {
        return false;
      }
      continue;
    }
    auto* meth = const_cast<DexMethod*>(m);
    if (rtype_candidates.count(meth) == 0) {
      return false;
    }
    const auto* candidate_rtype = rtype_candidates.at(meth);
    if (candidate_rtype != better_rtype) {
      TRACE(RESO, 4, "overridden mismatch better rtype %s -> %s vs %s",
            SHOW(candidate_rtype), SHOW(candidate_rtype), SHOW(better_rtype));
      return false;
    }
  }

  return true;
}

void RtypeSpecialization::specialize_non_true_virtuals(
    const method_override_graph::Graph& override_graph,
    DexMethod* meth,
    const DexType* better_rtype,
    InsertOnlyConcurrentMap<DexMethod*, const DexType*>& virtual_roots,
    RtypeStats& stats) const {
  const auto& overridings =
      method_override_graph::get_overriding_methods(override_graph, meth, true);
  always_assert(overridings.empty());
  virtual_roots.emplace(meth, better_rtype);
  stats.num_rtype_specialized_direct++;
}

void RtypeSpecialization::specialize_true_virtuals(
    const SubtypeMaps& subtype_maps,
    const method_override_graph::Graph& override_graph,
    DexMethod* meth,
    const DexType* better_rtype,
    InsertOnlyConcurrentMap<DexMethod*, const DexType*>& virtual_roots,
    RtypeStats& stats) const {
  const auto& overridings =
      method_override_graph::get_overriding_methods(override_graph, meth, true);
  if (!overridings.empty()) {
    // If a candidate is overridden by another concrete method, we give up.
    // We try to avoid more complex cases here. We can potentially expand on
    // this.
    stats.num_rtype_specialized_virtual_more_override++;
    return;
  }
  const auto& overriddens =
      method_override_graph::get_overridden_methods(override_graph, meth, true);
  if (overriddens.size() > 1) {
    // Too many overriddens. Give up
    return;
  }
  if (overriddens.size() == 1) {
    // For now, we only focus on methods with one abstract overridden here.
    DexMethod* overridden = const_cast<DexMethod*>(*unordered_any(overriddens));
    if (!is_safe_to_specialize(overridden) || overridden->is_external()) {
      // Overridden has code or is external. Give up
      TRACE(RESO, 4, "specialize bail on more complex overridden %s",
            SHOW(overridden));
      return;
    }

    if (!shares_identical_rtype_candidate(overridden, better_rtype)) {
      // The overridden has to share the identical `better_rtype` to be
      // specialized
      return;
    }

    const auto& global_overridings =
        method_override_graph::get_overriding_methods(override_graph,
                                                      overridden, true);
    if (global_overridings.size() > 100) {
      stats.num_rtype_specialized_virtual_100p++;
      return;
    } else if (global_overridings.size() > 10) {
      stats.num_rtype_specialized_virtual_10p++;
      return;
    }
    if (global_overridings.size() > 1) {
      stats.num_rtype_specialized_virtual_1p++;
      if (can_update_rtype_for(subtype_maps, overridden, better_rtype) &&
          share_common_rtype_candidate(m_candidates, global_overridings,
                                       better_rtype) &&
          share_common_overriddens_size(override_graph, global_overridings)) {
        TRACE(RESO, 4, "global overrides %zu -> %s ", global_overridings.size(),
              SHOW(better_rtype));
        DexProto* updated_proto =
            DexProto::make_proto(better_rtype, meth->get_proto()->get_args());
        if (can_update_rtype_for_list(subtype_maps, global_overridings,
                                      updated_proto)) {
          virtual_roots.emplace(overridden, better_rtype);
        }
      }
      return;
    }
    TRACE(RESO, 3, "specialize virtual 1 overridden %s w/ rtype %s", SHOW(meth),
          SHOW(better_rtype));
    if (can_update_rtype_for(subtype_maps, overridden, better_rtype) &&
        can_update_rtype_for(subtype_maps, meth, better_rtype)) {
      stats.num_rtype_specialized_virtual_1++;
      virtual_roots.emplace(overridden, better_rtype);
      TRACE(RESO, 3, "root virtual 1 overridden %s w/ rtype %s",
            SHOW(overridden), SHOW(better_rtype));
    }
  } else {
    not_reached_log("true virtual w/ 0 overridden & 0 overridding %s",
                    SHOW(meth));
  }
}

void RtypeSpecialization::specialize_rtypes(const Scope& scope,
                                            const SubtypeMaps& subtype_maps) {
  Timer t("specialize_rtype");
  const auto& override_graph = method_override_graph::build_graph(scope);
  InsertOnlyConcurrentMap<DexMethod*, const DexType*> virtual_roots;

  // Preprocess the candidates to cut down the size of candidates.
  // The main logic is filtering out complex virtual scopes that we choose not
  // to touch.
  auto process_candidates =
      [&](const std::pair<DexMethod*, const DexType*>& pair) {
        auto* meth = pair.first;
        const auto* better_rtype = const_cast<DexType*>(pair.second);

        if (!meth->is_virtual()) {
          // Simple direct methods. Fall through to 2nd step.
        } else if (!method_override_graph::is_true_virtual(*override_graph,
                                                           meth)) {
          // Non true virtual methods.
          TRACE(RESO, 4, "specialize non true virtual %s w/ rtype %s",
                SHOW(meth), SHOW(better_rtype));
          specialize_non_true_virtuals(*override_graph, meth, better_rtype,
                                       virtual_roots, m_stats);
        } else {
          specialize_true_virtuals(subtype_maps, *override_graph, meth,
                                   better_rtype, virtual_roots, m_stats);
        }
      };

  workqueue_run<std::pair<DexMethod*, const DexType*>>(process_candidates,
                                                       m_candidates);

  // Update direct targets.
  for (const auto& pair : m_candidates) {
    auto* meth = pair.first;
    if (meth->is_virtual()) {
      continue;
    }
    const auto* better_rtype = pair.second;
    update_rtype_for(subtype_maps, meth, better_rtype, m_stats);
    TRACE(RESO, 4, "specialize direct %s w/ rtype %s", SHOW(meth),
          SHOW(better_rtype));
    m_stats.num_rtype_specialized_direct++;
  }

  // Sort and update virtual targets.
  m_stats.num_virtual_candidates = virtual_roots.size();
  std::vector<DexMethod*> virtuals_lst;
  for (auto& pair : UnorderedIterable(virtual_roots)) {
    virtuals_lst.push_back(pair.first);
  }
  std::sort(virtuals_lst.begin(), virtuals_lst.end(), compare_dexmethods);

  for (auto* root : virtuals_lst) {
    const auto* better_rtype = virtual_roots.at(root);
    const auto& overrides = method_override_graph::get_overriding_methods(
        *override_graph, root, true);
    auto* new_proto =
        DexProto::make_proto(better_rtype, root->get_proto()->get_args());
    // Check the root before changing its overrides, so that a group is
    // either changed as a whole or not at all.
    if (can_update_rtype_for(subtype_maps, root, new_proto) &&
        update_rtype_for_list(subtype_maps, overrides, better_rtype, m_stats)) {
      update_rtype_unsafe_for(root, better_rtype, m_stats);
    }
  }
}

} // namespace resolve_refs
