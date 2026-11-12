/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResolveRefsPass.h"

#include <optional>

#include "ApiLevelChecker.h"
#include "ClassHierarchy.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "OptionalIO.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "SpecializeRtype.h"
#include "Trace.h"
#include "TypeInference.h"
#include "Walkers.h"
using namespace resolve_refs;

namespace impl {

struct RefStats {
  // simple_resolved is local ref resolution using Resolver with no additinoal
  // info.
  size_t num_mref_simple_resolved = 0;
  size_t num_fref_simple_resolved = 0;
  size_t num_invoke_virtual_refined = 0;
  size_t num_resolve_to_interface = 0;
  size_t num_array_clone_ref_resolved = 0;
  size_t num_invoke_interface_replaced = 0;
  size_t num_invoke_super_removed = 0;
  // External method/field refs
  size_t num_bailed_on_external = 0;
  size_t num_bailed_on_min_sdk_mismatch = 0;
  // The method ref is not solvable by the Resolver to continue.
  size_t num_unresolvable_mrefs = 0;
  size_t num_failed_infer_callee_target_type = 0;
  size_t num_failed_infer_callee_def = 0;
  // Sub stats count for num_failed_infer_callee_def.
  size_t num_failed_infer_resolver_fail = 0;
  size_t num_failed_infer_to_external = 0;
  size_t num_failed_infer_cannot_access = 0;

  // Only used for return type specialization
  RtypeCandidates rtype_candidates;

  void print(PassManager* mgr) {
    TRACE(RESO, 1, "[ref reso] method ref simple resolved %zu",
          num_mref_simple_resolved);
    TRACE(RESO, 1, "[ref reso] field ref simple resolved %zu",
          num_fref_simple_resolved);
    TRACE(RESO,
          1,
          "[ref reso] invoke-virtual refined %zu",
          num_invoke_virtual_refined);
    TRACE(RESO,
          1,
          "[ref reso] resolve invoke-virtual to invoke-interface %zu",
          num_resolve_to_interface);
    TRACE(RESO,
          1,
          "[ref reso] resolved array clone ref %zu",
          num_array_clone_ref_resolved);
    TRACE(RESO,
          1,
          "[ref reso] invoke-interface replaced %zu",
          num_invoke_interface_replaced);
    TRACE(RESO,
          1,
          "[ref reso] invoke-super removed %zu",
          num_invoke_super_removed);
    TRACE(RESO, 1, "[ref reso] bailed on external %zu", num_bailed_on_external);
    TRACE(RESO, 1, "[ref reso] bailed on min sdk mismatch %zu",
          num_bailed_on_min_sdk_mismatch);
    TRACE(RESO, 1, "[ref reso] un-resolvable method ref %zu",
          num_unresolvable_mrefs);
    TRACE(RESO, 1, "[ref reso] failed callee target type inference %zu",
          num_failed_infer_callee_target_type);
    TRACE(RESO, 1, "[ref reso] bailed callee method def inference %zu",
          num_failed_infer_callee_def);
    TRACE(RESO, 1, "[ref reso] bailed callee inference resolver fail %zu",
          num_failed_infer_resolver_fail);
    TRACE(RESO, 1,
          "[ref reso] bailed callee inference to excluded externals %zu",
          num_failed_infer_to_external);
    TRACE(RESO, 1, "[ref reso] bailed callee inference accessibility check %zu",
          num_failed_infer_cannot_access);
    mgr->incr_metric("method_refs_simple_resolved", num_mref_simple_resolved);
    mgr->incr_metric("field_refs_simple_resolved", num_fref_simple_resolved);
    mgr->incr_metric("num_invoke_virtual_refined", num_invoke_virtual_refined);
    mgr->incr_metric("num_resolve_to_interface", num_resolve_to_interface);
    mgr->incr_metric("num_array_clone_ref_resolved",
                     num_array_clone_ref_resolved);
    mgr->incr_metric("num_invoke_super_removed", num_invoke_super_removed);
    // For the following metrics on failed cases, we only need the ones from
    // final iteration.
    mgr->set_metric("num_bailed_on_external", num_bailed_on_external);
    mgr->set_metric("num_bailed_on_min_sdk_mismatch",
                    num_bailed_on_min_sdk_mismatch);
    mgr->set_metric("num_unresolvable_mrefs", num_unresolvable_mrefs);
    mgr->set_metric("num_failed_infer_callee_target_type",
                    num_failed_infer_callee_target_type);
    mgr->set_metric("num_failed_infer_callee_def", num_failed_infer_callee_def);
    mgr->set_metric("num_failed_infer_resolver_fail",
                    num_failed_infer_resolver_fail);
    mgr->set_metric("num_failed_infer_to_external",
                    num_failed_infer_to_external);
    mgr->set_metric("num_failed_infer_cannot_access",
                    num_failed_infer_cannot_access);

    TRACE(RESO,
          1,
          "[ref reso] rtype specialization candidates %zu",
          rtype_candidates.get_candidates().size());
    mgr->incr_metric("num_rtype_specialization_candidates",
                     rtype_candidates.get_candidates().size());
  }

  RefStats& operator+=(const RefStats& that) {
    num_mref_simple_resolved += that.num_mref_simple_resolved;
    num_fref_simple_resolved += that.num_fref_simple_resolved;
    num_invoke_virtual_refined += that.num_invoke_virtual_refined;
    num_resolve_to_interface += that.num_resolve_to_interface;
    num_array_clone_ref_resolved += that.num_array_clone_ref_resolved;
    num_invoke_interface_replaced += that.num_invoke_interface_replaced;
    num_invoke_super_removed += that.num_invoke_super_removed;
    num_bailed_on_external += that.num_bailed_on_external;
    num_bailed_on_min_sdk_mismatch += that.num_bailed_on_min_sdk_mismatch;
    num_unresolvable_mrefs += that.num_unresolvable_mrefs;
    num_failed_infer_callee_target_type +=
        that.num_failed_infer_callee_target_type;
    num_failed_infer_callee_def += that.num_failed_infer_callee_def;
    num_failed_infer_resolver_fail += that.num_failed_infer_resolver_fail;
    num_failed_infer_to_external += that.num_failed_infer_to_external;
    num_failed_infer_cannot_access += that.num_failed_infer_cannot_access;
    rtype_candidates += that.rtype_candidates;
    return *this;
  }
};

bool is_array_clone(IRInstruction* insn) {
  if (!opcode::is_invoke_virtual(insn->opcode())) {
    return false;
  }
  redex_assert(insn->has_method());
  auto* mref = insn->get_method();
  auto* type = mref->get_class();
  return type::is_array(type) && mref->get_name()->str() == "clone" &&
         !type::is_primitive(type::get_array_element_type(type));
}

void try_desuperify(const DexMethod* caller,
                    IRInstruction* insn,
                    RefStats& stats) {
  if (!opcode::is_invoke_super(insn->opcode())) {
    return;
  }
  auto* cls = type_class(caller->get_class());
  if (cls == nullptr) {
    return;
  }
  // Skip if the callee is an interface default method (037).
  auto* callee_cls = type_class(insn->get_method()->get_class());
  if ((callee_cls == nullptr) || is_interface(callee_cls)) {
    return;
  }
  // start resolve_method search in the superclass of :cls.
  auto* callee = resolve_method_deprecated(
      type_class(cls->get_super_class()), insn->get_method()->get_name(),
      insn->get_method()->get_proto(), MethodSearch::Virtual);
  // External methods may not always be final across runtime versions
  if (callee == nullptr || callee->is_external() || !is_final(callee)) {
    return;
  }

  TRACE(RESO, 5, "Desuperifying %s because %s is final", SHOW(insn),
        SHOW(callee));
  insn->set_opcode(OPCODE_INVOKE_VIRTUAL);
  stats.num_invoke_super_removed++;
}

bool is_excluded_external(const std::vector<std::string>& excluded_externals,
                          const std::string& name) {
  for (const auto& excluded : excluded_externals) {
    if (name.starts_with(excluded)) {
      return true;
    }
  }

  return false;
}

std::optional<DexMethod*> get_inferred_method_def(
    const DexMethod* caller,
    const std::vector<std::string>& excluded_externals,
    const bool /*is_support_lib*/,
    DexMethod* callee,
    const IROpcode invoke_op,
    const DexType* inferred_type,
    RefStats& stats) {

  auto* inferred_cls = type_class(inferred_type);
  auto method_search = opcode_to_search(invoke_op);
  if (inferred_cls != nullptr && !is_interface(inferred_cls) &&
      method_search == MethodSearch::Interface) {
    // If the inferred type is a non-interface class, we should use
    // Virtual search instead of Interface search.
    // Interface search will walk through interface hierarchy of inferred_cls
    // it won't check on interface hierarchy along inferred_cls's super
    // class hierarchy
    method_search = MethodSearch::Virtual;
  }
  auto* resolved = resolve_method_deprecated(
      inferred_cls, callee->get_name(), callee->get_proto(), method_search);
  // 1. If we cannot resolve the callee based on the inferred_cls, we bail.
  if ((resolved == nullptr) || !resolved->is_def()) {
    TRACE(RESO, 4, "Bailed resolved upon inferred_cls %s for %s",
          SHOW(inferred_cls), SHOW(callee));
    stats.num_failed_infer_resolver_fail++;
    return std::nullopt;
  }
  auto* resolved_cls = type_class(resolved->get_class());
  bool is_external = (resolved_cls != nullptr) && resolved_cls->is_external();
  // 2. If the resolved target is an excluded external, we bail.
  if (is_external && is_excluded_external(excluded_externals, show(resolved))) {
    TRACE(RESO, 4, "Bailed on excluded external%s", SHOW(resolved));
    stats.num_failed_infer_to_external++;
    return std::nullopt;
  }

  // 3. Accessibility check.
  if (!type::can_access(caller, resolved) ||
      (is_external && !is_public(resolved_cls))) {
    TRACE(RESO, 4, "Bailed on inaccessible %s from %s", SHOW(resolved),
          SHOW(caller));
    stats.num_failed_infer_cannot_access++;
    return std::nullopt;
  }
  if (!is_external && !is_public(resolved_cls)) {
    set_public(resolved_cls);
  }
  if (is_interface(inferred_cls) && !opcode::is_invoke_interface(invoke_op)) {
    // If we pass in an interface class with MethodSearch::Virtual into the
    // Resolver, it can resolve to an interface method.
    TRACE(RESO, 4, "Bailed on incompatible invoke opcode: %s is an interface",
          SHOW(inferred_cls));
    stats.num_failed_infer_callee_target_type++;
    return std::nullopt;
  }

  TRACE(RESO, 4, "Inferred to %s for type %s", SHOW(resolved),
        SHOW(inferred_type));
  return std::optional<DexMethod*>(resolved);
}

} // namespace impl

using namespace impl;

void ResolveRefsPass::resolve_method_refs(const DexMethod* caller,
                                          IRInstruction* insn,
                                          RefStats& stats) {
  always_assert(insn->has_method());
  auto* mref = insn->get_method();
  bool resolved_virtual_to_interface;
  auto* mdef = resolve_invoke_method_deprecated(insn, caller,
                                                &resolved_virtual_to_interface);
  if ((mdef == nullptr) && is_array_clone(insn)) {
    auto* object_array_clone = method::java_lang_Objects_clone();
    TRACE(RESO, 3, "Resolving %s\n\t=>%s", SHOW(mref),
          SHOW(object_array_clone));
    insn->set_method(object_array_clone);
    stats.num_mref_simple_resolved++;
    stats.num_array_clone_ref_resolved++;
    return;
  }
  if ((mdef == nullptr) || mdef == mref) {
    return;
  }
  // Handle external refs.
  if (!m_refine_to_external && mdef->is_external()) {
    return;
  } else if (mdef->is_external() && !m_min_sdk_api->has_method(mdef)) {
    // Resolving to external and the target is missing in the min_sdk_api.
    TRACE(RESO, 4, "Bailed on mismatch with min_sdk %s", SHOW(mdef));
    return;
  }

  auto* cls = type_class(mdef->get_class());
  // Bail out if the def is non public external
  if ((cls != nullptr) && cls->is_external() && !is_public(cls)) {
    return;
  }
  redex_assert(cls != nullptr || !cls->is_external());
  if (!is_public(cls)) {
    set_public(cls);
  }
  TRACE(RESO, 3, "Resolving %s\n\t=>%s", SHOW(mref), SHOW(mdef));
  insn->set_method(mdef);
  stats.num_mref_simple_resolved++;
  if (resolved_virtual_to_interface && (cls != nullptr) && is_interface(cls)) {
    TRACE(RESO, 4, "InterfaceVirtual resolve to %s in %s", SHOW(mdef),
          SHOW(insn));
    insn->set_opcode(OPCODE_INVOKE_INTERFACE);
    stats.num_resolve_to_interface++;
  }
}

void ResolveRefsPass::resolve_field_refs(IRInstruction* insn,
                                         const FieldSearch field_search,
                                         RefStats& stats) {
  auto* const fref = insn->get_field();
  auto* const fdef = resolve_field(fref, field_search);
  if ((fdef == nullptr) || fdef == fref) {
    return;
  }
  // Handle external refs.
  if (!m_refine_to_external && fdef->is_external()) {
    return;
  } else if (fdef->is_external() && !m_min_sdk_api->has_field(fdef)) {
    // Resolving to external and the target is missing in the min_sdk_api.
    TRACE(RESO, 4, "Bailed on mismatch with min_sdk %s", SHOW(fdef));
    stats.num_bailed_on_min_sdk_mismatch++;
    return;
  }

  auto* cls = type_class(fdef->get_class());
  // Bail out if the def is non public external
  if ((cls != nullptr) && cls->is_external() && !is_public(cls)) {
    return;
  }
  redex_assert(cls != nullptr || !cls->is_external());
  if (!is_public(cls)) {
    set_public(cls);
  }

  TRACE(RESO, 2, "Resolving %s\n\t=>%s", SHOW(fref), SHOW(fdef));
  insn->set_field(fdef);
  stats.num_fref_simple_resolved++;
}

RefStats ResolveRefsPass::resolve_refs(DexMethod* method) {
  RefStats stats;
  if ((method == nullptr) || (method->get_code() == nullptr)) {
    return stats;
  }

  auto& cfg = method->get_code()->cfg();
  for (auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    switch (insn->opcode()) {
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_STATIC:
      resolve_method_refs(method, insn, stats);
      break;
    case OPCODE_SGET:
    case OPCODE_SGET_WIDE:
    case OPCODE_SGET_OBJECT:
    case OPCODE_SGET_BOOLEAN:
    case OPCODE_SGET_BYTE:
    case OPCODE_SGET_CHAR:
    case OPCODE_SGET_SHORT:
    case OPCODE_SPUT:
    case OPCODE_SPUT_WIDE:
    case OPCODE_SPUT_OBJECT:
    case OPCODE_SPUT_BOOLEAN:
    case OPCODE_SPUT_BYTE:
    case OPCODE_SPUT_CHAR:
    case OPCODE_SPUT_SHORT:
      resolve_field_refs(insn, FieldSearch::Static, stats);
      break;
    case OPCODE_IGET:
    case OPCODE_IGET_WIDE:
    case OPCODE_IGET_OBJECT:
    case OPCODE_IGET_BOOLEAN:
    case OPCODE_IGET_BYTE:
    case OPCODE_IGET_CHAR:
    case OPCODE_IGET_SHORT:
    case OPCODE_IPUT:
    case OPCODE_IPUT_WIDE:
    case OPCODE_IPUT_OBJECT:
    case OPCODE_IPUT_BOOLEAN:
    case OPCODE_IPUT_BYTE:
    case OPCODE_IPUT_CHAR:
    case OPCODE_IPUT_SHORT:
      resolve_field_refs(insn, FieldSearch::Instance, stats);
      break;
    default:
      break;
    }
  }

  return stats;
}

RefStats ResolveRefsPass::refine_virtual_callsites(
    const XStoreRefs& xstores,
    DexMethod* method,
    bool desuperify,
    const SubtypeMaps* rtype_subtype_maps) {
  RefStats stats;
  if ((method == nullptr) || (method->get_code() == nullptr)) {
    return stats;
  }

  auto* code = method->get_code();
  auto& cfg = code->cfg();
  type_inference::TypeInference inference(cfg);
  inference.run(method);
  auto& envs = inference.get_type_environments();
  auto is_support_lib = api::is_support_lib_type(method->get_class());
  DexTypeDomain rtype_domain = DexTypeDomain::bottom();

  for (auto& mie : cfg::InstructionIterable(cfg)) {
    IRInstruction* insn = mie.insn;
    if (desuperify) {
      try_desuperify(method, insn, stats);
    }

    auto opcode = insn->opcode();
    if (rtype_subtype_maps != nullptr && opcode::is_return_object(opcode)) {
      auto& env = envs.at(insn);
      auto inferred_rtype = env.get_type_domain(insn->src(0));
      stats.rtype_candidates.collect_inferred_rtype(method, inferred_rtype,
                                                    rtype_domain);
      continue;
    }

    if (!opcode::is_invoke_virtual(opcode) &&
        !opcode::is_invoke_interface(opcode)) {
      continue;
    }

    auto* mref = insn->get_method();
    auto* callee =
        resolve_method_deprecated(mref, opcode_to_search(insn), method);
    if (callee == nullptr) {
      if (mref != method::java_lang_Objects_clone()) {
        stats.num_unresolvable_mrefs++;
      }
      continue;
    }
    TRACE(RESO, 4, "resolved method %s for %s", SHOW(callee), SHOW(insn));

    auto this_reg = insn->src(0);
    auto& env = envs.at(insn);
    auto dex_type = env.get_dex_type(this_reg);

    if (!dex_type) {
      // Unsuccessful inference.
      TRACE(RESO, 4, "bailed on inferred dex type %s for %s", SHOW(dex_type),
            SHOW(callee));
      stats.num_failed_infer_callee_target_type++;
      continue;
    }

    // replace it with the actual implementation if any provided.
    const auto invoke_op = insn->opcode();
    auto m_def =
        get_inferred_method_def(method, m_excluded_externals, is_support_lib,
                                callee, invoke_op, *dex_type, stats);
    if (!m_def) {
      stats.num_failed_infer_callee_def++;
      continue;
    }
    auto* def_meth = *m_def;
    auto* def_cls = type_class((def_meth)->get_class());
    if ((def_cls == nullptr) || mref == def_meth) {
      // The ref resolution is a nop.
      continue;
    }
    if (opcode::is_invoke_virtual(opcode)) {
      always_assert_log(!is_interface(def_cls),
                        "invoke-virtual to interface method %s",
                        SHOW(def_meth));
    }
    // Stop if the refine_to_external config is False.
    if (!m_refine_to_external && def_cls->is_external()) {
      TRACE(RESO, 4, "Bailed on external %s", SHOW(def_meth));
      stats.num_bailed_on_external++;
      continue;
    } else if (def_cls->is_external() && !m_min_sdk_api->has_method(def_meth)) {
      // Resolving to external and the target is missing in the min_sdk_api.
      TRACE(RESO, 4, "Bailed on mismatch with min_sdk %s", SHOW(def_meth));
      stats.num_bailed_on_min_sdk_mismatch++;
      continue;
    }
    TRACE(RESO, 3, "Resolving %s\n\t=>%s", SHOW(mref), SHOW(def_meth));
    insn->set_method(def_meth);
    if (opcode::is_invoke_interface(opcode) && !is_interface(def_cls)) {
      insn->set_opcode(OPCODE_INVOKE_VIRTUAL);
      stats.num_invoke_interface_replaced++;
    } else {
      stats.num_invoke_virtual_refined++;
    }
  }

  if (rtype_subtype_maps != nullptr) {
    stats.rtype_candidates.collect_specializable_rtype(
        m_min_sdk_api, xstores, *rtype_subtype_maps, method, rtype_domain);
  }
  return stats;
}

void ResolveRefsPass::run_pass(DexStoresVector& stores,
                               ConfigFiles& conf,
                               PassManager& mgr) {
  always_assert(m_min_sdk_api);
  Scope scope = build_class_scope(stores);
  XStoreRefs xstores(stores, conf.normal_primary_dex());
  std::optional<SubtypeMaps> subtype_maps;
  if (m_specialize_rtype) {
    subtype_maps = build_subtype_maps(scope);
  }
  const auto* rtype_subtype_maps = subtype_maps ? &*subtype_maps : nullptr;
  impl::RefStats stats = walk::parallel::methods<impl::RefStats>(
      scope, [this, &xstores, rtype_subtype_maps](DexMethod* method) {
        auto local_stats = resolve_refs(method);
        local_stats += refine_virtual_callsites(xstores, method, m_desuperify,
                                                rtype_subtype_maps);
        return local_stats;
      });
  stats.print(&mgr);

  if (!m_specialize_rtype) {
    return;
  }
  RtypeSpecialization rs(stats.rtype_candidates.get_candidates(), xstores);
  rs.specialize_rtypes(scope, *subtype_maps);
  rs.print_stats(&mgr);

  // Resolve virtual method refs again based on the new rtypes. But further
  // rtypes collection is disabled.
  stats =
      walk::parallel::methods<impl::RefStats>(scope, [&](DexMethod* method) {
        auto local_stats =
            refine_virtual_callsites(xstores, method, false /* desuperfy */,
                                     nullptr /* rtype_subtype_maps */);
        return local_stats;
      });
  stats.print(&mgr);
}

static ResolveRefsPass s_pass;
