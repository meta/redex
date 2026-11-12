/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "NoResolvablePureRefsChecker.h"

#include "ConfigFiles.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "FrameworkApi.h"
#include "PassManager.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {

bool is_type_defined(const DexType* type) {
  const auto* type_ref = type::make_element_type_if_array(type);
  if (!type::is_object(type_ref)) {
    return true;
  }
  const auto& cls = type_class(type_ref);
  return cls != nullptr;
}

/*
 * See array clone logic in ResolveRefsPass.
 */
bool is_array_clone(const DexMethodRef* mref) {
  auto* type = mref->get_class();
  if ((type == nullptr) || !type::is_array(type) ||
      type::is_primitive(type::make_array_element_type(type))) {
    return false;
  }
  return mref->get_name()->str() == "clone" &&
         show(mref->get_proto()) == "()Ljava/lang/Object;";
}

bool is_resolvable(const DexMethodRef* mref) {
  if (is_array_clone(mref)) {
    return false;
  }
  // TODO: resolve pure ref ctor.
  if (method::is_init(mref)) {
    return false;
  }
  std::vector<const DexType*> type_refs;
  mref->gather_types_shallow(type_refs);
  for (const auto* type : type_refs) {
    if (!is_type_defined(type)) {
      return false;
    }
  }
  return true;
}

bool is_resolvable(const DexFieldRef* fref) {
  std::vector<const DexType*> type_refs;
  fref->gather_types_shallow(type_refs);
  for (const auto* type : type_refs) {
    if (!is_type_defined(type)) {
      return false;
    }
  }
  return true;
}

} // namespace

namespace redex_properties {

void NoResolvablePureRefsChecker::run_checker(DexStoresVector& stores,
                                              ConfigFiles& conf,
                                              PassManager& mgr,
                                              bool established) {
  if (!established) {
    return;
  }

  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  auto min_sdk_api_file = conf.get_android_sdk_api_file(min_sdk);
  const api::AndroidSDK* min_sdk_api = nullptr;
  if (min_sdk_api_file) {
    min_sdk_api = &conf.get_android_sdk_api(min_sdk);
  } else {
    not_reached_log("Api list for api %d is missing", min_sdk);
  }

  const auto& scope = build_class_scope(stores);
  walk::parallel::opcodes(scope, [&](DexMethod* method, IRInstruction* insn) {
    if (insn->has_method()) {
      DexMethodRef* mref = insn->get_method();
      if (mref->is_def()) {
        return;
      }
      auto* mdef =
          resolve_method_deprecated(mref, opcode_to_search(insn), method);
      if (!is_resolvable(mref)) {
        // Method ref references type w/ no definition in scope.
        TRACE(RESO,
              3,
              "Pure ref Checker: not resolvable method ref %s def %s",
              SHOW(mref),
              SHOW(mdef));
        return;
      }
      if (mdef == nullptr) {
        // The existing Resolver logic cannot find the method definition. Other
        // passes probably cannot do anything with the pure ref. Therefore, it's
        // harmless.
        TRACE(RESO,
              3,
              "Pure ref Checker: Resolver cannot handle method ref %s",
              SHOW(mref));
        return;
      }
      if (mdef->is_external() && !min_sdk_api->has_method(mdef)) {
        // Method ref is not resolved to an external method def due to mismatch
        // in min_sdk API.
        TRACE(RESO,
              3,
              "Pure ref Checker: resolved to external missing in min sdk "
              "method ref %s def %s",
              SHOW(mref),
              SHOW(mdef));
        return;
      }
      always_assert_log(mref->is_def(),
                        "[%s] %s contains pure method ref!\n  {%s}",
                        get_name(get_property()), SHOW(method), SHOW(insn));
    } else if (insn->has_field()) {
      DexFieldRef* fref = insn->get_field();
      if (fref->is_def()) {
        return;
      }
      const auto* fdef = resolve_field(fref);
      if (!is_resolvable(fref)) {
        // Field ref references type w/ no definition in scope.
        TRACE(RESO,
              3,
              "Pure ref Checker: not resolvable field ref %s def %s",
              SHOW(fref),
              SHOW(fdef));
        return;
      }
      if (fdef == nullptr) {
        // The existing Resolver logic cannot find the field definition. Other
        // passes probably cannot do anything with the pure ref. Therefore, it's
        // harmless.
        TRACE(RESO,
              3,
              "Pure ref Checker: Resolver cannot handle field ref %s",
              SHOW(fref));
        return;
      }
      if (fdef->is_external() && !min_sdk_api->has_field(fdef)) {
        // Method ref is not resolved to an external method def due to mismatch
        // in min_sdk API.
        TRACE(RESO, 3,
              "Pure ref Checker: resolved to external missing in min sdk field "
              "ref %s def %s",
              SHOW(fref), SHOW(fdef));
        return;
      }
      always_assert_log(fref->is_def(),
                        "[%s] %s contains pure field ref!\n  {%s}",
                        get_name(get_property()), SHOW(method), SHOW(insn));
    }
  });
}

} // namespace redex_properties

namespace {
static redex_properties::NoResolvablePureRefsChecker s_checker;
} // namespace
