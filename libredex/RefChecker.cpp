/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RefChecker.h"

#include <algorithm>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"

CodeRefs::CodeRefs(const DexMethod* method,
                   const cfg::ControlFlowGraph* reduced_cfg) {
  if (method->get_code() == nullptr) {
    return;
  }
  always_assert(method->get_code()->cfg_built());
  const auto& cfg =
      reduced_cfg != nullptr ? *reduced_cfg : method->get_code()->cfg();
  UnorderedSet<const DexType*> types_set;
  UnorderedSet<const DexMethod*> methods_set;
  UnorderedSet<const DexField*> fields_set;
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->has_type()) {
      always_assert(insn->get_type());
      types_set.insert(insn->get_type());
    } else if (insn->has_method()) {
      auto* callee = resolve_invoke_method_deprecated(insn, method);
      if (callee == nullptr) {
        invalid_refs = true;
        break;
      }
      auto* callee_ref = insn->get_method();
      if (callee != callee_ref) {
        types_set.insert(callee_ref->get_class());
      }
      methods_set.insert(callee);
    } else if (insn->has_field()) {
      auto* field_ref = insn->get_field();
      auto* field = resolve_field(field_ref);
      if (field == nullptr) {
        invalid_refs = true;
        break;
      }
      if (field != field_ref) {
        types_set.insert(field_ref->get_class());
      }
      fields_set.insert(field);
    }
  }
  if (invalid_refs) {
    return;
  }

  std::vector<const DexType*> catch_types;
  cfg.gather_catch_types(catch_types);
  for (const auto* type : catch_types) {
    if (type != nullptr) {
      types_set.insert(type);
    }
  }

  types.reserve(types_set.size());
  insert_unordered_iterable(types, types.end(), types_set);

  methods.reserve(methods_set.size());
  insert_unordered_iterable(methods, methods.end(), methods_set);

  fields.reserve(fields_set.size());
  insert_unordered_iterable(fields, fields.end(), fields_set);
}

bool RefChecker::check_type(const DexType* type) const {
  return *m_type_cache
              .get_or_create_and_assert_equal(
                  type,
                  [this](const auto* _) { return check_type_internal(_); })
              .first;
}

bool RefChecker::check_method(const DexMethod* method) const {
  return *m_method_cache
              .get_or_create_and_assert_equal(
                  method,
                  [this](const auto* _) { return check_method_internal(_); })
              .first;
}

bool RefChecker::check_field(const DexField* field) const {
  return *m_field_cache
              .get_or_create_and_assert_equal(
                  field,
                  [this](const auto* _) { return check_field_internal(_); })
              .first;
}

bool RefChecker::check_class(
    const DexClass* cls,
    const std::unique_ptr<const method_override_graph::Graph>& mog) const {
  if (!check_type(cls->get_type())) {
    return false;
  }
  const auto fields = cls->get_all_fields();
  if (std::any_of(fields.begin(), fields.end(),
                  [this](DexField* field) { return !check_field(field); })) {
    return false;
  }
  const auto methods = cls->get_all_methods();
  for (const auto* method : methods) {
    if (!check_method_and_code(method)) {
      return false;
    }
    if (mog && method->is_virtual()) {
      if (method_override_graph::any_overridden_methods(
              *mog, method,
              [&](const auto* m) {
                if (!m->is_external()) {
                  return false;
                }
                if (m_min_sdk_api && !m_min_sdk_api->has_method(m)) {
                  TRACE(REFC, 4, "Risky external method override %s -> %s",
                        SHOW(method), SHOW(m));
                  return true;
                }
                return false;
              },
              true)) {
        return false;
      }
    }
  }

  return true;
}

bool RefChecker::check_code_refs(const CodeRefs& code_refs) const {
  if (code_refs.invalid_refs) {
    return false;
  }
  for (const auto* type : code_refs.types) {
    if (!check_type(type)) {
      return false;
    }
  }
  for (const auto* method : code_refs.methods) {
    if (!check_method(method)) {
      return false;
    }
  }
  for (const auto* field : code_refs.fields) {
    if (!check_field(field)) {
      return false;
    }
  }
  return true;
}

bool RefChecker::check_type_internal(const DexType* type) const {
  type = type::make_element_type_if_array(type);
  if (type::is_primitive(type)) {
    return true;
  }
  while (true) {
    auto* cls = type_class(type);
    if (cls == nullptr) {
      // This shouldn't be needed, as ideally we have a min-sdk loaded with
      // Object in it, but in some tests we don't set up the full
      // environment and do need this.
      return type == type::java_lang_String() ||
             type == type::java_lang_Class() ||
             type == type::java_lang_Enum() ||
             type == type::java_lang_Object() ||
             type == type::java_lang_Void() ||
             type == type::java_lang_Throwable() ||
             type == type::java_lang_Boolean() ||
             type == type::java_lang_Byte() ||
             type == type::java_lang_Short() ||
             type == type::java_lang_Character() ||
             type == type::java_lang_Integer() ||
             type == type::java_lang_Long() ||
             type == type::java_lang_Float() ||
             type == type::java_lang_Double();
    }
    if (cls->is_external()) {
      return (m_min_sdk_api != nullptr) && m_min_sdk_api->has_type(type);
    }
    if ((m_xstores != nullptr) && m_xstores->illegal_ref(m_store_idx, type)) {
      return false;
    }
    auto* interfaces = cls->get_interfaces();
    for (auto* t : *interfaces) {
      if (!check_type(t)) {
        return false;
      }
    }
    type = cls->get_super_class();
  }
}

bool RefChecker::check_method_internal(const DexMethod* method) const {
  auto* cls = type_class(method->get_class());
  if (cls->is_external()) {
    return (m_min_sdk_api != nullptr) && m_min_sdk_api->has_method(method);
  }
  return check_type(method->get_class()) && check_proto(method->get_proto());
}

bool RefChecker::check_proto(const DexProto* proto) const {
  const auto* args = proto->get_args();
  return std::all_of(args->begin(), args->end(),
                     [this](const DexType* t) { return check_type(t); }) &&
         check_type(proto->get_rtype());
}

bool RefChecker::check_field_internal(const DexField* field) const {
  auto* cls = type_class(field->get_class());
  if (cls->is_external()) {
    return (m_min_sdk_api != nullptr) && m_min_sdk_api->has_field(field);
  }
  return check_type(field->get_class()) && check_type(field->get_type());
}

bool RefChecker::is_in_primary_dex(const DexType* type) const {
  return (m_xstores != nullptr) && m_xstores->is_in_primary_dex(type);
}
