/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CheckBreadcrumbs.h"

#include <fstream>
#include <iosfwd>

#include <boost/algorithm/string/join.hpp>
#include <boost/filesystem/operations.hpp>

#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

/**
 * Performs 2 kind of verifications:
 * 1- no references should be to a DexClass that is "internal"
 * but not in scope (effectively deleted)
 * 2- if a field or method reference is a def the field or method
 * must exist on the class it is defined on
 * Those are 2 relatively common problems we introduce: leave references
 * to deleted types, methods or fields.
 */

namespace {

constexpr const char* METRIC_BAD_FIELDS = "bad_fields";
constexpr const char* METRIC_BAD_METHODS = "bad_methods";
constexpr const char* METRIC_BAD_TYPE_INSTRUCTIONS = "bad_type_instructions";
constexpr const char* METRIC_BAD_FIELD_INSTRUCTIONS = "bad_field_instructions";
constexpr const char* METRIC_BAD_METHOD_INSTRUCTIONS =
    "bad_method_instructions";
constexpr const char* METRIC_ILLEGAL_CROSS_STORE_REFS =
    "illegal_cross_store_refs";
constexpr const char* METRIC_TYPES_WITH_ALLOWED_VIOLATIONS =
    "allowed_types_with_violations";

bool class_contains(const DexField* field) {
  const auto* cls = type_class(field->get_class());
  if (cls == nullptr) {
    return true;
  }
  for (const auto& cls_field : cls->get_ifields()) {
    if (field == cls_field) {
      return true;
    }
  }
  for (const auto& cls_field : cls->get_sfields()) {
    if (field == cls_field) {
      return true;
    }
  }
  return false;
}

bool class_contains(const DexMethod* method) {
  const auto* cls = type_class(method->get_class());
  if (cls == nullptr) {
    return true;
  }
  for (const auto& cls_meth : cls->get_vmethods()) {
    if (method == cls_meth) {
      return true;
    }
  }
  for (const auto& cls_meth : cls->get_dmethods()) {
    if (method == cls_meth) {
      return true;
    }
  }
  return false;
}

using Fields = std::vector<const DexField*>;
using Methods = std::vector<const DexMethod*>;
using Instructions = std::vector<const IRInstruction*>;
using MethodInsns =
    std::map<const DexMethod*, Instructions, dexmethods_comparator>;

const DexType* get_type_from_insn(const IRInstruction* insn) {
  auto op = insn->opcode();
  if (opcode::is_an_invoke(op)) {
    return insn->get_method()->get_class();
  }
  if (opcode::is_an_ifield_op(op) || opcode::is_an_sfield_op(op)) {
    return insn->get_field()->get_class();
  }
  return insn->get_type();
}

std::string get_store_name(const XStoreRefs& xstores, size_t idx) {
  auto base_name = xstores.get_store(idx)->get_name();
  if (idx > 0) {
    base_name += std::to_string(idx);
  }
  return base_name;
}

std::string get_store_name(const XStoreRefs& xstores, const DexType* t) {
  std::string base_name = xstores.get_store(t)->get_name();
  size_t idx = xstores.get_store_idx(t);
  if (idx > 0) {
    base_name += std::to_string(idx);
  }
  return base_name;
}

size_t sum_instructions(const MethodInsnsType& map) {
  size_t result = 0;
  for (const auto& pair : map) {
    result += pair.second.size();
  }
  return result;
}

void build_allowed_violations(const Scope& scope,
                              const std::string& allowed_violations_file_path,
                              bool enforce_types_exist,
                              UnorderedSet<const DexType*>* types,
                              UnorderedSet<std::string>* type_prefixes,
                              std::vector<std::string>* unneeded_lines) {
  if (!boost::filesystem::exists(allowed_violations_file_path)) {
    return;
  }
  std::ifstream input(allowed_violations_file_path);
  if (!input) {
    fprintf(stderr,
            "[error] Can not open path %s\n",
            allowed_violations_file_path.c_str());
    return;
  }
  UnorderedMap<std::string, bool> allowed_class_names;
  std::string line;
  while (std::getline(input, line)) {
    if (line.empty() || line.starts_with("#")) {
      continue;
    }
    if (line.ends_with(";")) {
      allowed_class_names.emplace(line, false);
    } else {
      type_prefixes->emplace(line);
    }
  }
  for (const auto& cls : scope) {
    std::string dname = cls->get_deobfuscated_name_or_empty_copy();
    if (allowed_class_names.count(dname) != 0) {
      types->emplace(cls->get_type());
      allowed_class_names[dname] = true;
    }
  }
  if (enforce_types_exist) {
    for (const auto& pair : UnorderedIterable(allowed_class_names)) {
      if (!pair.second) {
        unneeded_lines->emplace_back(pair.first);
      }
    }
  }
}

void print_allowed_violations_per_class(
    const Scope& scope,
    const XStoreRefs& xstores,
    const std::map<const DexType*, FieldsAndType, dextypes_comparator>&
        illegal_fields,
    const std::map<const DexMethod*, TypesAndTypes, dexmethods_comparator>&
        illegal_method,
    const MethodInsnsType& illegal_type,
    const MethodInsnsType& illegal_field_type,
    const MethodInsnsType& illegal_field_cls,
    const MethodInsnsType& illegal_method_call) {
  for (const auto& cls : scope) {
    auto* type = cls->get_type();
    std::ostringstream fields_detail;
    auto fields = illegal_fields.find(type);
    if (fields != illegal_fields.end()) {
      for (const auto& f : fields->second) {
        fields_detail << "    " << f.first->get_deobfuscated_name_or_empty()
                      << " (" << get_store_name(xstores, f.first->get_type())
                      << ")\n";
      }
    }
    std::ostringstream methods_detail;
    for (const auto& method : cls->get_all_methods()) {
      std::ostringstream method_detail;
      auto protos = illegal_method.find(method);
      if (protos != illegal_method.end()) {
        for (const auto& proto_type : protos->second) {
          method_detail << "      Proto type "
                        << show_deobfuscated(proto_type.first) << " ("
                        << get_store_name(xstores, proto_type.first) << ")\n";
        }
      }
      auto type_insns = illegal_type.find(method);
      if (type_insns != illegal_type.end()) {
        for (const auto& insn : type_insns->second) {
          method_detail << "      Instruction type "
                        << show_deobfuscated(insn.first) << " ("
                        << get_store_name(xstores, insn.first->get_type())
                        << ")\n";
        }
      }
      auto field_type_insns = illegal_field_type.find(method);
      if (field_type_insns != illegal_field_type.end()) {
        for (const auto& insn : field_type_insns->second) {
          method_detail
              << "      Field type " << show_deobfuscated(insn.first) << " ("
              << get_store_name(xstores, insn.first->get_field()->get_type())
              << ")\n";
        }
      }
      auto field_cls_insns = illegal_field_cls.find(method);
      if (field_cls_insns != illegal_field_cls.end()) {
        for (const auto& insn : field_cls_insns->second) {
          method_detail
              << "      Field class " << show_deobfuscated(insn.first) << " ("
              << get_store_name(xstores, insn.first->get_field()->get_class())
              << ")\n";
        }
      }
      auto method_calls = illegal_method_call.find(method);
      if (method_calls != illegal_method_call.end()) {
        for (const auto& insn : method_calls->second) {
          method_detail
              << "      Callee class " << show_deobfuscated(insn.first) << " ("
              << get_store_name(xstores, insn.first->get_method()->get_class())
              << ")\n";
        }
      }
      auto detail_str = method_detail.str();
      if (!detail_str.empty()) {
        methods_detail << "    " << show_deobfuscated(method) << '\n'
                       << detail_str;
      }
    }
    auto fields_detail_str = fields_detail.str();
    auto methods_detail_str = methods_detail.str();
    if (!fields_detail_str.empty() || !methods_detail_str.empty()) {
      TRACE(BRCR, 3, "Allowed violations in type %s (%s)",
            show_deobfuscated(type).c_str(),
            get_store_name(xstores, type).c_str());
      if (!fields_detail_str.empty()) {
        TRACE(BRCR, 3, "  Fields:");
        TRACE(BRCR, 3, "%s", fields_detail_str.c_str());
      }
      if (!methods_detail_str.empty()) {
        TRACE(BRCR, 3, "  Methods:");
        TRACE(BRCR, 3, "%s", methods_detail_str.c_str());
      }
    }
  }
}

template <typename T, typename PrinterFn>
void gather_unnessary_allows(const UnorderedSet<T>& expected_violations,
                             const UnorderedSet<T>& actual_violations,
                             const PrinterFn& printer,
                             std::vector<std::string>* unneeded_lines) {
  for (auto& e : UnorderedIterable(expected_violations)) {
    if (!actual_violations.count(e)) {
      unneeded_lines->emplace_back(printer(e));
    }
  }
}

} // namespace

Breadcrumbs::Breadcrumbs(const Scope& scope,
                         const std::string& allowed_violations_file_path,
                         DexStoresVector& stores,
                         const ConfigFiles& conf,
                         const std::string& shared_module_prefix,
                         bool reject_illegal_refs_root_store,
                         bool only_verify_primary_dex,
                         bool verify_type_hierarchies,
                         bool verify_proto_cross_dex,
                         bool enforce_allowed_violations_file)
    : m_scope(scope),
      m_xstores(stores, conf.normal_primary_dex(), shared_module_prefix),
      m_reject_illegal_refs_root_store(reject_illegal_refs_root_store),
      m_verify_type_hierarchies(verify_type_hierarchies),
      m_verify_proto_cross_dex(verify_proto_cross_dex),
      m_enforce_allowed_violations_file(enforce_allowed_violations_file) {
  m_classes.insert(scope.begin(), scope.end());
  m_multiple_root_store_dexes = stores[0].get_dexen().size() > 1;
  if (only_verify_primary_dex) {
    for (const auto& c : scope) {
      if (m_xstores.is_in_primary_dex(c->get_type())) {
        m_scope_to_walk.push_back(c);
      }
    }
  } else {
    m_scope_to_walk.insert(m_scope_to_walk.end(), scope.begin(), scope.end());
  }
  build_allowed_violations(m_scope, allowed_violations_file_path,
                           enforce_allowed_violations_file, &m_allow_violations,
                           &m_allow_violation_type_prefixes,
                           &m_unneeded_violations_file_lines);
}

void Breadcrumbs::check_breadcrumbs() {
  check_fields();
  check_methods();
  check_opcodes();
}

void Breadcrumbs::report_deleted_types(bool report_only, PassManager& mgr) {
  size_t bad_fields_count = 0;
  size_t bad_methods_count = 0;
  size_t bad_type_insns_count = 0;
  size_t bad_field_insns_count = 0;
  size_t bad_meths_insns_count = 0;
  if (!m_bad_fields.empty() || !m_bad_methods.empty() ||
      !m_bad_type_insns.empty() || !m_bad_field_insns.empty() ||
      !m_bad_meth_insns.empty()) {
    std::ostringstream ss;
    for (const auto& bad_field : m_bad_fields) {
      for (const auto& field : bad_field.second) {
        bad_fields_count++;
        ss << "Reference to deleted type " << SHOW(bad_field.first)
           << " in field " << SHOW(field) << '\n';
      }
    }
    for (const auto& bad_meth : m_bad_methods) {
      for (const auto& meth : bad_meth.second) {
        bad_methods_count++;
        ss << "Reference to deleted type " << SHOW(bad_meth.first)
           << " in method " << SHOW(meth) << '\n';
      }
    }
    for (const auto& bad_insns : m_bad_type_insns) {
      for (const auto& insns : bad_insns.second) {
        for (const auto& insn : insns.second) {
          bad_type_insns_count++;
          ss << "Reference to deleted type " << SHOW(bad_insns.first)
             << " in instruction " << SHOW(insn) << " in method "
             << SHOW(insns.first) << '\n';
        }
      }
    }
    for (const auto& bad_insns : m_bad_field_insns) {
      for (const auto& insns : bad_insns.second) {
        for (const auto& insn : insns.second) {
          bad_field_insns_count++;
          ss << "Reference to deleted field " << SHOW(bad_insns.first)
             << " in instruction " << SHOW(insn) << " in method "
             << SHOW(insns.first) << '\n';
        }
      }
    }
    for (const auto& bad_insns : m_bad_meth_insns) {
      for (const auto& insns : bad_insns.second) {
        for (const auto& insn : insns.second) {
          bad_meths_insns_count++;
          ss << "Reference to deleted method " << SHOW(bad_insns.first)
             << " in instruction " << SHOW(insn) << " in method "
             << SHOW(insns.first) << '\n';
        }
      }
    }
    TRACE(BRCR, 1,
          "Dangling References in Fields: %zu\n"
          "Dangling References in Methods: %zu\n"
          "Dangling References in Type Instructions: %zu\n"
          "Dangling References in Fields Field Instructions: %zu\n"
          "Dangling References in Method Instructions: %zu\n",
          bad_fields_count, bad_methods_count, bad_type_insns_count,
          bad_field_insns_count, bad_meths_insns_count);
    TRACE(BRCR, 2, "%s", ss.str().c_str());
    always_assert_log(
        report_only,
        "ERROR - Dangling References (contact redex@on-call):\n%s",
        ss.str().c_str());
  } else {
    TRACE(BRCR, 1, "No dangling references");
  }
  mgr.incr_metric(METRIC_BAD_FIELDS, bad_fields_count);
  mgr.incr_metric(METRIC_BAD_METHODS, bad_methods_count);
  mgr.incr_metric(METRIC_BAD_TYPE_INSTRUCTIONS, bad_type_insns_count);
  mgr.incr_metric(METRIC_BAD_FIELD_INSTRUCTIONS, bad_field_insns_count);
  mgr.incr_metric(METRIC_BAD_METHOD_INSTRUCTIONS, bad_meths_insns_count);
}

std::string Breadcrumbs::get_methods_with_bad_refs() {
  std::ostringstream ss;
  for (const auto& class_meth : m_bad_methods) {
    const auto* const type = class_meth.first;
    const auto& methods = class_meth.second;
    ss << "Bad methods in class " << type->get_name()->c_str() << '\n';
    for (const auto* const method : methods) {
      ss << "\t" << method->get_name()->c_str() << '\n';
    }
    ss << '\n';
  }
  for (const auto& meth_field : m_bad_fields_refs) {
    auto* const type = meth_field.first->get_class();
    const auto* const method = meth_field.first;
    const auto& fields = meth_field.second;
    ss << "Bad field refs in method " << type->get_name()->c_str() << "."
       << method->get_name()->c_str() << '\n';
    for (const auto* const field : fields) {
      ss << "\t" << field->get_name()->c_str() << '\n';
    }
    ss << '\n';
  }
  return ss.str();
}

bool Breadcrumbs::should_allow_violations(const DexType* type) {
  if (m_allow_violations.count(type) > 0) {
    // Keep track simply for emitting metrics.
    m_types_with_allowed_violations.emplace(type);
    return true;
  }
  auto dname = show_deobfuscated(type);
  for (const auto& s : UnorderedIterable(m_allow_violation_type_prefixes)) {
    if (dname.starts_with(s)) {
      m_types_with_allowed_violations.emplace(type);
      m_type_prefixes_with_allowed_violations.emplace(s);
      return true;
    }
  }
  return false;
}

size_t Breadcrumbs::process_illegal_elements(
    const XStoreRefs& xstores,
    const MethodInsnsType& method_to_insns,
    const char* desc,
    MethodInsnsType& allowed,
    std::ostream& ss) {
  size_t num_illegal_cross_store_refs = 0;
  for (const auto& pair : method_to_insns) {
    const auto* const method = pair.first;
    const auto& insns = pair.second;
    if (should_allow_violations(method->get_class())) {
      allowed.emplace(method, insns);
      continue;
    }
    ss << "Illegal " << desc << " in method "
       << method->get_deobfuscated_name_or_empty() << " ("
       << get_store_name(xstores, method->get_class()) << ")\n";
    num_illegal_cross_store_refs += insns.size();
    for (const auto& insn : insns) {
      ss << "\t" << show_deobfuscated(insn.first) << " ("
         << get_store_name(xstores, get_type_from_insn(insn.first)) << ")  By  "
         << show_deobfuscated(insn.second) << " ("
         << get_store_name(xstores, insn.second) << ")\n";
    }
  }

  return num_illegal_cross_store_refs;
}

void Breadcrumbs::report_illegal_refs(bool fail_if_illegal_refs,
                                      PassManager& mgr) {
  size_t num_illegal_fields = 0;
  size_t num_allowed_illegal_fields = 0;
  std::ostringstream ss;
  std::map<const DexType*, FieldsAndType, dextypes_comparator>
      allowed_illegal_fields;
  for (const auto& pair : m_illegal_field) {
    const auto* const type = pair.first;
    const auto& fields = pair.second;
    if (should_allow_violations(type)) {
      allowed_illegal_fields.emplace(type, fields);
      num_allowed_illegal_fields += fields.size();
      continue;
    }
    num_illegal_fields += fields.size();

    ss << "Illegal fields in class "
       << type_class(type)->get_deobfuscated_name_or_empty() << " ("
       << get_store_name(m_xstores, type) << ")\n";
    for (const auto& field : fields) {
      ss << "\t" << field.first->get_deobfuscated_name_or_empty() << " ("
         << get_store_name(m_xstores, field.first->get_type()) << ")  By  "
         << show_deobfuscated(field.second) << " ("
         << get_store_name(m_xstores, field.second) << ")\n";
    }
  }

  size_t num_illegal_method_defs = 0;
  std::map<const DexMethod*, TypesAndTypes, dexmethods_comparator>
      allowed_illegal_method;
  for (const auto& pair : m_illegal_method) {
    const auto* const method = pair.first;
    const auto& types = pair.second;
    if (should_allow_violations(method->get_class())) {
      allowed_illegal_method.emplace(method, types);
      continue;
    }
    num_illegal_method_defs++;
    ss << "Illegal types in method proto " << show_deobfuscated(method) << " ("
       << get_store_name(m_xstores, method->get_class()) << ")\n";
    for (const auto& t : types) {
      ss << "\t" << show_deobfuscated(t.first) << " ("
         << get_store_name(m_xstores, t.first) << ")  By  "
         << show_deobfuscated(t.second) << " ("
         << get_store_name(m_xstores, t.second) << ")\n";
    }
  }

  MethodInsnsType allowed_illegal_type;
  size_t num_illegal_type_refs = process_illegal_elements(
      m_xstores, m_illegal_type, "type refs", allowed_illegal_type, ss);

  MethodInsnsType allowed_illegal_field_type;
  size_t num_illegal_field_type_refs = process_illegal_elements(
      m_xstores, m_illegal_field_type, "field type refs",
      allowed_illegal_field_type, ss);

  MethodInsnsType allowed_illegal_field_cls;
  size_t num_illegal_field_cls = process_illegal_elements(
      m_xstores, m_illegal_field_cls, "field class refs",
      allowed_illegal_field_cls, ss);

  MethodInsnsType allowed_illegal_method_call;
  size_t num_illegal_method_calls =
      process_illegal_elements(m_xstores, m_illegal_method_call, "method call",
                               allowed_illegal_method_call, ss);

  size_t num_illegal_cross_store_refs =
      num_illegal_fields + num_illegal_type_refs + num_illegal_field_cls +
      num_illegal_field_type_refs + num_illegal_method_calls +
      num_illegal_method_defs;
  mgr.set_metric(METRIC_ILLEGAL_CROSS_STORE_REFS, num_illegal_cross_store_refs);

  TRACE(BRCR,
        1,
        "Illegal fields : %zu\n"
        "Illegal type refs : %zu\n"
        "Illegal field type refs : %zu\n"
        "Illegal field cls refs : %zu\n"
        "Illegal method calls : %zu\n"
        "Illegal method defs : %zu\n",
        num_illegal_fields,
        num_illegal_type_refs,
        num_illegal_field_type_refs,
        num_illegal_field_cls,
        num_illegal_method_calls,
        num_illegal_method_defs);
  TRACE(BRCR, 2, "%s", ss.str().c_str());

  always_assert_type_log(ss.str().empty() || !fail_if_illegal_refs,
                         RedexError::REJECTED_CODING_PATTERN,
                         "ERROR - illegal cross store references!\n%s",
                         ss.str().c_str());

  mgr.set_metric(METRIC_TYPES_WITH_ALLOWED_VIOLATIONS,
                 m_types_with_allowed_violations.size());
  TRACE(BRCR,
        1,
        "Allowed Illegal fields : %zu\n"
        "Allowed Illegal type refs : %zu\n"
        "Allowed Illegal field type refs : %zu\n"
        "Allowed Illegal field cls refs : %zu\n"
        "Allowed Illegal method calls : %zu\n"
        "Allowed Illegal method defs : %zu\n",
        num_allowed_illegal_fields,
        sum_instructions(allowed_illegal_type),
        sum_instructions(allowed_illegal_field_type),
        sum_instructions(allowed_illegal_field_cls),
        sum_instructions(allowed_illegal_method_call),
        allowed_illegal_method.size());
  if (traceEnabled(BRCR, 3)) {
    print_allowed_violations_per_class(
        m_scope_to_walk, m_xstores, allowed_illegal_fields,
        allowed_illegal_method, allowed_illegal_type,
        allowed_illegal_field_type, allowed_illegal_field_cls,
        allowed_illegal_method_call);
  }
  if (m_enforce_allowed_violations_file) {
    // Enforce no unnecessary lines in violations file.
    gather_unnessary_allows(
        m_allow_violations, m_types_with_allowed_violations,
        [](const DexType* t) { return show_deobfuscated(t); },
        &m_unneeded_violations_file_lines);
    gather_unnessary_allows(
        m_allow_violation_type_prefixes,
        m_type_prefixes_with_allowed_violations,
        [](std::string s) { return s; },
        &m_unneeded_violations_file_lines);
    always_assert_log(
        m_unneeded_violations_file_lines.empty(),
        "Please prune the following lines from allowed "
        "violations list, they are not needed:\n%s",
        boost::algorithm::join(m_unneeded_violations_file_lines, "\n").c_str());
  }
}

bool Breadcrumbs::has_illegal_access(const DexMethod* input_method) {
  bool result = false;
  if (input_method->get_code() == nullptr) {
    return false;
  }
  auto& cfg = (const_cast<DexMethod*>(input_method))->get_code()->cfg();
  for (const auto& mie : cfg::InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->has_field()) {
      auto* res_field = resolve_field(insn->get_field());
      if (res_field != nullptr) {
        if (!check_field_accessibility(input_method, res_field)) {
          result = true;
        }
      } else if (referenced_field_is_deleted(insn->get_field())) {
        result = true;
      }
    }
    if (insn->has_method()) {
      auto* res_method = resolve_method_deprecated(
          insn->get_method(), opcode_to_search(insn), input_method);
      if (res_method != nullptr) {
        if (!check_method_accessibility(input_method, res_method)) {
          result = true;
        }
      } else if (referenced_method_is_deleted(insn->get_method())) {
        result = true;
      }
    }
  }
  return result;
}

std::pair<bool, const DexType*> Breadcrumbs::is_illegal_cross_store(
    const DexType* caller, const DexType* callee) {
  // Skip deleted types, as we don't know the store for those.
  if (m_classes.count(type_class(caller)) == 0 ||
      m_classes.count(type_class(callee)) == 0 || caller == callee) {
    return {false, nullptr};
  }

  std::set<const DexType*, dextypes_comparator> load_types;
  if (m_verify_type_hierarchies) {
    auto* callee_cls = type_class(callee);
    UnorderedSet<const DexType*> types;
    callee_cls->gather_load_types(types);
    insert_unordered_iterable(load_types, types);
  } else {
    load_types.emplace(callee);
  }

  size_t caller_store_idx = m_xstores.get_store_idx(caller);
  for (const auto& callee_to_check : load_types) {
    size_t callee_store_idx = m_xstores.get_store_idx(callee_to_check);
    if (m_multiple_root_store_dexes && caller_store_idx == 0 &&
        callee_store_idx == 1 && !m_reject_illegal_refs_root_store) {
      return {false, nullptr};
    }
    if (m_xstores.illegal_ref_between_stores(caller_store_idx,
                                             callee_store_idx)) {
      if (callee_to_check != callee) {
        TRACE(BRCR, 2,
              "Illegal reference from %s (%s) to class %s (%s) in type "
              "hierarchy of %s",
              show_deobfuscated(caller).c_str(),
              get_store_name(m_xstores, caller_store_idx).c_str(),
              show_deobfuscated(callee_to_check).c_str(),
              get_store_name(m_xstores, callee_store_idx).c_str(),
              show_deobfuscated(callee).c_str());
      }
      return {true, callee_to_check};
    }
  }
  return {false, nullptr};
}

/**
 * Return the type reference that is neither external nor defined, or return
 * null if the type reference is defined or external.
 */
const DexType* Breadcrumbs::check_type(const DexType* type) {
  const auto* type_ref = type::make_element_type_if_array(type);
  const auto& cls = type_class(type_ref);
  if (cls == nullptr) {
    return nullptr;
  }
  if (cls->is_external()) {
    return nullptr;
  }
  if (m_classes.count(cls) > 0) {
    return nullptr;
  }
  return type_ref;
}

/**
 * Return a type reference on the method ref if the definition of the type is
 * missing, or return null if all the type references are defined or external.
 */
const DexType* Breadcrumbs::check_method(const DexMethodRef* method) {
  std::vector<const DexType*> type_refs;
  method->gather_types_shallow(type_refs);
  for (const auto* type : type_refs) {
    const auto* bad_ref = check_type(type);
    if (bad_ref != nullptr) {
      return bad_ref;
    }
  }
  return nullptr;
}

const DexType* Breadcrumbs::check_anno(const DexAnnotationSet* anno) {
  if (anno == nullptr) {
    return nullptr;
  }
  std::vector<const DexType*> type_refs;
  anno->gather_types(type_refs);
  for (const auto* type : type_refs) {
    const auto* bad_ref = check_type(type);
    if (bad_ref != nullptr) {
      return bad_ref;
    }
  }
  return nullptr;
}

void Breadcrumbs::bad_type(const DexType* type,
                           const DexMethod* method,
                           const IRInstruction* insn) {
  m_bad_type_insns[type][method].emplace_back(insn);
}

// Verify that all field definitions reference types that are not deleted.
void Breadcrumbs::check_fields() {
  walk::fields(m_scope_to_walk, [&](DexField* field) {
    bool check_cross_store_ref = true;
    std::vector<const DexType*> type_refs;
    field->gather_types(type_refs);
    for (const auto* type : type_refs) {
      const auto* bad_ref = check_type(type);
      if (bad_ref != nullptr) {
        m_bad_fields[bad_ref].emplace_back(field);
        check_cross_store_ref = false;
      }
    }
    if (check_cross_store_ref) {
      auto* const cls = field->get_class();
      auto* const field_type = field->get_type();
      auto pair = is_illegal_cross_store(cls, field_type);
      if (pair.first) {
        m_illegal_field[cls].emplace_back(field, pair.second);
      }
      return;
    }
  });
}

// Verify that all method definitions use not deleted types in their signatures
// and annotations.
void Breadcrumbs::check_methods() {
  walk::methods(m_scope_to_walk, [&](DexMethod* method) {
    bool check_cross_store_ref = true;
    // Check type references on the method signature.
    const auto* bad_ref = check_method(method);
    if (bad_ref != nullptr) {
      m_bad_methods[bad_ref].emplace_back(method);
      check_cross_store_ref = false;
    }
    // Check type references on the annotations on the method.
    bad_ref = check_anno(method->get_anno_set());
    if (bad_ref != nullptr) {
      m_bad_methods[bad_ref].emplace_back(method);
      check_cross_store_ref = false;
    }

    if (check_cross_store_ref) {
      has_illegal_access(method);
      if (m_verify_proto_cross_dex) {
        // Ensure type hierarchies of proto types, which might be meaningful for
        // verification on some OS versions.
        auto* const cls = method->get_class();
        std::vector<const DexType*> proto_types;
        method->get_proto()->gather_types(proto_types);
        for (const auto& t : proto_types) {
          auto pair = is_illegal_cross_store(cls, t);
          if (pair.first) {
            m_illegal_method[method].emplace_back(t, pair.second);
          }
        }
      }
    }
  });
}

/* verify that all method instructions that access fields are valid */
bool Breadcrumbs::check_field_accessibility(const DexMethod* method,
                                            const DexField* res_field) {
  auto* const field_class = res_field->get_class();
  auto* const method_class = method->get_class();
  if (field_class != method_class && is_private(res_field)) {
    m_bad_fields_refs[method].emplace_back(res_field);
    return false;
  }
  return true;
}

bool Breadcrumbs::referenced_field_is_deleted(DexFieldRef* field_ref) {
  auto* field = field_ref->as_def();
  return (field != nullptr) && !class_contains(field);
}

bool Breadcrumbs::referenced_method_is_deleted(DexMethodRef* method_ref) {
  auto* method = method_ref->as_def();
  return (method != nullptr) && !class_contains(method);
}

/* verify that all method instructions that access methods are valid */
bool Breadcrumbs::check_method_accessibility(
    const DexMethod* method, const DexMethod* res_called_method) {
  auto* const called_method_class = res_called_method->get_class();
  auto* const method_class = method->get_class();
  if (called_method_class != method_class && is_private(res_called_method)) {
    m_bad_methods[method_class].emplace_back(res_called_method);
    return false;
  }
  return true;
}

// verify that all opcodes are to non deleted references
void Breadcrumbs::check_type_opcode(const DexMethod* method,
                                    IRInstruction* insn) {
  const DexType* type = insn->get_type();
  type = check_type(type);
  if (type != nullptr) {
    bad_type(type, method, insn);
  } else {
    auto* const cls = method->get_class();
    auto pair = is_illegal_cross_store(cls, insn->get_type());
    if (pair.first) {
      m_illegal_type[method].emplace_back(insn, pair.second);
    }
  }
}

void Breadcrumbs::check_field_opcode(const DexMethod* method,
                                     IRInstruction* insn) {
  bool check_cross_store_ref = true;

  auto* field = insn->get_field();
  std::vector<const DexType*> type_refs;
  field->gather_types_shallow(type_refs);
  for (const auto* type : type_refs) {
    const auto* bad_ref = check_type(type);
    if (bad_ref != nullptr) {
      bad_type(bad_ref, method, insn);
      check_cross_store_ref = false;
    }
  }

  if (check_cross_store_ref) {
    auto* cls = method->get_class();
    auto pair = is_illegal_cross_store(cls, field->get_type());
    if (pair.first) {
      m_illegal_field_type[method].emplace_back(insn, pair.second);
    }
    pair = is_illegal_cross_store(cls, field->get_class());
    if (pair.first) {
      m_illegal_field_cls[method].emplace_back(insn, pair.second);
    }
  }

  auto* res_field = resolve_field(field);
  if (res_field != nullptr) {
    // a resolved field can only differ in the owner class
    if (field != res_field) {
      const auto* bad_ref = check_type(field->get_class());
      if (bad_ref != nullptr) {
        bad_type(bad_ref, method, insn);
        return;
      }
    }
  } else {
    // the class of the field is around but the field may have
    // been deleted so let's verify the field exists on the class
    if (referenced_field_is_deleted(field)) {
      m_bad_field_insns[dynamic_cast<DexField*>(field)][method].emplace_back(
          insn);
      return;
    }
  }
}

void Breadcrumbs::check_method_opcode(const DexMethod* method,
                                      IRInstruction* insn) {
  const auto& meth = insn->get_method();
  const DexType* type = check_method(meth);
  if (type != nullptr) {
    bad_type(type, method, insn);
    return;
  }
  auto pair = is_illegal_cross_store(method->get_class(), meth->get_class());
  if (pair.first) {
    m_illegal_method_call[method].emplace_back(insn, pair.second);
  }

  DexMethod* res_meth =
      resolve_method_deprecated(meth, opcode_to_search(insn), method);
  if (res_meth != nullptr) {
    // a resolved method can only differ in the owner class
    if (res_meth != meth) {
      type = check_type(res_meth->get_class());
      if (type != nullptr) {
        bad_type(type, method, insn);
        return;
      }
    }
  } else {
    // the class of the method is around but the method may have
    // been deleted so let's verify the method exists on the class
    if (referenced_method_is_deleted(meth)) {
      m_bad_meth_insns[dynamic_cast<DexMethod*>(meth)][method].emplace_back(
          insn);
      return;
    }
  }
}

void Breadcrumbs::check_opcodes() {
  walk::opcodes(
      m_scope_to_walk,
      [](DexMethod*) { return true; },
      [&](DexMethod* method, IRInstruction* insn) {
        if (insn->has_type()) {
          check_type_opcode(method, insn);
          return;
        }
        if (insn->has_field()) {
          check_field_opcode(method, insn);
          return;
        }
        if (insn->has_method()) {
          check_method_opcode(method, insn);
        }
      });
}

void CheckBreadcrumbsPass::run_pass(DexStoresVector& stores,
                                    ConfigFiles& conf,
                                    PassManager& mgr) {
  auto scope = build_class_scope(stores);
  Breadcrumbs bc(scope, allowed_violations_file_path, stores, conf,
                 shared_module_prefix, reject_illegal_refs_root_store,
                 only_verify_primary_dex, verify_type_hierarchies,
                 verify_proto_cross_dex, enforce_allowed_violations_file);
  bc.check_breadcrumbs();
  bc.report_deleted_types(!fail, mgr);
  bc.report_illegal_refs(fail_if_illegal_refs, mgr);
}

static CheckBreadcrumbsPass s_pass;
