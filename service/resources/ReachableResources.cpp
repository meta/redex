/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReachableResources.h"

#include <boost/regex.hpp>

#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexUtil.h"
#include "IRInstruction.h"
#include "RedexResources.h"
#include "Resolver.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
// Return true if the given string is a relative file path, has .xml extension
// and can refer to the res directory of an .apk or .aab file.
bool is_resource_xml(const std::string& str) {
  if (str.ends_with(".xml")) {
    boost::filesystem::path p(str);
    if (p.is_relative()) {
      auto it = p.begin();
      if (it->string() == RES_DIRECTORY) {
        return true;
      }
      ++it;
      if (it != p.end() && it->string() == RES_DIRECTORY) {
        return true;
      }
    }
  }
  return false;
}

UnorderedSet<uint32_t> get_disallowed_resources(
    const std::vector<uint32_t>& sorted_res_ids,
    const UnorderedSet<uint32_t>& disallowed_types) {
  UnorderedSet<uint32_t> disallowed_resources;
  for (size_t index = 0; index < sorted_res_ids.size(); ++index) {
    uint32_t id = sorted_res_ids[index];
    uint32_t type_id = id & TYPE_MASK_BIT;
    if (disallowed_types.count(type_id) != 0u) {
      disallowed_resources.emplace(id);
    }
  }
  return disallowed_resources;
}

UnorderedSet<uint32_t> find_code_resource_references(
    DexStoresVector& stores,
    const resources::RClassReader& r_class_reader,
    const std::map<std::string, std::vector<uint32_t>>& name_to_ids,
    bool check_string_for_name,
    bool assume_id_inlined) {
  UnorderedSet<uint32_t> ids_from_code;
  Scope scope = build_class_scope(stores);
  ConcurrentSet<uint32_t> potential_ids_from_code;
  ConcurrentSet<DexField*> accessed_sfields;
  ConcurrentSet<uint32_t> potential_ids_from_strings;
  boost::regex find_ints("(\\d+)");

  walk::parallel::opcodes(scope, [&](DexMethod* m, IRInstruction* insn) {
    // Collect all accessed fields that could be R fields, including those that
    // method handles get or put, or values that got inlined elsewhere.
    for_each_field_access(insn, [&](IROpcode op, DexFieldRef* field_ref,
                                    const DexMethodHandle* handle) {
      if (!opcode::is_an_sfield_op(op)) {
        return;
      }
      auto* field = handle == nullptr
                        ? resolve_field(field_ref, FieldSearch::Static)
                        : resolve_field_handle(handle);
      if ((field != nullptr) && field->is_concrete()) {
        accessed_sfields.emplace(field);
      }
    });
    if (insn->opcode() == IOPCODE_R_CONST) {
      potential_ids_from_code.emplace(insn->get_literal());
    } else if (insn->has_literal()) {
      auto lit = insn->get_literal();
      if (assume_id_inlined && resources::is_potential_resid(lit)) {
        potential_ids_from_code.emplace(lit);
      }
    } else if (assume_id_inlined && insn->opcode() == OPCODE_FILL_ARRAY_DATA) {
      auto* op_data = insn->get_data();
      auto* cls = type_class(m->get_class());
      // Do not blanket assume the filling of customized arrays is a usage.
      auto customized_r = !resources::is_non_customized_r_class(cls) &&
                          r_class_reader.is_r_class(cls);
      if (!customized_r && fill_array_data_payload_width(op_data) == 4) {
        // Consider only int[] for resource ids.
        auto payload = get_fill_array_data_payload<uint32_t>(op_data);
        for (const auto& lit : payload) {
          if (resources::is_potential_resid(lit)) {
            potential_ids_from_code.emplace(lit);
          }
        }
      }
    }
    // An integer that a call site passes to its bootstrap method can be a
    // resource id too.
    if (assume_id_inlined && insn->has_callsite()) {
      for (const auto& arg : insn->get_callsite()->args()) {
        if (arg->evtype() == DEVT_INT || arg->evtype() == DEVT_LONG) {
          auto lit = static_cast<int64_t>(arg->value());
          if (resources::is_potential_resid(lit)) {
            potential_ids_from_code.emplace(lit);
          }
        }
      }
    }
    // Any string of the instruction, such as that of a const-string or one
    // that a call site passes to its bootstrap method, can hold a resource id
    // or name.
    std::vector<const DexString*> strings;
    insn->gather_strings(strings);
    for (const auto* string : strings) {
      std::string to_find = string->str_copy();
      if (assume_id_inlined) {
        // Redex evaluates expressions like
        // String.valueOf(R.drawable.inspiration_no_format)
        // which means we need to parse ints encoded as strings or ints that
        // were constant folded/concatenated at build time with other strings.
        std::vector<std::string> int_strings;
        int_strings.insert(int_strings.end(),
                           boost::sregex_token_iterator(
                               to_find.begin(), to_find.end(), find_ints),
                           boost::sregex_token_iterator());
        for (const auto& int_string : int_strings) {
          int64_t potential_num;
          try {
            potential_num = std::stol(int_string);
          } catch (...) {
            continue;
          }
          if (resources::is_potential_resid(potential_num)) {
            potential_ids_from_code.emplace(potential_num);
          }
        }
      }
      if (check_string_for_name) {
        // Being more conservative of what might get passed into
        // Landroid/content/res/Resources;.getIdentifier:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)I
        auto search = name_to_ids.find(to_find);
        if (search != name_to_ids.end()) {
          potential_ids_from_strings.insert(search->second.begin(),
                                            search->second.end());
        }
      }
    }
  });

  UnorderedSet<DexField*> array_fields;
  for (auto* field : UnorderedIterable(accessed_sfields)) {
    auto is_r_field =
        resources::is_non_customized_r_class(type_class(field->get_class()));
    if (type::is_primitive(field->get_type()) &&
        (field->get_static_value() != nullptr) &&
        resources::is_potential_resid(
            static_cast<int64_t>(field->get_static_value()->value())) &&
        (is_r_field || assume_id_inlined)) {
      ids_from_code.emplace(field->get_static_value()->value());
    } else if (is_r_field && type::is_array(field->get_type())) {
      array_fields.emplace(field);
    }
  }

  r_class_reader.extract_resource_ids_from_static_arrays(scope, array_fields,
                                                         &ids_from_code);
  insert_unordered_iterable(ids_from_code, potential_ids_from_code);
  insert_unordered_iterable(ids_from_code, potential_ids_from_strings);
  return ids_from_code;
}
} // namespace

namespace resources {
UnorderedSet<uint32_t> get_resources_by_prefix_and_name(
    const std::vector<std::string>& prefixes,
    const UnorderedSet<std::string>& names,
    const std::map<std::string, std::vector<uint32_t>>& name_to_ids) {
  UnorderedSet<uint32_t> found_resources;
  for (const auto& pair : name_to_ids) {
    if (names.find(pair.first) != names.end()) {
      TRACE(RES, 1, "Resource added by name matching: %s", pair.first.c_str());
      found_resources.insert(pair.second.begin(), pair.second.end());
      continue;
    }

    for (const auto& prefix : UnorderedIterable(prefixes)) {
      if (pair.first.starts_with(prefix)) {
        found_resources.insert(pair.second.begin(), pair.second.end());
      }
    }
  }
  return found_resources;
}

UnorderedSet<uint32_t> ReachableResources::get_resource_roots(
    DexStoresVector& stores) {
  // Roots from dex code.
  auto ids_from_code = find_code_resource_references(
      stores, *m_r_class_reader, m_res_table->name_to_ids,
      m_options.check_string_for_name, m_options.assume_id_inlined);
  const auto& sorted_res_ids = m_res_table->sorted_res_ids;
  UnorderedSet<uint32_t> existing_resids;
  for (size_t index = 0; index < sorted_res_ids.size(); ++index) {
    existing_resids.emplace(sorted_res_ids[index]);
  }
  unordered_erase_if(ids_from_code, [&](const auto& resid) {
    return existing_resids.find(resid) == existing_resids.end();
  });
  m_code_roots = ids_from_code.size();

  // Roots from AndroidManifest.xml files.
  UnorderedSet<uint32_t> manifest_roots;
  const auto& xml_files = m_resources->find_all_xml_files();
  for (const std::string& path : UnorderedIterable(xml_files)) {
    if (path.find("AndroidManifest.xml") == std::string::npos) {
      continue;
    }
    m_explored_xml_files.emplace(path);
    const auto& id_roots = m_resources->get_xml_reference_attributes(path);
    insert_unordered_iterable(manifest_roots, id_roots);
  }
  m_manifest_roots = manifest_roots.size();

  auto resources_to_keep = m_resources->get_all_keep_resources();
  insert_unordered_iterable(resources_to_keep,
                            m_options.assume_reachable_names);

  // Configured assumptions.
  auto assumed_reachable_roots = get_resources_by_prefix_and_name(
      m_options.assume_reachable_prefixes, resources_to_keep,
      m_res_table->name_to_ids);
  // Configured roots by resource type. These should be traversed like any other
  // reachable root.
  auto disallowed_type_ids =
      m_res_table->get_types_by_name(m_options.disallowed_types);
  auto disallowed_resouces = get_disallowed_resources(
      m_res_table->sorted_res_ids, disallowed_type_ids);
  m_assumed_roots = assumed_reachable_roots.size() + disallowed_resouces.size();
  // Overlayable ids
  auto overlayable_ids = m_res_table->get_overlayable_id_roots();

  UnorderedSet<uint32_t> result;
  insert_unordered_iterable(result, manifest_roots);
  insert_unordered_iterable(result, ids_from_code);
  insert_unordered_iterable(result, assumed_reachable_roots);
  insert_unordered_iterable(result, disallowed_resouces);
  insert_unordered_iterable(result, overlayable_ids);
  return result;
}

UnorderedSet<uint32_t> ReachableResources::compute_transitive_closure(
    const UnorderedSet<uint32_t>& roots) {
  UnorderedSet<uint32_t> nodes_visited;
  UnorderedSet<std::string> potential_file_paths;
  for (uint32_t root : UnorderedIterable(roots)) {
    m_res_table->walk_references_for_resource(root, ResourcePathType::ZipPath,
                                              m_options, &nodes_visited,
                                              &potential_file_paths);
  }

  UnorderedSet<std::string> next_xml_files;
  while (!potential_file_paths.empty()) {
    for (const auto& str : UnorderedIterable(potential_file_paths)) {
      if (is_resource_xml(str)) {
        auto r_str = std::string(m_zip_dir).append("/").append(str);
        if (m_explored_xml_files.find(r_str) == m_explored_xml_files.end()) {
          next_xml_files.emplace(std::move(r_str));
        }
      }
    }

    potential_file_paths.clear();
    for (const auto& str : UnorderedIterable(next_xml_files)) {
      m_explored_xml_files.emplace(str);
      auto xml_reference_attributes =
          m_resources->get_xml_reference_attributes(str);
      for (uint32_t attribute : UnorderedIterable(xml_reference_attributes)) {
        m_res_table->walk_references_for_resource(
            attribute, ResourcePathType::ZipPath, m_options, &nodes_visited,
            &potential_file_paths);
      }
    }
    next_xml_files.clear();
  }
  return nodes_visited;
}
} // namespace resources
