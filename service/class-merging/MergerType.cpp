/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MergerType.h"

#include <sstream>
#include <string>

#include "Debug.h"
#include "DexHasher.h"
#include "Trace.h"
#include "TypeReference.h"

namespace class_merging {

/**
 * Extract a minimal but identifiable name tag from the given root type.
 * E.g., "Lcom/facebook/analytics/structuredlogger/base/TypedEventBase;" ->
 * "EBase"
 */
std::string get_type_name_tag(const DexType* root_type) {
  auto root_type_name = type::get_simple_name(root_type);
  std::ostringstream root_name_tag;
  std::string::reverse_iterator rit = root_type_name.rbegin();
  // Scan the string from back to front.
  // Take out the last word in the simple type name starting with a cap letter.
  // E.g., "Lcom/facebook/TypedEventBase;" -> "esaB".
  for (; rit != root_type_name.rend(); ++rit) {
    auto c = *rit;
    if (isupper(c) != 0) {
      root_name_tag << c;
      break;
    } else {
      root_name_tag << c;
    }
  }
  // Advance if it's not the end.
  if (rit != root_type_name.rend()) {
    ++rit;
  }
  // Keep scanning backwards. Find the first cap letter of the second to last
  // word if any.
  // E.g., "Lcom/facebook/TypedEventBase;" -> "esaBE".
  for (; rit != root_type_name.rend(); ++rit) {
    auto c = *rit;
    if (isupper(c) != 0) {
      root_name_tag << c;
      break;
    }
  }
  auto root_name_tag_str = root_name_tag.str();
  // Apparently, since we were traversing in reverse, we need to reverse the
  // name tag string.
  // E.g., "esaBE" -> "EBase".
  std::reverse(root_name_tag_str.begin(), root_name_tag_str.end());
  TRACE(CLMG, 7, "  root_name_tag %s", root_name_tag_str.c_str());
  return root_name_tag_str;
}

std::pair<size_t, std::string> get_mergeables_hash(
    const ConstTypeVector& mergeables) {
  size_t hash = 0;
  boost::hash_combine(hash, mergeables.size());
  for (const auto* t : mergeables) {
    boost::hash_combine(hash, t->get_name()->str());
  }
  TRACE(CLMG, 5, "  mergeables_hash %zu", hash);

  std::string hash_str = hashing::hash_to_string(hash);
  TRACE(CLMG, 5, "  mergeables_hash string %s", hash_str.c_str());
  return {hash, hash_str};
}

/*
 * Example name:
 * com/google/common/collect/IDxUIteratorShape_I3_D9_S0100000_<hash>
 */
std::string MergerType::Shape::build_type_name(
    const std::string& prefix,
    const DexType* root_type,
    const ConstTypeVector& mergeables_set,
    const TypeSet& intf_set,
    size_t group_count,
    const std::optional<size_t>& opt_dex_id,
    const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
    UnorderedSet<size_t>& hash_cache) const {
  const auto* parent = root_type;
  if (root_type == type::java_lang_Object() && intf_set.size() == 1) {
    parent = *intf_set.begin();
  }
  auto root_name_tag = get_type_name_tag(parent);
  std::ostringstream ss;
  ss << "L" << prefix << root_name_tag << "Shape";

  if (interdex_subgroup_idx != std::nullopt) {
    ss << "_I" << *interdex_subgroup_idx;
  }

  if (opt_dex_id && *opt_dex_id >= 0) {
    ss << "_D" << *opt_dex_id;
  }

  ss << "_S" << string_fields << reference_fields << bool_fields << int_fields
     << long_fields << double_fields << float_fields;
  auto hash_pair = get_mergeables_hash(mergeables_set);
  size_t hash = hash_pair.first;
  std::string hash_str = hash_pair.second;
  if (!hash_cache.insert(hash).second) {
    hash_str = hash_str + "_" + std::to_string(group_count);
  }
  TRACE(CLMG, 5, "group_count %zu, hash_cache %zu", group_count,
        hash_cache.size());
  ss << "_" << hash_str << ";";
  return ss.str();
}

/*
 * Old naming scheme example: LPCreatorCreatorShape15S0000000_I1_9
 * <root_type_tag>'Shape'<count>'S'<shape_layout_tag>'_I'<interdex_group_id>'_'<subgroup_idx>
 *
 * The layout tag has one digit per field count, and a count of 10 or more
 * between underscores, so that (1, 11, 0, ...) and (11, 1, 0, ...) get the tags
 * 1_11_00000 and _11_100000.
 */
std::string MergerType::Shape::build_type_name_legacy(
    const std::string& prefix,
    const DexType* root_type,
    const TypeSet& intf_set,
    const std::optional<size_t>& opt_dex_id,
    size_t count,
    const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
    const InterdexSubgroupIdx subgroup_idx) const {
  const auto* parent = root_type;
  if (root_type == type::java_lang_Object() && intf_set.size() == 1) {
    parent = *intf_set.begin();
  }
  auto root_name_tag = get_type_name_tag(parent);
  std::ostringstream ss;
  ss << "L" << prefix << root_name_tag << "Shape";
  ss << count << "S";
  for (int field_count :
       {string_fields, reference_fields, bool_fields, int_fields, long_fields,
        double_fields, float_fields}) {
    if (field_count < 10) {
      ss << field_count;
    } else {
      ss << "_" << field_count << "_";
    }
  }

  if (opt_dex_id && *opt_dex_id > 0) {
    ss << "_" << *opt_dex_id;
  }

  if (interdex_subgroup_idx != std::nullopt) {
    ss << "_I" << *interdex_subgroup_idx;
  }

  if (subgroup_idx != 0) {
    ss << "_" << subgroup_idx;
  }
  ss << ";";
  return ss.str();
}

std::string MergerType::Shape::to_string() const {
  std::ostringstream ss;
  ss << "(" << string_fields << "," << reference_fields << "," << bool_fields
     << "," << int_fields << "," << long_fields << "," << double_fields << ","
     << float_fields << ")";
  return ss.str();
}

MergerType::Shape::Shape(const std::vector<DexField*>& fields) {
  for (const auto& field : fields) {
    auto* const field_type = field->get_type();
    if (field_type == type::java_lang_String()) {
      string_fields++;
      continue;
    }
    switch (type::type_shorty(field_type)) {
    case 'L':
    case '[':
      reference_fields++;
      break;
    case 'J':
      long_fields++;
      break;
    case 'D':
      double_fields++;
      break;
    case 'F':
      float_fields++;
      break;
    case 'Z':
      bool_fields++;
      break;
    case 'B':
    case 'S':
    case 'C':
    case 'I':
      int_fields++;
      break;
    default:
      not_reached();
    }
  }
}

} // namespace class_merging
