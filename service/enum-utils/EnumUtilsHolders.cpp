/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumUtilsHolders.h"

#include <algorithm>
#include <limits>

#include "DexAccess.h"
#include "DexClass.h"
#include "TypeUtil.h"

namespace enum_utils {

namespace {

constexpr std::string_view kBaseFamily = "Lredex/$EnumUtils";
constexpr std::string_view kCollisionSuffix = "$u";

// A decimal number without sign or leading zeros, as std::to_string writes it.
std::optional<uint32_t> parse_number(std::string_view s) {
  if (s.empty() || (s.size() > 1 && s.front() == '0')) {
    return std::nullopt;
  }
  uint64_t value = 0;
  for (char c : s) {
    if (c < '0' || c > '9') {
      return std::nullopt;
    }
    value = value * 10 + static_cast<uint64_t>(c - '0');
    if (value > std::numeric_limits<uint32_t>::max()) {
      return std::nullopt;
    }
  }
  return static_cast<uint32_t>(value);
}

bool is_family(std::string_view name) {
  if (!name.starts_with(kBaseFamily)) {
    return false;
  }
  name.remove_prefix(kBaseFamily.size());
  while (name.starts_with(kCollisionSuffix)) {
    name.remove_prefix(kCollisionSuffix.size());
  }
  return name.empty();
}

// Whether `name` is what holder_name returns for some family and chunk.
bool is_holder_name(std::string_view name) {
  if (!name.ends_with(';')) {
    return false;
  }
  name.remove_suffix(1);
  if (is_family(name)) {
    return true;
  }
  auto dollar = name.rfind('$');
  if (dollar == std::string_view::npos) {
    return false;
  }
  auto chunk = parse_number(name.substr(dollar + 1));
  return chunk && *chunk > 0 && is_family(name.substr(0, dollar));
}

} // namespace

std::string unused_family(uint32_t num_chunks) {
  std::string family(kBaseFamily);
  auto is_used = [&](uint32_t chunk) {
    return DexType::get_type(holder_name(family, chunk)) != nullptr;
  };
  for (uint32_t chunk = 0; chunk < std::max<uint32_t>(num_chunks, 1);) {
    if (is_used(chunk)) {
      family += kCollisionSuffix;
      chunk = 0;
    } else {
      ++chunk;
    }
  }
  return family;
}

std::string holder_name(std::string_view family, uint32_t chunk) {
  std::string name(family);
  if (chunk != 0) {
    name += "$" + std::to_string(chunk);
  }
  return name + ";";
}

std::string field_name(uint32_t value) { return "f" + std::to_string(value); }

bool is_holder(const DexType* type) {
  if (!is_holder_name(type->str())) {
    return false;
  }
  const auto* cls = type_class(type);
  return cls != nullptr && cls->rstate.is_generated();
}

std::optional<int32_t> boxed_value(const DexField* field) {
  auto name = field->str();
  if (!name.starts_with('f')) {
    return std::nullopt;
  }
  auto value = parse_number(name.substr(1));
  if (!value || *value > std::numeric_limits<int32_t>::max() ||
      !is_static(field) || !is_final(field) ||
      field->get_type() != type::java_lang_Integer() ||
      !is_holder(field->get_class())) {
    return std::nullopt;
  }
  return static_cast<int32_t>(*value);
}

} // namespace enum_utils
