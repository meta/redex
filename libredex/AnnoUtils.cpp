/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AnnoUtils.h"

#include <cinttypes>
#include <utility>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "Show.h"
#include "Trace.h"

namespace {

const DexEncodedValue* parse_anno_value_helper(const DexAnnotationSet* anno_set,
                                               const DexType* target_anno,
                                               DexEncodedValueTypes type,
                                               const std::string& elem_str) {
  const auto& annos = anno_set->get_annotations();
  for (const auto& anno : annos) {
    if (anno->type() != target_anno) {
      continue;
    }
    TRACE(ANNO, 9, "   anno %s", SHOW(anno));
    const auto& elems = anno->anno_elems();
    if (elem_str.empty()) {
      const auto& elem = only(elems);
      always_assert(elem.encoded_value->evtype() == type);
      auto val = elem.encoded_value->value();
      TRACE(ANNO, 9, " parsed annotation value: %" PRIu64, val);
      return elem.encoded_value.get();
    }

    for (const auto& elem : elems) {
      if (strcmp(elem.string->c_str(), elem_str.c_str()) != 0) {
        continue;
      }
      always_assert(elem.encoded_value->evtype() == type);
      TRACE(ANNO, 9, " parsed annotation elem: %s", SHOW(elem.encoded_value));
      return elem.encoded_value.get();
    }

    const DexEncodedValue* default_value =
        parse_default_anno_value(target_anno, elem_str);

    if (default_value != nullptr) {
      return default_value;
    }
  }
  not_reached_log("Unable to parse annotation value of %s\non %s\n",
                  elem_str.c_str(),
                  SHOW(anno_set));
}

template <class DexMember>
uint32_t parse_anno_value(const DexMember* member,
                          const DexType* target_anno,
                          DexEncodedValueTypes type,
                          const std::string& elem_str = "") {
  auto anno_set = member->get_anno_set();
  always_assert(anno_set != nullptr);
  TRACE(ANNO,
        9,
        " Parsing annotations elem %s on %s: %s",
        elem_str.c_str(),
        SHOW(member),
        SHOW(anno_set));
  auto val = parse_anno_value_helper(anno_set, target_anno, type, elem_str);
  return static_cast<uint32_t>(val->value());
}

template <class DexMember>
std::string parse_str_anno_value(const DexMember* member,
                                 const DexType* target_anno,
                                 DexEncodedValueTypes type,
                                 const std::string& elem_str = "") {
  always_assert(target_anno);
  always_assert(type == DEVT_STRING);
  auto anno_set = member->get_anno_set();
  always_assert(anno_set != nullptr);
  TRACE(ANNO,
        9,
        " Parsing annotations elem %s on %s: %s",
        elem_str.c_str(),
        SHOW(member),
        SHOW(anno_set));
  auto val = parse_anno_value_helper(anno_set, target_anno, type, elem_str);
  return std::string(
      static_cast<const DexEncodedValueString*>(val)->string()->c_str());
}

} // namespace

const DexEncodedValue* parse_default_anno_value(
    const DexType* target_anno_type,
    const std::string& target_anno_element_name) {

  if (target_anno_type == nullptr || target_anno_element_name.empty()) {
    return nullptr;
  }
  TRACE(ANNO, 9, "Looking up default value for anno [%s], element_name %s \n",
        SHOW(target_anno_type), target_anno_element_name.c_str());
  DexClass* target_anno_class = type_class(target_anno_type);
  const auto* target_anno_class_annoset = target_anno_class->get_anno_set();
  if (target_anno_class_annoset == nullptr) {
    return nullptr;
  }
  const auto& target_anno_class_annos =
      target_anno_class_annoset->get_annotations();

  auto* const default_annotation_dextype =
      DexType::get_type("Ldalvik/annotation/AnnotationDefault;");

  for (const auto& target_anno_class_anno : target_anno_class_annos) {
    if (target_anno_class_anno->type() != default_annotation_dextype) {
      continue;
    }
    always_assert(target_anno_class_anno->system_visible());
    const auto& target_elems = target_anno_class_anno->anno_elems();
    const std::string VALUE_ELEM_STR = "value";
    for (const auto& target_elem : target_elems) {
      if (target_elem.string->str() != VALUE_ELEM_STR) {
        continue;
      }
      DexEncodedValueAnnotation* default_values =
          dynamic_cast<DexEncodedValueAnnotation*>(
              target_elem.encoded_value.get());
      TRACE(ANNO, 9, "default values: %s type %d\n", SHOW(default_values),
            target_elem.encoded_value->evtype());
      always_assert(target_elem.encoded_value->evtype() == DEVT_ANNOTATION);

      const auto& default_value_annos = default_values->annotations();
      for (const auto& default_value_anno : default_value_annos) {
        if (default_value_anno.string->str() != target_anno_element_name) {
          continue;
        }
        return default_value_anno.encoded_value.get();
      }
    }
  }
  return nullptr;
}

bool parse_bool_anno_value(const DexMethod* method,
                           const DexType* target_anno,
                           const std::string& name) {
  auto val = parse_anno_value(method, target_anno, DEVT_BOOLEAN, name);
  return static_cast<bool>(val);
}

uint32_t parse_int_anno_value(const DexMethod* method,
                              const DexType* target_anno,
                              const std::string& name) {
  auto val = parse_anno_value(method, target_anno, DEVT_INT, name);
  return val;
}

uint32_t parse_int_anno_value(const DexClass* cls,
                              const DexType* target_anno,
                              const std::string& name) {
  auto val = parse_anno_value(cls, target_anno, DEVT_INT, name);
  return val;
}

std::string parse_str_anno_value(const DexMethod* method,
                                 const DexType* target_anno,
                                 const std::string& name) {
  return parse_str_anno_value(method, target_anno, DEVT_STRING, name);
}

bool has_any_parameter_annotation(const DexMethod* method) {
  const auto& param_annos = method->get_param_anno();
  if (param_annos == nullptr) {
    return false;
  }
  return !param_annos->empty();
}

std::unique_ptr<DexAnnotationSet> create_anno_set(
    const std::vector<std::pair<std::string, std::string>>& elements,
    DexType* anno_type) {
  auto anno = std::make_unique<DexAnnotation>(
      anno_type, DexAnnotationVisibility::DAV_BUILD);
  for (const auto& pair : elements) {
    auto key = pair.first;
    auto elem_val = pair.second;
    anno->add_element(
        key.c_str(),
        std::unique_ptr<DexEncodedValue>(
            new DexEncodedValueString(DexString::make_string(elem_val))));
  }
  auto anno_set = std::make_unique<DexAnnotationSet>();
  anno_set->add_annotation(std::move(anno));
  return anno_set;
}
