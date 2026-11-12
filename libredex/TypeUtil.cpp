/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeUtil.h"

#include "Debug.h"
#include "DexUtil.h"
#include "KotlinLambdaAnalyzer.h"
#include "Lazy.h"
#include "RedexContext.h"
#include "Show.h"
#include "Trace.h"

namespace {
bool contains_digits_only(std::string_view str) {
  return std::all_of(str.begin(), str.end(),
                     [](unsigned char c) { return std::isdigit(c); });
}
} // namespace

namespace type {

#define DEFINE_CACHED_TYPE(func_name, _) \
  DexType* func_name() { return g_redex->pointers_cache().type_##func_name(); }

#define FOR_EACH DEFINE_CACHED_TYPE
WELL_KNOWN_TYPES
KOTLIN_JVM_INTERNAL_TYPES
#undef FOR_EACH

namespace pseudo {

#define DEFINE_CACHED_PSEUDO_TYPE(func_name, _)           \
  DexFieldRef* func_name() {                              \
    return g_redex->pointers_cache().field_##func_name(); \
  }

#define FOR_EACH DEFINE_CACHED_PSEUDO_TYPE
PRIMITIVE_PSEUDO_TYPE_FIELDS
KOTLIN_JVM_INTERNAL_FIELDS
#undef FOR_EACH

} // namespace pseudo

bool is_valid(std::string_view descriptor) {
  if (descriptor.empty()) {
    return false;
  }
  size_t non_array_start = 0;

  while (non_array_start < descriptor.length() &&
         descriptor[non_array_start] == '[') {
    ++non_array_start;
  }
  if (non_array_start == descriptor.length()) {
    return false;
  }

  switch (descriptor[non_array_start]) {
  case 'Z':
  case 'B':
  case 'S':
  case 'C':
  case 'I':
  case 'J':
  case 'F':
  case 'D':
  case 'V':
    return non_array_start + 1 == descriptor.length(); // Must be last character
  case 'L':
    break;
  default:
    return false;
  }

  // Object type now.

  // Must be at least three characters.
  if (non_array_start + 3 > descriptor.length()) {
    return false;
  }

  // Last one is a semicolon.
  if (descriptor[descriptor.length() - 1] != ';') {
    return false;
  }

  // Scan the identifiers.
  size_t start = non_array_start + 1;
  size_t i = start;
  for (; i != descriptor.length() - 1; ++i) {
    if (descriptor[i] == '/') {
      // Found a segment, do a check.
      if (!is_valid_identifier(descriptor.substr(start, i - start))) {
        return false;
      }
      start = i + 1;
    }
  }
  if (start != i) {
    // Handle tail.
    if (!is_valid_identifier(descriptor.substr(start, i - start))) {
      return false;
    }
  }

  return true;
}

bool is_primitive(const DexType* type) {
  auto const name = type->get_name()->str();
  always_assert_type_log(is_valid(name), INVALID_DEX, "Invalid type name: %s",
                         type->get_name()->c_str());
  switch (name[0]) {
  case 'Z':
  case 'B':
  case 'S':
  case 'C':
  case 'I':
  case 'J':
  case 'F':
  case 'D':
  case 'V':
    return true;
  case 'L':
  case '[':
    return false;
  default:
    not_reached_log("unexpected leading character in type: %s",
                    type->get_name()->c_str());
  }
}

bool is_wide_type(const DexType* type) {
  const auto* const name = type->get_name()->c_str();
  switch (name[0]) {
  case 'J':
  case 'D':
    return true;
  default:
    return false;
  }
  not_reached();
}

bool is_array(const DexType* type) {
  return type->get_name()->c_str()[0] == '[';
}

bool is_object(const DexType* type) {
  char sig = type->get_name()->c_str()[0];
  return (sig == 'L') || (sig == '[');
}

bool is_java_lang_object_array(const DexType* type) {
  if (!is_array(type)) {
    return false;
  }
  return make_array_component_type(type) == java_lang_Object();
}

bool is_enum_array(const DexType* type) {
  if (!is_array(type)) {
    return false;
  }
  return make_array_component_type(type) == java_lang_Enum();
}

bool is_reference_array(const DexType* type) {
  if (!is_array(type)) {
    return false;
  }
  auto* ctype = make_array_component_type(type);
  return !is_primitive(ctype);
}

bool is_integral(const DexType* type) {
  char sig = type->get_name()->c_str()[0];
  switch (sig) {
  case 'Z':
  case 'B':
  case 'S':
  case 'C':
  case 'I': {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool is_int(const DexType* type) { return type->get_name()->c_str()[0] == 'I'; }

bool is_char(const DexType* type) {
  return type->get_name()->c_str()[0] == 'C';
}

bool is_short(const DexType* type) {
  return type->get_name()->c_str()[0] == 'S';
}

bool is_boolean(const DexType* type) {
  return type->get_name()->c_str()[0] == 'Z';
}

bool is_byte(const DexType* type) {
  return type->get_name()->c_str()[0] == 'B';
}

bool is_long(const DexType* type) {
  return type->get_name()->c_str()[0] == 'J';
}

bool is_float(const DexType* type) {
  return type->get_name()->c_str()[0] == 'F';
}

bool is_double(const DexType* type) {
  return type->get_name()->c_str()[0] == 'D';
}

bool is_void(const DexType* type) {
  return type->get_name()->c_str()[0] == 'V';
}

char type_shorty(const DexType* type) {
  const auto* const name = type->get_name()->c_str();
  switch (name[0]) {
  case '[':
    return 'L';
  case 'V':
  case 'Z':
  case 'B':
  case 'S':
  case 'C':
  case 'I':
  case 'J':
  case 'F':
  case 'D':
  case 'L':
    return name[0];
  default:
    not_reached();
  }
}

bool check_cast(const DexType* type, const DexType* base_type) {
  if (type == base_type) {
    return true;
  }
  if (type != nullptr && is_array(type)) {
    if (base_type != nullptr && is_array(base_type)) {
      auto* component_type = make_array_component_type(type);
      auto* component_base_type = make_array_component_type(base_type);
      if (!is_primitive(component_type) && !is_primitive(component_base_type) &&
          check_cast(component_type, component_base_type)) {
        return true;
      }
    }
    return base_type == java_lang_Object();
  }
  auto* const cls = type_class(type);
  if (cls == nullptr) {
    return false;
  }
  if (check_cast(cls->get_super_class(), base_type)) {
    return true;
  }
  auto* intfs = cls->get_interfaces();
  for (auto* intf : *intfs) {
    if (check_cast(intf, base_type)) {
      return true;
    }
  }
  return false;
}

/**
 * Lcom/facebook/ClassA; ==> Lcom/facebook/
 */
std::string_view get_package_name(const DexType* type) {
  const auto name = type->get_name()->str();
  auto pos = name.find_last_of('/');
  if (pos == std::string::npos) {
    return "";
  }
  return name.substr(0, pos + 1);
}

bool same_package(const DexType* type1, const DexType* type2) {
  return get_package_name(type1) == get_package_name(type2);
}

std::string get_simple_name(const DexType* type) {
  return java_names::internal_to_simple(type->str());
}

uint32_t get_array_level(const DexType* type) {
  const auto* name = type->get_name()->c_str();
  uint32_t level = 0;
  while (*name++ == '[' && (++level != 0u)) {
    ;
  }
  return level;
}

DexType* make_array_component_type(const DexType* type) {
  if (!is_array(type)) {
    return nullptr;
  }
  const auto* name = type->get_name()->c_str();
  name++;
  return DexType::make_type(name);
}

DexType* make_array_element_type(const DexType* type) {
  if (!is_array(type)) {
    return nullptr;
  }
  const auto* name = type->get_name()->c_str();
  while (*name == '[') {
    name++;
  }
  return DexType::make_type(name);
}

const DexType* make_element_type_if_array(const DexType* type) {
  if (is_array(type)) {
    return make_array_element_type(type);
  }
  return type;
}

DexType* make_array_type(const DexType* type) {
  always_assert(type != nullptr);
  return DexType::make_type(
      DexString::make_string("[" + type->get_name()->str()));
}

DexType* make_array_type(const DexType* type, uint32_t level) {
  always_assert(type != nullptr);
  if (level == 0) {
    return DexType::make_type(type->get_name());
  }
  const auto elem_name = type->str();
  const uint32_t size = static_cast<uint32_t>(elem_name.size()) + level;
  std::string name;
  name.reserve(size + 1);
  name.append(level, '[');
  name.append(elem_name.begin(), elem_name.end());
  return DexType::make_type(DexString::make_string(name));
}

DexType* get_boxed_reference_type(const DexType* type) {
  switch (type::type_shorty(type)) {
  case 'Z':
    return type::java_lang_Boolean();
  case 'B':
    return type::java_lang_Byte();
  case 'S':
    return type::java_lang_Short();
  case 'C':
    return type::java_lang_Character();
  case 'I':
    return type::java_lang_Integer();
  case 'J':
    return type::java_lang_Long();
  case 'F':
    return type::java_lang_Float();
  case 'D':
    return type::java_lang_Double();
  default:
    return nullptr;
  }
}

// Takes a reference type, returns its corresponding unboxing method
DexMethodRef* make_unboxing_method_for_type(const DexType* type) {
  if (type == type::java_lang_Boolean()) {
    return DexMethod::make_method("Ljava/lang/Boolean;.booleanValue:()Z");
  } else if (type == type::java_lang_Byte()) {
    return DexMethod::make_method("Ljava/lang/Byte;.byteValue:()B");
  } else if (type == type::java_lang_Short()) {
    return DexMethod::make_method("Ljava/lang/Short;.shortValue:()S");
  } else if (type == type::java_lang_Character()) {
    return DexMethod::make_method("Ljava/lang/Character;.charValue:()C");
  } else if (type == type::java_lang_Integer()) {
    return DexMethod::make_method("Ljava/lang/Integer;.intValue:()I");
  } else if (type == type::java_lang_Long()) {
    return DexMethod::make_method("Ljava/lang/Long;.longValue:()J");
  } else if (type == type::java_lang_Float()) {
    return DexMethod::make_method("Ljava/lang/Float;.floatValue:()F");
  } else if (type == type::java_lang_Double()) {
    return DexMethod::make_method("Ljava/lang/Double;.doubleValue:()D");
  }
  return nullptr;
}

DexMethodRef* make_Number_unboxing_method_for_type(const DexType* type) {
  if (type == type::java_lang_Boolean()) {
    return DexMethod::make_method("Ljava/lang/Number;.booleanValue:()Z");
  } else if (type == type::java_lang_Byte()) {
    return DexMethod::make_method("Ljava/lang/Number;.byteValue:()B");
  } else if (type == type::java_lang_Short()) {
    return DexMethod::make_method("Ljava/lang/Number;.shortValue:()S");
  } else if (type == type::java_lang_Character()) {
    return DexMethod::make_method("Ljava/lang/Number;.charValue:()C");
  } else if (type == type::java_lang_Integer()) {
    return DexMethod::make_method("Ljava/lang/Number;.intValue:()I");
  } else if (type == type::java_lang_Long()) {
    return DexMethod::make_method("Ljava/lang/Number;.longValue:()J");
  } else if (type == type::java_lang_Float()) {
    return DexMethod::make_method("Ljava/lang/Number;.floatValue:()F");
  } else if (type == type::java_lang_Double()) {
    return DexMethod::make_method("Ljava/lang/Number;.doubleValue:()D");
  }
  return nullptr;
}

// Take a reference type, returns its valueOf function
DexMethodRef* make_value_of_method_for_type(const DexType* type) {
  if (type == type::java_lang_Boolean()) {
    return DexMethod::make_method(
        "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;");
  } else if (type == type::java_lang_Byte()) {
    return DexMethod::make_method(
        "Ljava/lang/Byte;.valueOf:(B)Ljava/lang/Byte;");
  } else if (type == type::java_lang_Short()) {
    return DexMethod::make_method(
        "Ljava/lang/Short;.valueOf:(S)Ljava/lang/Short;");
  } else if (type == type::java_lang_Character()) {
    return DexMethod::make_method(
        "Ljava/lang/Character;.valueOf:(C)Ljava/lang/Character;");
  } else if (type == type::java_lang_Integer()) {
    return DexMethod::make_method(
        "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;");
  } else if (type == type::java_lang_Long()) {
    return DexMethod::make_method(
        "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;");
  } else if (type == type::java_lang_Float()) {
    return DexMethod::make_method(
        "Ljava/lang/Float;.valueOf:(F)Ljava/lang/Float;");
  } else if (type == type::java_lang_Double()) {
    return DexMethod::make_method(
        "Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;");
  }
  return nullptr;
}

DataType to_datatype(const DexType* t) {
  const auto* const name = t->get_name()->c_str();
  switch (name[0]) {
  case 'V':
    return DataType::Void;
  case 'Z':
    return DataType::Boolean;
  case 'B':
    return DataType::Byte;
  case 'S':
    return DataType::Short;
  case 'C':
    return DataType::Char;
  case 'I':
    return DataType::Int;
  case 'J':
    return DataType::Long;
  case 'F':
    return DataType::Float;
  case 'D':
    return DataType::Double;
  case 'L':
    return DataType::Object;
  case '[':
    return DataType::Array;
  default:
    not_reached();
  }
}

bool is_subclass(const DexType* parent, const DexType* child) {
  const auto* super = child;
  while (super != nullptr) {
    if (parent == super) {
      return true;
    }
    auto* const cls = type_class(super);
    if (cls == nullptr) {
      break;
    }
    super = cls->get_super_class();
  }
  return false;
}

std::optional<int32_t> evaluate_type_check(const DexType* src_type,
                                           const DexType* test_type) {
  if (test_type == src_type) {
    // Trivial.
    return 1;
  }

  // Early optimization: always true for test_type = java.lang.Object.
  if (test_type == java_lang_Object()) {
    return 1;
  }

  auto* test_cls = type_class(test_type);
  if (test_cls == nullptr) {
    return std::nullopt;
  }

  auto* src_cls = type_class(src_type);
  if (src_cls == nullptr) {
    return std::nullopt;
  }

  // OK, let's simplify for now. While some SDK classes should be set in
  // stone, let's only work on internals.
  if (test_cls->is_external() || src_cls->is_external()) {
    return std::nullopt;
  }

  // Class vs class, for simplicity.
  if (!is_interface(test_cls) && !is_interface(src_cls)) {
    if (type::check_cast(src_cls->get_type(), test_cls->get_type())) {
      // If check-cast succeeds, the result will be `true`.
      return 1;
    } else if (!type::check_cast(test_cls->get_type(), src_cls->get_type())) {
      // The check can never succeed, as the test class is not a subtype.
      return 0;
    }
    return std::nullopt;
  }

  return std::nullopt;
}

/*
 * Returns true if the type is a kotlin function interface.
 * https://github.com/JetBrains/kotlin/blob/v2.2.0/libraries/stdlib/jvm/runtime/kotlin/jvm/functions/Functions.kt
 * https://github.com/JetBrains/kotlin/blob/v2.2.0/libraries/stdlib/jvm/runtime/kotlin/jvm/functions/FunctionN.kt
 */
bool is_kotlin_function_interface(const DexType* type) {
  auto name = type->get_name()->str();
  std::string_view prefix{"Lkotlin/jvm/functions/Function"};
  if (!name.starts_with(prefix)) {
    return false;
  }
  auto suffix = name.substr(prefix.length());
  const auto ends_with_semicolon = suffix.ends_with(";");
  redex_assert(ends_with_semicolon);
  suffix = suffix.substr(0, suffix.length() - 1);
  return !suffix.empty() &&
         // FunctionN, for lambdas with more than 22 arguments
         (suffix == "N" ||
          // Check numbers but don't check `Function{0..22}`, to leave some room
          // for future kotlinc internal changes.
          contains_digits_only(suffix));
}

bool is_kotlin_lambda(const DexClass* cls) {
  return KotlinLambdaAnalyzer::for_class(cls).has_value();
}

bool is_kotlin_class(DexClass* cls) {
  const auto* src_string = cls->get_source_file();
  return (src_string != nullptr) && src_string->str().ends_with(".kt");
}

bool is_kotlin_internal_type(const DexType* type) {
  return type == type::kotlin_jvm_internal_Lambda() ||
         type == type::kotlin_coroutines_jvm_internal_ContinuationImpl() ||
         type ==
             type::kotlin_coroutines_jvm_internal_RestrictedSuspendLambda() ||
         type == type::kotlin_coroutines_jvm_internal_SuspendLambda();
}

bool is_min_sdk_acceptable_impl(const DexType* source_type,
                                const DexType* cur_type,
                                const DexType* target_type,
                                const api::AndroidSDK& api,
                                Lazy<std::ostringstream>& msg) {
  // Adapted check_cast algorithm.
  if (cur_type == target_type) {
    return true;
  }

  auto* const cls = type_class(cur_type);
  if (cls == nullptr) {
    return false;
  }

  bool is_external = cls->is_external();
  if (is_external && !api.has_type(cur_type)) {
    *msg << "Filtering " << show(source_type) << " -> " << show(target_type)
         << " because " << show(cur_type) << " is not available in min-sdk";
    return false;
  }

  if (is_min_sdk_acceptable_impl(source_type, cls->get_super_class(),
                                 target_type, api, msg)) {
    if (is_external && api.get_framework_classes().at(cur_type).super_cls !=
                           cls->get_super_class()) {
      *msg << "Filtering " << show(source_type) << " -> " << show(target_type)
           << " because " << show(cur_type) << "'s superclass is "
           << show(api.get_framework_classes().at(cur_type).super_cls)
           << " in min-sdk but " << show(cls->get_super_class()) << " now.";
      return false;
    }
    return true;
  }

  auto* intfs = cls->get_interfaces();
  for (auto* intf : *intfs) {
    if (is_min_sdk_acceptable_impl(source_type, intf, target_type, api, msg)) {
      // We do not currently know implemented interfaces in AndroidSDK.
      return true;
    }
  }

  return false;
}

bool is_min_sdk_acceptable_sdk_chain(const DexType* cur_type,
                                     const DexType* target_type,
                                     const api::AndroidSDK& api) {
  // Adapted check_cast algorithm.
  if (cur_type == target_type) {
    return true;
  }

  auto* const cls = type_class(cur_type);
  if (cls == nullptr) {
    return false;
  }

  bool is_external = cls->is_external();
  if (is_external && !api.has_type(cur_type)) {
    return false;
  }

  auto* superclass = cls->get_super_class();
  if (is_external) {
    superclass = api.get_framework_classes().at(cur_type).super_cls;
  }
  if (superclass == nullptr) {
    return false;
  }

  return is_min_sdk_acceptable_sdk_chain(superclass, target_type, api);
  // No support for interfaces.
}

// Ensure that the relationship is available in the MinSdk. Assumes a type
// cast would succeed in the current SDK representation.
bool is_min_sdk_acceptable(const DexType* source_type,
                           const DexType* target_type,
                           const api::AndroidSDK& api) {
  // For arrays, this is really about the element types.
  source_type = type::make_element_type_if_array(source_type);
  target_type = type::make_element_type_if_array(target_type);

  // Early cutout: always accept target-type = Object.
  if (target_type == type::java_lang_Object()) {
    return true;
  }

  auto* cls = type_class(target_type);
  if (cls == nullptr || (cls->is_external() && !api.has_type(target_type))) {
    // The Android verifier used to have a limitation around filled-new-array
    // instructions that caused hard verification failures when the verifier
    // couldn't establish the type correctness at verification time. The
    // ReduceArrayLiteralsPass introduces check-casts instructions to deal with
    // this, and we need to make that such casts to external types are retained.
    // This issue is only fixed in Android 14, min-sdk 34, see
    // https://android-review.googlesource.com/c/platform/art/+/2438373 .
    return false;
  }

  Lazy<std::ostringstream> impl_msg{
      []() { return std::make_unique<std::ostringstream>(); }};

  // This checks whether the current hierarchy is accepted at MinSDK.
  if (is_min_sdk_acceptable_impl(source_type, source_type, target_type, api,
                                 impl_msg)) {
    return true;
  }

  // There are common cases around exceptions where the hierarchy changed.
  // Attempt to walk along the superclass chain.
  if (!is_interface(type_class(source_type)) &&
      !is_interface(type_class(target_type))) {
    if (is_min_sdk_acceptable_sdk_chain(source_type, target_type, api)) {
      TRACE(RMRCC, 1, "%s -> %s accepted with MinSDK superclass chain",
            SHOW(source_type), SHOW(target_type));
      return true;
    }
  }

  redex_assert(impl_msg);
  TRACE(RMRCC, 1, "%s", impl_msg->str().c_str());

  return false;
}

}; // namespace type
