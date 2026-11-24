/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumConfig.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "IRCode.h"
#include "LocalPointersAnalysis.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"
#include <algorithm>
#include <utility>

#include "KotlinNullCheckMethods.h"

namespace ptrs = local_pointers;

namespace {

// Whether `instance-of type` may tell a value of some enum, or an array of
// them, apart from the Integer, or Integer array, that OptimizeEnumsPass boxes
// it to. Both are instances of `Object`, `Comparable` and `Serializable`, and
// neither of a class like `String`, but an enum may implement any interface.
// For an array type, the same holds of its element type.
bool may_tell_boxed_enum_apart(const DexType* type) {
  type = type::make_element_type_if_array(type);
  if (type::is_primitive(type)) {
    return false;
  }
  auto integer = type::is_instance_of_if_known(type::java_lang_Integer(), type);
  if (integer == std::optional<bool>(true) &&
      type::is_instance_of_if_known(type::java_lang_Enum(), type) ==
          std::optional<bool>(true)) {
    return false;
  }
  const auto* cls = type_class(type);
  return cls == nullptr || is_interface(cls) ||
         integer != std::optional<bool>(false) ||
         type::is_instance_of_if_known(type, type::java_lang_Enum()) !=
             std::optional<bool>(false);
}

// The uses of a value that can tell an enum constant apart from its boxed
// Integer.
const ptrs::TypeAndIdentityUses BOXED_ENUM_USES{may_tell_boxed_enum_apart};
// The structure is used for hardcoding external method param summaries.
struct ExternalMethodData {
  std::string method_name;
  std::optional<uint16_t> returned_param;
  UnorderedSet<uint16_t> safe_params;
  ExternalMethodData(std::string name,
                     std::optional<uint16_t> returned,
                     std::initializer_list<uint16_t> params)
      : method_name(std::move(name)),
        returned_param(returned),
        safe_params(params) {}
};

void sanity_check_method_summary(const DexMethodRef* method,
                                 const optimize_enums::ParamSummary& summary,
                                 const DexType* object_type) {
  auto* args = method->get_proto()->get_args();
  for (auto param : UnorderedIterable(summary.safe_params)) {
    always_assert_log(param < args->size() &&
                          *(args->begin() + param) == object_type,
                      "%u is not Object;\n", param);
  }
  if (summary.returned_param) {
    always_assert(summary.safe_params.count(*summary.returned_param) &&
                  method->get_proto()->get_rtype() == object_type);
  }
  summary.print(method);
  if (method->is_def() && !method->is_external()) {
    // To improve:
    // 1. `equals` method is final on Integer and Enum, we can specialize equals
    // call.
    // 2. Run the method summary analysis multiple times until no new discovery.
    TRACE(ENUM, 9, "%s is not external but its method summary is hardcoded",
          SHOW(method));
    const auto* code = method->as_def()->get_code();
    TRACE(ENUM, 9, "%s", (code ? SHOW(code) : "**no code**"));
  }
}

/**
 * Hardcode some empirical summaries for some external methods.
 */
void load_external_method_summaries(
    const DexType* object_type, optimize_enums::SummaryMap* param_summary_map) {
  std::vector<ExternalMethodData> methods(
      {ExternalMethodData("Lcom/google/common/base/Objects;.equal:(Ljava/lang/"
                          "Object;Ljava/lang/"
                          "Object;)Z",
                          std::nullopt, {0, 1})});
  for (auto& item : methods) {
    auto* method = DexMethod::get_method(item.method_name);
    if (method == nullptr) {
      continue;
    }
    always_assert(!param_summary_map->count(method));
    optimize_enums::ParamSummary summary(std::move(item.safe_params),
                                         item.returned_param);
    sanity_check_method_summary(method, summary, object_type);
    param_summary_map->emplace(method, summary);
  }
  // Load summaries for kotlin null assertion methods.
  const auto trusted_null_checks =
      kotlin_nullcheck_wrapper::get_trusted_kotlin_null_assertions();
  for (auto* method : UnorderedIterable(trusted_null_checks)) {
    if (param_summary_map->count(method) != 0u) {
      // Already summarized from its code.
      continue;
    }
    // Kotlin's null checks, and the wrappers Redex makes for them, only test
    // the nullity of their first argument and return void, wherever their code
    // lives. A summary of a wrapper from its code alone would count the call
    // to the null check it wraps as an escape.
    optimize_enums::ParamSummary summary({0}, std::nullopt);
    always_assert(method->get_proto()->get_rtype() == type::_void());
    sanity_check_method_summary(method, summary, object_type);
    param_summary_map->emplace(method, summary);
  }
}
} // namespace

namespace optimize_enums {
void ParamSummary::print(const DexMethodRef* method) const {
  if (!traceEnabled(ENUM, 9)) {
    return;
  }
  TRACE(ENUM, 9, "summary of %s", SHOW(method));
  TRACE_NO_LINE(ENUM, 9, "safe_params: ");
  for (auto param : UnorderedIterable(safe_params)) {
    TRACE_NO_LINE(ENUM, 9, "%d ", param);
  }
  if (returned_param) {
    TRACE(ENUM, 9, "returned: %d", *returned_param);
  } else {
    TRACE(ENUM, 9, "returned: none");
  }
}

/**
 * Return true if a method signature contains java.lang.Object type.
 */
bool params_contain_object_type(const DexMethod* method,
                                const DexType* object_type) {
  auto* args = method->get_proto()->get_args();
  for (const auto* arg : *args) {
    if (arg == object_type) {
      return true;
    }
  }
  return false;
}

ParamSummary calculate_param_summary(DexMethod* method,
                                     const DexType* object_type) {
  auto& code = *method->get_code();
  auto& cfg = code.cfg();
  cfg.calculate_exit_block();
  ParamSummary summary;

  ptrs::FixpointIterator fp_iter(cfg, ptrs::InvokeToSummaryMap(),
                                 &BOXED_ENUM_USES);
  fp_iter.run(ptrs::Environment());
  bool result_may_be_pointer =
      !type::is_primitive(method->get_proto()->get_rtype());
  auto escape_summary =
      ptrs::get_escape_summary(fp_iter, code, result_may_be_pointer);

  auto* args = method->get_proto()->get_args();
  auto& escaping_params = escape_summary.escaping_parameters;
  // The parameters the method may return. A returned null hands the caller
  // no object it did not pass in; any other object does.
  auto& returned_elements = escape_summary.returned_parameters;
  returned_elements.erase(ptrs::NULL_RETURN);
  const bool returns_other_object =
      returned_elements.erase(ptrs::FRESH_RETURN) +
          returned_elements.erase(ptrs::ESCAPED_FRESH_RETURN) >
      0;
  if (returned_elements.size() == 1 && !returns_other_object) {
    auto returned = only(returned_elements);
    if (!escaping_params.contains(returned)) {
      const DexType* cmp = is_static(method) ? *(args->begin() + returned)
                           : returned == 0
                               ? method->get_class() // Implicit `this`
                               : *(args->begin() + returned - 1);
      if (method->get_proto()->get_rtype() == cmp) {
        // Set returned_param to the only one returned parameter index.
        summary.returned_param = returned;
      } else {
        escaping_params.insert(returned);
      }
    }
  } else {
    // The caller cannot tell which value it got, so a parameter returned
    // beside another parameter or beside some other object escapes.
    insert_unordered_iterable(escaping_params, returned_elements);
  }
  // Non-escaping java.lang.Object params are stored in safe_params.
  auto arg_it = args->begin();
  uint32_t index = 0;
  if (!is_static(method)) {
    index = 1;
  }
  for (; arg_it != args->end(); ++arg_it, ++index) {
    if ((escaping_params.count(index) == 0u) && (*arg_it == object_type)) {
      summary.safe_params.insert(index);
    }
  }
  return summary;
}

/**
 * Calculate escape summaries for static methods whose arguments contain
 * java.lang.Object type. Then convert the escape summaries to param summaries.
 */
void calculate_param_summaries(
    const Scope& scope,
    const method_override_graph::Graph& override_graph,
    SummaryMap* param_summary_map) {
  auto* object_type = type::java_lang_Object();
  walk::parallel::code(
      scope,
      [object_type, &override_graph](DexMethod* method) {
        // The code of a method marked `no_optimizations` may not be what
        // runs, so its body says nothing about what it does.
        return (method->get_code() != nullptr) &&
               !method->rstate.no_optimizations() &&
               !method_override_graph::is_true_virtual(override_graph,
                                                       method) &&
               params_contain_object_type(method, object_type);
      },
      [object_type, param_summary_map](DexMethod* method, IRCode&) {
        auto summary = calculate_param_summary(method, object_type);
        if (!summary.returned_param && summary.safe_params.empty()) {
          return;
        }
        param_summary_map->emplace(method, summary);
        summary.print(method);
      });
  TRACE(ENUM, 9, "External method summaries");
  load_external_method_summaries(object_type, param_summary_map);
}
} // namespace optimize_enums
