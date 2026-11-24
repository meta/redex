/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "ConcurrentContainers.h"
#include "MethodOverrideGraph.h"

namespace optimize_enums {
/**
 * A summary of how the parameters are used in a method.
 */
struct ParamSummary {
  // Indices of parameters that do not escape through other ways except escaping
  // as return value.
  UnorderedSet<uint16_t> safe_params;
  // Index of parameter if it's exactly the return value.
  std::optional<uint16_t> returned_param;

  ParamSummary() : returned_param(std::nullopt) {}

  ParamSummary(UnorderedSet<uint16_t>&& safe_params,
               std::optional<uint16_t> returned_param)
      : safe_params(std::move(safe_params)), returned_param(returned_param) {}

  void print(const DexMethodRef* method) const;
};

using SummaryMap = InsertOnlyConcurrentMap<const DexMethodRef*, ParamSummary>;

struct Config {
  /**
   * We create helper classes `EnumUtils` in primary dex with all the boxed
   * integer fields for representing enum values. The maximum number of the
   * fields is equal to largest number of values of candidate enum classes. To
   * limit the size of the classes, exclude the enum classes that contain more
   * than max_enum_size values before the transformation.
   */
  uint32_t max_enum_size;
  /**
   * When positive, put each block of this many boxed values into its own
   * holder class, which the runtime initializes, and so boxes, only when code
   * first reads one of its fields. Otherwise `EnumUtils` holds every value.
   */
  uint32_t enum_utils_split_size{0};
  bool skip_sanity_check{false};
  bool support_kt_19_enum_entries{false};
  /**
   * Will try to optimize the enums in the allowlist without considering
   * reference equality of the enum objects.
   */
  UnorderedSet<const DexType*> breaking_reference_equality_allowlist;
  SummaryMap param_summary_map;
  /**
   * The override graph of the scope, which the analysis of `<clinit>` needs
   * to know which methods a virtual call may run.
   */
  const method_override_graph::Graph* override_graph{nullptr};
  ConcurrentSet<const DexType*> candidate_enums;

  explicit Config(uint32_t max_size) : max_enum_size(max_size) {}
};

bool params_contain_object_type(const DexMethod* method,
                                const DexType* object_type);

/**
 * Apply escape analysis on the method and transfrom the escape summary to param
 * summary.
 */
ParamSummary calculate_param_summary(DexMethod* method,
                                     const DexType* object_type);

void calculate_param_summaries(
    const Scope& scope,
    const method_override_graph::Graph& override_graph,
    SummaryMap* param_summary_map);
} // namespace optimize_enums
