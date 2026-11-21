/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexStructure.h"
#include "PassManager.h"

namespace interdex {

constexpr const char* METRIC_COLD_START_SET_DEX_COUNT =
    "cold_start_set_dex_count";

constexpr const char* METRIC_REORDER_CLASSES = "num_reorder_classes";
constexpr const char* METRIC_REORDER_RESETS = "num_reorder_resets";
constexpr const char* METRIC_REORDER_REPRIORITIZATIONS =
    "num_reorder_reprioritization";
constexpr const char* METRIC_REORDER_CLASSES_SEEDS = "reorder_classes_seeds";

constexpr const char* METRIC_CLASSES_ADDED_FOR_RELOCATED_METHODS =
    "num_classes_added_for_relocated_methods";
constexpr const char* METRIC_RELOCATABLE_STATIC_METHODS =
    "num_relocatable_static_methods";
constexpr const char* METRIC_RELOCATABLE_NON_STATIC_DIRECT_METHODS =
    "num_relocatable_non_static_direct_methods";
constexpr const char* METRIC_RELOCATABLE_VIRTUAL_METHODS =
    "num_relocatable_virtual_methods";
constexpr const char* METRIC_RELOCATED_STATIC_METHODS =
    "num_relocated_static_methods";
constexpr const char* METRIC_RELOCATED_NON_STATIC_DIRECT_METHODS =
    "num_relocated_non_static_direct_methods";
constexpr const char* METRIC_RELOCATED_VIRTUAL_METHODS =
    "num_relocated_virtual_methods";
constexpr const char* METRIC_CURRENT_CLASSES_WHEN_EMITTING_REMAINING =
    "num_current_classes_when_emitting_remaining";

constexpr const char* METRIC_LINEAR_ALLOC_LIMIT = "linear_alloc_limit";
// Headroom later passes must still leave free in every dex. Plugin
// reservations are excluded; see METRIC_PLUGIN_RESERVED_*.
constexpr const char* METRIC_RESERVED_FREFS = "reserved_frefs";
constexpr const char* METRIC_RESERVED_TREFS = "reserved_trefs";
constexpr const char* METRIC_RESERVED_MREFS = "reserved_mrefs";
// Headroom InterDexPassPlugin::get_reserve_refs() held back in the root
// store's dexes and the plugins' cleanup() then spent. Reported for
// observability only -- it is gone by the time InterDex returns.
constexpr const char* METRIC_PLUGIN_RESERVED_FREFS = "plugin_reserved_frefs";
constexpr const char* METRIC_PLUGIN_RESERVED_TREFS = "plugin_reserved_trefs";
constexpr const char* METRIC_PLUGIN_RESERVED_MREFS = "plugin_reserved_mrefs";
constexpr const char* METRIC_EMIT_CANARIES = "emit_canaries";
constexpr const char* METRIC_ORDER_INTERDEX = "order_interdex";

// The headroom InterDex left free in every dex, as it published it in its
// metrics, or none if InterDex did not run. Unlike
// `PassManager::get_reserved_refs()`, which sums the reservations passes still
// hold, this is what passes after InterDex must stay out of.
inline ReserveRefsInfo get_interdex_reserved_refs(PassManager& mgr) {
  const auto& metrics = mgr.get_interdex_metrics();
  auto get = [&metrics](const char* name) {
    auto it = metrics.find(name);
    return it == metrics.end() ? size_t{0} : static_cast<size_t>(it->second);
  };
  return ReserveRefsInfo(get(METRIC_RESERVED_FREFS),
                         get(METRIC_RESERVED_TREFS),
                         get(METRIC_RESERVED_MREFS));
}

} // namespace interdex
