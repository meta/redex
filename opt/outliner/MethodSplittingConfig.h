/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace method_splitting_impl {

struct Config {
  bool split_clinits{true};
  uint64_t split_block_size{1000};
  uint64_t min_original_size{10000};
  uint64_t min_original_size_hot_method{1000};
  uint64_t min_original_size_too_large_for_inlining{6000};
  uint64_t min_hot_cold_split_size{100};
  uint64_t min_hot_split_size{1500};
  uint64_t min_cold_split_size{4000};
  uint64_t huge_threshold{9000};
  float max_overhead_ratio{0.01};
  float max_hot_overhead_ratio{0.02};
  float max_huge_overhead_ratio{0.04};
  int64_t max_live_in{32};
  uint64_t max_iteration{10};

  // When a `Hot` split is created, the splitter records it in
  // `concurrent_new_hot_split_methods`, and `MethodSplittingPass` derives
  // profile stats for it, so the split is itself profile-hot and AOT-compiled.
  // With this flag set, the split joins `concurrent_hot_methods` as well, so
  // later iterations treat it as the compiled host it is. Otherwise they see
  // an uncompiled host: `is_sufficiently_large` does not consider the split
  // for further splitting at all while its size is between
  // `min_original_size_hot_method` and `min_original_size`, and above that
  // its overhead-ratio sweep is capped at `max_overhead_ratio` instead of the
  // looser `max_hot_overhead_ratio`. Off by default so the effect can be
  // attributed on its own.
  bool fix_new_hot_split_registration{false};

  size_t min_large_switch_size{8};

  // Estimated overhead of having a split method and its metadata.
  size_t cost_split_method{16};
  size_t cost_split_switch{6};
  size_t cost_split_switch_case{4};

  std::vector<std::string> excluded_prefices;

  // Master switch for cold-region outlining. When false,
  // MethodSplittingPass runs suffix splitting only.
  bool enable_region_splitting{false};

  // ---- Net cost-model aggregates (tunable) ----------------------------------
  // Code-unit costs of the net cost model (`split_net_saving`,
  // SplitNetSaving.cpp) that no single instruction's size determines; a single
  // opcode costs its dex size where the model uses it. Unit tests build their
  // config from these defaults rather than from a refig, so a configuration
  // that departs from a default runs a cost model the suite does not check.
  //
  // Per split: its encoded method, method id, proto and name in the dex
  // tables, amortized.
  size_t net_cu_method_metadata{28};
  // Per argument the split takes. Its `load-param` lowers to no instruction;
  // what the argument costs around the invoke depends on register allocation.
  size_t net_cu_load_param{1};
  // Per argument register when the invoke needs the /range form (more than
  // five argument registers). Whether a register needs a move, and which form
  // it takes, depends on register allocation.
  size_t net_cu_range_spill_per_reg{1};
  // The weight W in net saving = W * (saved - added_ccuc) - dex_added. `saved`
  // is the compiled cold code a split takes out of the host, and `added_ccuc`
  // the compiled code its launchpad adds back. W is how many code units of DEX
  // growth a split may spend per code unit of compiled cold code it takes out.
  //
  // A DEX code unit is 2 bytes, so weighing OAT and DEX bytes equally breaks
  // even at W = (OAT bytes per compiled cold code unit) / 2.
  float net_oat_weight{4.0f};
};

} // namespace method_splitting_impl
