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
};

} // namespace method_splitting_impl
