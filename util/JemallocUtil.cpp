/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "JemallocUtil.h"

#include <iostream>

#ifdef USE_JEMALLOC
#include <jemalloc/jemalloc.h>
#include <json/json.h>
#include <sstream>

#include "Debug.h"
#endif

namespace jemalloc_util {

#ifdef USE_JEMALLOC

namespace {

void set_profile_active(bool active) {
  int err =
      mallctl("prof.active", nullptr, nullptr, (void*)&active, sizeof(active));
  always_assert_log(err == 0, "mallctl failed with: %d", err);
}

} // namespace

void enable_profiling() { set_profile_active(true); }

void disable_profiling() { set_profile_active(false); }

void dump(const std::string& file_name) {
  auto* c_str = file_name.c_str();
  int err = mallctl("prof.dump", nullptr, nullptr, &c_str, sizeof(const char*));
  if (err != 0) {
    std::cerr << "mallctl failed with: " << err << std::endl;
  }
}

std::string get_malloc_stats() {
  std::string res;
  malloc_stats_print(
      [](void* opaque, const char* s) { ((std::string*)opaque)->append(s); },
      /* cbopaque= */ &res, /* opts= */ "J");
  return res;
}

void some_malloc_stats(const std::function<void(const char*, uint64_t)>& fn) {
  constexpr std::array<const char*, 8> STATS = {
      "stats.allocated",    "stats.active",        "stats.metadata",
      "stats.metadata_thp", "stats.resident",      "stats.mapped",
      "stats.retained",     "stats.zero_reallocs",
  };

  // jemalloc caches its statistics; they only refresh when the epoch advances.
  uint64_t epoch = 1;
  size_t epoch_len = sizeof(epoch);
  auto epoch_err = mallctl("epoch", &epoch, &epoch_len, &epoch, epoch_len);
  if (epoch_err != 0) {
    std::cerr << "Failed refreshing jemalloc stats: " << epoch_err << std::endl;
  }

  for (const char* stat : STATS) {
    size_t value;
    size_t len = sizeof(value);
    auto err = mallctl(stat, &value, &len, nullptr, 0);
    if (err != 0) {
      std::cerr << "Failed reading " << stat << ": " << err << std::endl;
      continue;
    }
    fn(stat, value);
  }

  // Consider stats.arenas here.
}

#else // !USE_JEMALLOC

void enable_profiling() {}

void disable_profiling() {}

void dump(const std::string&) {
  std::cerr << "Jemalloc dump unsupported" << std::endl;
}

std::string get_malloc_stats() { return ""; }
void some_malloc_stats(const std::function<void(const char*, uint64_t)>&) {}

#endif

} // namespace jemalloc_util
