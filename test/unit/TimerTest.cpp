/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <chrono>
#include <thread>
#include <vector>

#include <gtest/gtest.h>

#include "Timer.h"

#include "Sanitizers.h"

namespace {

constexpr size_t NUM_THREADS = 10;
constexpr size_t NUM_ITERS = 3;

constexpr uint64_t kOneSecInMus = static_cast<uint64_t>(1000 * 1000);

// Allow 250ms delta.
constexpr uint64_t kAllowedDelta = static_cast<uint64_t>(250 * 1000);

::testing::AssertionResult is_close(uint64_t expected,
                                    uint64_t actual,
                                    uint64_t multiplier = 1) {
  // Ignore result with sanitization.
  if (sanitizers::kIsAsan) {
    return ::testing::AssertionSuccess();
  }

  uint64_t delta = expected < actual ? actual - expected : expected - actual;
  uint64_t allowed = kAllowedDelta * multiplier;
  if (delta <= allowed) {
    return ::testing::AssertionSuccess();
  }
  return ::testing::AssertionFailure()
         << "actual time " << actual << " deviates more than allowed (" << delta
         << " vs " << allowed << ") from expected time " << expected;
}

} // namespace

TEST(AccumulatingTimer, singleThread) {
  AccumulatingTimer timer{};

  {
    auto scope1 = timer.scope();
    std::this_thread::sleep_for(std::chrono::seconds(1));
  }

  auto mus = timer.get_microseconds();
  EXPECT_TRUE(is_close(kOneSecInMus, mus));

  {
    auto scope2 = timer.scope();
    std::this_thread::sleep_for(std::chrono::seconds(1));
  }

  auto mus2 = timer.get_microseconds();
  EXPECT_TRUE(is_close(2 * kOneSecInMus, mus2, 2));

  {
    auto scope3 = timer.scope();
    std::this_thread::sleep_for(std::chrono::seconds(1));
  }

  auto mus3 = timer.get_microseconds();
  EXPECT_TRUE(is_close(3 * kOneSecInMus, mus3, 3));
}

TEST(AccumulatingTimer, multipleThreadsOneScope) {
  AccumulatingTimer timer{};
  AccumulatingTimer timer_global{};
  {
    auto global_scope = timer_global.scope();
    std::vector<std::thread> threads;
    for (size_t idx = 0; idx < NUM_THREADS; ++idx) {
      threads.emplace_back([&timer]() {
        auto scope = timer.scope();
        std::this_thread::sleep_for(std::chrono::seconds(1));
      });
    }
    for (auto& thread : threads) {
      thread.join();
    }
  }
  auto mus = timer.get_microseconds();
  EXPECT_TRUE(is_close(NUM_THREADS * kOneSecInMus, mus, NUM_THREADS));
  auto global_mus = timer_global.get_microseconds();
  // Assume that thread startup is not too expensive.
  EXPECT_TRUE(is_close(kOneSecInMus, global_mus));
}

TEST(AccumulatingTimer, multipleThreadsMultipleScopes) {
  AccumulatingTimer timer{};
  AccumulatingTimer timer_global{};
  {
    auto global_scope = timer_global.scope();
    std::vector<std::thread> threads;
    for (size_t idx = 0; idx < NUM_THREADS; ++idx) {
      threads.emplace_back([&timer]() {
        for (int j = 0; j < NUM_ITERS; ++j) {
          auto scope = timer.scope();
          std::this_thread::sleep_for(std::chrono::seconds(1));
        }
      });
    }
    for (auto& thread : threads) {
      thread.join();
    }
  }
  auto mus = timer.get_microseconds();
  EXPECT_TRUE(is_close(
      NUM_ITERS * NUM_THREADS * kOneSecInMus, mus, NUM_THREADS * NUM_ITERS));
  auto global_mus = timer_global.get_microseconds();
  // Assume that thread startup is not too expensive.
  EXPECT_TRUE(is_close(NUM_ITERS * kOneSecInMus, global_mus, NUM_ITERS));
}

TEST(AccumulatingTimer, shortDurationsAreNotTruncated) {
  AccumulatingTimer timer{};
  constexpr int kDurations = 2000;
  constexpr auto kDuration = std::chrono::nanoseconds(500);
  for (int i = 0; i < kDurations; ++i) {
    timer.add(kDuration);
  }
  // Truncating each duration to whole microseconds would sum to zero.
  EXPECT_EQ(timer.get_microseconds(), 1000);
  EXPECT_DOUBLE_EQ(timer.get_seconds(), 0.001);
}
