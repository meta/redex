/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <chrono>
#include <list>
#include <memory>
#include <mutex>
#include <string>
#include <utility>
#include <vector>

struct Timer {
  explicit Timer(std::string msg, bool indent = true);
  ~Timer();

  using times_t = std::vector<std::pair<std::string, double>>;

  // there should be no currently running Timers when this function is called
  static const times_t& get_times() { return get_s_times(); }
  static void clear_times() { get_s_times().clear(); }

  static void add_timer(std::string msg, double dur_s);

  // Run a callable under a Timer scope. Equivalent to:
  //   { Timer t(msg); fn(); }
  template <typename Fn>
  static decltype(auto) scope(std::string msg, Fn&& fn) {
    Timer t(std::move(msg));
    return std::forward<Fn>(fn)();
  }

 private:
  static std::mutex& get_s_lock();
  static times_t& get_s_times();
  static int s_indent;
  std::string m_msg;
  std::chrono::high_resolution_clock::time_point m_start;
  bool m_indent;
};

// Helper to record a chrome trace event without exposing ChromeTraceWriter
// in this header. Defined in Timer.cpp.
void maybe_record_chrome_trace(
    const std::string& name,
    std::chrono::high_resolution_clock::time_point start,
    std::chrono::high_resolution_clock::time_point end);

// An accumulating thread-safe timer with a scope-based approach.
// Note: uses uint64_t nanoseconds to simplify and use optimized atomic. Each
// scope adds its exact duration: truncating every scope to a coarser unit
// would undercount timers whose scopes are short and numerous.
class AccumulatingTimer {
 public:
  class AccumulatingTimerScope {
   public:
    explicit AccumulatingTimerScope(AccumulatingTimer* context)
        : m_context(context),
          m_start(std::chrono::high_resolution_clock::now()) {}
    ~AccumulatingTimerScope() {
      m_context->add(std::chrono::high_resolution_clock::now() - m_start);
    }

    // Disallow copying.
    AccumulatingTimerScope(const AccumulatingTimerScope&) = delete;
    AccumulatingTimerScope& operator=(const AccumulatingTimerScope&) = delete;

    // Allow move.
    AccumulatingTimerScope(AccumulatingTimerScope&&) = default;
    AccumulatingTimerScope& operator=(AccumulatingTimerScope&&) = default;

   private:
    AccumulatingTimer* m_context;
    std::chrono::high_resolution_clock::time_point m_start;
  };

  AccumulatingTimer() {}

  explicit AccumulatingTimer(std::string msg);

  AccumulatingTimerScope scope() { return AccumulatingTimerScope(this); }

  void add(std::chrono::nanoseconds duration) {
    m_nanoseconds->fetch_add((uint64_t)duration.count());
  }

  uint64_t get_microseconds() const { return m_nanoseconds->load() / 1000; }
  double get_seconds() const {
    return ((double)m_nanoseconds->load()) / 1000000000;
  }

  using times_t = std::vector<std::pair<std::string, double>>;

  // there should be no currently running Timers when this function is called
  static times_t get_times();

 private:
  using times_impl_t =
      std::list<std::pair<std::string, std::shared_ptr<std::atomic<uint64_t>>>>;

  static void add_timer(std::string msg,
                        std::shared_ptr<std::atomic<uint64_t>> nanoseconds);

  static std::mutex& get_s_lock();
  // We dynamically allocate the static list of times to avoid problems with the
  // static initialization / destruction order.
  static times_impl_t* s_times;
  std::shared_ptr<std::atomic<uint64_t>> m_nanoseconds{
      std::make_shared<std::atomic<uint64_t>>(0)};
};
