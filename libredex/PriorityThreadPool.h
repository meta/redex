/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>

#include <chrono>
#include <condition_variable>
#include <mutex>
#include <queue>
#include <vector>

#include "Debug.h"
#include "ThreadPool.h"
#include "WorkQueue.h" // For redex_queue_exception_handler.

/*
 * Individual work items are posted with a priority:
 * - Work items with the highest priority are executed first.
 * - Priorities are signed integers, allowing flexibility for negative
 *   priorities.
 *
 * The thread-pool must be initialized with a positive number of threads to be
 * functional.
 */
class PriorityThreadPool {
 private:
  std::vector<boost::thread> m_pool;
  size_t m_threads{0};
  // The following data structures are guarded by this mutex.
  std::mutex m_mutex;
  size_t m_running{0};
  std::condition_variable m_work_condition;
  std::condition_variable m_done_condition;
  std::condition_variable m_not_running_condition;
  std::map<int, std::queue<std::function<void()>>> m_pending_work_items;
  std::atomic<size_t> m_running_work_items{0};
  std::chrono::duration<double> m_waited_time{0};
  bool m_shutdown{false};

 public:
  // Creates an instance with a default number of threads
  PriorityThreadPool() {
    set_num_threads(redex_parallel::default_num_threads());
  }

  // Creates an instance with a custom number of threads
  explicit PriorityThreadPool(size_t num_threads) {
    set_num_threads(num_threads);
  }

  ~PriorityThreadPool() {
    // If the pool was created (>0 threads), `join` must be manually called
    // before the executor may be destroyed.
    always_assert(m_pending_work_items.empty());
    if (m_threads > 0) {
      always_assert(m_shutdown);
      always_assert(m_running_work_items == 0);
    }
  }

  long get_waited_seconds() {
    return std::chrono::duration_cast<std::chrono::seconds>(m_waited_time)
        .count();
  }

  // The number of threads may be set at most once to a positive number
  void set_num_threads(size_t num_threads) {
    always_assert(m_threads == 0);
    always_assert(!m_shutdown);
    m_threads = num_threads;
    {
      std::unique_lock<std::mutex> lock{m_mutex};
      m_running = num_threads;
    }

    if (num_threads == 0) {
      return;
    }

    sparta::AsyncRunner* async_runner =
        redex_thread_pool::ThreadPool::get_instance();
    if (async_runner != nullptr) {
      for (size_t i = 0; i < num_threads; ++i) {
        async_runner->run_async(&PriorityThreadPool::run, this);
      }
      return;
    }

    boost::thread::attributes attrs;
    attrs.set_stack_size(static_cast<size_t>(8 * 1024 * 1024)); // 8MB stack.

    for (size_t i = 0; i < num_threads; ++i) {
      m_pool.emplace_back(attrs, [this]() { this->run(); });
    }
  }

  // Post a work item with a priority. This method is thread safe.
  void post(int priority, std::function<void()> f) {
    always_assert(m_threads > 0);
    std::unique_lock<std::mutex> lock{m_mutex};
    always_assert(!m_shutdown);
    m_pending_work_items[priority].push(std::move(f));
    m_work_condition.notify_one();
  }

  // Wait for all work items to be processed.
  void wait(bool init_shutdown = false) {
    always_assert(m_threads > 0);
    auto start = std::chrono::steady_clock::now();
    {
      // We wait until *all* work is done, i.e. nothing is running or pending.
      std::unique_lock<std::mutex> lock{m_mutex};
      m_done_condition.wait(lock, [&]() {
        return m_running_work_items == 0 && m_pending_work_items.empty();
      });
      if (init_shutdown) {
        m_shutdown = true;
        m_work_condition.notify_all();
      }
    }
    auto end = std::chrono::steady_clock::now();
    m_waited_time += end - start;
  }

  void join(bool allow_new_work = true) {
    always_assert(m_threads > 0);
    always_assert(!m_shutdown);
    if (!allow_new_work) {
      std::unique_lock<std::mutex> lock{m_mutex};
      m_shutdown = true;
      m_work_condition.notify_all();
    }
    wait(/*init_shutdown=*/allow_new_work);
    {
      std::unique_lock<std::mutex> lock{m_mutex};
      m_not_running_condition.wait(lock, [this] { return m_running == 0; });
    }
    for (auto& thread : m_pool) {
      thread.join();
    }
    m_pool = decltype(m_pool)();
  }

 private:
  void run() {
    auto not_running = [&]() {
      std::unique_lock<std::mutex> lock{m_mutex};
      if (--m_running == 0) {
        m_not_running_condition.notify_one();
      }
    };

    for (bool first = true;; first = false) {
      auto highest_priority_f = [&]() -> std::function<void()> {
        std::unique_lock<std::mutex> lock{m_mutex};

        // Notify when *all* work is done, i.e. nothing is running or pending.
        //
        // Moving this check here from the end of the loop avoids
        // potential repeated lock acquisition.
        if (!first && m_pending_work_items.empty() &&
            m_running_work_items == 0) {
          m_done_condition.notify_one();
        }

        // Wait for work or shutdown.
        m_work_condition.wait(lock, [&]() {
          return !m_pending_work_items.empty() || m_shutdown;
        });
        if (m_pending_work_items.empty()) {
          redex_assert(m_shutdown);
          return nullptr;
        }

        m_running_work_items++;

        // Find work item with highest priority
        auto p_it = std::prev(m_pending_work_items.end());
        auto& queue = p_it->second;
        auto f = std::move(queue.front());
        queue.pop();
        if (queue.empty()) {
          m_pending_work_items.erase(p_it);
        }
        return f;
      }();
      if (!highest_priority_f) {
        not_running();
        return;
      }

      // Run!
      try {
        highest_priority_f();
      } catch (std::exception& e) {
        redex_workqueue_impl::redex_queue_exception_handler(e);
        not_running();
        throw;
      }

      --m_running_work_items;
    }
  }
};
