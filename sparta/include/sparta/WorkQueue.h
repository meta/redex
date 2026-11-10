/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <algorithm>
#include <atomic>
#include <boost/optional/optional.hpp>
#include <chrono>
#include <condition_variable>
#include <exception>
#include <mutex>
#include <numeric>
#include <random>
#include <thread>
#include <utility>

#include <sparta/Arity.h>
#include <sparta/Exceptions.h>
#include <sparta/ThreadPool.h>

namespace sparta {

namespace parallel {

/**
 * Sparta uses the number of physical cores.
 */
static inline unsigned int default_num_threads() {
  unsigned int threads = std::thread::hardware_concurrency();
  return std::max(1u, threads);
}

} // namespace parallel

namespace workqueue_impl {

/**
 * Creates a random ordering of which threads to visit.  This prevents threads
 * from being prematurely emptied (if everyone targets thread 0, for example)
 *
 * Each thread should empty its own queue first, so we explicitly set the
 * thread's index as the first element of the list.
 */
inline std::vector<unsigned int> create_permutation(unsigned int num,
                                                    unsigned int thread_idx) {
  std::vector<unsigned int> attempts(num);
  std::iota(attempts.begin(), attempts.end(), 0);
  auto seed = std::chrono::system_clock::now().time_since_epoch().count();
  std::shuffle(attempts.begin(), attempts.end(),
               std::default_random_engine(seed));
  std::iter_swap(attempts.begin(),
                 std::find(attempts.begin(), attempts.end(), thread_idx));
  return attempts;
}

class Semaphore {
 public:
  explicit Semaphore(size_t initial = 0u) : m_count(initial) {}

  inline void give(size_t n = 1u) {
    {
      std::lock_guard<std::mutex> lock(m_mtx);
      m_count += n;
    }
    if (n == 1) {
      m_cv.notify_one();
    } else {
      m_cv.notify_all(); // A bit suboptimal, but easier than precise counting.
    }
  }

  inline void take() {
    std::unique_lock<std::mutex> lock(m_mtx);
    while (m_count == 0) {
      m_cv.wait(lock);
    }
    --m_count;
  }

  inline void take_all() {
    std::lock_guard<std::mutex> lock(m_mtx);
    m_count = 0;
  }

 private:
  std::mutex m_mtx;
  std::condition_variable m_cv;
  size_t m_count;
};

struct StateCounters {
  std::atomic_uint num_non_empty_initial;
  std::atomic_uint num_non_empty_additional;
  std::atomic_uint num_running;
  const unsigned int num_all;
  // Mutexes aren't move-able.
  std::unique_ptr<Semaphore> waiter;

  explicit StateCounters(unsigned int num)
      : num_non_empty_initial(0),
        num_non_empty_additional(0),
        num_running(0),
        num_all(num),
        waiter(new Semaphore(0)) {}
  StateCounters(StateCounters&& other)
      : num_non_empty_initial(other.num_non_empty_initial.load()),
        num_non_empty_additional(other.num_non_empty_additional.load()),
        num_running(other.num_running.load()),
        num_all(other.num_all),
        waiter(std::move(other.waiter)) {}
};

} // namespace workqueue_impl

template <class Input, typename Executor>
class WorkQueue;

template <class Input>
class WorkerState final {
 public:
  WorkerState(size_t id, workqueue_impl::StateCounters* sc, bool can_push)
      : m_id(id), m_state_counters(sc), m_can_push_task(can_push) {}

  /*
   * Add more items to the queue of the currently-running worker. When a
   * `WorkQueue` is running, this should be used instead of
   * `WorkQueue::add_item()` as the latter is not thread-safe.
   */
  void push_task(Input task) {
    SPARTA_RUNTIME_CHECK(m_can_push_task, internal_error());
    auto* node = new Node{std::move(task), m_additional_tasks.load()};
    do {
      if (node->prev == nullptr) {
        // Increment before updating additional_tasks, as some other thread
        // might steal our new additional task immediately
        m_state_counters->num_non_empty_additional.fetch_add(1);
      }
      // Try to add a new head to the list
    } while (!m_additional_tasks.compare_exchange_strong(node->prev, node));
    if (m_state_counters->num_running.load() < m_state_counters->num_all) {
      m_state_counters->waiter->give(1u); // May consider waking all.
    }
  }

  size_t worker_id() const { return m_id; }

  void set_running(bool running) {
    if (m_running && !running) {
      auto num = m_state_counters->num_running.fetch_sub(1);
      SPARTA_RUNTIME_CHECK(num > 0, internal_error());
      SPARTA_UNUSED_VARIABLE(num);
    } else if (!m_running && running) {
      m_state_counters->num_running.fetch_add(1);
    }
    m_running = running;
  };

  ~WorkerState() {
    for (auto* erased = m_erased.load(); erased != nullptr;) {
      auto* next = erased->next_erased;
      delete erased;
      erased = next;
    }
  }

 private:
  boost::optional<Input> pop_task(WorkerState<Input>* other) {
    auto i = m_next_initial_task.load();
    auto size = m_initial_tasks.size();
    // If i < size, (try to) increment.
    while (i < size && !m_next_initial_task.compare_exchange_strong(i, i + 1)) {
    }
    // If we successfully incremented, we can pop.
    if (i < size) {
      if (size - 1 == i) {
        auto num = m_state_counters->num_non_empty_initial.fetch_sub(1);
        SPARTA_RUNTIME_CHECK(num > 0, internal_error());
        SPARTA_UNUSED_VARIABLE(num);
      }
      other->set_running(true);
      return boost::optional<Input>(std::move(m_initial_tasks.at(i)));
    }

    auto* node = m_additional_tasks.load();
    // Try to remove head from list
    while (node != nullptr) {
      bool exchanged =
          m_additional_tasks.compare_exchange_strong(node, node->prev);
      if (exchanged) {
        // We successfully dequeued an element,
        // node holds the element we intend to remove.
        if (node->prev == nullptr) {
          auto num = m_state_counters->num_non_empty_additional.fetch_sub(1);
          SPARTA_RUNTIME_CHECK(num > 0, internal_error());
          SPARTA_UNUSED_VARIABLE(num);
        }
        // We can't just delete the node right here, as there may be racing
        // pop_tasks that read the `->prev` field above. So we stack it away in
        // a different list that gets destructed later, linked through a field
        // of its own: writing `->prev` here would race with those reads.
        node->next_erased = m_erased.load();
        while (!m_erased.compare_exchange_strong(node->next_erased, node)) {
        }
        other->set_running(true);
        return boost::optional<Input>(std::move(node->task));
      }
      // Otherwise, we depend on the behaviour of
      // compare_exchange_strong to update `node` with the actual
      // contained value.
    }

    return boost::none;
  }

  size_t m_id;
  bool m_running{false};
  std::vector<Input> m_initial_tasks;
  std::atomic<size_t> m_next_initial_task{0};
  struct Node {
    Input task;
    Node* prev;
    Node* next_erased{nullptr};
  };
  std::atomic<Node*> m_additional_tasks{nullptr};
  std::atomic<Node*> m_erased{nullptr};
  workqueue_impl::StateCounters* m_state_counters;
  const bool m_can_push_task{false};

  template <class, typename>
  friend class WorkQueue;
};

template <class Input, typename Executor>
class WorkQueue {
 private:
  // Using templates for Executor to avoid the performance overhead of
  // std::function
  Executor m_executor;
  std::vector<std::unique_ptr<WorkerState<Input>>> m_states;
  const size_t m_num_threads{1};
  size_t m_insert_idx{0};
  workqueue_impl::StateCounters m_state_counters;
  const bool m_can_push_task{false};
  AsyncRunner* m_async_runner;

  // Run the worker on num_runners threads, and wait for them to finish.
  template <typename Worker>
  void run_in_parallel(const Worker& worker, size_t num_runners);

 public:
  explicit WorkQueue(Executor,
                     unsigned int num_threads = parallel::default_num_threads(),
                     // push_tasks_while_running:
                     // * When this flag is true, all threads stay alive until
                     //   the last task is finished. Useful when threads are
                     //   adding more work to the queue via
                     //   `WorkerState::push_task`.
                     // * When this flag is false, threads can
                     //   exit as soon as there is no more work (to avoid
                     //   preempting a thread that has useful work)
                     bool push_tasks_while_running = false,
                     AsyncRunner* async_runner = nullptr);

  // copies are not allowed
  WorkQueue(const WorkQueue&) = delete;
  // moves are allowed
  WorkQueue(WorkQueue&&) = default;

  /* Adds (a copy of) an item to a pseudo-random worker. */
  void add_item(Input task);

  /* Add an item on the queue of the given worker. */
  void add_item(Input task, size_t worker_id);

  /**
   * Spawn threads and evaluate function.  This method blocks.
   */
  void run_all();

  template <class>
  friend class WorkerState;
};

template <class Input, typename Executor>
WorkQueue<Input, Executor>::WorkQueue(Executor executor,
                                      unsigned int num_threads,
                                      bool push_tasks_while_running,
                                      AsyncRunner* async_runner)
    : m_executor(executor),
      m_num_threads(num_threads),
      m_state_counters(num_threads),
      m_can_push_task(push_tasks_while_running),
      m_async_runner(async_runner) {
  SPARTA_RUNTIME_CHECK(num_threads >= 1, invalid_argument()
                                             << argument_name("num_threads"));
  for (unsigned int i = 0; i < m_num_threads; ++i) {
    m_states.emplace_back(std::make_unique<WorkerState<Input>>(
        i, &m_state_counters, m_can_push_task));
  }
}

template <class Input, typename Executor>
void WorkQueue<Input, Executor>::add_item(Input task) {
  m_insert_idx = (m_insert_idx + 1) % m_num_threads;
  SPARTA_RUNTIME_CHECK(m_insert_idx < m_states.size(), internal_error());
  m_states[m_insert_idx]->m_initial_tasks.push_back(std::move(task));
}

template <class Input, typename Executor>
void WorkQueue<Input, Executor>::add_item(Input task, size_t worker_id) {
  SPARTA_RUNTIME_CHECK(worker_id < m_states.size(),
                       invalid_argument() << argument_name("worker_id"));
  m_states[worker_id]->m_initial_tasks.push_back(std::move(task));
}

/*
 * Each worker thread pulls from its own queue first, and then once finished
 * looks randomly at other queues to try and steal work.
 */
template <class Input, typename Executor>
void WorkQueue<Input, Executor>::run_all() {
  m_state_counters.num_non_empty_initial.store(0, std::memory_order_relaxed);
  m_state_counters.num_non_empty_additional.store(0, std::memory_order_relaxed);
  m_state_counters.num_running.store(0, std::memory_order_relaxed);
  m_state_counters.waiter->take_all();
  std::mutex exception_mutex;
  std::exception_ptr exception;
  auto worker = [&](WorkerState<Input>* state, size_t state_idx) {
    try {
      auto attempts =
          workqueue_impl::create_permutation(m_num_threads, state_idx);
      while (true) {
        auto have_task = false;
        for (auto idx : attempts) {
          auto other_state = m_states[idx].get();
          auto task = other_state->pop_task(state);
          if (task) {
            have_task = true;
            m_executor(state, std::move(*task));
            break;
          }
        }
        if (have_task) {
          continue;
        }

        state->set_running(false);
        if (!m_can_push_task) {
          // New tasks can't be added. We don't need to wait for the currently
          // running jobs to finish.
          return;
        }

        // Let the thread quit if all the threads are not running and there
        // is no task in any queue.
        if (m_state_counters.num_running.load() == 0 &&
            m_state_counters.num_non_empty_initial.load() == 0 &&
            m_state_counters.num_non_empty_additional.load() == 0) {
          // Wake up everyone who might be waiting, so they can quit.
          m_state_counters.waiter->give(m_state_counters.num_all);
          return;
        }

        m_state_counters.waiter->take(); // Wait for work.
      }
    } catch (...) {
      {
        std::unique_lock<std::mutex> lock(exception_mutex);
        if (exception) {
          // An exception was already caught.
          state->set_running(false);
          return;
        }
        exception = std::current_exception();
      }

      // Make all other threads stop gracefully, by stealing their tasks.
      for (unsigned int idx = 0; idx < m_num_threads; idx++) {
        auto other_state = m_states[idx].get();
        while (true) {
          auto task = other_state->pop_task(state);
          if (!task) {
            break;
          }
        }
      }
      state->set_running(false);
      m_state_counters.waiter->give(m_state_counters.num_all);
    }
  };

  size_t initial_task_count{0};
  for (size_t i = 0; i < m_num_threads; ++i) {
    const auto size = m_states[i]->m_initial_tasks.size();
    initial_task_count += size;
    if (size != 0) {
      m_state_counters.num_non_empty_initial.fetch_add(
          1, std::memory_order_relaxed);
    }
  }

  const auto num_runners = m_can_push_task
                               ? m_num_threads
                               : std::min(m_num_threads, initial_task_count);
  run_in_parallel(worker, num_runners);

  for (size_t i = 0; i < m_num_threads; ++i) {
    SPARTA_RUNTIME_CHECK(!m_states[i]->m_running, internal_error());
  }

  if (exception) {
    std::rethrow_exception(exception);
  }

  for (size_t i = 0; i < m_num_threads; ++i) {
    SPARTA_RUNTIME_CHECK(
        m_states[i]->m_next_initial_task.load(std::memory_order_relaxed) ==
            m_states[i]->m_initial_tasks.size(),
        internal_error());
    SPARTA_RUNTIME_CHECK(m_states[i]->m_additional_tasks.load(
                             std::memory_order_relaxed) == nullptr,
                         internal_error());
  }
}

template <class Input, typename Executor>
template <typename Worker>
void WorkQueue<Input, Executor>::run_in_parallel(const Worker& worker,
                                                 size_t num_runners) {
  if (num_runners == 0) {
    return;
  }
  if (m_async_runner) {
    // We have been given a custom way to run work asynchronously, so we use
    // that (instead of spawning and joining threads explicitly).

    // We need some scaffolding to track how many spawned async runs are still
    // in progress.
    std::condition_variable condition_variable;
    std::mutex mutex;
    size_t remaining = num_runners;
    auto func = [&](size_t i) {
      worker(m_states[i].get(), i);
      // Notify under the lock: once `remaining` is zero the waiter can return
      // and destroy `condition_variable`, which a notification after the
      // unlock would then use.
      std::lock_guard<std::mutex> lock(mutex);
      if (--remaining == 0) {
        condition_variable.notify_one();
      }
    };

    for (size_t i = 0; i < num_runners; ++i) {
      m_async_runner->run_async(func, i);
    }

    // Wait for all spawned async runs to finish.
    std::unique_lock<std::mutex> lock(mutex);
    condition_variable.wait(lock, [&]() { return remaining == 0; });
    return;
  }

  std::vector<std::thread> all_threads;
  all_threads.reserve(num_runners);
  for (size_t i = 0; i < num_runners; ++i) {
    all_threads.emplace_back(worker, m_states[i].get(), i);
  }

  for (auto& thread : all_threads) {
    thread.join();
  }
}

namespace workqueue_impl {
// Helper classes so the type of Executor can be inferred
template <typename Input, typename Fn>
struct NoStateWorkQueueHelper {
  Fn fn;
  void operator()(WorkerState<Input>*, Input a) { fn(std::move(a)); }
};
template <typename Input, typename Fn>
struct WithStateWorkQueueHelper {
  Fn fn;
  void operator()(WorkerState<Input>* state, Input a) {
    fn(state, std::move(a));
  }
};
} // namespace workqueue_impl

// These functions are the most convenient way to create a WorkQueue
template <class Input,
          typename Fn,
          typename std::enable_if<Arity<Fn>::value == 1, int>::type = 0>
WorkQueue<Input, workqueue_impl::NoStateWorkQueueHelper<Input, Fn>> work_queue(
    const Fn& fn,
    unsigned int num_threads = parallel::default_num_threads(),
    bool push_tasks_while_running = false,
    AsyncRunner* async_runner = nullptr) {
  return WorkQueue<Input, workqueue_impl::NoStateWorkQueueHelper<Input, Fn>>(
      workqueue_impl::NoStateWorkQueueHelper<Input, Fn>{fn}, num_threads,
      push_tasks_while_running, async_runner);
}
template <class Input,
          typename Fn,
          typename std::enable_if<Arity<Fn>::value == 2, int>::type = 0>
WorkQueue<Input, workqueue_impl::WithStateWorkQueueHelper<Input, Fn>>
work_queue(const Fn& fn,
           unsigned int num_threads = parallel::default_num_threads(),
           bool push_tasks_while_running = false,
           AsyncRunner* async_runner = nullptr) {
  return WorkQueue<Input, workqueue_impl::WithStateWorkQueueHelper<Input, Fn>>(
      workqueue_impl::WithStateWorkQueueHelper<Input, Fn>{fn}, num_threads,
      push_tasks_while_running, async_runner);
}

} // namespace sparta
