/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <tuple>
#include <utility>
#include <vector>

#include "ControlFlow.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "EditableCfgAdapter.h"
#include "IRCode.h"
#include "Match.h"
#include "Thread.h"
#include "Trace.h"
#include "WorkQueue.h"

/**
 * A wrapper around a type which allocates it aligned to the cache line.
 * This avoids potential cache line bouncing as different cores issue
 * concurrent writes to distinct instances of \p T that would otherwise have
 * occupied the same line.
 */
template <typename T>
class CacheAligned {
 public:
  template <typename... Args>
  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  CacheAligned(Args&&... args) : m_aligned(std::forward<Args>(args)...) {}

  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  inline operator T&();

 private:
  alignas(CACHE_LINE_SIZE) T m_aligned;
};

template <typename T>
inline CacheAligned<T>::operator T&() {
  // TODO: Restore assertion.
  // struct Canary {
  //   int x;
  //   CacheAligned<T> aligned;
  // };
  // static_assert(offsetof(Canary, aligned) % CACHE_LINE_SIZE == 0,
  //              "Expecting alignment to cache line size.");

  return m_aligned;
}

/**
 * A collection of methods useful for iterating over elements of DexClasses.
 *
 * The name is intentionally lowercase. Think of this as a namespace with public
 * and private visibility.
 *
 * This is header-only because of the template arguments.
 */

class walk {
 private:
  static constexpr bool all_methods(DexMethod*) { return true; }

 public:
  // This is a "static class". Disallow construction.
  walk() = delete;
  ~walk() = delete;

  // Call walker on all classes in `classes`
  //   WalkerFn should accept a `DexClass*`.
  template <class Classes, typename WalkerFn>
  static void classes(Classes const& classes, const WalkerFn& walker) {
    for (auto const& cls : classes) {
      walker(cls);
    }
  }

  // Call walker on all methods defined in `classes`
  //   WalkerFn should accept a `DexMethod*`.
  template <class Classes, typename WalkerFn>
  static void methods(const Classes& classes, const WalkerFn& walker) {
    for (const auto& cls : classes) {
      iterate_methods(cls, walker);
    };
  }

  // Call `walker` on all fields defined in `classes`
  //   WalkerFn should accept a `DexField*`.
  template <class Classes, typename WalkerFn>
  static void fields(const Classes& classes, const WalkerFn& walker) {
    for (const auto& cls : classes) {
      iterate_fields(cls, walker);
    };
  }

  // Call `walker` on the code of every method defined in classes that
  // satisfies the filter function
  //   FilterFn should accept `DexMethod*` and return a bool.
  //   WalkerFn should accept `(DexMethod*, IRCode&)`.
  template <class Classes, typename FilterFn, typename WalkerFn>
  static void code(const Classes& classes,
                   const FilterFn& filter,
                   const WalkerFn& walker) {
    for (const auto& cls : classes) {
      iterate_code(cls, filter, walker);
    };
  }

  // Same as `code()` but with a filter that accepts all methods
  template <class Classes, typename WalkerFn>
  static void code(const Classes& classes, const WalkerFn& walker) {
    walk::code(classes, all_methods, walker);
  }

  // Call `walker` on every instruction in the code of every method defined in
  // `classes` that satisfies the filter function.
  //   FilterFn should accept `DexMethod*` and return a bool.
  //   WalkerFn should accept `(DexMethod*, IRInstruction*)`.
  template <class Classes, typename FilterFn, typename WalkerFn>
  static void opcodes(const Classes& classes,
                      const FilterFn& filter,
                      const WalkerFn& walker) {
    for (const auto& cls : classes) {
      iterate_opcodes(cls, filter, walker);
    };
  }

  // Same as `opcodes()` but with a filter that accepts all methods
  template <class Classes, typename WalkerFn>
  static void opcodes(const Classes& classes, const WalkerFn& walker) {
    walk::opcodes(classes, all_methods, walker);
  }

  // Call `walker` on every annotation on the classes (and its fields, methods,
  // and method parameters) defined in `classes`
  //   WalkerFn should accept a `DexAnnotation*`.
  template <class Classes, typename WalkerFn>
  static void annotations(const Classes& classes, const WalkerFn& walker) {
    for (auto& cls : classes) {
      iterate_annotations(cls, walker);
    }
  }

  /**
   * Visit sequences of opcodes that satisfy the give matcher.
   *
   * Example
   * -------
   *
   * The following code (taken from ReachableClasses) visits all opcode
   * sequences that match the form "const-string, invoke-static" where
   * invoke-static is specifically invoking Class.forName that takes one
   * argument.
   *
   * In the walker callback, you can see that the opcodes are further inspected
   * to ensure that the register that const-string loads into is actually the
   * register that is referenced by invoke-static. (Without captures, this can't
   * be expressed in the matcher language alone)
   *
   * The opcodes that match are passed in as a pointer to an array of
   * IRInstruction pointers. The size of the array is passed in as 'n'.
   *
   * Example Code
   * ------------
   *
   * auto match = std::make_tuple(
   *     m::const_string(),
   *     m::invoke_static(
   *         m::has_method(m::named<DexMethod>("forName") &&
   *                       m::on_class<DexMethod>("Ljava/lang/Class;")) &&
   *         m::has_n_args(1)));
   *
   * match_opcodes(classes,
   *               match,
   *               [&](DexMethod* m, const std::vector<IRInstruction*>& insns) {
   *                 auto const_string = insns[0];
   *                 auto invoke_static = insns[1];
   *                 // Make sure that the registers agree
   *                 if (const_string->dest() == invoke_static->src(0)) {
   *                   ...
   *                 }
   *               });
   */

  template <class Classes,
            typename Predicate,
            size_t N = std::tuple_size<Predicate>::value,
            typename Walker = void(DexMethod*,
                                   const std::vector<IRInstruction*>&),
            typename FilterFn>
  static void matching_opcodes(const Classes& classes,
                               const Predicate& predicate,
                               const Walker& walker,
                               const FilterFn& filter = all_methods) {
    for (const auto& cls : classes) {
      iterate_matching(cls, predicate, walker, filter);
    }
  }

  // walker that respects basic block boundaries.
  //
  // It will not match a pattern that crosses block boundaries
  //
  // WalkerFn should accept
  //     `(DexMethod*, cfg::Block*, const std::vector<IRInstruction*>&)`
  template <class Classes,
            typename Predicate,
            typename WalkerFn,
            typename FilterFn = decltype(all_methods),
            size_t N = std::tuple_size<Predicate>::value>
  static void matching_opcodes_in_block(const Classes& classes,
                                        const Predicate& predicate,
                                        const WalkerFn& walker,
                                        const FilterFn& filter = all_methods) {
    for (const auto& cls : classes) {
      iterate_matching_block(cls, predicate, walker, filter);
    }
  }

  template <typename Predicate,
            typename WalkerFn,
            size_t N = std::tuple_size<Predicate>::value>
  static void matching_opcodes_in_block(DexMethod& method,
                                        const Predicate& predicate,
                                        const WalkerFn& walker) {
    always_assert(method.get_code() != nullptr);
    iterate_matching_block_worker(
        method, *method.get_code(), predicate, walker);
  }

 private:
  /* The iterate_* methods take a single dexclass and call the walker on the
   * elements requested. The reason that these are done on a class level is so
   * that we can share code with the `parallel::` methods.
   */
  template <typename WalkerFn>
  static void iterate_methods(const DexClass* cls, const WalkerFn& walker) {
    for (auto* dmethod : cls->get_dmethods()) {
      TraceContext context(dmethod);
      walker(dmethod);
    }
    for (auto* vmethod : cls->get_vmethods()) {
      TraceContext context(vmethod);
      walker(vmethod);
    }
  }

  template <typename WalkerFn>
  static void iterate_fields(const DexClass* cls, const WalkerFn& walker) {
    for (auto* ifield : cls->get_ifields()) {
      walker(ifield);
    }
    for (auto* sfield : cls->get_sfields()) {
      walker(sfield);
    }
  }

  template <typename FilterFn, typename WalkerFn>
  static void iterate_code(const DexClass* cls,
                           const FilterFn& filter,
                           const WalkerFn& walker) {
    iterate_methods(cls, [&filter, &walker](DexMethod* m) {
      if (filter(m)) {
        auto* code = m->get_code();
        if (code) {
          walker(m, *code);
        }
      }
    });
  }

  template <typename FilterFn, typename WalkerFn>
  static void iterate_opcodes(const DexClass* cls,
                              const FilterFn& filter,
                              const WalkerFn& walker) {
    iterate_code(cls, filter, [&walker](DexMethod* m, IRCode& code) {
      cfg_adapter::iterate(&code, [&walker, &m](MethodItemEntry& mie) {
        walker(m, mie.insn);
        return cfg_adapter::LOOP_CONTINUE;
      });
    });
  }

  template <typename WalkerFn>
  static void iterate_annotations(DexClass* cls, const WalkerFn& walker) {
    call_annotation_walker(cls, walker);
    iterate_fields(cls, [&walker](DexField* field) {
      call_annotation_walker(field, walker);
    });
    iterate_methods(cls, [&walker](DexMethod* method) {
      call_annotation_walker(method, walker);
      const auto& param_anno = method->get_param_anno();
      if (!param_anno) {
        return;
      }
      for (const auto& it : *param_anno) {
        auto& anno_list = it.second->get_annotations();
        for (auto& anno : anno_list) {
          walker(anno.get());
        }
      }
    });
  }

  template <typename WalkerFn>
  static void iterate_encoded_values(DexClass* cls, const WalkerFn& walker) {
    iterate_fields(cls, [&walker](DexField* field) {
      if (const auto* value = field->get_static_value()) {
        walker(static_cast<const Gatherable&>(*value));
      }
    });
    iterate_annotations(cls, [&walker](const DexAnnotation* annotation) {
      walker(static_cast<const Gatherable&>(*annotation));
    });
  }

  template <class T, typename WalkerFn>
  static void call_annotation_walker(T* dex_thingy, const WalkerFn& walker) {
    const auto& anno_set = dex_thingy->get_anno_set();
    if (!anno_set) {
      return;
    }
    auto& anno_list = anno_set->get_annotations();
    for (auto& anno : anno_list) {
      walker(anno.get());
    }
  }

  template <typename Predicate,
            size_t N = std::tuple_size<Predicate>::value,
            typename Walker = void(DexMethod*,
                                   const std::vector<IRInstruction*>&)>
  static void iterate_matching_worker(DexMethod& m,
                                      IRCode& ir_code,
                                      const Predicate& predicate,
                                      const Walker& walker) {
    std::vector<IRInstruction*> insns;
    for (MethodItemEntry& mie : ir_list::InstructionIterable(ir_code)) {
      insns.emplace_back(mie.insn);
    }

    std::vector<std::vector<IRInstruction*>> matches;
    m::find_matches(insns, predicate, matches);
    for (const std::vector<IRInstruction*>& matching_insns : matches) {
      walker(&m, matching_insns);
    }
  }

  template <typename Predicate,
            size_t N = std::tuple_size<Predicate>::value,
            typename Walker = void(DexMethod*,
                                   const std::vector<IRInstruction*>&),
            typename FilterFn = decltype(all_methods)>
  static void iterate_matching(DexClass* cls,
                               const Predicate& predicate,
                               const Walker& walker,
                               const FilterFn& filter = all_methods) {
    iterate_code(
        cls, filter, [&predicate, &walker](DexMethod* m, IRCode& ir_code) {
          iterate_matching_worker(*m, ir_code, predicate, walker);
        });
  }

  template <typename Predicate,
            size_t N = std::tuple_size<Predicate>::value,
            typename WalkerFn>
  static void iterate_matching_block_worker(DexMethod& m,
                                            IRCode& ir_code,
                                            const Predicate& predicate,
                                            const WalkerFn& walker) {
    std::vector<std::pair<cfg::Block*, std::vector<IRInstruction*>>>
        block_matches;
    always_assert(ir_code.cfg_built());
    for (cfg::Block* block : ir_code.cfg().blocks()) {
      std::vector<std::vector<IRInstruction*>> method_matches;
      std::vector<IRInstruction*> insns;
      for (const auto& mie : ir_list::InstructionIterable(block)) {
        insns.emplace_back(mie.insn);
      }
      m::find_matches(insns, predicate, method_matches);
      for (auto& matched_insns : method_matches) {
        block_matches.emplace_back(block, std::move(matched_insns));
      }
    }

    for (const auto& match : block_matches) {
      walker(&m, match.first, match.second);
    }
  }

  template <typename Predicate,
            size_t N = std::tuple_size<Predicate>::value,
            typename WalkerFn,
            typename FilterFn = decltype(all_methods)>
  static void iterate_matching_block(DexClass* cls,
                                     const Predicate& predicate,
                                     const WalkerFn& walker,
                                     const FilterFn& filter = all_methods) {
    iterate_code(
        cls, filter, [&predicate, &walker](DexMethod* m, IRCode& ir_code) {
          iterate_matching_block_worker(*m, ir_code, predicate, walker);
        });
  }

  // Contract for the `Reduce` of every reducing walk::parallel overload:
  //
  //   - `Accumulator()` must be an identity for it, because that is what each
  //     per-thread slot starts from and what an idle thread contributes;
  //   - it must be associative and commutative, because slots are folded in
  //     worker-id order and work is distributed by a stealing queue, so which
  //     element lands in which slot is not reproducible.
  //
  // Neither can be expressed as a static_assert, so they are stated here. A
  // `Reduce` that violates either makes the walk's result depend on the host's
  // core count and on thread timing.
  template <class T>
  struct plus_assign {
    void operator()(const T& addend, T* accumulator) const {
      *accumulator += addend;
    }
  };

 public:
  /**
   * The parallel:: methods have very similar signatures (and names) to their
   * sequential counterparts.
   * The unit of parallelization is a DexClass. The reason is that we don't want
   * to create too many tasks on the WorkQueue, paying the overhead for each.
   */
  class parallel {
   public:
    template <typename Fn>
    using Arity = sparta::Arity<Fn>;

    parallel() = delete;
    ~parallel() = delete;

    /**
     * Call walker on all classes in `classes` in parallel.
     */
    template <class Classes, typename WalkerFn>
    static void classes(
        Classes const& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>( // over-parallelized maybe
          [&walker](DexClass* cls) { walker(cls); },
          classes,
          num_threads);
    }

    template <class Accumulator,
              class Reduce = plus_assign<Accumulator>,
              class Classes,
              typename WalkerFn>
    static Accumulator classes(
        Classes const& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads(),
        Accumulator init = Accumulator()) {
      // Seed the per-thread slots with the identity, not with `init`: the
      // loop below reduces every slot into `init` as well, so seeding them
      // with `init` folds it num_threads + 1 times, and the result then
      // depends on the host's thread count.
      std::vector<CacheAligned<Accumulator>> acc_vec(num_threads,
                                                     Accumulator());
      auto reduce = Reduce();
      workqueue_run<DexClass*>( // over-parallelized maybe
          [&walker, &acc_vec, &reduce](sparta::WorkerState<DexClass*>* state,
                                       DexClass* cls) {
            Accumulator& acc = acc_vec[state->worker_id()];
            reduce(walker(cls), &acc);
          },
          classes,
          num_threads);
      for (Accumulator& acc : acc_vec) {
        reduce(acc, &init);
      }
      return init;
    }

    // Call `walker` on all methods in `classes` in parallel.
    //   WalkerFn should accept a `DexMethod*`.
    template <class Classes, typename WalkerFn>
    static void methods(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&walker](DexClass* cls) { walk::iterate_methods(cls, walker); },
          classes,
          num_threads);
    }

    // Call `walker` on all methods in `classes` in parallel. Then combine the
    // Accumulator objects with Sum.
    //
    // Each thread has its own Accumulator object that the walker can modify
    // without taking a lock.
    //
    // WalkerFn should accept `(DexMethod*, Accumulator&)`.
    template <
        class Accumulator,
        class Reduce = plus_assign<Accumulator>,
        class Classes,
        typename WalkerFn,
        typename std::enable_if<Arity<WalkerFn>::value == 2, int>::type = 0>
    static Accumulator methods(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads(),
        Accumulator init = Accumulator()) {
      // Seed the per-thread slots with the identity, not with `init`: the
      // loop below reduces every slot into `init` as well, so seeding them
      // with `init` folds it num_threads + 1 times, and the result then
      // depends on the host's thread count.
      std::vector<CacheAligned<Accumulator>> acc_vec(num_threads,
                                                     Accumulator());

      workqueue_run<DexClass*>(
          [&](sparta::WorkerState<DexClass*>* state, DexClass* cls) {
            Accumulator& acc = acc_vec[state->worker_id()];
            for (auto* dmethod : cls->get_dmethods()) {
              TraceContext context(dmethod);
              walker(dmethod, &acc);
            }
            for (auto* vmethod : cls->get_vmethods()) {
              TraceContext context(vmethod);
              walker(vmethod, &acc);
            }
          },
          classes,
          num_threads);

      auto reduce = Reduce();
      for (Accumulator& acc : acc_vec) {
        reduce(acc, &init);
      }
      return init;
    }

    // Call `walker` on all methods in `classes` in parallel. Then combine the
    // Accumulator objects with Sum.
    //
    // This version doesn't pass an Accumulator object to the walker -- instead
    // the walker returns a fresh Accumulator object which gets summed up.
    //
    // WalkerFn should accept a `DexMethod*` and return `Accumulator`.
    template <
        class Accumulator,
        class Reduce = plus_assign<Accumulator>,
        class Classes,
        typename WalkerFn,
        typename std::enable_if<Arity<WalkerFn>::value == 1, int>::type = 0>
    static Accumulator methods(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads(),
        Accumulator init = Accumulator()) {
      auto reduce = Reduce();
      return methods<Accumulator, Reduce, Classes>(
          classes,
          [&](DexMethod* method, Accumulator* acc) {
            reduce(walker(method), acc);
          },
          num_threads,
          init);
    }

    //
    // Call `walker` on all fields in `classes` in parallel.
    //   WalkerFn should accept a `DexField*`.
    template <class Classes, typename WalkerFn>
    static void fields(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&walker](DexClass* cls) { walk::iterate_fields(cls, walker); },
          classes,
          num_threads);
    }

    template <class Accumulator,
              class Reduce = plus_assign<Accumulator>,
              class Classes,
              typename WalkerFn>
    static Accumulator fields(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads(),
        Accumulator init = Accumulator()) {
      // Seed the per-thread slots with the identity, not with `init`: the
      // loop below reduces every slot into `init` as well, so seeding them
      // with `init` folds it num_threads + 1 times, and the result then
      // depends on the host's thread count.
      std::vector<CacheAligned<Accumulator>> acc_vec(num_threads,
                                                     Accumulator());
      auto reduce = Reduce();
      workqueue_run<DexClass*>(
          [&walker, &acc_vec, &reduce](sparta::WorkerState<DexClass*>* state,
                                       DexClass* cls) {
            Accumulator& acc = acc_vec[state->worker_id()];
            walk::iterate_fields(cls,
                                 [&](auto arg) { reduce(walker(arg), &acc); });
          },
          classes,
          num_threads);
      for (Accumulator& acc : acc_vec) {
        reduce(acc, &init);
      }
      return init;
    }

    // Call `walker` on all code (of methods approved by `filter`) in `classes`
    // in parallel.
    //   FilterFn should accept a `DexMethod*` and return a bool.
    //   WalkerFn should accept `(DexMethod*, IRCode&)`.
    template <class Classes, typename FilterFn, typename WalkerFn>
    static void code(
        const Classes& classes,
        const FilterFn& filter,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&filter, &walker](DexClass* cls) {
            walk::iterate_code(cls, filter, walker);
          },
          classes,
          num_threads);
    }

    // Same as `code()` but with a filter function that accepts all methods
    template <class Classes, typename WalkerFn>
    static void code(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      walk::parallel::code(classes, all_methods, walker, num_threads);
    }

    // Call `walker` on all opcodes (of methods approved by `filter`) in
    // `classes` in parallel.
    //   FilterFn should accept a `DexMethod*` and return a bool.
    //   WalkerFn should accept `(DexMethod*, IRInstruction*)`.
    template <class Classes, typename FilterFn, typename WalkerFn>
    static void opcodes(
        const Classes& classes,
        const FilterFn& filter,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&filter, &walker](DexClass* cls) {
            walk::iterate_opcodes(cls, filter, walker);
          },
          classes,
          num_threads);
    }

    // Same as `opcodes()` but with a filter function that accepts all methods
    template <class Classes, typename WalkerFn>
    static void opcodes(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      walk::parallel::opcodes(classes, all_methods, walker, num_threads);
    }

    // Call `walker` on all annotations in `classes` in parallel.
    //   WalkerFn should accept a `DexAnnotation*`.
    template <class Classes, typename WalkerFn>
    static void annotations(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&walker](DexClass* cls) { walk::iterate_annotations(cls, walker); },
          classes,
          num_threads);
    }

    // Call `walker`, in parallel, on each encoded value that `classes` hold
    // outside code: the initial value of each static field that has one, and
    // each annotation of the classes, their fields, their methods and the
    // methods' parameters. The value's gather_* functions also reach the
    // arrays and annotations nested in it.
    //   WalkerFn should accept a `const Gatherable&`.
    template <class Classes, typename WalkerFn>
    static void encoded_values(
        const Classes& classes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&walker](DexClass* cls) {
            walk::iterate_encoded_values(cls, walker);
          },
          classes,
          num_threads);
    }

    // Call `walker` on all matching opcodes (according to `predicate`) in
    // `classes` in parallel.
    // This will match across basic block boundaries. So be careful!
    template <class Classes,
              typename Predicate,
              size_t N = std::tuple_size<Predicate>::value,
              typename Walker = void(DexMethod*,
                                     const std::vector<IRInstruction*>&)>
    static void matching_opcodes(
        const Classes& classes,
        const Predicate& predicate,
        const Walker& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&predicate, &walker](DexClass* cls) {
            walk::iterate_matching(cls, predicate, walker);
          },
          classes,
          num_threads);
    }

    // Call `walker` on all matching opcodes (according to `predicate`) in
    // `classes` in parallel.
    // This will not match across basic block boundaries.
    //
    // WalkerFn should accept
    //     `(DexMethod*, cfg::Block*, const std::vector<IRInstruction*>&)`.
    template <class Classes,
              typename Predicate,
              typename WalkerFn,
              size_t N = std::tuple_size<Predicate>::value>
    static void matching_opcodes_in_block(
        const Classes& classes,
        const Predicate& predicate,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<DexClass*>(
          [&predicate, &walker](DexClass* cls) {
            walk::iterate_matching_block(cls, predicate, walker);
          },
          classes,
          num_threads);
    }

    // Call `walker` on all given virtual scopes in parallel. The scope pointer
    // type is deduced from the container, so this works with both legacy
    template <class VirtualScopes, typename WalkerFn>
    static void virtual_scopes(
        const VirtualScopes& virtual_scopes,
        const WalkerFn& walker,
        size_t num_threads = redex_parallel::default_num_threads()) {
      workqueue_run<typename VirtualScopes::value_type>(
          walker, virtual_scopes, num_threads);
    }
  };
};
