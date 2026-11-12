/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodInliner.h"

#include <algorithm>
#include <string>
#include <vector>

#include "AnnoUtils.h"
#include "BaselineProfile.h"
#include "ClassUtil.h"
#include "ConfigFiles.h"
#include "ConstructorAnalysis.h"
#include "Debug.h"
#include "Deleter.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "LiveRange.h"
#include "MethodOverrideGraph.h"
#include "ReachableClasses.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "ScopedMetrics.h"
#include "Shrinker.h"
#include "SourceBlocks.h"
#include "Timer.h"
#include "Walkers.h"
#include "WorkQueue.h"

namespace mog = method_override_graph;

namespace {

static bool has_bridgelike_access(DexMethod* m) {
  return m->is_virtual() &&
         (is_bridge(m) || (is_synthetic(m) && !method::is_constructor(m)));
}

static void filter_candidates_bridge_synth_only(
    PassManager& mgr,
    Scope& scope,
    UnorderedSet<DexMethod*>& candidates,
    const std::string& prefix) {
  ConcurrentSet<DexMethod*> bridgees;
  ConcurrentSet<DexMethod*> getters;
  ConcurrentSet<DexMethod*> ctors;
  ConcurrentSet<DexMethod*> wrappers;
  walk::parallel::code(scope, [&bridgees, &getters, &ctors,
                               &wrappers](DexMethod* method, IRCode& code) {
    cfg::ScopedCFG cfg(&code);
    UnorderedSet<DexFieldRef*> field_refs;
    UnorderedSet<DexMethod*> invoked_methods;
    size_t other = 0;
    for (auto& mie : InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (insn->has_field()) {
        if (opcode::is_an_iget(op) || opcode::is_an_sget(op)) {
          field_refs.insert(insn->get_field());
          continue;
        }
      } else if (insn->has_method()) {
        if (opcode::is_invoke_static(op) || opcode::is_invoke_direct(op)) {
          auto* callee = resolve_method_deprecated(
              insn->get_method(), opcode_to_search(insn), method);
          if (callee != nullptr) {
            invoked_methods.insert(callee);
            continue;
          }
        }
      }
      if (opcode::is_a_load_param(op) || opcode::is_check_cast(op) ||
          opcode::is_move_result_any(op) || opcode::is_a_move(op) ||
          opcode::is_a_return(op)) {
        continue;
      }
      other++;
    }

    if (field_refs.size() + other == 0 && invoked_methods.size() == 1 &&
        has_bridgelike_access(method)) {
      auto* bridgee = *unordered_any(invoked_methods);
      if (method->get_class() == bridgee->get_class()) {
        bridgees.insert(bridgee);
      }
    }

    // Looks for similar patterns as the legacy SynthPass
    if (is_synthetic(method)) {
      if (is_static(method)) {
        if (invoked_methods.size() + other == 0 && field_refs.size() == 1) {
          // trivial_get_field_wrapper / trivial_get_static_field_wrapper
          getters.insert(method);
        }
      } else if (method::is_init(method)) {
        if (field_refs.size() + other == 0 && invoked_methods.size() == 1) {
          // trivial_ctor_wrapper
          ctors.insert(method);
        }
      }
    }
    if (!method->is_virtual() && !method::is_init(method) &&
        field_refs.size() + other == 0 && invoked_methods.size() == 1) {
      // trivial_method_wrapper
      wrappers.insert(method);
    }
  });
  unordered_erase_if(candidates, [&](auto method) {
    return !bridgees.count_unsafe(method) && !wrappers.count_unsafe(method) &&
           !getters.count_unsafe(method) && !ctors.count_unsafe(method);
  });
  mgr.incr_metric(prefix + "bridgees", bridgees.size());
  mgr.incr_metric(prefix + "wrappers", wrappers.size());
  mgr.incr_metric(prefix + "getters", getters.size());
  mgr.incr_metric(prefix + "ctors", ctors.size());
}

// When inlining with making local decisions only, we remove some candidates
// with many relevant invokes, as this reduces the length of the critical path
// and thus speeds up the inlining pass, while not reducing the effectiveness of
// the pass in a meaningful way.
static void filter_candidates_local_only(
    PassManager& mgr,
    Scope& scope,
    uint64_t max_relevant_invokes_when_local_only,
    UnorderedSet<DexMethod*>& candidates) {
  ConcurrentSet<DexMethod*> large_candidates;
  walk::parallel::code(scope, [&large_candidates, &candidates,
                               max_relevant_invokes_when_local_only](
                                  DexMethod* caller, IRCode& code) {
    if (candidates.count(caller) == 0u) {
      return;
    }
    size_t relevant_invokes{0};
    for (auto& mie : InstructionIterable(code.cfg())) {
      if (!opcode::is_an_invoke(mie.insn->opcode())) {
        continue;
      }
      auto* callee = resolve_method_deprecated(
          mie.insn->get_method(), opcode_to_search(mie.insn), caller);
      if (candidates.count(callee) != 0u) {
        relevant_invokes++;
      }
    }
    if (relevant_invokes > max_relevant_invokes_when_local_only) {
      large_candidates.insert(caller);
    }
  });
  unordered_erase_if(
      candidates, [&](auto method) { return large_candidates.count(method); });
  mgr.incr_metric("large_candidates", large_candidates.size());
}

/**
 * Collect all non virtual methods and make all small methods candidates
 * for inlining.
 */
UnorderedSet<DexMethod*> gather_non_virtual_methods(
    Scope& scope,
    const InsertOnlyConcurrentSet<DexMethod*>* non_virtual,
    const UnorderedSet<DexType*>& no_devirtualize_anno) {
  // trace counter
  size_t all_methods = 0;
  size_t direct_methods = 0;
  size_t direct_no_code = 0;
  size_t non_virtual_no_code = 0;
  size_t clinit = 0;
  size_t init = 0;
  size_t static_methods = 0;
  size_t private_methods = 0;
  size_t dont_strip = 0;
  size_t non_virt_dont_strip = 0;
  size_t non_virt_methods = 0;
  // collect all non virtual methods (dmethods and vmethods)
  UnorderedSet<DexMethod*> methods;
  walk::methods(scope, [&](DexMethod* method) {
    all_methods++;
    if (method->is_virtual()) {
      return;
    }

    auto* code = method->get_code();
    bool dont_inline = code == nullptr;

    direct_methods++;
    if (code == nullptr) {
      direct_no_code++;
    }
    if (method::is_constructor(method)) {
      (is_static(method)) ? clinit++ : init++;
      if (method::is_clinit(method)) {
        dont_inline = true;
      }
    } else {
      (is_static(method)) ? static_methods++ : private_methods++;
    }

    if (dont_inline) {
      return;
    }

    methods.insert(method);
  });
  if (non_virtual != nullptr) {
    non_virt_methods = non_virtual->size();
    for (const auto& vmeth : UnorderedIterable(*non_virtual)) {
      auto* code = vmeth->get_code();
      if (code == nullptr) {
        non_virtual_no_code++;
        continue;
      }
      if (has_any_annotation(vmeth, no_devirtualize_anno)) {
        continue;
      }
      methods.insert(vmeth);
    }
  }

  TRACE(INLINE, 2, "All methods count: %zu", all_methods);
  TRACE(INLINE, 2, "Direct methods count: %zu", direct_methods);
  TRACE(INLINE, 2, "Virtual methods count: %zu", all_methods - direct_methods);
  TRACE(INLINE, 2, "Direct methods no code: %zu", direct_no_code);
  TRACE(INLINE, 2, "Direct methods with code: %zu",
        direct_methods - direct_no_code);
  TRACE(INLINE, 2, "Constructors with or without code: %zu", init);
  TRACE(INLINE, 2, "Static constructors: %zu", clinit);
  TRACE(INLINE, 2, "Static methods: %zu", static_methods);
  TRACE(INLINE, 2, "Private methods: %zu", private_methods);
  TRACE(INLINE, 2, "Virtual methods non virtual count: %zu", non_virt_methods);
  TRACE(INLINE, 2, "Non virtual no code count: %zu", non_virtual_no_code);
  TRACE(INLINE, 2, "Non virtual no strip count: %zu", non_virt_dont_strip);
  TRACE(INLINE, 2, "Don't strip inlinable methods count: %zu", dont_strip);
  return methods;
}

struct SameImplementation {
  DexMethod* representative;
  std::vector<DexMethod*> methods;
};

using SameImplementationMap =
    UnorderedMap<const DexMethod*, std::shared_ptr<SameImplementation>>;

/**
 * Get a map of method -> implementation method that hold the same
 * implementation as the method would perform at run time.
 * So if a abtract method have multiple implementor but they all have the same
 * implementation, we can have a mapping between the abstract method and
 * one of its implementor.
 */
SameImplementationMap get_same_implementation_map(
    const Scope& scope, const mog::Graph& method_override_graph) {
  UnorderedMap<const DexMethod*, std::shared_ptr<SameImplementation>>
      method_to_implementations;
  walk::methods(scope, [&](DexMethod* method) {
    if (method->is_external() || !method->is_virtual() ||
        ((method->get_code() == nullptr) && !is_abstract(method))) {
      return;
    }
    // Why can_rename? To mirror what VirtualRenamer looks at.
    if (is_interface(type_class(method->get_class())) &&
        (root(method) || !can_rename(method))) {
      // We cannot rule out that there are dynamically added classes, possibly
      // even created at runtime via Proxy.newProxyInstance, that override this
      // method. So we assume the worst.
      return;
    }
    auto overriding_methods =
        mog::get_overriding_methods(method_override_graph, method);
    SameImplementation same_implementation{nullptr, {}};
    auto consider_method = [&](DexMethod* method) {
      always_assert(method->get_code());
      always_assert(method->get_code()->cfg_built());
      if (same_implementation.representative != nullptr) {
        always_assert(
            same_implementation.representative->get_code()->cfg_built());
        if (!method->get_code()->cfg().structural_equals(
                same_implementation.representative->get_code()->cfg())) {
          return false;
        }
      }
      if (same_implementation.representative == nullptr ||
          compare_dexmethods(method, same_implementation.representative)) {
        same_implementation.representative = method;
      }
      same_implementation.methods.push_back(method);
      return true;
    };
    for (const auto* overriding_method :
         UnorderedIterable(overriding_methods)) {
      if (!method::may_be_invoke_target(overriding_method)) {
        continue;
      }
      if (overriding_method->get_code() == nullptr) {
        // If the method is not abstract method and it doesn't have
        // implementation, we bail out.
        return;
      }
      if (!consider_method(const_cast<DexMethod*>(overriding_method))) {
        return;
      }
    }
    if ((method->get_code() != nullptr) && !consider_method(method)) {
      return;
    }
    if (same_implementation.methods.size() <= 1) {
      return;
    }

    // All methods have the same implementation, so we create mapping between
    // methods and their representative implementation.
    auto sp = std::make_shared<SameImplementation>(same_implementation);
    method_to_implementations.emplace(method, sp);
    for (const auto* overriding_method :
         UnorderedIterable(overriding_methods)) {
      method_to_implementations.emplace(overriding_method, sp);
    }
  });
  return method_to_implementations;
}

bool can_have_unknown_implementations(const mog::Graph& method_override_graph,
                                      const DexMethod* method) {
  if (method->is_external()) {
    return true;
  }
  // Why can_rename? To mirror what VirtualRenamer looks at.
  if (is_interface(type_class(method->get_class())) &&
      (root(method) || !can_rename(method))) {
    // We cannot rule out that there are dynamically added classes, possibly
    // even created at runtime via Proxy.newProxyInstance, that override
    // this method. So we assume the worst.
    return true;
  }
  // Also check that for all overridden methods.
  return mog::any_overridden_methods(
      method_override_graph, method,
      [&](auto* overridden_method) {
        return static_cast<bool>(
            is_interface(type_class(overridden_method->get_class())) &&
            (root(overridden_method) || !can_rename(overridden_method)));
      },
      /* include_interfaces */ true);
};

/**
 * Gather candidates of true virtual methods that can be inlined and their
 * call site in true_virtual_callers.
 * A true virtual method can be inlined to its callsite if the callsite can
 * be resolved to only one method implementation deterministically.
 * We are currently ruling out candidates that use the receiver in ways that
 * would require additional casts.
 */
void gather_true_virtual_methods(
    const mog::Graph& method_override_graph,
    const InsertOnlyConcurrentSet<DexMethod*>& non_virtual,
    const Scope& scope,
    const SameImplementationMap& same_implementation_map,
    CalleeCallerInsns* true_virtual_callers) {
  Timer t("gather_true_virtual_methods");
  ConcurrentMap<const DexMethod*, CallerInsns> concurrent_true_virtual_callers;
  InsertOnlyConcurrentMap<IRInstruction*, SameImplementation*>
      same_implementation_invokes;
  // Add mapping from callee to monomorphic callsites.
  auto add_monomorphic_call_site = [&](const DexMethod* caller,
                                       IRInstruction* callsite,
                                       const DexMethod* callee) {
    concurrent_true_virtual_callers.update(
        callee, [&](const DexMethod*, CallerInsns& m, bool) {
          m.caller_insns[caller].emplace(callsite);
        });
  };
  auto add_other_call_site =
      [&](const DexMethod* callee,
          bool other_call_sites_overriding_methods_added = false) {
        bool res;
        concurrent_true_virtual_callers.update(
            callee, [&](const DexMethod*, CallerInsns& m, bool) {
              m.other_call_sites = true;
              res = m.other_call_sites_overriding_methods_added;
              if (other_call_sites_overriding_methods_added) {
                m.other_call_sites_overriding_methods_added = true;
              }
            });
        return res;
      };
  auto add_candidate = [&](const DexMethod* callee) {
    concurrent_true_virtual_callers.emplace(callee, CallerInsns());
  };

  struct Key {
    DexMethod* callee;
    DexType* static_base_type;
    bool operator==(const Key& other) const {
      return callee == other.callee &&
             static_base_type == other.static_base_type;
    }
  };
  struct Hash {
    size_t operator()(const Key& key) const {
      size_t hash = 0;
      boost::hash_combine(hash, key.callee);
      boost::hash_combine(hash, key.static_base_type);
      return hash;
    }
  };
  // The value is an (unordered) bag of overriding methods; two threads racing
  // to create the same key may build it in a different element order, so the
  // concurrency sanity-check compares the bags as sets (interned DexMethod
  // pointers => pointer identity), not as ordered sequences.
  InsertOnlyConcurrentMap<Key, UnorderedBag<const DexMethod*>, Hash>
      concurrent_overriding_methods;
  auto get_overriding_methods =
      [&](DexMethod* callee,
          DexType* static_base_type) -> const UnorderedBag<const DexMethod*>& {
    return *concurrent_overriding_methods
                .get_or_create_and_assert_equal<
                    UnorderedEqual<UnorderedBag<const DexMethod*>>>(
                    Key{callee, static_base_type},
                    [&](const Key&) {
                      auto overriding_methods = mog::get_overriding_methods(
                          method_override_graph, callee,
                          /* include_interfaces */ false, static_base_type);
                      unordered_erase_if(overriding_methods, [&](auto* m) {
                        return !method::may_be_invoke_target(m);
                      });
                      return overriding_methods;
                    })
                .first;
  };

  walk::parallel::methods(scope, [&non_virtual, &method_override_graph,
                                  &add_monomorphic_call_site,
                                  &add_other_call_site, &add_candidate,
                                  &same_implementation_invokes,
                                  &same_implementation_map,
                                  &get_overriding_methods](DexMethod* method) {
    if (method->is_virtual() && (non_virtual.count_unsafe(method) == 0u)) {
      add_candidate(method);
      if (root(method)) {
        add_other_call_site(method);
      } else {
        const auto& overridden_methods = mog::get_overridden_methods(
            method_override_graph, method, /* include_interfaces */ true);
        for (const auto* overridden_method :
             UnorderedIterable(overridden_methods)) {
          if (root(overridden_method) || overridden_method->is_external()) {
            add_other_call_site(method);
            break;
          }
        }
      }
    }
    auto* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    auto& cfg = code->cfg();
    for (auto* block : cfg.blocks()) {
      for (auto& mie : InstructionIterable(block)) {
        auto* insn = mie.insn;
        if (insn->opcode() != OPCODE_INVOKE_VIRTUAL &&
            insn->opcode() != OPCODE_INVOKE_INTERFACE &&
            insn->opcode() != OPCODE_INVOKE_SUPER) {
          continue;
        }
        auto* insn_method = insn->get_method();
        auto* callee = resolve_invoke_method_deprecated(insn, method);
        if (callee == nullptr) {
          continue;
        }
        if (non_virtual.count_unsafe(callee) != 0) {
          // Not true virtual, no need to continue;
          continue;
        }
        auto* static_base_type = insn_method->get_class();
        if (can_have_unknown_implementations(method_override_graph, callee)) {
          bool consider_overriding_methods =
              insn->opcode() != OPCODE_INVOKE_SUPER;
          if (!add_other_call_site(callee, consider_overriding_methods) &&
              consider_overriding_methods) {
            const auto& overriding_methods =
                get_overriding_methods(callee, static_base_type);
            for (const auto* overriding_method :
                 UnorderedIterable(overriding_methods)) {
              add_other_call_site(
                  overriding_method,
                  /* other_call_sites_overriding_methods_added */ true);
            }
          }
          continue;
        }
        always_assert_log(callee->is_def(), "Resolved method not def %s",
                          SHOW(callee));
        if (insn->opcode() == OPCODE_INVOKE_SUPER) {
          add_monomorphic_call_site(method, insn, callee);
          continue;
        }
        auto it = same_implementation_map.find(callee);
        if (it != same_implementation_map.end()) {
          // We can find the resolved callee in same_implementation_map,
          // just use that piece of info because we know the implementors are
          // all the same
          add_monomorphic_call_site(method, insn, it->second->representative);
          same_implementation_invokes.emplace(insn, it->second.get());
          continue;
        }
        const auto& overriding_methods =
            get_overriding_methods(callee, static_base_type);
        if (overriding_methods.empty()) {
          // There is no override for this method
          add_monomorphic_call_site(method, insn, callee);
        } else if (is_abstract(callee) && overriding_methods.size() == 1) {
          // The method is an abstract method, the only override is its
          // implementation.
          const auto* implementing_method = *unordered_any(overriding_methods);
          add_monomorphic_call_site(method, insn, implementing_method);
        } else {
          if (!add_other_call_site(
                  callee,
                  /* other_call_sites_overriding_methods_added */ true)) {
            for (const auto* overriding_method :
                 UnorderedIterable(overriding_methods)) {
              add_other_call_site(
                  overriding_method,
                  /* other_call_sites_overriding_methods_added */ true);
            }
          }
        }
      }
    }
  });

  // Post processing candidates.
  // A call site recorded for a cluster's representative can reach any other
  // method of the cluster at run time, so none of those sees all its callers.
  UnorderedSet<const SameImplementation*> called_same_implementations;
  for (const auto& p : UnorderedIterable(same_implementation_invokes)) {
    called_same_implementations.insert(p.second);
  }
  for (const auto* same_implementation :
       UnorderedIterable(called_same_implementations)) {
    for (const auto* method : same_implementation->methods) {
      if (method != same_implementation->representative) {
        add_other_call_site(method);
      }
    }
  }
  std::vector<const DexMethod*> true_virtual_callees;
  for (auto& p : UnorderedIterable(concurrent_true_virtual_callers)) {
    true_virtual_callees.push_back(p.first);
  }
  workqueue_run<const DexMethod*>(
      [&](sparta::WorkerState<const DexMethod*>*, const DexMethod* callee) {
        auto& caller_to_invocations =
            concurrent_true_virtual_callers.at_unsafe(callee);
        if (caller_to_invocations.caller_insns.empty()) {
          return;
        }
        auto* code = const_cast<DexMethod*>(callee)->get_code();
        if ((code == nullptr) || !method::no_invoke_super(*code)) {
          if (!caller_to_invocations.caller_insns.empty()) {
            caller_to_invocations.caller_insns =
                decltype(caller_to_invocations.caller_insns)();
            caller_to_invocations.other_call_sites = true;
          }
          return;
        }
        UnorderedSet<DexType*> formal_callee_types;
        bool any_same_implementation_invokes{false};
        for (auto& p : UnorderedIterable(caller_to_invocations.caller_insns)) {
          for (auto* insn : UnorderedIterable(p.second)) {
            formal_callee_types.insert(insn->get_method()->get_class());
            if (same_implementation_invokes.count_unsafe(insn) != 0u) {
              any_same_implementation_invokes = true;
            }
          }
        }
        // Figure out if candidates use the receiver in a way that does require
        // a cast. Note that the callee-rtype is the same for all methods in a
        // same-implementations cluster.
        auto type_demands = live_range::get_receiver_type_demands(callee);
        if (!type_demands) {
          formal_callee_types.clear();
        } else {
          for (const auto* type_demand : UnorderedIterable(*type_demands)) {
            always_assert_log(
                type::check_cast(callee->get_class(), type_demand),
                "For the incoming code to be type correct, %s must "
                "be castable to %s.",
                SHOW(callee->get_class()), SHOW(type_demand));
            unordered_erase_if(formal_callee_types, [&](auto* t) {
              return !type::check_cast(t, type_demand);
            });
          }
        }
        const auto* combined_type_demand =
            type_demands ? live_range::reduce_type_demands(*type_demands)
                         : nullptr;
        for (auto& p : UnorderedIterable(caller_to_invocations.caller_insns)) {
          unordered_erase_if(p.second, [&](auto* insn) {
            if (!formal_callee_types.count(insn->get_method()->get_class())) {
              auto it2 = same_implementation_invokes.find(insn);
              if (it2 != same_implementation_invokes.end()) {
                always_assert(any_same_implementation_invokes);
                if (combined_type_demand) {
                  for (auto same_implementation_callee : it2->second->methods) {
                    always_assert_log(
                        type::check_cast(
                            same_implementation_callee->get_class(),
                            combined_type_demand),
                        "For the incoming code to be type correct, %s must "
                        "be castable to %s.",
                        SHOW(same_implementation_callee->get_class()),
                        SHOW(combined_type_demand));
                  }
                  caller_to_invocations.inlined_invokes_need_cast.emplace(
                      insn, combined_type_demand);
                } else {
                  // We can't just cast to the type of the representative. And
                  // it's not trivial to find the right common base type of the
                  // representatives, it might not even exist. (Imagine all
                  // subtypes happen the implement a set of interfaces.)
                  // TODO: Try harder.
                  caller_to_invocations.other_call_sites = true;
                  return true;
                }
              } else {
                caller_to_invocations.inlined_invokes_need_cast.emplace(
                    insn, callee->get_class());
              }
            }
            return false;
          });
        }
        unordered_erase_if(caller_to_invocations.caller_insns,
                           [&](auto& p) { return p.second.empty(); });
      },
      true_virtual_callees);
  for (auto& pair : UnorderedIterable(concurrent_true_virtual_callers)) {
    DexMethod* callee = const_cast<DexMethod*>(pair.first);
    true_virtual_callers->emplace(callee, std::move(pair.second));
  }
}

// If a constructor cannot be inlined because it writes to final fields, then we
// can "simply" remove the final modifier. We typically run the
// AccessMarkingMarking pass multiple times, including after the final inliner,
// so that the final modifier gets re-added where appropriate.
//
// Assigning final fields in a constructor comes certain visibility guarantees.
// See https://gee.cs.oswego.edu/dl/jmm/cookbook.html In particular, when we
// remove the final modifier of any field, then we need to insert an explicit
// store-store fence when the constructor returns. Eventually, the CFGInliner is
// inserting a write barrier pseudo instruction to lower at the end.
void unfinalize_fields_if_beneficial_for_relaxed_init_inlining(
    const Scope& scope,
    const inliner::UnfinalizePerfMode& unfinalize_perf_mode,
    InsertOnlyConcurrentMap<DexField*, std::vector<DexMethod*>>*
        unfinalized_fields,
    InsertOnlyConcurrentSet<DexMethod*>* methods_with_write_barrier) {
  walk::parallel::classes(scope, [&](DexClass* cls) {
    // Since we run inliner several times, in previous inliner run we might
    // unfinalized some fields and added write barrier in method already.
    // We need to take these method into consideration when we check
    // inlining eligibility.
    for (auto* method : cls->get_all_methods()) {
      if (method->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : InstructionIterable(method->get_code()->cfg())) {
        if (opcode::is_write_barrier(mie.insn->opcode())) {
          methods_with_write_barrier->insert(method);
          break;
        }
      }
    }

    // We also exclude possibly anonymous classes as those may
    // regress the effectiveness of the class-merging passes.
    // TODO T184662680: While this is not a correctness issue,
    // we should fully support relaxed init methods in
    // class-merging. Align with what happens in
    // MultiMethodInliner::can_inline_init.
    if (klass::maybe_anonymous_class(cls)) {
      return;
    }
    UnorderedSet<DexField*> final_ifields;
    for (auto* field : cls->get_ifields()) {
      if (is_final(field)) {
        final_ifields.insert(field);
      }
    }
    if (final_ifields.empty()) {
      return;
    }
    UnorderedMap<DexField*, std::vector<DexMethod*>> local_unfinalized_fields;
    bool perf_sensitive = false;
    for (auto* init_method : cls->get_ctors()) {
      if ((unfinalize_perf_mode == inliner::UnfinalizePerfMode::NOT_COLD &&
           source_blocks::method_is_not_cold(init_method)) ||
          (unfinalize_perf_mode == inliner::UnfinalizePerfMode::MAYBE_HOT &&
           source_blocks::method_maybe_hot(init_method)) ||
          (unfinalize_perf_mode == inliner::UnfinalizePerfMode::HOT &&
           source_blocks::method_is_hot(init_method))) {
        perf_sensitive = true;
        break;
      }
      UnorderedSet<DexField*> written_final_fields;
      if (!constructor_analysis::can_inline_init(
              init_method, /* finalizable_fields */ nullptr,
              /* relaxed */ true, &written_final_fields)) {
        for (auto* field : UnorderedIterable(written_final_fields)) {
          always_assert(final_ifields.count(field));
          local_unfinalized_fields[field].push_back(init_method);
        }
      }
    }
    if (perf_sensitive) {
      // If we turned on perf checking mode and any constructor meet the check,
      // we need to give up unfinalizing the field, otherwise even not inlining
      // the non-hot constructor, we would still need to add write barrier
      // before return if there is another constructor being inlined and the
      // field kept being unfinalized.
      return;
    }
    for (auto&& [field, init_methods] :
         UnorderedIterable(local_unfinalized_fields)) {
      field->set_access(field->get_access() & ~ACC_FINAL);
      auto emplaced =
          unfinalized_fields->emplace(field, std::move(init_methods)).second;
      always_assert(emplaced);
    }
  });
}

void insert_barrier_at_init_return(DexMethod* init) {
  auto& cfg = init->get_code()->cfg();
  auto return_blocks = cfg.return_blocks();
  for (auto* ret_block : return_blocks) {
    auto last_insn_it = ret_block->get_last_insn();
    always_assert(opcode::is_return_void(last_insn_it->insn->opcode()));
    auto last_insn_cfg_it =
        ret_block->to_cfg_instruction_iterator(last_insn_it);
    ret_block->insert_before(last_insn_cfg_it,
                             (new IRInstruction(IOPCODE_WRITE_BARRIER)));
  }
}

} // namespace

namespace inliner {
void run_inliner(
    DexStoresVector& stores,
    PassManager& mgr,
    ConfigFiles& conf,
    InlinerCostConfig inliner_cost_config /* DEFAULT_COST_CONFIG */,
    HotColdInliningBehavior hot_cold_inlining_behavior /* None */,
    bool partial_hot_hot /* false */,
    bool intra_dex /* false */,
    bool baseline_profile_guided /* false */,
    InlineForSpeed* inline_for_speed /* nullptr */,
    bool inline_bridge_synth_only /* false */,
    bool local_only /* false */) {
  always_assert_log(
      !mgr.init_class_lowering_has_run(),
      "Implementation limitation: The inliner could introduce new "
      "init-class instructions.");
  auto scope = build_class_scope(stores);

  auto inliner_config =
      *conf.get_global_config().get_config_by_name<::InlinerConfig>("inliner");
  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  const api::AndroidSDK* min_sdk_api{nullptr};
  if (inliner_config.check_min_sdk_refs) {
    mgr.incr_metric("min_sdk", min_sdk);
    TRACE(INLINE, 2, "min_sdk: %d", min_sdk);
    auto min_sdk_api_file = conf.get_android_sdk_api_file(min_sdk);
    if (!min_sdk_api_file) {
      mgr.incr_metric("min_sdk_no_file", 1);
      TRACE(INLINE, 2, "Android SDK API %d file cannot be found.", min_sdk);
    } else {
      min_sdk_api = &conf.get_android_sdk_api(min_sdk);
    }
  }

  if (partial_hot_hot && !g_redex->instrument_mode) {
    inliner_config.partial_hot_hot_inline = true;
  }

  CalleeCallerInsns true_virtual_callers;
  bool cross_dex_penalty = true;
  // Gather all inlinable candidates.
  if (intra_dex) {
    inliner_config.apply_intradex_allowlist();
    cross_dex_penalty = false;
  }

  if (inline_for_speed != nullptr) {
    inliner_config.shrink_other_methods = false;
  }

  if (inline_bridge_synth_only) {
    inliner_config.true_virtual_inline = false;
    inliner_config.virtual_inline = false;
    inliner_config.use_call_site_summaries = false;
    inliner_config.shrink_other_methods = false;
    inliner_config.intermediate_shrinking = false;
    inliner_config.multiple_callers = true;
    inliner_config.delete_non_virtuals = true;
    // We disable relaxed init inlining as bridge-synth-inlining likely runs
    // before general class merging, and relaxed init inlining may regress the
    // effectiveness of class merging, as it currently simply excludes classes
    // affected by relaxed inits.
    // TODO T184662680: While this is not a correctness issue, we should fully
    // support relaxed init methods in class-merging and then not change
    // the relaxed_init_inline here.
    inliner_config.relaxed_init_inline = false;
    inliner_config.shrinker = shrinker::ShrinkerConfig();
    inliner_config.shrinker.compute_pure_methods = false;
    inliner_config.shrinker.run_const_prop = true;
    cross_dex_penalty = false;
  }

  if (local_only) {
    inliner_config.true_virtual_inline = false;
    inliner_config.shrink_other_methods = false;
    inliner_config.delete_non_virtuals = true;
  }

  InsertOnlyConcurrentMap<DexField*, std::vector<DexMethod*>>
      unfinalized_fields;
  InsertOnlyConcurrentSet<DexMethod*> methods_with_write_barrier;
  UnorderedSet<const DexMethod*> unfinalized_init_methods;
  if (inliner_config.relaxed_init_inline &&
      inliner_config.unfinalize_relaxed_init_inline) {
    unfinalize_fields_if_beneficial_for_relaxed_init_inlining(
        scope, inliner_config.unfinalize_perf_mode, &unfinalized_fields,
        &methods_with_write_barrier);
    mgr.set_metric("unfinalized_fields", unfinalized_fields.size());
    TRACE(INLINE, 3, "unfinalized %zu fields", unfinalized_fields.size());
    for (auto&& [_, init_methods] : UnorderedIterable(unfinalized_fields)) {
      unfinalized_init_methods.insert(init_methods.begin(), init_methods.end());
    }
    mgr.set_metric("unfinalized_init_methods", unfinalized_init_methods.size());
    TRACE(INLINE, 3, "unfinalized %zu init methods",
          unfinalized_init_methods.size());
  }

  inliner_config.unique_inlined_registers = false;

  std::unique_ptr<const mog::Graph> method_override_graph;
  std::unique_ptr<const InsertOnlyConcurrentSet<DexMethod*>> non_virtual;
  if (inliner_config.virtual_inline) {
    method_override_graph = mog::build_graph(scope);
    non_virtual = std::make_unique<const InsertOnlyConcurrentSet<DexMethod*>>(
        mog::get_non_true_virtuals(*method_override_graph, scope));
  }

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns(), method_override_graph.get());

  auto candidates = gather_non_virtual_methods(scope, non_virtual.get(),
                                               conf.get_do_not_devirt_anon());

  // The candidates list computed above includes all constructors, regardless of
  // whether it's safe to inline them or not. We'll let the inliner decide
  // what to do with constructors.
  bool analyze_and_prune_inits = true;

  std::unique_ptr<SameImplementationMap> same_implementation_map;
  if (inliner_config.virtual_inline && inliner_config.true_virtual_inline) {
    same_implementation_map = std::make_unique<SameImplementationMap>(
        get_same_implementation_map(scope, *method_override_graph));
  }

  if (inliner_config.virtual_inline && inliner_config.true_virtual_inline) {
    gather_true_virtual_methods(*method_override_graph, *non_virtual, scope,
                                *same_implementation_map,
                                &true_virtual_callers);
    same_implementation_map = nullptr;
  }

  non_virtual = nullptr;

  if (inline_bridge_synth_only) {
    filter_candidates_bridge_synth_only(mgr, scope, candidates, "initial_");
  }

  if (local_only) {
    filter_candidates_local_only(
        mgr, scope, inliner_config.max_relevant_invokes_when_local_only,
        candidates);
  }

  inliner_config.shrinker.analyze_constructors =
      inliner_config.shrinker.run_const_prop;

  auto baseline_profile =
      baseline_profile_guided
          ? std::make_optional(
                baseline_profiles::get_default_baseline_profile(scope, conf))
          : std::nullopt;

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;
  // inline candidates
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex, true_virtual_callers, inline_for_speed,
      analyze_and_prune_inits, conf.get_pure_methods(), min_sdk_api,
      cross_dex_penalty,
      /* configured_finalish_field_names */ {}, local_only,
      hot_cold_inlining_behavior, std::move(baseline_profile),
      inliner_cost_config, &unfinalized_init_methods,
      &methods_with_write_barrier, method_override_graph.get());
  inliner.inline_methods();

  // refinalize where possible
  if (!unfinalized_fields.empty()) {
    auto inlined_with_fence = inliner.get_inlined_with_fence();
    size_t refinalized_fields = 0;
    UnorderedSet<DexMethod*> inits_inserted_barrier;
    for (auto&& [field, init_methods] : UnorderedIterable(unfinalized_fields)) {
      if (std::none_of(
              init_methods.begin(), init_methods.end(),
              [&](DexMethod* m) { return inlined_with_fence.count(m); })) {
        set_final(field);
        refinalized_fields++;
      } else {
        // We need to insert a write barrier for the constructors that has
        // fields not refinalized, in case the constructor is not inlined at all
        // callsites, or it's called reflectively. We are inserting write
        // barrier for every constructors because can_inline_init can have early
        // return before registering written_final_fields.
        for (auto* init_method : type_class(field->get_class())->get_ctors()) {
          auto emplaced = inits_inserted_barrier.emplace(init_method).second;
          if (!emplaced) {
            continue;
          }
          insert_barrier_at_init_return(init_method);
        }
      }
    }
    mgr.set_metric("inits_inserted_barrier", inits_inserted_barrier.size());
    mgr.set_metric("refinalized_fields", refinalized_fields);
    TRACE(INLINE, 3, "refinalized %zu fields", refinalized_fields);
  }

  // delete all methods that can be deleted
  auto inlined = inliner.get_inlined();
  size_t inlined_count = inlined.size();
  size_t inlined_init_count = 0;
  for (DexMethod* m : UnorderedIterable(inlined)) {
    if (method::is_init(m)) {
      inlined_init_count++;
    }
  }

  std::vector<DexMethod*> deleted;
  if (inliner_config.delete_non_virtuals) {
    // Do not erase true virtual methods that are inlined because we are only
    // inlining callsites that are monomorphic, for polymorphic callsite we
    // didn't inline, but in run time the callsite may still be resolved to
    // those methods that are inlined. We are relying on RMU to clean up
    // true virtual methods that are not referenced.
    for (const auto& pair : UnorderedIterable(true_virtual_callers)) {
      inlined.erase(pair.first);
    }
    deleted =
        delete_methods(scope, inlined, std::ref(concurrent_method_resolver));
  }

  if (inline_bridge_synth_only) {
    UnorderedSet<DexMethod*> deleted_set(deleted.begin(), deleted.end());
    unordered_erase_if(candidates,
                       [&](auto method) { return deleted_set.count(method); });
    filter_candidates_bridge_synth_only(mgr, scope, candidates, "remaining_");
  }

  if (!deleted.empty()) {
    // Can't really delete because of possible deob links. At least let's erase
    // any code.
    for (auto* m : deleted) {
      m->release_code();
    }
  }

  TRACE(INLINE, 3, "recursive %zu", inliner.get_info().recursive);
  TRACE(INLINE, 3, "max_call_stack_depth %zu",
        inliner.get_info().max_call_stack_depth);
  TRACE(INLINE, 3, "waited seconds %zu", inliner.get_info().waited_seconds);
  TRACE(INLINE, 3, "blocklisted meths %zu",
        (size_t)inliner.get_info().blocklisted);
  TRACE(INLINE, 3, "virtualizing methods %zu",
        (size_t)inliner.get_info().need_vmethod);
  TRACE(INLINE, 3, "invoke super %zu", (size_t)inliner.get_info().invoke_super);
  TRACE(INLINE, 3, "escaped virtual %zu",
        (size_t)inliner.get_info().escaped_virtual);
  TRACE(INLINE, 3, "known non public virtual %zu",
        (size_t)inliner.get_info().non_pub_virtual);
  TRACE(INLINE, 3, "non public ctor %zu",
        (size_t)inliner.get_info().non_pub_ctor);
  TRACE(INLINE, 3, "unknown field %zu",
        (size_t)inliner.get_info().escaped_field);
  TRACE(INLINE, 3, "non public field %zu",
        (size_t)inliner.get_info().non_pub_field);
  TRACE(INLINE, 3, "throws %zu", (size_t)inliner.get_info().throws);
  TRACE(INLINE, 3, "multiple returns %zu",
        (size_t)inliner.get_info().multi_ret);
  TRACE(INLINE, 3, "references cross stores %zu",
        (size_t)inliner.get_info().cross_store);
  TRACE(INLINE, 3, "api level mismatches %zu",
        (size_t)inliner.get_info().api_level_mismatch);
  TRACE(INLINE, 3, "illegal references %zu",
        (size_t)inliner.get_info().problematic_refs);
  TRACE(INLINE, 3, "not found %zu", (size_t)inliner.get_info().not_found);
  TRACE(INLINE, 3, "caller too large %zu",
        (size_t)inliner.get_info().caller_too_large);
  TRACE(INLINE, 3, "inlined ctors %zu", inlined_init_count);
  TRACE(INLINE, 1,
        "%zu inlined calls (of which %zu partial) over %zu methods and %zu "
        "methods removed",
        (size_t)inliner.get_info().calls_inlined,
        (size_t)inliner.get_info().partially_inlined, inlined_count,
        deleted.size());

  const auto& shrinker = inliner.get_shrinker();
  mgr.incr_metric("recursive", inliner.get_info().recursive);
  mgr.incr_metric("max_call_stack_depth",
                  inliner.get_info().max_call_stack_depth);
  mgr.incr_metric("cross_dex", inliner.get_info().cross_dex);
  mgr.incr_metric("cross_store", inliner.get_info().cross_store);
  mgr.incr_metric("api_level_mismatch", inliner.get_info().api_level_mismatch);
  mgr.incr_metric("problematic_refs", inliner.get_info().problematic_refs);
  mgr.incr_metric("caller_too_large", inliner.get_info().caller_too_large);
  mgr.incr_metric("inlined_init_count", inlined_init_count);
  mgr.incr_metric("init_classes", inliner.get_info().init_classes);
  mgr.incr_metric("constructor_fences", inliner.get_info().constructor_fences);
  mgr.incr_metric("calls_inlined", inliner.get_info().calls_inlined);
  mgr.incr_metric("kotlin_lambda_inlined",
                  inliner.get_info().kotlin_lambda_inlined);
  mgr.incr_metric("partially_inlined", inliner.get_info().partially_inlined);

  // Log top-10 partially inlined callees
  std::vector<std::pair<const DexMethod*, size_t>> partially_inlined_callees;
  const auto& atomic_map = inliner.get_info().partially_inlined_callees;
  partially_inlined_callees.reserve(atomic_map.size());
  for (auto&& [callee, count] : UnorderedIterable(atomic_map)) {
    partially_inlined_callees.emplace_back(callee, count.load());
  }
  std::sort(partially_inlined_callees.begin(), partially_inlined_callees.end(),
            [](const auto& p, const auto& q) {
              if (p.second != q.second) {
                return p.second > q.second;
              }
              return compare_dexmethods(p.first, q.first);
            });
  for (size_t i = 0; i < partially_inlined_callees.size() && i < 10; i++) {
    auto [callee, count] = partially_inlined_callees[i];
    mgr.incr_metric(
        "partially_inlined_callee_" + std::to_string(i) + "_" + show(callee),
        count);
  }

  mgr.incr_metric("calls_not_inlinable",
                  inliner.get_info().calls_not_inlinable);
  mgr.incr_metric("no_returns", inliner.get_info().no_returns);
  mgr.incr_metric("intermediate_shrinkings",
                  inliner.get_info().intermediate_shrinkings);
  mgr.incr_metric("intermediate_remove_unreachable_blocks",
                  inliner.get_info().intermediate_remove_unreachable_blocks);
  mgr.incr_metric("calls_not_inlined", inliner.get_info().calls_not_inlined);
  mgr.incr_metric(
      "calls_not_inlined_with_perf_sensitive_constructors",
      inliner.get_info().calls_not_inlined_with_perf_sensitive_constructors);
  mgr.incr_metric("methods_removed", deleted.size());
  mgr.incr_metric("escaped_virtual", inliner.get_info().escaped_virtual);
  mgr.incr_metric("unresolved_methods", inliner.get_info().unresolved_methods);
  mgr.incr_metric("known_public_methods",
                  inliner.get_info().known_public_methods);
  mgr.incr_metric(
      "constant_invoke_callers_analyzed",
      inliner.get_info()
          .call_site_summary_stats.constant_invoke_callers_analyzed);
  mgr.incr_metric(
      "constant_invoke_callers_unreachable",
      inliner.get_info()
          .call_site_summary_stats.constant_invoke_callers_unreachable);
  mgr.incr_metric(
      "constant_invoke_callers_unreachable_blocks",
      inliner.get_info()
          .call_site_summary_stats.constant_invoke_callers_unreachable_blocks);
  mgr.incr_metric("constant_invoke_callers_critical_path_length",
                  inliner.get_info()
                      .call_site_summary_stats
                      .constant_invoke_callers_critical_path_length);
  mgr.incr_metric("constant_invoke_callees_analyzed",
                  inliner.get_info().constant_invoke_callees_analyzed);
  mgr.incr_metric("constant_invoke_callees_no_return",
                  inliner.get_info().constant_invoke_callees_no_return);
  mgr.incr_metric("constant_invoke_callees_unused_results",
                  inliner.get_info().constant_invoke_callees_unused_results);
  mgr.incr_metric("critical_path_length",
                  inliner.get_info().critical_path_length);
  mgr.incr_metric("methods_shrunk", shrinker.get_methods_shrunk());
  mgr.incr_metric("callers", inliner.get_callers());
  mgr.incr_metric(
      "instructions_eliminated_const_prop",
      shrinker.get_const_prop_stats().branches_removed +
          shrinker.get_const_prop_stats().unreachable_instructions_removed +
          shrinker.get_const_prop_stats().branches_forwarded +
          shrinker.get_const_prop_stats().materialized_consts +
          shrinker.get_const_prop_stats().added_param_const +
          shrinker.get_const_prop_stats().throws +
          shrinker.get_const_prop_stats().null_checks);
  {
    ScopedMetrics sm(mgr);
    auto sm_scope = sm.scope("inliner");
    shrinker.log_metrics(sm);
  }
  mgr.incr_metric("instructions_eliminated_cse",
                  shrinker.get_cse_stats().instructions_eliminated);
  mgr.incr_metric("instructions_eliminated_copy_prop",
                  shrinker.get_copy_prop_stats().moves_eliminated);
  mgr.incr_metric("instructions_eliminated_localdce_dead",
                  shrinker.get_local_dce_stats().dead_instruction_count);
  mgr.incr_metric("instructions_eliminated_localdce_unreachable",
                  shrinker.get_local_dce_stats().unreachable_instruction_count);
  mgr.incr_metric("instructions_eliminated_unreachable",
                  inliner.get_info().unreachable_insns);
  mgr.incr_metric("instructions_eliminated_dedup_blocks",
                  shrinker.get_dedup_blocks_stats().insns_removed);
  mgr.incr_metric("instructions_eliminated_branch_prefix_hoisting",
                  shrinker.get_branch_prefix_hoisting_stats());
  mgr.incr_metric("blocks_eliminated_by_dedup_blocks",
                  shrinker.get_dedup_blocks_stats().blocks_removed);
  mgr.incr_metric("methods_reg_alloced", shrinker.get_methods_reg_alloced());
  mgr.incr_metric("localdce_init_class_instructions_added",
                  shrinker.get_local_dce_stats().init_class_instructions_added);
  mgr.incr_metric(
      "localdce_init_class_instructions",
      shrinker.get_local_dce_stats().init_classes.init_class_instructions);
  mgr.incr_metric("localdce_init_class_instructions_removed",
                  shrinker.get_local_dce_stats()
                      .init_classes.init_class_instructions_removed);
  mgr.incr_metric("localdce_init_class_instructions_refined",
                  shrinker.get_local_dce_stats()
                      .init_classes.init_class_instructions_refined);
  mgr.incr_metric("not_cold_methods", inliner.get_not_cold_methods());
  mgr.incr_metric("maybe_hot_methods", inliner.get_maybe_hot_methods());

  // Expose the shrinking timers as Timers.
  Timer::add_timer("Inliner.Shrinking.ConstantPropagation",
                   shrinker.get_const_prop_seconds());
  Timer::add_timer("Inliner.Shrinking.CSE", shrinker.get_cse_seconds());
  Timer::add_timer("Inliner.Shrinking.CopyPropagation",
                   shrinker.get_copy_prop_seconds());
  Timer::add_timer("Inliner.Shrinking.LocalDCE",
                   shrinker.get_local_dce_seconds());
  Timer::add_timer("Inliner.Shrinking.DedupBlocks",
                   shrinker.get_dedup_blocks_seconds());
  Timer::add_timer("Inliner.Shrinking.BranchPrefixHoisting",
                   shrinker.get_branch_prefix_hoisting_seconds());
  Timer::add_timer("Inliner.Shrinking.RegAlloc",
                   shrinker.get_reg_alloc_seconds());
  Timer::add_timer("Inliner.Inlining.inline_callees",
                   inliner.get_inline_callees_seconds());
  Timer::add_timer("Inliner.Inlining.inline_callees_should_inline",
                   inliner.get_inline_callees_should_inline_seconds());
  Timer::add_timer("Inliner.Inlining.inline_callees_init",
                   inliner.get_inline_callees_init_seconds());
  Timer::add_timer("Inliner.Inlining.inline_inlinables",
                   inliner.get_inline_inlinables_seconds());
  Timer::add_timer("Inliner.Inlining.inline_with_cfg",
                   inliner.get_inline_with_cfg_seconds());
  Timer::add_timer("Inliner.Inlining.call_site_inlined_cost",
                   inliner.get_call_site_inlined_cost_seconds());
  Timer::add_timer("Inliner.Inlining.cannot_inline_sketchy_code",
                   inliner.get_cannot_inline_sketchy_code_timer_seconds());
}

HotColdInliningBehavior parse_hot_cold_inlining_behavior(
    const std::string& str) {
  if (str == "none") {
    return HotColdInliningBehavior::None;
  }
  if (str == "respect-not-cold") {
    return HotColdInliningBehavior::RespectNotCold;
  }
  if (str == "respect-maybe-hot") {
    return HotColdInliningBehavior::RespectMaybeHot;
  }
  always_assert_log(false, "Unknown hot-cold inlining behavior: %s",
                    str.c_str());
}
} // namespace inliner
