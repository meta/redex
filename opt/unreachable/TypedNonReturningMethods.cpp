/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypedNonReturningMethods.h"

#include <vector>

#include "AtomicStatCounter.h"
#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexDefs.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "ReachableClasses.h"
#include "Show.h"
#include "Trace.h"
#include "UnreachableDefUseChains.h"
#include "Walkers.h"

namespace typed_nonreturning_methods {

namespace {

// The 3-code-unit `invoke-static` of `UnreachableException.createAndThrow()`.
constexpr size_t SAVED_BYTES_PER_CALL_SITE = 6;

// The CFG shape of an `unreachable` that is the value a following `throw`
// throws, and nothing else.
bool is_thrown_unreachable(const cfg::ControlFlowGraph& cfg,
                           const cfg::InstructionIterator& unreachable_it,
                           const live_range::DefUseChains& du_chains) {
  auto throw_it = cfg.next_following_gotos(unreachable_it);
  if (throw_it.is_end() || throw_it.block() != unreachable_it.block() ||
      throw_it->insn->opcode() != OPCODE_THROW ||
      throw_it->insn->src(0) != unreachable_it->insn->dest()) {
    return false;
  }
  auto it = du_chains.find(unreachable_it->insn);
  return it != du_chains.end() && it->second.size() == 1 &&
         unordered_any(it->second)->insn == throw_it->insn;
}

// Whether the definition `nonreturning_method` may be changed at all.
bool is_eligible_definition(const DexMethod* nonreturning_method) {
  if (!is_static(nonreturning_method) ||
      nonreturning_method->get_code() == nullptr ||
      !nonreturning_method->get_proto()->is_void() ||
      !method::can_change_signature(nonreturning_method) ||
      !can_delete(nonreturning_method)) {
    return false;
  }
  const auto* cls = type_class(nonreturning_method->get_class());
  return cls != nullptr && can_rename(cls) && !marked_by_string(cls) &&
         !is_serde(cls);
}

DexProto* make_typed_proto(const DexMethod* method, DexType* result_type) {
  return DexProto::make_proto(result_type, method->get_proto()->get_args());
}

// The `unreachable` that is the value thrown right after `invoke_it`, if any:
// in the same block, or, if the invoke may throw to a handler, first in the
// block reached only from the invoke's block through its goto edge (the CFG
// shape of a result of such an invoke).
IRInstruction* match_call_site(const cfg::ControlFlowGraph& cfg,
                               const cfg::InstructionIterator& invoke_it,
                               const live_range::DefUseChains& du_chains) {
  auto unreachable_it = cfg.next_following_gotos(invoke_it);
  if (unreachable_it.is_end() ||
      !opcode::is_unreachable(unreachable_it->insn->opcode())) {
    return nullptr;
  }
  auto* invoke_block = invoke_it.block();
  auto* unreachable_block = unreachable_it.block();
  if (unreachable_block != invoke_block) {
    const auto& preds = unreachable_block->preds();
    if (cfg.get_succ_edge_of_type(invoke_block, cfg::EDGE_THROW) == nullptr ||
        preds.size() != 1 || preds.front()->src() != invoke_block ||
        preds.front()->type() != cfg::EDGE_GOTO ||
        invoke_block->get_last_insn()->insn != invoke_it->insn ||
        unreachable_block->get_first_insn()->insn != unreachable_it->insn) {
      return nullptr;
    }
  }
  if (!is_thrown_unreachable(cfg, unreachable_it, du_chains)) {
    return nullptr;
  }
  return unreachable_it->insn;
}

// The method that `insn` calls, if `insn` is an `invoke-static` of a void
// method definition.
DexMethod* get_static_void_callee(const IRInstruction* insn) {
  if (insn->opcode() != OPCODE_INVOKE_STATIC) {
    return nullptr;
  }
  auto* callee = insn->get_method()->as_def();
  if (callee == nullptr || !callee->get_proto()->is_void()) {
    return nullptr;
  }
  return callee;
}

// The protos of the methods that `dex` defines or references.
UnorderedSet<const DexProto*> gather_dex_protos(const DexClasses& dex) {
  std::vector<DexMethodRef*> methods;
  for (const auto* cls : dex) {
    cls->gather_methods(methods);
  }
  UnorderedSet<const DexProto*> res;
  for (const auto* m : methods) {
    res.insert(m->get_proto());
  }
  return res;
}

// A non-returning method to type, with its new signature and the `unreachable`
// instructions of its call sites, each of which becomes the result of the call
// before it.
struct Selection {
  DexMethod* method;
  DexProto* typed_proto;
  std::vector<IRInstruction*> unreachables;
};

class Analysis {
 public:
  Analysis(const DexStoresVector& stores,
           const Scope& scope,
           DexType* result_type,
           const baseline_profiles::BaselineProfile& baseline_profile,
           uint32_t huge_method_max)
      : m_result_type(result_type),
        m_baseline_profile(baseline_profile),
        m_huge_method_max(huge_method_max),
        m_scope(scope),
        m_xdexes(stores) {
    for (const auto& store : stores) {
      for (const auto& dex : store.get_dexen()) {
        m_dexen.push_back(&dex);
      }
    }
  }

  // Returns the selected methods, in a deterministic order. Does not change
  // anything.
  std::vector<Selection> run(Stats* stats) {
    find_call_sites(stats);
    auto candidates = unordered_to_ordered_keys(m_sites, compare_dexmethods);
    stats->candidate_methods = candidates.size();
    for (auto* method : candidates) {
      if (!is_eligible_definition(method) ||
          !method->get_code()->cfg().return_blocks().empty()) {
        m_rejected.insert(method);
        continue;
      }
      auto* typed = make_typed_proto(method, m_result_type);
      // No method of the app returns the result type, and static methods are
      // not inherited, so only the method's own class can hold the new
      // signature, as a method or a reference.
      if (DexMethod::get_method(method->get_class(), method->get_name(),
                                typed) != nullptr) {
        m_rejected.insert(method);
        continue;
      }
      m_typed_protos.emplace(method, typed);
    }
    check_references();
    stats->rejected_methods = m_rejected.size();

    std::vector<Selection> selected;
    for (auto* method : candidates) {
      if (m_rejected.count(method) != 0u) {
        continue;
      }
      if (!select_if_profitable(method)) {
        stats->unprofitable_methods++;
        continue;
      }
      selected.push_back(Selection{method, m_typed_protos.at(method),
                                   std::move(m_sites.at(method))});
    }
    return selected;
  }

 private:
  // Records the convertible call sites: in a caller that is not compiled, or
  // covered by a handler.
  void find_call_sites(Stats* stats) {
    ConcurrentMap<DexMethod*, std::vector<IRInstruction*>> sites;
    AtomicStatCounter<size_t> compiled_call_sites{0};
    walk::parallel::code(m_scope, [&](DexMethod* caller, IRCode& code) {
      auto& cfg = code.cfg();
      if (caller->rstate.no_optimizations()) {
        return;
      }
      auto ii = cfg::InstructionIterable(cfg);
      bool compiled = baseline_profiles::dex2oat_compiles(
          m_baseline_profile, caller, m_huge_method_max);
      Lazy<live_range::DefUseChains> du_chains(
          [&cfg]() { return unreachable::get_def_use_chains(cfg); });
      for (auto it = ii.begin(); it != ii.end(); ++it) {
        auto* callee = get_static_void_callee(it->insn);
        if (callee == nullptr) {
          continue;
        }
        auto* unreachable = match_call_site(cfg, it, *du_chains);
        if (unreachable == nullptr) {
          continue;
        }
        if (compiled &&
            cfg.get_succ_edge_of_type(it.block(), cfg::EDGE_THROW) == nullptr) {
          compiled_call_sites++;
          continue;
        }
        sites.update(callee, [&](DexMethod*, auto& v, bool) {
          v.push_back(unreachable);
        });
      }
    });
    for (auto& [method, v] : UnorderedIterable(sites)) {
      m_sites.emplace(method, std::move(v));
    }
    stats->compiled_call_sites = compiled_call_sites;
  }

  // The candidate that `ref` is, if any. Method references are resolved to
  // their definitions, so a candidate is referenced only as itself.
  DexMethod* get_candidate(DexMethodRef* ref) const {
    auto* method = ref->as_def();
    return method != nullptr && m_typed_protos.count(method) != 0u ? method
                                                                   : nullptr;
  }

  void check_references() {
    InsertOnlyConcurrentSet<DexMethod*> rejected;
    ConcurrentMap<DexMethod*, UnorderedSet<size_t>> referencing_dexen;
    auto reject_all = [&](const std::vector<DexMethodRef*>& refs) {
      for (auto* ref : refs) {
        if (auto* method = get_candidate(ref)) {
          rejected.insert(method);
        }
      }
    };
    walk::parallel::classes(m_scope, [&](DexClass* cls) {
      // References from metadata: class and member annotations, parameter
      // annotations and static values.
      std::vector<DexMethodRef*> metadata_refs;
      if (cls->get_anno_set() != nullptr) {
        cls->get_anno_set()->gather_methods(metadata_refs);
      }
      for (auto* field : cls->get_all_fields()) {
        field->gather_methods(metadata_refs);
      }
      for (auto* method : cls->get_all_methods()) {
        method->gather_methods_from_annos(metadata_refs);
      }
      reject_all(metadata_refs);

      auto dex = m_xdexes.get_dex_idx(cls->get_type());
      for (auto* method : cls->get_all_methods()) {
        auto* code = method->get_code();
        if (code == nullptr) {
          continue;
        }
        for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
          auto* insn = mie.insn;
          if (!insn->has_method()) {
            // References from call sites and method handles.
            std::vector<DexMethodRef*> indirect_refs;
            insn->gather_methods(indirect_refs);
            reject_all(indirect_refs);
            continue;
          }
          auto* nonreturning_method = get_candidate(insn->get_method());
          if (nonreturning_method == nullptr) {
            continue;
          }
          if (method->rstate.no_optimizations()) {
            rejected.insert(nonreturning_method);
          } else {
            referencing_dexen.update(
                nonreturning_method,
                [&](DexMethod*, auto& dexen, bool) { dexen.insert(dex); });
          }
        }
      }
    });
    insert_unordered_iterable(m_rejected, rejected);
    for (auto& [method, dexen] : UnorderedIterable(referencing_dexen)) {
      m_referencing_dexen.emplace(method, std::move(dexen));
    }
    // The definition is also in a dex.
    for (auto& [method, _] : UnorderedIterable(m_typed_protos)) {
      m_referencing_dexen[method].insert(
          m_xdexes.get_dex_idx(method->get_class()));
    }
  }

  UnorderedSet<const DexProto*>& get_dex_protos(size_t dex) {
    auto it = m_dex_protos.find(dex);
    if (it == m_dex_protos.end()) {
      it = m_dex_protos.emplace(dex, gather_dex_protos(*m_dexen.at(dex))).first;
    }
    return it->second;
  }

  // Selects `method` if its call sites save more than the proto entries its
  // new signature adds to the dexes that reference it.
  bool select_if_profitable(DexMethod* method) {
    auto* typed = m_typed_protos.at(method);
    std::vector<size_t> adding_dexen;
    for (auto dex : unordered_to_ordered(m_referencing_dexen.at(method))) {
      if (get_dex_protos(dex).count(typed) == 0u) {
        adding_dexen.push_back(dex);
      }
    }
    size_t cost = adding_dexen.size() * sizeof(dex_proto_id);
    size_t saving = m_sites.at(method).size() * SAVED_BYTES_PER_CALL_SITE;
    if (saving <= cost) {
      return false;
    }
    for (auto dex : adding_dexen) {
      get_dex_protos(dex).insert(typed);
    }
    return true;
  }

  DexType* m_result_type;
  const baseline_profiles::BaselineProfile& m_baseline_profile;
  uint32_t m_huge_method_max;
  const Scope& m_scope;
  XDexRefs m_xdexes;
  std::vector<const DexClasses*> m_dexen;
  UnorderedMap<DexMethod*, std::vector<IRInstruction*>> m_sites;
  UnorderedSet<const DexMethod*> m_rejected;
  UnorderedMap<const DexMethod*, DexProto*> m_typed_protos;
  UnorderedMap<const DexMethod*, UnorderedSet<size_t>> m_referencing_dexen;
  UnorderedMap<size_t, UnorderedSet<const DexProto*>> m_dex_protos;
};

} // namespace

Stats type_nonreturning_methods(
    const DexStoresVector& stores,
    const Scope& scope,
    DexType* result_type,
    const baseline_profiles::BaselineProfile& baseline_profile,
    uint32_t huge_method_max) {
  Stats stats;
  Analysis analysis(stores, scope, result_type, baseline_profile,
                    huge_method_max);
  auto selected = analysis.run(&stats);

  // Nothing above changed the program; from here on, only the selected
  // methods and their recorded call sites change.
  for (auto& [method, typed, unreachables] : selected) {
    method->change(DexMethodSpec(nullptr, nullptr, typed),
                   /* rename_on_collision */ false);
    for (auto* unreachable : unreachables) {
      unreachable->set_opcode(OPCODE_MOVE_RESULT_OBJECT);
    }
    stats.typed_methods++;
    stats.typed_call_sites += unreachables.size();
    TRACE(UNREACHABLE, 2, "typed %s, %zu call sites", SHOW(method),
          unreachables.size());
  }
  return stats;
}

} // namespace typed_nonreturning_methods
