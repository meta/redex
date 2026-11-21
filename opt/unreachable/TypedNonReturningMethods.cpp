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
#include "DexStructure.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "ReachableClasses.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SourceBlocksUtils.h"
#include "Trace.h"
#include "UnreachableDefUseChains.h"
#include "Walkers.h"

namespace typed_nonreturning_methods {

namespace {

// The 3-code-unit `invoke-static` of `UnreachableException.createAndThrow()`.
constexpr size_t SAVED_BYTES_PER_CALL_SITE = 6;

// What keeping the original method as a stub adds besides method references
// and protos: the stub's code item, a header and the 4 code units of
// `invoke-static` and `return-void`, and an encoded_method entry, whose
// uleb128 index difference, access flags and code offset take about 6 bytes.
constexpr size_t STUB_BYTES = sizeof(dex_code_item) + 4 * sizeof(uint16_t) + 6;

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

// The room a dex has for more method references, and the protos of the
// methods that it defines or references.
struct DexRefs {
  MethodRefRoom method_ref_room;
  UnorderedSet<const DexProto*> protos;
};

DexRefs gather_dex_refs(const DexClasses& dex, size_t reserved_mrefs) {
  UnorderedSet<DexMethodRef*> methods;
  for (const auto* cls : dex) {
    cls->gather_methods(methods);
  }
  DexRefs res{MethodRefRoom(methods.size(), reserved_mrefs), {}};
  for (const auto* m : UnorderedIterable(methods)) {
    res.protos.insert(m->get_proto());
  }
  return res;
}

// The dexes that reference a candidate, by whether the reference can change.
struct References {
  // Instructions in methods without `no_optimizations`, which can reference
  // the typed method instead.
  UnorderedSet<size_t> retargetable_dexen;
  // Annotations, static values, method handles and instructions in
  // `no_optimizations` methods, which must keep the original signature.
  UnorderedSet<size_t> fixed_dexen;
};

// A non-returning method to type, with its new signature, whether its original
// signature stays for references that must not change, and the `unreachable`
// instructions of its call sites, each of which becomes the result of the call
// before it.
struct Selection {
  DexMethod* method;
  DexProto* typed_proto;
  bool keep_original;
  std::vector<IRInstruction*> unreachables;
};

// The code of a stub with the signature of `method` that passes its arguments
// to `target` and returns.
std::unique_ptr<IRCode> make_stub_code(DexMethod* method, DexMethod* target) {
  auto code = std::make_unique<IRCode>(method, /* temp_regs */ 0);
  std::vector<reg_t> args;
  for (const auto& mie : InstructionIterable(code->get_param_instructions())) {
    args.push_back(mie.insn->dest());
  }
  auto* invoke = new IRInstruction(OPCODE_INVOKE_STATIC);
  invoke->set_method(target)->set_srcs_size(args.size());
  for (size_t i = 0; i < args.size(); ++i) {
    invoke->set_src(i, args[i]);
  }
  code->push_back(invoke);
  code->push_back(new IRInstruction(OPCODE_RETURN_VOID));
  code->build_cfg();
  return code;
}

class Analysis {
 public:
  Analysis(const DexStoresVector& stores,
           const Scope& scope,
           DexType* result_type,
           const baseline_profiles::BaselineProfile& baseline_profile,
           uint32_t huge_method_max,
           size_t reserved_mrefs)
      : m_result_type(result_type),
        m_baseline_profile(baseline_profile),
        m_huge_method_max(huge_method_max),
        m_reserved_mrefs(reserved_mrefs),
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
      // Every candidate has references: the call sites it was found at are
      // instructions in methods without `no_optimizations`.
      bool keep_original = !m_references.at(method).fixed_dexen.empty();
      switch (select(method, keep_original)) {
      case Outcome::Unprofitable:
        stats->unprofitable_methods++;
        continue;
      case Outcome::NoMethodRefRoom:
        stats->no_method_ref_room_methods++;
        continue;
      case Outcome::Selected:
        break;
      }
      selected.push_back(Selection{method, m_typed_protos.at(method),
                                   keep_original,
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

  // Records which dexes reference each candidate, and whether each reference
  // can be changed to reference the typed method.
  void check_references() {
    ConcurrentMap<DexMethod*, References> references;
    auto add_fixed = [&](const std::vector<DexMethodRef*>& refs, size_t dex) {
      for (auto* ref : refs) {
        if (auto* method = get_candidate(ref)) {
          references.update(method, [&](DexMethod*, References& r, bool) {
            r.fixed_dexen.insert(dex);
          });
        }
      }
    };
    walk::parallel::classes(m_scope, [&](DexClass* cls) {
      auto dex = m_xdexes.get_dex_idx(cls->get_type());
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
      add_fixed(metadata_refs, dex);

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
            add_fixed(indirect_refs, dex);
            continue;
          }
          auto* nonreturning_method = get_candidate(insn->get_method());
          if (nonreturning_method == nullptr) {
            continue;
          }
          bool fixed = method->rstate.no_optimizations();
          references.update(
              nonreturning_method, [&](DexMethod*, References& r, bool) {
                (fixed ? r.fixed_dexen : r.retargetable_dexen).insert(dex);
              });
        }
      }
    });
    for (auto& [method, refs] : UnorderedIterable(references)) {
      m_references.emplace(method, std::move(refs));
    }
  }

  DexRefs& get_dex_refs(size_t dex) {
    auto it = m_dex_refs.find(dex);
    if (it == m_dex_refs.end()) {
      it =
          m_dex_refs
              .emplace(dex, gather_dex_refs(*m_dexen.at(dex), m_reserved_mrefs))
              .first;
    }
    return it->second;
  }

  enum class Outcome { Selected, Unprofitable, NoMethodRefRoom };

  // Selects `method` if its converted call sites save more than its typed
  // signature adds: a proto in each dex that references the typed method and
  // lacks it and, if `keep_original`, the stub and a second method reference
  // in each dex that references both signatures, which must have room for it.
  Outcome select(DexMethod* method, bool keep_original) {
    auto* typed = m_typed_protos.at(method);
    const auto& refs = m_references.at(method);
    auto definition_dex = m_xdexes.get_dex_idx(method->get_class());
    auto typed_dexen = refs.retargetable_dexen;
    // The definition is also in a dex.
    typed_dexen.insert(definition_dex);
    std::vector<size_t> adding_proto_dexen;
    std::vector<size_t> adding_ref_dexen;
    for (auto dex : unordered_to_ordered(typed_dexen)) {
      if (get_dex_refs(dex).protos.count(typed) == 0u) {
        adding_proto_dexen.push_back(dex);
      }
      if (keep_original &&
          (dex == definition_dex || refs.fixed_dexen.count(dex) != 0u)) {
        adding_ref_dexen.push_back(dex);
      }
    }
    size_t cost = adding_proto_dexen.size() * sizeof(dex_proto_id);
    if (keep_original) {
      cost += adding_ref_dexen.size() * sizeof(dex_method_id) + STUB_BYTES;
    }
    size_t saving = m_sites.at(method).size() * SAVED_BYTES_PER_CALL_SITE;
    if (saving <= cost) {
      return Outcome::Unprofitable;
    }
    for (auto dex : adding_ref_dexen) {
      if (!get_dex_refs(dex).method_ref_room.can_add()) {
        return Outcome::NoMethodRefRoom;
      }
    }
    for (auto dex : adding_proto_dexen) {
      get_dex_refs(dex).protos.insert(typed);
    }
    for (auto dex : adding_ref_dexen) {
      get_dex_refs(dex).method_ref_room.add();
    }
    return Outcome::Selected;
  }

  DexType* m_result_type;
  const baseline_profiles::BaselineProfile& m_baseline_profile;
  uint32_t m_huge_method_max;
  size_t m_reserved_mrefs;
  const Scope& m_scope;
  XDexRefs m_xdexes;
  std::vector<const DexClasses*> m_dexen;
  UnorderedMap<DexMethod*, std::vector<IRInstruction*>> m_sites;
  UnorderedSet<const DexMethod*> m_rejected;
  UnorderedMap<const DexMethod*, DexProto*> m_typed_protos;
  UnorderedMap<const DexMethod*, References> m_references;
  UnorderedMap<size_t, DexRefs> m_dex_refs;
};

} // namespace

DexMethod* split_off_typed_method(DexMethod* method,
                                  DexProto* typed_proto,
                                  method_profiles::MethodProfiles& profiles) {
  always_assert_log(is_static(method) && method->get_code() != nullptr, "%s",
                    SHOW(method));
  always_assert_log(DexMethod::get_method(method->get_class(),
                                          method->get_name(),
                                          typed_proto) == nullptr,
                    "%s already has a method with the typed signature",
                    SHOW(method));
  auto* cls = type_class(method->get_class());
  auto* typed_method =
      DexMethod::make_method(method->get_class(), method->get_name(),
                             typed_proto)
          ->make_concrete(method->get_access(), method->release_code(),
                          /* is_virtual */ false);
  typed_method->rstate = method->rstate;
  // The body keeps the original's deobfuscated name, as it does when typed in
  // place, so that profiles and symbolication find it under the same name in
  // both cases. The stub gets a name of its own, which must be unique.
  const auto* original_name = method->get_deobfuscated_name_or_null();
  if (original_name != nullptr && !original_name->str().empty()) {
    method->set_deobfuscated_name(
        show_deobfuscated(method->get_class()) + "." +
        method->get_simple_deobfuscated_name() +
        "$stub:" + show_deobfuscated(method->get_proto()));
    typed_method->set_deobfuscated_name(original_name->str_copy());
  }
  cls->add_method(typed_method);
  method->set_code(make_stub_code(method, typed_method));
  auto* entry_source_block =
      source_blocks::get_first_source_block_of_method(typed_method);
  if (entry_source_block != nullptr) {
    source_blocks::insert_synthetic_source_blocks_in_method(method, [&]() {
      return source_blocks::clone_as_synthetic(entry_source_block, method);
    });
  }
  profiles.derive_stats(typed_method, {method});
  return typed_method;
}

Stats type_nonreturning_methods(
    const DexStoresVector& stores,
    const Scope& scope,
    DexType* result_type,
    const baseline_profiles::BaselineProfile& baseline_profile,
    uint32_t huge_method_max,
    size_t reserved_mrefs,
    method_profiles::MethodProfiles& method_profiles) {
  Stats stats;
  Analysis analysis(stores, scope, result_type, baseline_profile,
                    huge_method_max, reserved_mrefs);
  auto selected = analysis.run(&stats);

  // Nothing above changed the program; from here on, only the selected
  // methods, their recorded call sites and the instructions that reference
  // them change.
  UnorderedMap<const DexMethodRef*, DexMethod*> typed_methods;
  for (auto& [method, typed, keep_original, unreachables] : selected) {
    if (keep_original) {
      typed_methods.emplace(
          method, split_off_typed_method(method, typed, method_profiles));
      stats.stub_methods++;
    } else {
      method->change(DexMethodSpec(nullptr, nullptr, typed),
                     /* rename_on_collision */ false);
    }
    for (auto* unreachable : unreachables) {
      unreachable->set_opcode(OPCODE_MOVE_RESULT_OBJECT);
    }
    stats.typed_methods++;
    stats.typed_call_sites += unreachables.size();
    TRACE(UNREACHABLE, 2, "typed %s, %zu call sites%s", SHOW(method),
          unreachables.size(), keep_original ? ", original kept" : "");
  }
  if (typed_methods.empty()) {
    return stats;
  }
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    if (caller->rstate.no_optimizations()) {
      return;
    }
    for (const auto& mie : cfg::InstructionIterable(code.cfg())) {
      if (!mie.insn->has_method()) {
        continue;
      }
      auto it = typed_methods.find(mie.insn->get_method());
      if (it != typed_methods.end()) {
        mie.insn->set_method(it->second);
      }
    }
  });
  return stats;
}

} // namespace typed_nonreturning_methods
