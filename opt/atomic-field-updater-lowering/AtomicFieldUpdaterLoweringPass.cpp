/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AtomicFieldUpdaterLoweringPass.h"

#include "AtomicFieldUpdaters.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "CFGMutation.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "Deleter.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "InitClassesWithSideEffects.h"
#include "Inliner.h"
#include "InlinerConfig.h"
#include "LiveRange.h"
#include "LocalDce.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "ReflectionAnalysis.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeInference.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
using namespace dex_asm;
using atomic_field_updaters::Kind;
using atomic_field_updaters::kind_name;
using atomic_field_updaters::SYNTH_HOLDER_DESC;
using atomic_field_updaters::UNSAFE_DESC;

// A recognized updater: a `static final Atomic*FieldUpdater` field whose sole
// write is `newUpdater(holder, [T,] "field_name")` in the holder's <clinit>,
// and where `holder.field_name` is a non-static volatile field.
struct UpdaterInfo {
  DexField* updater; // the static final updater field
  DexType* holder; // class declaring the volatile field
  const DexString* field_name; // the volatile field's name
  const DexType* field_type{nullptr}; // the volatile field's declared type
  DexField* offset_field{nullptr}; // synthesized: static final long offset
  Kind kind{Kind::REFERENCE};
};

bool is_volatile_instance_field(const DexField* f) {
  return !is_static(f) && is_volatile(f);
}

// How many updaters were recognized, per flavor, indexed by `Kind`. Sized off
// `all_kinds` so a fourth flavor could not leave the array behind.
using KindCounts =
    std::array<size_t,
               std::tuple_size_v<decltype(atomic_field_updaters::all_kinds())>>;

// Below API 32, d8 never emits `AtomicReferenceFieldUpdater.compareAndSet`
// directly. It routes every call through a synthetic forwarder,
// `<Ctx>$$ExternalSyntheticBackportWithForwardingN.m(u, o, e, n)`, whose body
// retries while the field still holds `expect` -- its workaround for
// b/211646483. Inside the forwarder the updater is a parameter, so nothing
// there resolves; at the call site it is still the field load. So the call to
// the forwarder is treated as the operation itself.
//
// Maps each recognized forwarder to the `compareAndSet` its body calls.
using BackportForwarders =
    UnorderedMap<const DexMethodRef*, const DexMethodRef*>;

// A call that performs an updater operation, and which one: an updater method
// invoked directly, or a recognized forwarder. The srcs line up in both shapes
// -- src0 the updater, src1 the holder, then the values -- so the analysis
// indexes them the same way.
struct OperationSite {
  IRInstruction* insn;
  Kind kind;
  // The updater method performed. For a forwarder, the `compareAndSet` it
  // calls: names, signatures and statistics keys are read from this, never
  // from the forwarder itself.
  const DexMethodRef* api;
  bool via_backport{false};
};

// Which calls are updater operations. Every walker asks the same question, so
// it is answered in one place, from the updater types the program references
// and the forwarders recognized in it.
class UpdaterOperations {
 public:
  explicit UpdaterOperations(BackportForwarders forwarders)
      : m_kinds(atomic_field_updaters::present_kinds()),
        m_forwarders(std::move(forwarders)) {}

  // The updater types present, mapped to their flavor. Empty when the program
  // references none.
  const UnorderedMap<const DexType*, Kind>& kinds() const { return m_kinds; }

  // The operation sites in `cfg`, in instruction order. Empty for the great
  // majority of methods, which touch no updater -- worth knowing before any
  // dataflow is built, because `MoveAwareChains` is not free.
  std::vector<OperationSite> sites_in(cfg::ControlFlowGraph& cfg) const {
    std::vector<OperationSite> sites;
    for (auto& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      const auto op = insn->opcode();
      if (opcode::is_invoke_virtual(op)) {
        auto it = m_kinds.find(insn->get_method()->get_class());
        if (it != m_kinds.end()) {
          sites.push_back(OperationSite{insn, it->second, insn->get_method()});
        }
      } else if (opcode::is_invoke_static(op)) {
        auto it = m_forwarders.find(insn->get_method());
        if (it != m_forwarders.end()) {
          sites.push_back(OperationSite{insn, Kind::REFERENCE, it->second,
                                        /*via_backport=*/true});
        }
      }
    }
    return sites;
  }

  // A forwarder's own calls take the updater as a parameter, so they can never
  // resolve; its call sites are where the operation is lowered.
  bool is_forwarder(const DexMethod* method) const {
    return m_forwarders.count(method) != 0u;
  }

 private:
  UnorderedMap<const DexType*, Kind> m_kinds;
  BackportForwarders m_forwarders;
};

// Recognition is confined to a single <clinit>: an updater is accepted only
// when the class that declares it also declares the volatile field it targets.
// A cross-class updater would need the writing and target classes analyzed
// together, which this does not attempt.
//
// All flavors are handled in one walk. `ReflectionAnalysis` and the use-def
// chains are the expensive part and are per-<clinit>, not per-flavor: a class
// declaring both an Integer and a Long updater -- the common shape, since
// atomicfu emits one per volatile field -- would otherwise rebuild both for
// each flavor in turn.
std::vector<UpdaterInfo> find_updaters(
    const Scope& scope,
    const UnorderedMap<const DexType*, Kind>& kinds,
    KindCounts& per_kind) {
  std::vector<UpdaterInfo> result;
  per_kind.fill(0);
  const auto* new_updater = atomic_field_updaters::new_updater_name();
  if (new_updater == nullptr || kinds.empty()) {
    return result;
  }

  // What a `newUpdater` call produced, keyed by the invoke itself --
  // `MoveAwareChains` looks through the `move-result`, so the invoke is what
  // its chains name as the def.
  struct Produced {
    DexType* holder;
    const DexString* name;
    Kind kind;
  };

  for (auto* cls : scope) {
    // Candidate updater fields: static final, of an updater type, carrying the
    // flavor that type implies.
    UnorderedMap<DexField*, Kind> candidates;
    for (auto* f : cls->get_sfields()) {
      auto kit = kinds.find(f->get_type());
      if (kit != kinds.end() && is_final(f)) {
        candidates.emplace(f, kit->second);
      }
    }
    if (candidates.empty()) {
      continue;
    }
    auto* clinit = cls->get_clinit();
    if (clinit == nullptr || clinit->get_code() == nullptr) {
      continue;
    }
    auto& cfg = clinit->get_code()->cfg();
    reflection::ReflectionAnalysis analysis(clinit);

    UnorderedMap<const IRInstruction*, Produced> produced_by;
    // Every store into a candidate field. A field written more than once is
    // rejected below rather than resolved to one of the writes: the lowering
    // substitutes a single offset for a single field, so two writes naming
    // different fields would leave one of them addressed through the other's
    // offset -- a raw memory access at the wrong address, not an exception.
    UnorderedMap<DexField*, std::vector<IRInstruction*>> stores;
    // Fields in the order their first store appears, so that what this returns
    // -- and with it the order offset fields are synthesized in later -- does
    // not depend on hash iteration order.
    std::vector<DexField*> store_order;

    for (auto& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      auto op = insn->opcode();

      if (opcode::is_invoke_static(op) &&
          insn->get_method()->get_name() == new_updater) {
        auto kit = kinds.find(insn->get_method()->get_class());
        if (kit == kinds.end()) {
          continue;
        }
        const uint16_t name_arg =
            atomic_field_updaters::field_name_arg_index(kit->second);
        if (insn->srcs_size() <= name_arg) {
          continue;
        }
        const auto& cls_obj = analysis.get_abstract_object(insn->src(0), insn);
        const auto& name_obj =
            analysis.get_abstract_object(insn->src(name_arg), insn);
        if (cls_obj && cls_obj->is_class() && cls_obj->dex_type != nullptr &&
            name_obj && name_obj->is_string() &&
            name_obj->dex_string != nullptr) {
          produced_by.emplace(insn,
                              Produced{const_cast<DexType*>(cls_obj->dex_type),
                                       name_obj->dex_string, kit->second});
        }
        continue;
      }

      if (opcode::is_sput_object(op) && insn->get_field()->is_def()) {
        auto* fdef = insn->get_field()->as_def();
        if (candidates.count(fdef) != 0) {
          if (stores[fdef].empty()) {
            store_order.push_back(fdef);
          }
          stores[fdef].push_back(insn);
        }
      }
    }
    if (store_order.empty()) {
      continue;
    }

    // Use-def rather than a scan over the instruction stream: the store and the
    // call that produced its value need not share a block -- a try region, or a
    // value computed under a branch, separates them -- and a register may be
    // reused for something else in between.
    live_range::MoveAwareChains chains(cfg);
    auto use_defs = chains.get_use_def_chains();

    for (auto* fdef : store_order) {
      const auto& sputs = stores.at(fdef);
      if (sputs.size() != 1) {
        TRACE(ATOMUP, 2, "skipping %s: %zu writes in <clinit>", SHOW(fdef),
              sputs.size());
        continue;
      }
      auto def_it = use_defs.find(live_range::Use{sputs.front(), 0});
      if (def_it == use_defs.end() || def_it->second.size() != 1) {
        continue;
      }
      auto info_it = produced_by.find(*def_it->second.begin());
      if (info_it == produced_by.end()) {
        continue;
      }
      const Produced& produced = info_it->second;
      const Kind kind = candidates.at(fdef);
      // The flavor that produced the value must be the flavor of the field it
      // is stored into, or the argument positions it was read with were the
      // wrong ones.
      if (produced.kind != kind) {
        continue;
      }
      // Require the updater to target a field of its own declaring class
      // (the atomicfu shape); cross-class holders are not handled.
      if (produced.holder != cls->get_type()) {
        continue;
      }
      DexField* target = nullptr;
      for (auto* ifield : cls->get_ifields()) {
        if (ifield->get_name() == produced.name &&
            is_volatile_instance_field(ifield)) {
          target = ifield;
          break;
        }
      }
      if (target == nullptr) {
        continue;
      }
      // The named field must have the type the flavor implies. The reference
      // flavor is checked too, rather than left unconstrained: javac would not
      // produce a reference updater over an `int`, but recognition should not
      // rest on the dex having come from javac.
      const auto* target_type = target->get_type();
      const bool type_matches_flavor =
          kind == Kind::INTEGER ? target_type == type::_int()
          : kind == Kind::LONG  ? target_type == type::_long()
                                : type::is_object(target_type);
      if (!type_matches_flavor) {
        continue;
      }
      per_kind.at(static_cast<size_t>(kind))++;
      result.push_back(UpdaterInfo{fdef, produced.holder, produced.name,
                                   target->get_type(), nullptr, kind});
      TRACE(ATOMUP, 3, "recognized %s updater %s for %s.%s", kind_name(kind),
            SHOW(fdef), SHOW(produced.holder), SHOW(produced.name));
    }
  }
  return result;
}

bool has_signature(const DexMethodRef* mref,
                   const DexType* rtype,
                   std::initializer_list<const DexType*> args) {
  const auto* proto = mref->get_proto();
  const auto* actual = proto->get_args();
  return proto->get_rtype() == rtype &&
         std::equal(actual->begin(), actual->end(), args.begin(), args.end());
}

bool is_reference_cas(const DexMethodRef* mref, const DexType* updater_type) {
  const auto* object_type = type::java_lang_Object();
  return mref->get_class() == updater_type &&
         mref->get_name()->str() == "compareAndSet" &&
         has_signature(mref, type::_boolean(),
                       {object_type, object_type, object_type});
}

bool is_reference_get(const DexMethodRef* mref, const DexType* updater_type) {
  const auto* object_type = type::java_lang_Object();
  return mref->get_class() == updater_type &&
         mref->get_name()->str() == "get" &&
         has_signature(mref, object_type, {object_type});
}

// The instructions of a forwarder that the match reasons about.
struct ForwarderShape {
  std::vector<IRInstruction*> params;
  IRInstruction* cas{nullptr};
  IRInstruction* get{nullptr};
  IRInstruction* test_swapped{nullptr};
  IRInstruction* test_unchanged{nullptr};
  cfg::Block* cas_block{nullptr};
  cfg::Block* get_block{nullptr};
};

// Four object parameters, and nothing in the body but one `compareAndSet`, one
// `get`, a test of each, and the moves, constants and returns around them.
// Nothing can throw to a handler.
std::optional<ForwarderShape> find_forwarder_shape(
    const cfg::ControlFlowGraph& cfg, const DexType* updater_type) {
  ForwarderShape shape;
  for (auto& mie : cfg.get_param_instructions()) {
    shape.params.push_back(mie.insn);
  }
  if (shape.params.size() != 4 ||
      !std::all_of(shape.params.begin(), shape.params.end(),
                   [](const IRInstruction* p) {
                     return opcode::is_load_param_object(p->opcode());
                   })) {
    return std::nullopt;
  }
  for (auto* block : cfg.blocks()) {
    if (cfg.get_succ_edge_of_type(block, cfg::EDGE_THROW) != nullptr) {
      return std::nullopt;
    }
    for (auto& mie : ir_list::InstructionIterable(block)) {
      auto* insn = mie.insn;
      const auto op = insn->opcode();
      if (opcode::is_a_load_param(op) || opcode::is_a_move(op) ||
          opcode::is_a_move_result(op) || op == OPCODE_RETURN) {
        continue;
      }
      if (op == OPCODE_CONST &&
          (insn->get_literal() == 0 || insn->get_literal() == 1)) {
        continue;
      }
      if (opcode::is_invoke_virtual(op) && shape.cas == nullptr &&
          is_reference_cas(insn->get_method(), updater_type)) {
        shape.cas = insn;
        shape.cas_block = block;
      } else if (opcode::is_invoke_virtual(op) && shape.get == nullptr &&
                 is_reference_get(insn->get_method(), updater_type)) {
        shape.get = insn;
        shape.get_block = block;
      } else if ((op == OPCODE_IF_EQZ || op == OPCODE_IF_NEZ) &&
                 shape.test_swapped == nullptr && block == shape.cas_block) {
        shape.test_swapped = insn;
      } else if ((op == OPCODE_IF_EQ || op == OPCODE_IF_NE) &&
                 shape.test_unchanged == nullptr && block == shape.get_block) {
        shape.test_unchanged = insn;
      } else {
        return std::nullopt;
      }
    }
  }
  if (shape.cas == nullptr || shape.get == nullptr ||
      shape.test_swapped == nullptr || shape.test_unchanged == nullptr) {
    return std::nullopt;
  }
  return shape;
}

// The `compareAndSet` takes the parameters in order, the `get` reads the same
// field, and the tests examine the swap's result and compare the re-read field
// with `expect`. Through use-def chains, so register allocation does not
// matter.
bool has_forwarder_dataflow(const cfg::ControlFlowGraph& cfg,
                            const ForwarderShape& shape) {
  live_range::MoveAwareChains chains(cfg);
  auto use_defs = chains.get_use_def_chains();
  auto def_of = [&](IRInstruction* insn, src_index_t i) -> IRInstruction* {
    auto it = use_defs.find(live_range::Use{insn, i});
    if (it == use_defs.end() || it->second.size() != 1) {
      return nullptr;
    }
    return *it->second.begin();
  };
  const auto& params = shape.params;
  for (src_index_t i = 0; i < 4; ++i) {
    if (def_of(shape.cas, i) != params[i]) {
      return false;
    }
  }
  if (def_of(shape.get, 0) != params[0] || def_of(shape.get, 1) != params[1] ||
      def_of(shape.test_swapped, 0) != shape.cas) {
    return false;
  }
  auto* lhs = def_of(shape.test_unchanged, 0);
  auto* rhs = def_of(shape.test_unchanged, 1);
  return (lhs == shape.get && rhs == params[2]) ||
         (lhs == params[2] && rhs == shape.get);
}

// A successful swap returns true, a failed one re-reads the field, an unchanged
// field retries the swap, and a changed one returns false.
bool has_forwarder_control_flow(const cfg::ControlFlowGraph& cfg,
                                const ForwarderShape& shape) {
  auto succ_of = [&](cfg::Block* b, cfg::EdgeType type) -> cfg::Block* {
    auto* e = cfg.get_succ_edge_of_type(b, type);
    return e == nullptr ? nullptr : e->target();
  };
  // Where a run of empty goto-only blocks starting at `b` ends.
  auto past_empty = [&](cfg::Block* b) {
    for (int steps = 0;
         b != nullptr && steps < 4 && b->get_first_insn() == b->end() &&
         succ_of(b, cfg::EDGE_BRANCH) == nullptr;
         ++steps) {
      b = succ_of(b, cfg::EDGE_GOTO);
    }
    return b;
  };
  // The literal a straight-line path from `b` returns.
  auto returned_literal = [&](cfg::Block* b) -> std::optional<int64_t> {
    UnorderedMap<reg_t, int64_t> literals;
    for (int steps = 0; b != nullptr && steps < 4; ++steps) {
      for (auto& mie : ir_list::InstructionIterable(b)) {
        auto* insn = mie.insn;
        if (insn->opcode() == OPCODE_CONST) {
          literals[insn->dest()] = insn->get_literal();
        } else if (opcode::is_a_move(insn->opcode())) {
          auto it = literals.find(insn->src(0));
          if (it == literals.end()) {
            literals.erase(insn->dest());
          } else {
            literals[insn->dest()] = it->second;
          }
        } else if (insn->opcode() == OPCODE_RETURN) {
          auto it = literals.find(insn->src(0));
          return it == literals.end() ? std::nullopt
                                      : std::optional<int64_t>(it->second);
        } else {
          return std::nullopt;
        }
      }
      if (succ_of(b, cfg::EDGE_BRANCH) != nullptr) {
        return std::nullopt;
      }
      b = succ_of(b, cfg::EDGE_GOTO);
    }
    return std::nullopt;
  };
  // if-eqz branches when the swap failed, if-nez when it succeeded; likewise
  // if-eq branches when the field is unchanged.
  const bool branches_on_swap = shape.test_swapped->opcode() == OPCODE_IF_NEZ;
  auto* on_swapped = succ_of(
      shape.cas_block, branches_on_swap ? cfg::EDGE_BRANCH : cfg::EDGE_GOTO);
  auto* on_lost = succ_of(shape.cas_block,
                          branches_on_swap ? cfg::EDGE_GOTO : cfg::EDGE_BRANCH);
  const bool branches_on_unchanged =
      shape.test_unchanged->opcode() == OPCODE_IF_EQ;
  auto* on_unchanged =
      succ_of(shape.get_block,
              branches_on_unchanged ? cfg::EDGE_BRANCH : cfg::EDGE_GOTO);
  auto* on_changed =
      succ_of(shape.get_block,
              branches_on_unchanged ? cfg::EDGE_GOTO : cfg::EDGE_BRANCH);
  return returned_literal(on_swapped) == 1 &&
         past_empty(on_lost) == shape.get_block &&
         past_empty(on_unchanged) == shape.cas_block &&
         returned_literal(on_changed) == 0;
}

// Is `method` d8's `compareAndSet` forwarder? Returns the `compareAndSet` it
// calls, or null.
//
// Matched on what the body does, never on the name, which d8 takes from
// whichever class happened to need the forwarder first. The match establishes
// the two things a rewrite of the call relies on:
//
//   - the call is the operation: one strong `compareAndSet` on the parameters
//     in order, retried while a `get` of the same field still equals `expect`,
//     returning the outcome;
//   - calling it does nothing else: no other effectful instruction, and no
//     class initialization, because replacing `invoke-static Fwd.m` drops the
//     initialization of `Fwd`.
const DexMethodRef* match_backport_cas_forwarder(const DexMethod* method,
                                                 const DexType* updater_type) {
  const auto* cls = type_class(method->get_class());
  if (cls == nullptr || is_interface(cls) || cls->get_clinit() != nullptr ||
      cls->get_super_class() != type::java_lang_Object() ||
      is_synchronized(method) || is_declared_synchronized(method) ||
      method->rstate.no_optimizations() || method->get_code() == nullptr) {
    return nullptr;
  }
  const auto& cfg = method->get_code()->cfg();
  auto shape = find_forwarder_shape(cfg, updater_type);
  if (!shape.has_value() || !has_forwarder_dataflow(cfg, *shape) ||
      !has_forwarder_control_flow(cfg, *shape)) {
    return nullptr;
  }
  return shape->cas->get_method();
}

// Recognizes every forwarder in the program. A method with the forwarder's
// signature that fails the match is counted, because it means d8 changed the
// shape and the pass has quietly stopped reaching those sites.
BackportForwarders find_backport_cas_forwarders(const Scope& scope,
                                                PassManager& mgr) {
  BackportForwarders forwarders;
  size_t rejected = 0;
  auto* updater_type = DexType::get_type(atomic_field_updaters::REFERENCE_DESC);
  const DexProto* proto = nullptr;
  if (updater_type != nullptr) {
    auto* object_type = type::java_lang_Object();
    const auto* args = DexTypeList::get_type_list(
        {updater_type, object_type, object_type, object_type});
    proto =
        args == nullptr ? nullptr : DexProto::get_proto(type::_boolean(), args);
  }
  // No interned proto means no method can have it.
  if (proto != nullptr) {
    InsertOnlyConcurrentMap<const DexMethodRef*, const DexMethodRef*> found;
    rejected = walk::parallel::methods<size_t>(
        scope, [&](DexMethod* method) -> size_t {
          if (!is_static(method) || method->get_proto() != proto ||
              method->get_code() == nullptr) {
            return 0;
          }
          if (const auto* cas =
                  match_backport_cas_forwarder(method, updater_type)) {
            found.emplace(method, cas);
            TRACE(ATOMUP, 2, "compareAndSet forwarder: %s", SHOW(method));
            return 0;
          }
          TRACE(ATOMUP, 2, "forwarder-shaped but not matched: %s",
                SHOW(method));
          return 1;
        });
    insert_unordered_iterable(forwarders, found);
  }
  mgr.set_metric("backport_cas_forwarders_recognized", forwarders.size());
  mgr.set_metric("backport_cas_forwarders_rejected", rejected);
  return forwarders;
}

// Count operation call sites on the updater types, keyed by flavor and
// operation name. Sizes the opportunity independently of how much of it the
// recognition above can actually reach.
//
// `ops_total` keeps counting direct calls only, the two inside each forwarder
// included, so it stays comparable across builds; calls to a forwarder are
// counted on their own.
void census_ops(const Scope& scope,
                const UpdaterOperations& ops,
                PassManager& mgr) {
  const auto& kinds = ops.kinds();
  if (kinds.empty()) {
    // Still report the total. A program with no updaters has zero operations,
    // which is not the same thing as the metric being missing -- absent, it is
    // indistinguishable from the pass not having run at all.
    mgr.set_metric("ops_total", 0);
    mgr.set_metric("ops_backport_cas_calls", 0);
    return;
  }
  // Every method in the program is visited, so this walks in parallel, and the
  // counters are keyed by the method ref -- a pointer hash, with no string
  // built at any call site. `AtomicMap` accumulates them without a lock.
  AtomicMap<const DexMethodRef*, size_t> per_operation;
  std::atomic<size_t> backport_calls{0};
  walk::parallel::code(scope, [&](DexMethod*, IRCode& code) {
    for (const auto& site : ops.sites_in(code.cfg())) {
      if (site.via_backport) {
        backport_calls.fetch_add(1, std::memory_order_relaxed);
      } else if (atomic_field_updaters::is_operation_name(
                     site.api->get_name()->str())) {
        per_operation.fetch_add(site.api, 1);
      }
    }
  });
  // One label per distinct operation rather than per call site, sorted so the
  // trace reads the same way on every run. The proto is part of the label so
  // that overloads stay distinct here too: keying the counters by method ref
  // would buy nothing if the report merged them back together by name.
  //
  // Sorted by the derived label rather than by the container's key, so this is
  // a build-and-sort rather than `unordered_to_ordered`; nothing is summed,
  // because one method ref produces exactly one label.
  size_t total = 0;
  for (auto&& [mref, n] : UnorderedIterable(per_operation)) {
    total += n.load();
  }
  mgr.set_metric("ops_total", total);
  mgr.set_metric("ops_backport_cas_calls", backport_calls.load());

  // Everything below is for the trace and nothing else. The per-operation
  // breakdown is not a metric: which rows exist depends on which operations the
  // program happens to call, so two builds being compared would not have the
  // same set. Metrics are for counters whose cardinality is fixed.
  if (traceEnabled(ATOMUP, 2)) {
    std::vector<std::pair<std::string, size_t>> counts;
    counts.reserve(per_operation.size());
    for (auto&& [mref, n] : UnorderedIterable(per_operation)) {
      auto it = kinds.find(mref->get_class());
      counts.emplace_back(std::string("ops_") + kind_name(it->second) + "_" +
                              mref->get_name()->str_copy() +
                              show(mref->get_proto()),
                          n.load());
    }
    std::sort(counts.begin(), counts.end());
    for (const auto& [name, n] : counts) {
      TRACE(ATOMUP, 2, "%s = %zu", name.c_str(), n);
    }
  }
}

// The members synthesized for lowering: the shared `Unsafe` instance every
// rewritten call site loads from, the holder check called where non-nullness
// could not be proven, and -- only when a planned site calls it -- the
// retrying reference compare-and-set.
struct Helpers {
  DexField* s_unsafe{nullptr};
  DexMethod* check_holder{nullptr};
  DexMethod* cas_object_retry{nullptr};
};

// The JDK symbols the synthesized `<clinit>`s reach for. Interned in one place
// rather than respelled at each use: two spellings of the same descriptor that
// drift apart produce two distinct refs and a dex that fails verification only
// at runtime.
//
// `java.lang.reflect.Field` and `sun.misc.Unsafe` deliberately stay here rather
// than joining `WellKnownTypes`: membership there opts a type into
// `IRTypeChecker`'s assignability checking, which is skipped for external types
// outside the set, and neither is a type this pass wants to claim that for.
DexType* unsafe_type() { return DexType::make_type(UNSAFE_DESC); }

DexType* reflect_field_type() {
  return DexType::make_type("Ljava/lang/reflect/Field;");
}

// Class.getDeclaredField(String) -> Field
DexMethodRef* class_get_declared_field() {
  return DexMethod::make_method(
      type::java_lang_Class(), DexString::make_string("getDeclaredField"),
      DexProto::make_proto(
          reflect_field_type(),
          DexTypeList::make_type_list({type::java_lang_String()})));
}

// Field.setAccessible(boolean) -> void
DexMethodRef* field_set_accessible() {
  return DexMethod::make_method(
      reflect_field_type(), DexString::make_string("setAccessible"),
      DexProto::make_proto(type::_void(),
                           DexTypeList::make_type_list({type::_boolean()})));
}

// Field.get(Object) -> Object
DexMethodRef* field_get_value() {
  return DexMethod::make_method(
      reflect_field_type(), DexString::make_string("get"),
      DexProto::make_proto(
          type::java_lang_Object(),
          DexTypeList::make_type_list({type::java_lang_Object()})));
}

// The helper synthesis emits these Unsafe members rather than a lowering plan,
// so they do not pass through `plan_is_linkable`. Classified here instead, so
// that "every Unsafe member this pass emits is vetted" holds for every emission
// path and not merely the planned ones. Unlike a plan there is no call site to
// decline, so anything but ALLOWED is a programming error rather than a
// refusal.
void assert_synthesis_may_emit(std::string_view member) {
  const auto status = atomic_field_updaters::hidden_api_status(member);
  always_assert_log(
      status.has_value() &&
          *status == atomic_field_updaters::HiddenApiStatus::ALLOWED,
      "sun.misc.Unsafe.%s is not classified as permitted in "
      "atomic_field_updaters::hidden_api_status, but the helper synthesis has "
      "no way to skip it.",
      std::string(member).c_str());
}

// Unsafe.objectFieldOffset(Field) -> long
DexMethodRef* unsafe_object_field_offset() {
  assert_synthesis_may_emit("objectFieldOffset");
  return DexMethod::make_method(
      unsafe_type(), DexString::make_string("objectFieldOffset"),
      DexProto::make_proto(
          type::_long(), DexTypeList::make_type_list({reflect_field_type()})));
}

// Unsafe.compareAndSwapObject(Object, long, Object, Object) -> boolean
DexMethodRef* unsafe_compare_and_swap_object() {
  assert_synthesis_may_emit("compareAndSwapObject");
  auto* object_type = type::java_lang_Object();
  return DexMethod::make_method(
      unsafe_type(), DexString::make_string("compareAndSwapObject"),
      DexProto::make_proto(
          type::_boolean(),
          DexTypeList::make_type_list(
              {object_type, type::_long(), object_type, object_type})));
}

// Unsafe.getObjectVolatile(Object, long) -> Object
DexMethodRef* unsafe_get_object_volatile() {
  assert_synthesis_may_emit("getObjectVolatile");
  auto* object_type = type::java_lang_Object();
  return DexMethod::make_method(
      unsafe_type(), DexString::make_string("getObjectVolatile"),
      DexProto::make_proto(object_type, DexTypeList::make_type_list(
                                            {object_type, type::_long()})));
}

// `static boolean compareAndSwapObjectRetrying(Object o, long offset,
// Object expect, Object update)`, which a strong reference compare-and-set
// lowers to below `kReferenceCasReliableMinSdk`:
//
//   loop:
//     if (sUnsafe.compareAndSwapObject(o, offset, expect, update)) return true;
//     if (sUnsafe.getObjectVolatile(o, offset) == expect) goto loop;
//     return false;
//
// The retry d8 puts around `AtomicReferenceFieldUpdater.compareAndSet`, and R8
// around `Unsafe.compareAndSwapObject`, for b/211646483. One shared method
// rather than a loop at every site, as both of them do. Built on the CFG
// because `MethodCreator` cannot express a back edge.
DexMethod* synthesize_cas_object_retry(DexType* synth_type,
                                       DexField* s_unsafe) {
  auto* object_type = type::java_lang_Object();
  auto* method =
      DexMethod::make_method(
          synth_type,
          DexString::make_string(atomic_field_updaters::CAS_RETRY_METHOD_NAME),
          DexProto::make_proto(
              type::_boolean(),
              DexTypeList::make_type_list(
                  {object_type, type::_long(), object_type, object_type})))
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  // The parameters load into v0 (o), v1:v2 (offset), v3 (expect), v4 (update).
  method->set_code(std::make_unique<IRCode>(method, 0));
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  auto* entry = cfg.entry_block();
  auto* loop = cfg.create_block();
  auto* swapped = cfg.create_block();
  auto* recheck = cfg.create_block();
  auto* lost = cfg.create_block();

  entry->push_back({dasm(OPCODE_SGET_OBJECT, s_unsafe),
                    dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {5_v})});
  cfg.add_edge(entry, loop, cfg::EDGE_GOTO);

  loop->push_back({dasm(OPCODE_INVOKE_VIRTUAL, unsafe_compare_and_swap_object(),
                        {5_v, 0_v, 1_v, 3_v, 4_v}),
                   dasm(OPCODE_MOVE_RESULT, {6_v})});
  cfg.create_branch(loop, dasm(OPCODE_IF_EQZ, {6_v}), swapped, recheck);

  swapped->push_back(
      {dasm(OPCODE_CONST, {7_v, 1_L}), dasm(OPCODE_RETURN, {7_v})});

  recheck->push_back({dasm(OPCODE_INVOKE_VIRTUAL, unsafe_get_object_volatile(),
                           {5_v, 0_v, 1_v}),
                      dasm(OPCODE_MOVE_RESULT_OBJECT, {8_v})});
  cfg.create_branch(recheck, dasm(OPCODE_IF_EQ, {8_v, 3_v}), lost, loop);

  lost->push_back({dasm(OPCODE_CONST, {7_v, 0_L}), dasm(OPCODE_RETURN, {7_v})});
  cfg.recompute_registers_size();

  method->set_deobfuscated_name(show(method));
  method->rstate.set_generated();
  return method;
}

// Synthesizes the class holding the shared `Unsafe` instance,
// obtained reflectively in its <clinit>. The per-field offsets deliberately do
// not live here -- see add_offsets_to_holders.
//
// `with_cas_retry` adds `synthesize_cas_object_retry`'s method.
Helpers synthesize_unsafe_holder(DexStoresVector& stores, bool with_cas_retry) {
  auto* synth_type = DexType::make_type(SYNTH_HOLDER_DESC);
  auto* object_type = type::java_lang_Object();

  ClassCreator cc(synth_type);
  cc.set_super(object_type);
  cc.set_access(ACC_PUBLIC | ACC_FINAL);

  auto* s_unsafe =
      DexField::make_field(synth_type, DexString::make_string("sUnsafe"),
                           unsafe_type())
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
  // Synthesized members start with an empty deobfuscated name; once they
  // survive to the end (i.e. once call sites actually use them) the final
  // duplicate-deobfuscated-name check rejects the second one.
  s_unsafe->set_deobfuscated_name(show(s_unsafe));
  s_unsafe->rstate.set_generated();
  cc.add_field(s_unsafe);

  auto* get_declared_field = class_get_declared_field();
  auto* set_accessible = field_set_accessible();
  auto* field_get = field_get_value();

  MethodCreator mc(
      synth_type, DexString::make_string("<clinit>"),
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})),
      ACC_STATIC | ACC_CONSTRUCTOR);
  auto* mb = mc.get_main_block();

  // sUnsafe = (Unsafe) Unsafe.class.getDeclaredField("theUnsafe").get(null);
  // with setAccessible(true) in between.
  auto cls_loc = mc.make_local(type::java_lang_Class());
  mb->load_const(cls_loc, unsafe_type());
  auto name_loc = mc.make_local(type::java_lang_String());
  mb->load_const(name_loc, DexString::make_string("theUnsafe"));
  auto field_loc = mc.make_local(reflect_field_type());
  mb->invoke(OPCODE_INVOKE_VIRTUAL, get_declared_field, {cls_loc, name_loc});
  mb->move_result(field_loc, reflect_field_type());
  auto true_loc = mc.make_local(type::_boolean());
  mb->load_const(true_loc, (int32_t)1);
  mb->invoke(OPCODE_INVOKE_VIRTUAL, set_accessible, {field_loc, true_loc});
  auto null_loc = mc.make_local(object_type);
  mb->load_null(null_loc);
  auto obj_loc = mc.make_local(object_type);
  mb->invoke(OPCODE_INVOKE_VIRTUAL, field_get, {field_loc, null_loc});
  mb->move_result(obj_loc, object_type);
  mb->check_cast(obj_loc, unsafe_type());
  mb->sput(s_unsafe, obj_loc);

  mb->ret_void();

  auto* clinit = mc.create();
  clinit->set_deobfuscated_name(show(clinit));
  clinit->rstate.set_generated();
  cc.add_method(clinit);

  // `static void checkHolder(Object o) { if (o == null) throw new
  // ClassCastException(); }`
  //
  // AtomicReferenceFieldUpdater.accessCheck throws ClassCastException for a
  // null holder -- `cclass.isInstance(null)` is false -- so that, not NPE, is
  // the behaviour to preserve. Emitting this as a call keeps the rewrite
  // straight-line; the inliner flattens it into the branch later.
  auto* cce_type = DexType::make_type("Ljava/lang/ClassCastException;");
  auto* cce_init = DexMethod::make_method(
      cce_type, DexString::make_string("<init>"),
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})));
  MethodCreator cm(
      synth_type, DexString::make_string("checkHolder"),
      DexProto::make_proto(type::_void(),
                           DexTypeList::make_type_list({object_type})),
      ACC_PUBLIC | ACC_STATIC);
  auto holder_loc = cm.get_local(0);
  auto* cb = cm.get_main_block();
  // if_testz returns the block taken when the condition fails, so testing
  // "holder != null" hands back the null path.
  auto* null_block = cb->if_testz(OPCODE_IF_NEZ, holder_loc);
  auto ex_loc = cm.make_local(cce_type);
  null_block->new_instance(cce_type, ex_loc);
  null_block->invoke(OPCODE_INVOKE_DIRECT, cce_init, {ex_loc});
  null_block->throwex(ex_loc);
  cb->ret_void();
  auto* check_holder = cm.create();
  check_holder->set_deobfuscated_name(show(check_holder));
  check_holder->rstate.set_generated();
  check_holder->get_code()->build_cfg();
  cc.add_method(check_holder);

  DexMethod* cas_object_retry = nullptr;
  if (with_cas_retry) {
    cas_object_retry = synthesize_cas_object_retry(synth_type, s_unsafe);
    cc.add_method(cas_object_retry);
  }

  auto* cls = cc.create();
  cls->set_deobfuscated_name(show(cls));
  // Nothing here has a source counterpart: no stable name to preserve, and no
  // place in coldstart tracking. Saying so keeps it out of class merging's
  // models and out of original-name recording.
  cls->rstate.set_generated();
  // cfg-friendly contract: every method with code must leave with a built CFG.
  clinit->get_code()->build_cfg();

  redex_assert(!stores.empty());
  auto& dexen = stores.at(0).get_dexen();
  redex_assert(!dexen.empty());
  dexen.at(0).push_back(cls);
  return Helpers{s_unsafe, check_holder, cas_object_retry};
}

// Give each recognized updater a `static final long` offset *in its own holder
// class*, initialized at the top of that class's own <clinit>.
//
// The offset cannot live in a shared synthetic class. Computing it needs
// `Holder.class.getDeclaredField(name)`, and a holder is frequently not public
// -- `kotlinx.coroutines` internals, and any nested class -- so a `const-class`
// from another package throws IllegalAccessError when the shared class
// initializes, taking every later use down with NoClassDefFoundError. Emitting
// the lookup inside the holder sidesteps access control entirely: a class may
// always reflect over itself.
//
// It is also better placed. The work is exactly what `newUpdater` already did,
// so it now happens when that class initializes, rather than dragging every
// holder in the program into the initializer of whichever one ran first.
void add_offsets_to_holders(std::vector<UpdaterInfo>& updaters,
                            DexField* s_unsafe,
                            PassManager& mgr) {
  auto* long_type = type::_long();
  auto* get_declared_field = class_get_declared_field();
  auto* object_field_offset = unsafe_object_field_offset();

  size_t added = 0;
  for (auto& info : updaters) {
    auto* holder_cls = type_class(info.holder);
    if (holder_cls == nullptr) {
      continue;
    }
    auto* clinit = holder_cls->get_clinit();
    // Recognition required the updater to be initialized in the holder's
    // <clinit>, so one exists with code.
    if (clinit == nullptr || clinit->get_code() == nullptr) {
      continue;
    }

    // Prepend, rather than append: the computation depends on nothing else in
    // the <clinit>, and the entry block is the one point guaranteed to run
    // before any other statement regardless of the method's control flow.
    auto& cfg = clinit->get_code()->cfg();

    // Anchor on the first real instruction: a block can open with a position
    // or source-block entry, which is not a valid instruction iterator.
    //
    // Settled before the field is created, so that the field and its
    // initializer stand or fall together. A field added without one would read
    // 0, and lowering -- which only checks that the field exists -- would then
    // address the object header instead of the intended field.
    auto* entry = cfg.entry_block();
    auto first = entry->get_first_insn();
    if (first == entry->end()) {
      continue;
    }

    auto* offset = DexField::make_field(
                       info.holder,
                       DexString::make_string(info.updater->str() + "$offset"),
                       long_type)
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    offset->set_deobfuscated_name(show(offset));
    offset->rstate.set_generated();
    holder_cls->add_field(offset);
    info.offset_field = offset;

    reg_t u_reg = cfg.allocate_temp();
    reg_t cls_reg = cfg.allocate_temp();
    reg_t name_reg = cfg.allocate_temp();
    reg_t field_reg = cfg.allocate_temp();
    reg_t off_reg = cfg.allocate_wide_temp();

    std::vector<IRInstruction*> init{
        dasm(OPCODE_SGET_OBJECT, s_unsafe),
        dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {{VREG, u_reg}}),
        dasm(OPCODE_CONST_CLASS, info.holder),
        dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {{VREG, cls_reg}}),
        dasm(OPCODE_CONST_STRING, info.field_name),
        dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {{VREG, name_reg}}),
        dasm(OPCODE_INVOKE_VIRTUAL, get_declared_field,
             {{VREG, cls_reg}, {VREG, name_reg}}),
        dasm(OPCODE_MOVE_RESULT_OBJECT, {{VREG, field_reg}}),
        dasm(OPCODE_INVOKE_VIRTUAL, object_field_offset,
             {{VREG, u_reg}, {VREG, field_reg}}),
        dasm(OPCODE_MOVE_RESULT_WIDE, {{VREG, off_reg}}),
        dasm(OPCODE_SPUT_WIDE, offset, {{VREG, off_reg}}),
    };

    cfg::CFGMutation mutation(cfg);
    mutation.insert_before(entry->to_cfg_instruction_iterator(first), init);
    mutation.flush();
    added++;
  }
  mgr.set_metric("offset_fields_added", added);
}

// Kotlin emits the `$FU` field as private and reads it through a
// synthetic static getter (`get_state$volatile$FU()`), with an
// `access$getOwner$volatile$FU()` bridge on top for nested-class use. So at a
// call site the updater receiver is defined by an invoke-static, not by a bare
// sget-object.
//
// Those calls are found by following the receiver rather than by searching for
// them: the use-def walk that resolution already performs lands on the accessor
// by construction, so there is no shape to guess at and nothing to decide about
// which methods are worth considering.

// Is `m` an accessor for a recognized updater? On success `chain` gets every
// method on the path, which is what has to be inlined: flattening a bridge
// alone would leave the getter it calls still standing between the call site
// and the field.
//
// The pattern is small and fixed. A method reads one recognized updater field
// and hands it back, or hands back what one other such method returns. A
// second read, a second call, or any other instruction is not this pattern, so
// bail and leave the call site unresolved. Having exactly one source is also
// what makes the chain a simple path, walked with a loop.
//
// Every step stays on the accessor's own class -- the field it reads and the
// method it delegates to are both declared there. That is not a coincidence to
// be exploited but the JVM's rule for synthetic accessors, which are emitted in
// the class owning the private member they reach. Requiring it is what makes
// the body free of observable effect in the strict sense: the only <clinit> a
// permitted instruction can trigger is the accessor's own class's, and calling
// the accessor already triggered that.
//
// Two properties fall out of that whitelist rather than being tested for.
// Nothing else in it can produce an object value, so whatever `return-object`
// hands back must be the field that was read or the result of the delegate --
// there is no second value for it to return. And a method taking arguments has
// `load-param` instructions, which the whitelist does not admit, so it bails;
// being static is guaranteed by arriving here from an `invoke-static`.
//
// Not a safety condition -- inlining preserves semantics whatever the body
// does, class initialization included -- but scope discipline: "log, then
// return NEXT" would be copied into every caller for no reason.
bool is_accessor_chain(
    DexMethod* m,
    const UnorderedMap<DexField*, const UpdaterInfo*>& by_field,
    UnorderedSet<DexMethod*>* chain) {
  UnorderedSet<DexMethod*> walked;
  while (m != nullptr && m->get_code() != nullptr &&
         !m->rstate.no_optimizations() && walked.insert(m).second) {
    DexField* field = nullptr;
    DexMethod* delegate = nullptr;
    for (auto& mie : cfg::InstructionIterable(m->get_code()->cfg())) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (opcode::is_sget_object(op) && field == nullptr &&
          delegate == nullptr && insn->get_field()->is_def()) {
        field = insn->get_field()->as_def();
      } else if (opcode::is_invoke_static(op) && field == nullptr &&
                 delegate == nullptr) {
        delegate = resolve_method(insn->get_method(), MethodSearch::Static);
      } else if (!opcode::is_move_result_pseudo_object(op) &&
                 !opcode::is_move_result_object(op) &&
                 !opcode::is_move_object(op) && !opcode::is_return_object(op)) {
        return false;
      }
    }
    if (delegate != nullptr) {
      if (delegate->get_class() != m->get_class()) {
        return false;
      }
      m = delegate;
      continue;
    }
    if (field == nullptr || field->get_class() != m->get_class() ||
        by_field.count(field) == 0u) {
      return false;
    }
    insert_unordered_iterable(*chain, walked);
    return true;
  }
  return false;
}

// The accessors standing between an operation and its updater field.
//
// Driven by the call sites rather than by a scan of the program: every
// operation's receiver is walked back through `MoveAwareChains`, and a receiver
// defined by an invoke-static names the accessor directly. So relevance is not
// judged, it is where the walk arrived, and a bridge is reached by following
// the chain rather than by iterating selection to a fixed point.
UnorderedSet<DexMethod*> find_receiver_chain_accessors(
    const Scope& scope,
    const UpdaterOperations& ops,
    const UnorderedMap<DexField*, const UpdaterInfo*>& by_field,
    PassManager& mgr) {
  InsertOnlyConcurrentSet<DexMethod*> selected;
  // Callees a receiver came from that could not be followed. Recorded per
  // method rather than per call site, so a body reached from twenty sites
  // counts once.
  InsertOnlyConcurrentSet<DexMethod*> rejected;

  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr || method->rstate.no_optimizations() ||
        ops.is_forwarder(method)) {
      return;
    }
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    const auto sites = ops.sites_in(cfg);
    if (sites.empty()) {
      return;
    }
    live_range::MoveAwareChains chains(cfg);
    auto use_defs = chains.get_use_def_chains();

    for (const auto& site : sites) {
      auto* insn = site.insn;
      auto it = use_defs.find(live_range::Use{insn, 0});
      if (it == use_defs.end()) {
        continue;
      }
      for (auto* def : it->second) {
        // An sget-object receiver already resolves; anything that is not a
        // call is not something inlining could help with.
        if (!opcode::is_invoke_static(def->opcode())) {
          continue;
        }
        auto* callee = resolve_method(def->get_method(), MethodSearch::Static);
        UnorderedSet<DexMethod*> chain;
        if (is_accessor_chain(callee, by_field, &chain)) {
          for (auto* on_chain : UnorderedIterable(chain)) {
            selected.insert(on_chain);
          }
        } else if (callee != nullptr) {
          rejected.insert(callee);
          TRACE(ATOMUP, 3, "receiver of %s comes from %s, which is not a chain",
                SHOW(insn), SHOW(callee));
        }
      }
    }
  });

  UnorderedSet<DexMethod*> result;
  insert_unordered_iterable(result, selected);
  mgr.set_metric("accessors_rejected_impure", rejected.size());
  return result;
}

// Inline the selected accessors so the updater reaches its call sites as a
// plain sget-object. Uses the shared inliner rather than splicing by hand: it
// already models init-class side effects, which matters because a bridge in one
// class delegating to a getter in another would otherwise silently drop the
// bridge class's static initializer.
void inline_updater_accessors(DexStoresVector& stores,
                              Scope& scope,
                              ConfigFiles& conf,
                              PassManager& mgr,
                              const UnorderedSet<DexMethod*>& candidates) {
  mgr.set_metric("accessors_selected", candidates.size());
  if (candidates.empty()) {
    // Record it anyway: a metric that vanishes when the count is zero is
    // indistinguishable from the pass not having run.
    mgr.set_metric("accessors_inlined", 0);
    mgr.set_metric("accessors_deleted", 0);
    return;
  }
  auto method_override_graph = method_override_graph::build_graph(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns(), method_override_graph.get());
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;
  auto inliner_config =
      *conf.get_global_config().get_config_by_name<InlinerConfig>("inliner");
  // The global config has `shrink_other_methods` on, which schedules *every*
  // method in the scope for shrinking, not just the ones inlined into. That is
  // right for MethodInlinePass and wrong here: it would run a whole-app shrink
  // as a side effect of inlining 65 accessors, duplicating ShrinkerPass a few
  // passes ahead of it, and leave this pass's size effect unmeasurable because
  // the delta would be dominated by work that has nothing to do with atomics.
  // Callers we inline into are still shrunk.
  inliner_config.shrink_other_methods = false;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config,
      mgr.get_redex_options().min_sdk, MultiMethodInlinerMode::InterDex);
  inliner.inline_methods();
  auto inlined_methods = inliner.get_inlined();
  auto inlined = inlined_methods.size();
  mgr.set_metric("accessors_inlined", inlined);

  // Inlining copies a body; it does not remove the original. The leftover still
  // reads the updater, so the reference count cleanup relies on never reaches
  // zero and every holder keeps its field. Deleting the accessors is what makes
  // cleanup possible at all on Kotlin code.
  //
  // MethodInliner has to withhold true virtuals here, because a monomorphic
  // callsite it inlined can still resolve elsewhere at runtime. Every accessor
  // we select is reached through invoke-static and resolved with
  // MethodSearch::Static, so that case cannot arise. `delete_methods` still
  // checks each candidate for remaining callers, annotation references and keep
  // rules, so a partially inlined accessor survives.
  auto deleted = delete_methods(scope, inlined_methods,
                                std::ref(concurrent_method_resolver));
  mgr.set_metric("accessors_deleted", deleted.size());

  TRACE(ATOMUP, 1,
        "SUMMARY accessors selected=%zu inlined=%zu deleted=%zu "
        "(rejected_impure counted separately)",
        candidates.size(), inlined, deleted.size());
}

// How one updater operation lowers to sun.misc.Unsafe.
//
// `value_srcs` are taken from the original call site, after the holder.
// `literal` supplies a constant value argument instead (getAndIncrement is
// getAndAdd(+1)). `add_result` means Unsafe returns the *old* value and the
// updater's contract wants the new one, so the addend is applied afterwards.
struct UnsafePlan {
  // The flavor the operation belongs to. Carried here rather than passed
  // alongside, since every use of a plan needs it: it picks the Unsafe method
  // name, the value type, and whether the value is wide.
  Kind kind;
  // sun.misc.Unsafe method name, with `%s` standing in for the flavor suffix
  // that `unsafe_ref` substitutes: getObjectVolatile / getIntVolatile / ...
  const char* name;
  int value_srcs{0};
  std::optional<int64_t> literal;
  bool add_result{false};
  bool needs_api24{false}; // getAndAdd*/getAndSet* arrived in Android N
  // Emit a call to the synthesized retrying compare-and-set instead of the raw
  // primitive.
  bool retry_spurious_failure{false};
};

// Suffix of the Unsafe method name for a flavor: getObjectVolatile /
// getIntVolatile / getLongVolatile.
const char* unsafe_suffix(Kind kind) {
  switch (kind) {
  case Kind::REFERENCE:
    return "Object";
  case Kind::INTEGER:
    return "Int";
  case Kind::LONG:
    return "Long";
  }
  not_reached();
}

// The plan for an updater method, or nullopt if this pass does not lower it.
//
// Keyed by name rather than by argument shape: for the reference flavor the
// value type is `Object`, so a shape test could not tell `set(T, V)` from
// `equals(Object)`. The functional forms have no plan: their trailing argument
// is an operator, so the value written is only known at runtime.
std::optional<UnsafePlan> plan_for(Kind kind,
                                   std::string_view op,
                                   int min_sdk) {
  const bool numeric = kind != Kind::REFERENCE;
  if (op == "get") {
    return UnsafePlan{kind, "get%sVolatile", 0, std::nullopt, false, false};
  }
  if (op == "set") {
    return UnsafePlan{kind, "put%sVolatile", 1, std::nullopt, false, false};
  }
  if (op == "lazySet") {
    return UnsafePlan{kind, "putOrdered%s", 1, std::nullopt, false, false};
  }
  if (op == "compareAndSet" || op == "weakCompareAndSet") {
    // libcore implements the weak form identically to the strong one, so both
    // map to the same primitive. The weak form may fail spuriously by
    // contract; the strong one may not, so where a reference CAS can, it goes
    // through the retry helper instead. See `kReferenceCasReliableMinSdk`.
    UnsafePlan plan{kind, "compareAndSwap%s", 2, std::nullopt, false, false};
    plan.retry_spurious_failure =
        kind == Kind::REFERENCE && op == "compareAndSet" &&
        min_sdk < atomic_field_updaters::kReferenceCasReliableMinSdk;
    return plan;
  }
  if (op == "getAndSet") {
    return UnsafePlan{kind, "getAndSet%s", 1, std::nullopt, false, true};
  }
  if (!numeric) {
    return std::nullopt;
  }
  if (op == "getAndAdd") {
    return UnsafePlan{kind, "getAndAdd%s", 1, std::nullopt, false, true};
  }
  if (op == "getAndIncrement") {
    return UnsafePlan{kind, "getAndAdd%s", 0, 1, false, true};
  }
  if (op == "getAndDecrement") {
    return UnsafePlan{kind, "getAndAdd%s", 0, -1, false, true};
  }
  if (op == "addAndGet") {
    return UnsafePlan{kind, "getAndAdd%s", 1, std::nullopt, true, true};
  }
  if (op == "incrementAndGet") {
    return UnsafePlan{kind, "getAndAdd%s", 0, 1, true, true};
  }
  if (op == "decrementAndGet") {
    return UnsafePlan{kind, "getAndAdd%s", 0, -1, true, true};
  }
  return std::nullopt;
}

// Resolve a plan's name template against its flavor: getAndAdd%s ->
// getAndAddInt.
std::string unsafe_member_name(const UnsafePlan& plan) {
  std::string n{plan.name};
  auto at = n.find("%s");
  always_assert_log(at != std::string::npos,
                    "Unsafe method template %s has no flavor placeholder",
                    plan.name);
  n.replace(at, 2, unsafe_suffix(plan.kind));
  return n;
}

// Whether Android permits app code to link what this plan would emit.
//
// An unclassified member is a programming error rather than a refusal: someone
// has taught the pass to emit something nobody checked, and silently declining
// to lower it would hide that until the same question is asked again the hard
// way.
bool plan_is_linkable(const UnsafePlan& plan) {
  const auto member = unsafe_member_name(plan);
  auto status = atomic_field_updaters::hidden_api_status(member);
  always_assert_log(
      status.has_value(),
      "sun.misc.Unsafe.%s has no hidden-API classification. Look it up in "
      "fbandroid/apps/oxygen/testing/veridex/hiddenapi-flags.csv and record it "
      "in atomic_field_updaters::hidden_api_status before emitting it.",
      member.c_str());
  return *status == atomic_field_updaters::HiddenApiStatus::ALLOWED;
}

// Resolve a plan's name template and build the Unsafe method reference.
DexMethodRef* unsafe_ref(const UnsafePlan& plan) {
  std::string n = unsafe_member_name(plan);
  auto* object_type = type::java_lang_Object();
  auto* long_type = type::_long();
  auto* vtype = atomic_field_updaters::value_type(plan.kind);

  DexType* rtype;
  if (n.rfind("put", 0) == 0) {
    rtype = type::_void();
  } else if (n.rfind("compareAndSwap", 0) == 0) {
    rtype = type::_boolean();
  } else {
    rtype = vtype;
  }
  // (receiver-object, offset) followed by however many value arguments the
  // plan supplies, whether from the call site or as a literal.
  DexTypeList::ContainerType args{object_type, long_type};
  const int n_values = plan.value_srcs + (plan.literal.has_value() ? 1 : 0);
  for (int i = 0; i < n_values; ++i) {
    args.push_back(vtype);
  }
  return DexMethod::make_method(
      unsafe_type(), DexString::make_string(n),
      DexProto::make_proto(rtype,
                           DexTypeList::make_type_list(std::move(args))));
}

// Build a static-field load (sget + pseudo) into `dst`.
void emit_sget(std::vector<IRInstruction*>* out,
               IROpcode sget_op,
               IROpcode pseudo_op,
               DexField* field,
               reg_t dst) {
  out->push_back(dasm(sget_op, field));
  out->push_back(dasm(pseudo_op, {{VREG, dst}}));
}

// Every updater operation call site is measured against the obligations that
// lowering it to `sun.misc.Unsafe` must discharge. Sites that discharge all of
// them are rewritten; the rest are counted and left alone.
//
// Three obligations, all required:
//   1. the receiver resolves to a known updater field -- without one there is
//      no offset to substitute;
//   2. the holder is a subtype of the updater's declaring class, and non-null;
//   3. for reference operations that write a value, the value is a subtype of
//      the field type.
//
// Obligation 2 is not pedantry. `accessCheck` throws ClassCastException for a
// null or wrong-typed holder, whereas `Unsafe` would perform a raw memory
// access at that address -- undefined behaviour rather than an exception. The
// checks may only be dropped once they are proven redundant.
//
// Nullness is tracked separately from the type test, because a site blocked
// only on nullness remains reachable by emitting a runtime check; counting it
// as blocked would understate the opportunity.

// Does every argument after the holder carry a value of the flavor's type?
// True for the operations this pass models (`get`, `set`, `compareAndSet` and
// friends); false for the functional-style ones, whose trailing argument is a
// `UnaryOperator`/`BinaryOperator` rather than a value.
bool writes_only_values(const DexMethodRef* mref, Kind kind) {
  const auto* value_type = atomic_field_updaters::value_type(kind);
  const auto* args = mref->get_proto()->get_args();
  bool holder = true;
  for (const auto* arg : *args) {
    if (holder) {
      holder = false;
      continue;
    }
    if (arg != value_type) {
      return false;
    }
  }
  return true;
}

// A site the analysis found lowerable, and what emission needs to rewrite it.
// Recorded by the parallel phase, consumed by the serial one; nothing here
// refers to a CFG iterator, which would not outlive the walk.
struct Rewrite {
  IRInstruction* insn;
  const UpdaterInfo* info;
  UnsafePlan plan;
  // The holder could not be proven non-null, so emission precedes the rewrite
  // with a check that throws what `accessCheck` would have.
  bool needs_guard;
  // The site was a call to d8's `compareAndSet` forwarder.
  bool via_backport;
};

// Filled from many threads, read from one. Keyed by method, so the serial
// phase can visit methods in scope order rather than in completion order.
using RewritePlan = InsertOnlyConcurrentMap<DexMethod*, std::vector<Rewrite>>;

// Counted per thread and summed after the walk. The analysis visits every
// instruction in the program -- the check for "does this method touch an
// updater at all" cannot be answered more cheaply -- so it runs in parallel,
// and shared counters would need synchronising on the hot path.
struct Stats {
  // Sites passing every obligation, keyed by the operation's method ref and
  // whether the holder was proven non-null. A pointer and a flag: no string
  // is built on the hot path, and overloads stay distinct.
  std::map<std::pair<const DexMethodRef*, bool>, size_t> feasible;
  size_t skipped_unresolved{0};
  size_t skipped_unproven{0};
  size_t blocked_holder_type{0};
  size_t blocked_value_type{0};
  size_t blocked_unmodeled_op{0};
  size_t blocked_min_sdk{0};
  size_t blocked_hidden_api{0};
  // Breakdown of why resolution failed, to tell a fixable receiver pattern
  // apart from a fundamentally untrackable one.
  size_t no_defs{0};
  size_t def_not_sget{0};
  size_t field_not_def{0};
  size_t field_unknown{0};
  size_t conflicting_defs{0};

  Stats& operator+=(const Stats& that) {
    for (const auto& [key, n] : that.feasible) {
      feasible[key] += n;
    }
    skipped_unresolved += that.skipped_unresolved;
    skipped_unproven += that.skipped_unproven;
    blocked_holder_type += that.blocked_holder_type;
    blocked_value_type += that.blocked_value_type;
    blocked_unmodeled_op += that.blocked_unmodeled_op;
    blocked_min_sdk += that.blocked_min_sdk;
    blocked_hidden_api += that.blocked_hidden_api;
    no_defs += that.no_defs;
    def_not_sget += that.def_not_sget;
    field_not_def += that.field_not_def;
    field_unknown += that.field_unknown;
    conflicting_defs += that.conflicting_defs;
    return *this;
  }
};

// What judging a call site needs from the method containing it, built once per
// method and queried at each site.
struct MethodAnalysis {
  DexMethod* method;
  const UnorderedMap<DexField*, const UpdaterInfo*>& by_field;
  const UnorderedMap<const IRInstruction*, type_inference::TypeEnvironment>&
      envs;
  const live_range::UseDefChains& use_defs;
  // The load-param defining `this`, or null in a static method. An instance
  // method's receiver is non-null on entry -- the invoke that got us here would
  // already have thrown otherwise -- but TypeInference does not encode that.
  IRInstruction* receiver_insn;
  // Run-wide, but read where an operation is judged: some Unsafe methods do
  // not exist on every platform the app targets.
  int min_sdk;
};

// The updater behind a call's receiver, or null if the receiver does not
// resolve to exactly one recognized updater.
const UpdaterInfo* resolve_updater(IRInstruction* insn,
                                   const MethodAnalysis& ma,
                                   Stats* stats) {
  auto it = ma.use_defs.find(live_range::Use{insn, 0});
  if (it == ma.use_defs.end() || it->second.empty()) {
    stats->skipped_unresolved++;
    stats->no_defs++;
    return nullptr;
  }
  const UpdaterInfo* info = nullptr;
  for (auto* def : it->second) {
    const UpdaterInfo* cand = nullptr;
    DexField* fdef = nullptr;
    if (opcode::is_sget_object(def->opcode())) {
      if (def->get_field()->is_def()) {
        fdef = def->get_field()->as_def();
      } else {
        stats->field_not_def++;
      }
    } else {
      stats->def_not_sget++;
      TRACE(ATOMUP, 4, "unresolved (def not sget-object): def=[%s] in %s",
            SHOW(def), SHOW(ma.method));
    }
    if (fdef != nullptr) {
      auto fit = ma.by_field.find(fdef);
      if (fit != ma.by_field.end()) {
        cand = fit->second;
      } else {
        stats->field_unknown++;
      }
    }
    if (cand == nullptr || (info != nullptr && info != cand)) {
      if (cand != nullptr) {
        stats->conflicting_defs++;
      }
      stats->skipped_unresolved++;
      return nullptr;
    }
    info = cand;
  }
  return info;
}

bool holder_is_non_null(IRInstruction* insn,
                        bool ti_not_null,
                        const MethodAnalysis& ma) {
  if (ti_not_null) {
    return true;
  }
  if (ma.receiver_insn == nullptr) {
    return false;
  }
  auto it = ma.use_defs.find(live_range::Use{insn, 1});
  if (it == ma.use_defs.end() || it->second.empty()) {
    return false;
  }
  for (auto* def : it->second) {
    if (def != ma.receiver_insn) {
      return false;
    }
  }
  return true;
}

// Judges one updater call against the obligations `Atomic*FieldUpdater`
// discharges at runtime, recording why it was turned away. Returns nothing for
// a site that is not rewritten -- which includes feasible sites whose operation
// this pass cannot yet express.
std::optional<Rewrite> classify_site(const OperationSite& site,
                                     const MethodAnalysis& ma,
                                     Stats* stats) {
  always_assert(stats != nullptr);
  IRInstruction* insn = site.insn;
  const Kind kind = site.kind;
  const auto* name = site.api->get_name();

  // Every argument after the holder must be a value of the flavor's type.
  // The functional-style operations -- getAndUpdate, updateAndGet,
  // getAndAccumulate, accumulateAndGet -- take a UnaryOperator or
  // BinaryOperator there instead, and compute the written value at runtime.
  // Their valueCheck cannot be discharged statically, so they are not
  // modeled at all rather than being judged against a value obligation
  // that does not describe them.
  //
  // Arity is checked alongside the name, not implied by it. The plan table
  // says which operations the pass models; it does not say that *this*
  // invoke has the API's signature. A method named `get` taking no holder
  // is not `get(T)`, and reading a holder out of it would index a source
  // that is not there.
  auto plan = plan_for(kind, name->str(), ma.min_sdk);
  if (!plan.has_value() || insn->srcs_size() < 2 ||
      !writes_only_values(site.api, kind)) {
    stats->blocked_unmodeled_op++;
    return std::nullopt;
  }
  // Whether the platform provides the Unsafe method: getAndAdd*/getAndSet*
  // only exist on sun.misc.Unsafe from Android N. Checked below, after the
  // obligations, so the buckets stay disjoint.
  const bool platform_supports = !plan->needs_api24 || ma.min_sdk >= 24;

  const UpdaterInfo* info = resolve_updater(insn, ma, stats);
  if (info == nullptr) {
    return std::nullopt;
  }
  auto eit = ma.envs.find(insn);
  if (eit == ma.envs.end()) {
    stats->skipped_unproven++;
    return std::nullopt;
  }
  const auto& env = eit->second;

  // Guaranteed by the arity check in the gate above. Stated again here
  // because that guarantee sits twenty lines from the use depending on it,
  // and because reading a holder out of an invoke that has none is the
  // specific way this analysis has gone wrong before. `IRInstruction::src`
  // asserts in release regardless, so this costs nothing.
  redex_assert(insn->srcs_size() >= 2);
  auto holder_dom = env.get_type_domain(insn->src(1));
  auto holder_type = holder_dom.get_dex_type();
  if (!holder_type || !type::check_cast(*holder_type, info->holder)) {
    stats->blocked_holder_type++;
    stats->skipped_unproven++;
    return std::nullopt;
  }
  const bool holder_null_proven =
      holder_is_non_null(insn, holder_dom.is_not_null(), ma);

  // Only the reference flavor performs a valueCheck; an int or long value
  // needs no type test. Among the modeled operations the written value is
  // always the last argument -- `compareAndSet(obj, expect, update)`
  // valueChecks `update` only -- and the check above has already excluded
  // the operations whose last argument is not a value at all.
  if (atomic_field_updaters::has_value_check(kind) && insn->srcs_size() > 2) {
    reg_t value_reg = insn->src(insn->srcs_size() - 1);
    auto value_dom = env.get_type_domain(value_reg);
    auto value_type = value_dom.get_dex_type();
    // An Object-typed field admits every reference: `valueCheck` is
    // `v != null && !vclass.isInstance(v)`, and `Object.isInstance` is true
    // of anything non-null. Worth special-casing because `check_cast` needs
    // a loaded DexClass to walk the hierarchy and returns false without
    // one -- so a value of any framework type, `String` included, would
    // otherwise be blocked.
    bool ok = value_dom.is_null() ||
              info->field_type == type::java_lang_Object() ||
              (value_type.has_value() && info->field_type != nullptr &&
               type::check_cast(*value_type, info->field_type));
    if (!ok) {
      stats->blocked_value_type++;
      stats->skipped_unproven++;
      return std::nullopt;
    }
  }

  // Both remaining gates put the site outside what any lowering could reach,
  // so they are counted apart from the reachable set rather than inflating it.
  //
  // The hidden-API gate goes first because it is the permanent one: a
  // restricted member stays restricted whatever the app's min_sdk, so counting
  // it under min_sdk would suggest raising min_sdk would recover the site.
  //
  // Asked here rather than alongside `platform_supports` above, so that a plan
  // naming an unclassified member aborts the run only once the site is one the
  // pass would otherwise have emitted -- and so that the member name is not
  // built for sites the checks above already rejected.
  if (!plan_is_linkable(*plan)) {
    stats->blocked_hidden_api++;
    // The four restricted members are expressible as a compareAndSwap{Int,Long}
    // retry loop over unrestricted members, but that loop is not a lowering
    // worth having. libcore's path ends in a single atomic add that cannot
    // fail; the loop reads, then swaps, and retries whenever another thread
    // wrote in between. On a Galaxy S23 it was faster on one thread and slower
    // as soon as threads shared the field -- 0.45x to 0.64x at eight -- and
    // these sites are the coroutine counters every dispatcher thread updates.
    // R8 leaves them alone too.
    return std::nullopt;
  }
  // `getAndAdd`/`getAndSet` arrived in Android N.
  if (!platform_supports) {
    stats->blocked_min_sdk++;
    return std::nullopt;
  }

  stats->feasible[{site.api, holder_null_proven}]++;
  return Rewrite{insn, info, *plan, !holder_null_proven, site.via_backport};
}

// Reads the whole program for lowerable sites and records them in `rewrites`.
// Nothing is mutated here: emission is a separate serial phase, so the output
// does not depend on which thread reached a method first.
Stats analyze_calls(const Scope& scope,
                    const UnorderedMap<DexField*, const UpdaterInfo*>& by_field,
                    const UpdaterOperations& ops,
                    int min_sdk,
                    RewritePlan* rewrites) {
  return walk::parallel::methods<Stats>(scope, [&](DexMethod* method) {
    Stats stats;
    auto* code = method->get_code();
    if (code == nullptr || method->rstate.no_optimizations() ||
        ops.is_forwarder(method)) {
      return stats;
    }
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    const auto sites = ops.sites_in(cfg);
    if (sites.empty()) {
      return stats;
    }

    type_inference::TypeInference ti(cfg);
    ti.run(method);

    // Move-aware use-def chains resolve the receiver and the holder across
    // basic blocks: a load hoisted out of a loop lands in a different block
    // from the call that uses it.
    live_range::MoveAwareChains chains(cfg);
    auto use_defs = chains.get_use_def_chains();

    IRInstruction* receiver_insn = nullptr;
    if (!is_static(method)) {
      auto* first = cfg.get_first_param_instruction();
      if (first != nullptr && opcode::is_load_param_object(first->opcode())) {
        receiver_insn = first;
      }
    }
    MethodAnalysis ma{method,   by_field,      ti.get_type_environments(),
                      use_defs, receiver_insn, min_sdk};

    std::vector<Rewrite> planned;
    for (const auto& site : sites) {
      auto rewrite = classify_site(site, ma, &stats);
      if (rewrite.has_value()) {
        planned.push_back(*rewrite);
      }
    }
    if (!planned.empty()) {
      rewrites->emplace(method, std::move(planned));
    }
    return stats;
  });
}

// The instructions replacing one updater call: load the shared `Unsafe` and the
// field's offset, then the unsafe operation.
std::vector<IRInstruction*> build_replacement(
    cfg::ControlFlowGraph& cfg,
    const cfg::InstructionIterator& it,
    const Rewrite& rewrite,
    const Helpers& helpers) {
  IRInstruction* insn = rewrite.insn;
  const UnsafePlan& plan = rewrite.plan;
  const bool wide = atomic_field_updaters::is_wide(plan.kind);

  std::vector<IRInstruction*> repl;
  if (rewrite.needs_guard) {
    // Preserve the ClassCastException `accessCheck` would have thrown.
    repl.push_back(dasm(OPCODE_INVOKE_STATIC, helpers.check_holder,
                        {{VREG, insn->src(1)}}));
  }

  reg_t offset_reg = cfg.allocate_wide_temp();
  reg_t lit_reg = 0;
  DexMethodRef* callee = nullptr;
  if (plan.retry_spurious_failure) {
    // The helper loads `Unsafe` itself: (holder, offset, expect, update).
    always_assert(helpers.cas_object_retry != nullptr);
    always_assert(plan.value_srcs == 2 && !plan.literal.has_value());
    emit_sget(&repl, OPCODE_SGET_WIDE, IOPCODE_MOVE_RESULT_PSEUDO_WIDE,
              rewrite.info->offset_field, offset_reg);
    callee = helpers.cas_object_retry;
    repl.push_back(dasm(OPCODE_INVOKE_STATIC, callee,
                        {{VREG, insn->src(1)}, // holder
                         {VREG, offset_reg},
                         {VREG, insn->src(2)}, // expect
                         {VREG, insn->src(3)}})); // update
  } else {
    reg_t unsafe_reg = cfg.allocate_temp();
    emit_sget(&repl, OPCODE_SGET_OBJECT, IOPCODE_MOVE_RESULT_PSEUDO_OBJECT,
              helpers.s_unsafe, unsafe_reg);
    emit_sget(&repl, OPCODE_SGET_WIDE, IOPCODE_MOVE_RESULT_PSEUDO_WIDE,
              rewrite.info->offset_field, offset_reg);

    // A literal value argument, for the increment/decrement forms.
    if (plan.literal.has_value()) {
      lit_reg = wide ? cfg.allocate_wide_temp() : cfg.allocate_temp();
      repl.push_back(dasm(wide ? OPCODE_CONST_WIDE : OPCODE_CONST,
                          {{VREG, lit_reg}, {LITERAL, *plan.literal}}));
    }

    callee = unsafe_ref(plan);
    std::vector<Operand> srcs{{VREG, unsafe_reg},
                              {VREG, insn->src(1)}, // holder
                              {VREG, offset_reg}};
    for (int i = 0; i < plan.value_srcs; ++i) {
      // Value arguments follow the holder at the original call site.
      srcs.push_back({VREG, insn->src(2 + i)});
    }
    if (plan.literal.has_value()) {
      srcs.push_back({VREG, lit_reg});
    }
    repl.push_back(
        dasm(OPCODE_INVOKE_VIRTUAL, callee, srcs.begin(), srcs.end()));
  }

  // Propagate the result. `CFGMutation::replace` drops the replaced invoke's
  // move-result, so it is re-emitted here. Unsafe's getAndAdd returns the *old*
  // value, so the addAndGet/incrementAndGet family needs the addend applied
  // after.
  auto mr_it = cfg.move_result_of(it);
  auto* unsafe_rtype = callee->get_proto()->get_rtype();
  const bool returns_void = unsafe_rtype == type::_void();
  if (!returns_void && !mr_it.is_end()) {
    const reg_t final_dest = mr_it->insn->dest();
    IROpcode mr_op =
        plan.kind == Kind::REFERENCE && !plan.add_result
            ? OPCODE_MOVE_RESULT_OBJECT
            : (wide ? OPCODE_MOVE_RESULT_WIDE : OPCODE_MOVE_RESULT);
    if (unsafe_rtype == type::_boolean()) {
      mr_op = OPCODE_MOVE_RESULT;
    }
    if (!plan.add_result) {
      repl.push_back(dasm(mr_op, {{VREG, final_dest}}));
    } else {
      reg_t old_reg = wide ? cfg.allocate_wide_temp() : cfg.allocate_temp();
      repl.push_back(dasm(mr_op, {{VREG, old_reg}}));
      reg_t addend = plan.literal.has_value() ? lit_reg : insn->src(2);
      repl.push_back(
          dasm(wide ? OPCODE_ADD_LONG : OPCODE_ADD_INT,
               {{VREG, final_dest}, {VREG, old_reg}, {VREG, addend}}));
    }
  }
  return repl;
}

// What emission did: the counts for the metrics, and the methods that now call
// each synthesized helper.
struct EmitStats {
  size_t rewritten{0};
  size_t null_checks{0};
  // Subsets of `rewritten`.
  size_t backport_calls_rewritten{0};
  size_t cas_retry_calls{0};
  std::vector<DexMethod*> check_holder_callers;
  std::vector<DexMethod*> cas_retry_callers;
  // The d8 forwarders that lowered sites used to call, each once.
  std::vector<DexMethod*> forwarders_replaced;
  // Filled after emission, by `derive_helper_profiles`.
  size_t helper_profile_stats{0};
};

// Applies the plan. Single threaded and in scope order: emission is
// proportional to the sites that survived analysis -- a few hundred on a large
// app -- so serialising it costs nothing, and it keeps `CFGMutation`, register
// allocation and method ref interning off the parallel path entirely.
EmitStats emit_rewrites(const Scope& scope,
                        const RewritePlan& rewrites,
                        const Helpers& helpers) {
  EmitStats emitted;
  UnorderedSet<DexMethod*> forwarders_seen;
  walk::methods(scope, [&](DexMethod* method) {
    const auto* planned = rewrites.get(method);
    if (planned == nullptr) {
      return;
    }
    UnorderedMap<const IRInstruction*, const Rewrite*> by_insn;
    for (const auto& r : *planned) {
      by_insn.emplace(r.insn, &r);
    }
    auto& cfg = method->get_code()->cfg();
    cfg::CFGMutation mutation(cfg);
    bool calls_check_holder = false;
    bool calls_cas_retry = false;
    auto iterable = cfg::InstructionIterable(cfg);
    for (auto it = iterable.begin(); it != iterable.end(); ++it) {
      auto rit = by_insn.find(it->insn);
      if (rit == by_insn.end()) {
        continue;
      }
      const Rewrite& rewrite = *rit->second;
      // An updater whose holder could not be given an offset -- no class, or
      // a <clinit> with nowhere to insert -- cannot be rewritten. Recognition
      // is supposed to rule those out, but the offset is what the rewrite
      // reads, so this does not lean on that: substituting a null field here
      // would put an unresolved field reference into the output.
      if (rewrite.info->offset_field == nullptr) {
        continue;
      }
      if (rewrite.via_backport) {
        auto* forwarder =
            resolve_method(rewrite.insn->get_method(), MethodSearch::Static);
        if (forwarder != nullptr && forwarders_seen.insert(forwarder).second) {
          emitted.forwarders_replaced.push_back(forwarder);
        }
      }
      mutation.replace(it, build_replacement(cfg, it, rewrite, helpers));
      emitted.rewritten++;
      if (rewrite.needs_guard) {
        emitted.null_checks++;
        calls_check_holder = true;
      }
      if (rewrite.via_backport) {
        emitted.backport_calls_rewritten++;
      }
      if (rewrite.plan.retry_spurious_failure) {
        emitted.cas_retry_calls++;
        calls_cas_retry = true;
      }
    }
    mutation.flush();
    if (calls_check_holder) {
      emitted.check_holder_callers.push_back(method);
    }
    if (calls_cas_retry) {
      emitted.cas_retry_callers.push_back(method);
    }
  });
  return emitted;
}

// The helpers are synthesized here, so no input profile mentions them, and
// profile-guided passes read that as cold. ArtProfileWriterPass then leaves
// them out of the baseline profile and, since hot code calls them, annotates
// them @NeverInline, so ART keeps every hot call to them a call.
//
// The retry helper does the job of the d8 forwarders it replaced, so their
// stats measure it most closely. `derive_stats` only fills interactions the
// target has no stats for, so the callers come second: they fill what the
// forwarders lack, and they are all a direct reference CAS has. `checkHolder`
// replaces nothing, so it takes its callers' stats.
size_t derive_helper_profiles(ConfigFiles& conf,
                              const Helpers& helpers,
                              const EmitStats& emitted) {
  auto& method_profiles = conf.get_method_profiles();
  size_t derived = method_profiles.derive_stats(helpers.check_holder,
                                                emitted.check_holder_callers);
  if (helpers.cas_object_retry != nullptr) {
    derived += method_profiles.derive_stats(helpers.cas_object_retry,
                                            emitted.forwarders_replaced);
    derived += method_profiles.derive_stats(helpers.cas_object_retry,
                                            emitted.cas_retry_callers);
  }
  return derived;
}

void report(PassManager& mgr,
            const Stats& totals,
            const EmitStats& emitted,
            const UnorderedMap<const DexType*, Kind>& updater_kinds) {
  mgr.set_metric("calls_rewritten", emitted.rewritten);
  mgr.set_metric("null_checks_emitted", emitted.null_checks);
  mgr.set_metric("backport_cas_calls_rewritten",
                 emitted.backport_calls_rewritten);
  mgr.set_metric("cas_retry_calls_emitted", emitted.cas_retry_calls);
  mgr.set_metric("helper_profile_stats_derived", emitted.helper_profile_stats);
  mgr.set_metric("blocked_min_sdk", totals.blocked_min_sdk);
  mgr.set_metric("blocked_hidden_api", totals.blocked_hidden_api);
  mgr.set_metric("calls_skipped_unresolved_updater", totals.skipped_unresolved);
  mgr.set_metric("calls_skipped_unproven_types", totals.skipped_unproven);

  // Why a site was blocked, and why resolution failed: traced rather than
  // reported. These answer a question only someone investigating coverage
  // asks, and the totals they roll up into are already metrics.
  TRACE(ATOMUP, 2, "blocked: holder_type=%zu value_type=%zu unmodeled_op=%zu",
        totals.blocked_holder_type, totals.blocked_value_type,
        totals.blocked_unmodeled_op);
  TRACE(ATOMUP, 2,
        "unresolved: no_defs=%zu def_not_sget=%zu "
        "field_not_def=%zu "
        "field_unknown=%zu conflicting_defs=%zu",
        totals.no_defs, totals.def_not_sget, totals.field_not_def,
        totals.field_unknown, totals.conflicting_defs);

  size_t feasible_total = 0;
  size_t needs_null_check_total = 0;
  for (const auto& [key, n] : totals.feasible) {
    (key.second ? feasible_total : needs_null_check_total) += n;
  }

  // Everything below is for the trace and nothing else -- the per-(flavor,
  // operation) rows are not metrics, for the same reason the census breakdown
  // is not: which rows exist depends on the program. Guarded so the labels are
  // not formatted when no one is reading them.
  if (traceEnabled(ATOMUP, 2)) {
    std::vector<std::pair<std::string, size_t>> breakdown;
    breakdown.reserve(totals.feasible.size());
    for (const auto& [key, n] : totals.feasible) {
      const auto* mref = key.first;
      auto kit = updater_kinds.find(mref->get_class());
      breakdown.emplace_back(
          std::string(key.second ? "feasible_" : "needs_null_check_") +
              kind_name(kit->second) + "_" + mref->get_name()->str_copy() +
              show(mref->get_proto()),
          n);
    }
    std::sort(breakdown.begin(), breakdown.end());
    for (const auto& [label, n] : breakdown) {
      TRACE(ATOMUP, 2, "%s = %zu", label.c_str(), n);
    }
  }
  mgr.set_metric("feasible_total", feasible_total);
  mgr.set_metric("needs_null_check_total", needs_null_check_total);
  // What a full lowering would reach: proven sites plus those a null check
  // makes safe.
  mgr.set_metric("rewritable_total", feasible_total + needs_null_check_total);
  TRACE(ATOMUP, 1,
        "SUMMARY rewritten=%zu null_checks=%zu rewritable=%zu (proven=%zu "
        "needs_null_check=%zu) "
        "unresolved=%zu blocked_holder_type=%zu blocked_value_type=%zu "
        "unmodeled_op=%zu blocked_min_sdk=%zu blocked_hidden_api=%zu",
        emitted.rewritten, emitted.null_checks,
        feasible_total + needs_null_check_total, feasible_total,
        needs_null_check_total, totals.skipped_unresolved,
        totals.blocked_holder_type, totals.blocked_value_type,
        totals.blocked_unmodeled_op, totals.blocked_min_sdk,
        totals.blocked_hidden_api);
}

// A rewritten call no longer reads its updater, so the load that fed it is
// dead. Removing it here is what lets cleanup find the updater field
// unreferenced.
void dce_rewritten_methods(const Scope& scope,
                           ConfigFiles& conf,
                           const RewritePlan& rewrites) {
  auto method_override_graph = method_override_graph::build_graph(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns(), method_override_graph.get());
  const UnorderedSet<DexMethodRef*> pure_methods;
  LocalDce local_dce(&init_classes_with_side_effects, pure_methods,
                     method_override_graph.get());
  for (auto&& [method, ignored] : UnorderedIterable(rewrites)) {
    local_dce.dce(method->get_code(), true, method->get_class());
  }
}

struct CleanupStats {
  size_t updater_fields_removed{0};
  size_t updater_inits_removed{0};
  // Counted per field, so a holder whose updater and offset field are both
  // pinned contributes two. `can_delete` is false for any root or kept member,
  // not only for one named by a keep rule.
  size_t skipped_undeletable{0};
  // Also per field, and only for one that was otherwise about to be removed --
  // a holder whose fields are all still referenced is not counted, however its
  // <clinit> is written.
  size_t skipped_try_region{0};
  size_t offset_fields_removed{0};
  size_t offset_inits_removed{0};
};

IRInstruction* find_static_store(DexMethod* method,
                                 DexField* field,
                                 IROpcode store_opcode) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return nullptr;
  }
  auto& cfg = code->cfg();
  for (auto& mie : cfg::InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->opcode() == store_opcode && insn->has_field() &&
        insn->get_field()->is_def() && insn->get_field()->as_def() == field) {
      return insn;
    }
  }
  return nullptr;
}

void collect_single_use_init_slice(cfg::ControlFlowGraph& cfg,
                                   const live_range::UseDefChains& use_defs,
                                   const live_range::DefUseChains& def_uses,
                                   IRInstruction* insn,
                                   UnorderedSet<IRInstruction*>* slice) {
  if (!slice->insert(insn).second) {
    return;
  }
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    auto def_it =
        use_defs.find(live_range::Use{insn, static_cast<src_index_t>(i)});
    if (def_it == use_defs.end() || def_it->second.size() != 1) {
      continue;
    }
    auto* def = *def_it->second.begin();
    auto use_it = def_uses.find(def);
    if (use_it == def_uses.end()) {
      continue;
    }
    size_t n_uses = 0;
    bool only_used_by_insn = true;
    for (const auto& use : UnorderedIterable(use_it->second)) {
      n_uses++;
      only_used_by_insn &= use.insn == insn;
    }
    if (n_uses != 1 || !only_used_by_insn) {
      continue;
    }
    collect_single_use_init_slice(cfg, use_defs, def_uses, def, slice);
  }
}

// Does this method have a try region that can actually be entered?
//
// Cleanup deletes a field's init slice, and the slice is built from
// `newUpdater` and `getDeclaredField`, both of which throw. Deleting one out of
// a try region removes a path the catch block was written for.
//
// Refusing the whole method is deliberate, rather than asking which blocks the
// slice lands in. Throw edges are how a CFG records "reachable from a handler",
// but `add_catch_edges` only attaches them to blocks that *end* in a may-throw
// instruction, so a slice instruction sitting in the non-throwing tail of a try
// region carries none and a per-block test would wave it through.
//
// A try region containing nothing that throws has no edges either, so it reads
// as absent here. Nothing is lost by that: its handler cannot be reached.
//
// R8 declines to instrument such a class at all (`Reason.UNDER_CATCH_HANDLER`).
// Declining only to clean it up is enough here, because the code this pass
// *inserts* cannot throw -- recognition has already proven the named volatile
// field exists on the holder, so the added `getDeclaredField` resolves.
bool has_live_try_region(cfg::ControlFlowGraph& cfg) {
  const auto blocks = cfg.blocks();
  return std::any_of(blocks.begin(), blocks.end(), [&cfg](cfg::Block* block) {
    return block != nullptr &&
           cfg.get_succ_edge_of_type(block, cfg::EDGE_THROW) != nullptr;
  });
}

CleanupStats cleanup_redundant_fields(const Scope& scope,
                                      std::vector<UpdaterInfo>* updaters,
                                      PassManager& mgr) {
  CleanupStats stats;
  struct Counts {
    std::atomic<size_t> updater_refs{0};
    std::atomic<size_t> offset_refs{0};
  };
  UnorderedMap<const DexField*, UpdaterInfo*> by_updater;
  UnorderedMap<const DexField*, UpdaterInfo*> by_offset;
  UnorderedMap<UpdaterInfo*, Counts> counts;
  for (auto& info : *updaters) {
    by_updater.emplace(info.updater, &info);
    if (info.offset_field != nullptr) {
      by_offset.emplace(info.offset_field, &info);
    }
    counts.try_emplace(&info);
  }

  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    for (auto& mie : cfg::InstructionIterable(code->cfg())) {
      auto* insn = mie.insn;
      if (!insn->has_field() || !insn->get_field()->is_def()) {
        continue;
      }
      auto* field = insn->get_field()->as_def();
      auto up_it = by_updater.find(field);
      if (up_it != by_updater.end()) {
        if (insn->opcode() != OPCODE_SPUT_OBJECT) {
          counts.at(up_it->second)
              .updater_refs.fetch_add(1, std::memory_order_relaxed);
        }
        continue;
      }
      auto off_it = by_offset.find(field);
      if (off_it != by_offset.end() && insn->opcode() != OPCODE_SPUT_WIDE) {
        counts.at(off_it->second)
            .offset_refs.fetch_add(1, std::memory_order_relaxed);
      }
    }
  });

  UnorderedMap<DexMethod*, UnorderedSet<IRInstruction*>> remove_from_method;
  std::vector<std::pair<DexClass*, DexField*>> fields_to_delete;
  for (auto& info : *updaters) {
    auto* holder_cls = type_class(info.holder);
    auto* clinit = holder_cls == nullptr ? nullptr : holder_cls->get_clinit();
    if (clinit == nullptr || clinit->get_code() == nullptr) {
      continue;
    }
    auto& cfg = clinit->get_code()->cfg();
    live_range::MoveAwareChains chains(cfg);
    auto use_defs = chains.get_use_def_chains();
    auto def_uses = chains.get_def_use_chains();
    const auto& c = counts.at(&info);

    // Answered at most once per holder, and only for a field that reached the
    // point of being removed -- both so the metric counts real refusals and so
    // holders with nothing to clean up do not pay for the walk.
    std::optional<bool> under_handler;
    auto in_try_region = [&]() {
      if (!under_handler) {
        under_handler = has_live_try_region(cfg);
      }
      return *under_handler;
    };

    // May this field be deleted at all, and if so, which instructions exist
    // only to initialize it?
    auto removable = [&](DexField* field, IROpcode store_opcode,
                         UnorderedSet<IRInstruction*>* slice) {
      if (!can_delete(field)) {
        stats.skipped_undeletable++;
        return false;
      }
      if (in_try_region()) {
        stats.skipped_try_region++;
        return false;
      }
      auto* store = find_static_store(clinit, field, store_opcode);
      if (store != nullptr) {
        collect_single_use_init_slice(cfg, use_defs, def_uses, store, slice);
      }
      return true;
    };

    if (c.offset_refs.load(std::memory_order_relaxed) == 0 &&
        info.offset_field != nullptr) {
      UnorderedSet<IRInstruction*> slice;
      if (removable(info.offset_field, OPCODE_SPUT_WIDE, &slice)) {
        fields_to_delete.emplace_back(holder_cls, info.offset_field);
        stats.offset_fields_removed++;
        info.offset_field = nullptr;
        // A field with no store has an empty slice and removes no init. Only
        // the field itself goes.
        if (!slice.empty()) {
          insert_unordered_iterable(remove_from_method[clinit], slice);
          stats.offset_inits_removed++;
        }
      }
    }
    if (c.updater_refs.load(std::memory_order_relaxed) == 0) {
      // The offset field is one we synthesize and may not exist; the updater is
      // what recognition matched on, so it is always present.
      always_assert(info.updater != nullptr);
      UnorderedSet<IRInstruction*> slice;
      if (removable(info.updater, OPCODE_SPUT_OBJECT, &slice)) {
        fields_to_delete.emplace_back(holder_cls, info.updater);
        stats.updater_fields_removed++;
        if (!slice.empty()) {
          insert_unordered_iterable(remove_from_method[clinit], slice);
          stats.updater_inits_removed++;
        }
      }
    }
  }

  for (auto&& [method, to_remove] : UnorderedIterable(remove_from_method)) {
    auto& cfg = method->get_code()->cfg();
    cfg::CFGMutation mutation(cfg);
    auto iterable = cfg::InstructionIterable(cfg);
    for (auto it = iterable.begin(); it != iterable.end(); ++it) {
      if (to_remove.count(it->insn) == 0u) {
        continue;
      }
      auto mr_it = cfg.move_result_of(it);
      if (!mr_it.is_end()) {
        mutation.remove(mr_it);
      }
      mutation.remove(it);
    }
    mutation.flush();
  }
  for (auto&& [cls, field] : fields_to_delete) {
    cls->remove_field_definition(field);
  }

  mgr.set_metric("updater_fields_removed", stats.updater_fields_removed);
  mgr.set_metric("updater_inits_removed", stats.updater_inits_removed);
  mgr.set_metric("cleanup_skipped_undeletable", stats.skipped_undeletable);
  mgr.set_metric("cleanup_skipped_try_region", stats.skipped_try_region);
  mgr.set_metric("offset_fields_removed", stats.offset_fields_removed);
  mgr.set_metric("offset_inits_removed", stats.offset_inits_removed);
  return stats;
}

} // namespace

void AtomicFieldUpdaterLoweringPass::run_pass(DexStoresVector& stores,
                                              ConfigFiles& conf,
                                              PassManager& mgr) {
  auto scope = build_class_scope(stores);
  const UpdaterOperations ops(find_backport_cas_forwarders(scope, mgr));
  census_ops(scope, ops, mgr);

  // Recognition reads each holder's <clinit>, so it only needs the root store,
  // where the updaters this pass can act on are declared.
  Scope root_scope;
  redex_assert(!stores.empty());
  for (auto& dex : stores.at(0).get_dexen()) {
    for (auto* cls : dex) {
      root_scope.push_back(cls);
    }
  }

  KindCounts per_kind{};
  auto updaters = find_updaters(root_scope, ops.kinds(), per_kind);
  // Report every flavor, including any absent from the program: a metric that
  // vanishes at zero is indistinguishable from the pass not running.
  for (auto kind : atomic_field_updaters::all_kinds()) {
    mgr.set_metric(std::string("updaters_recognized_") + kind_name(kind),
                   per_kind.at(static_cast<size_t>(kind)));
  }
  mgr.set_metric("updaters_recognized", updaters.size());

  if (updaters.empty()) {
    return;
  }
  UnorderedMap<DexField*, const UpdaterInfo*> by_field;
  for (const auto& info : updaters) {
    by_field.emplace(info.updater, &info);
  }
  // Flatten the synthetic accessors Kotlin puts between a call site
  // and a recognized updater field, so resolution below sees a plain field
  // read rather than a call.
  auto accessors = find_receiver_chain_accessors(scope, ops, by_field, mgr);
  inline_updater_accessors(stores, scope, conf, mgr, accessors);

  const int min_sdk = mgr.get_redex_options().min_sdk;
  RewritePlan rewrites;
  const Stats totals = analyze_calls(scope, by_field, ops, min_sdk, &rewrites);
  EmitStats emitted;
  // Nothing is synthesized unless a site is planned: an app with updaters it
  // cannot lower should not be given an unreachable class whose <clinit>
  // reflects over `sun.misc.Unsafe`.
  if (!rewrites.empty()) {
    // The retry helper exists only if a planned site calls it, so whether to
    // synthesize it is read from the plan rather than decided a second time.
    const bool needs_cas_retry =
        unordered_any_of(rewrites, [](const auto& entry) {
          const auto& planned = entry.second;
          return std::any_of(
              planned.begin(), planned.end(),
              [](const Rewrite& r) { return r.plan.retry_spurious_failure; });
        });
    const Helpers helpers = synthesize_unsafe_holder(stores, needs_cas_retry);
    add_offsets_to_holders(updaters, helpers.s_unsafe, mgr);
    emitted = emit_rewrites(scope, rewrites, helpers);
    emitted.helper_profile_stats =
        derive_helper_profiles(conf, helpers, emitted);
    dce_rewritten_methods(scope, conf, rewrites);
  }
  report(mgr, totals, emitted, ops.kinds());
  cleanup_redundant_fields(scope, &updaters, mgr);
}

static AtomicFieldUpdaterLoweringPass s_pass;
