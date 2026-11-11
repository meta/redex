/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSplitter.h"

#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexLimits.h"
#include "DexPosition.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "InterDexPassMetrics.h"
#include "MethodClosures.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"
#include "WorkQueue.h"

namespace {

using namespace method_splitting_impl;

class DexState {
 private:
  UnorderedSet<const DexType*> m_type_refs;
  size_t m_method_refs_count;
  size_t max_type_refs;

 public:
  DexState() = delete;
  DexState(const DexState&) = delete;
  DexState& operator=(const DexState&) = delete;
  DexState(int32_t min_sdk,
           const init_classes::InitClassesWithSideEffects&
               init_classes_with_side_effects,
           DexClasses& dex,
           size_t reserved_trefs,
           size_t reserved_mrefs) {
    UnorderedSet<DexMethodRef*> method_refs;
    std::vector<const DexType*> init_classes;
    for (auto* cls : dex) {
      cls->gather_methods(method_refs);
      cls->gather_types(m_type_refs);
      cls->gather_init_classes(init_classes);
    }
    m_method_refs_count = method_refs.size() + reserved_mrefs;

    UnorderedSet<DexType*> refined_types;
    for (const auto* type : init_classes) {
      const auto* refined_type = init_classes_with_side_effects.refine(type);
      if (refined_type != nullptr) {
        m_type_refs.insert(refined_type);
      }
    }
    max_type_refs = get_max_type_refs(min_sdk) - reserved_trefs;
  }

  bool can_insert_type_refs(const UnorderedSet<const DexType*>& types) {
    // `unordered_count_if` returns a signed difference_type; the sum below is
    // compared against an unsigned size, so narrow it here rather than let the
    // comparison do it.
    auto inserted_count = static_cast<size_t>(unordered_count_if(
        types, [this](const auto* t) { return !m_type_refs.contains(t); }));
    // Yes, looks a bit quirky, but matching what happens in
    // InterDex/DexStructure: The number of type refs must stay *below* the
    // maximum, and must never reach it.
    if ((m_type_refs.size() + inserted_count) >= max_type_refs) {
      TRACE(MS, 2, "[invoke sequence outliner] hit kMaxTypeRefs");
      return false;
    }
    return true;
  }

  void insert_type_refs(const UnorderedSet<const DexType*>& types) {
    always_assert(can_insert_type_refs(types));
    insert_unordered_iterable(m_type_refs, types);
    always_assert(m_type_refs.size() < max_type_refs);
  }

  bool can_insert_method_ref() {
    if (m_method_refs_count >= kMaxMethodRefs) {
      TRACE(MS, 2, "[invoke sequence outliner] hit kMaxMethodRefs");
      return false;
    }
    return true;
  }

  void insert_method_ref() {
    always_assert(can_insert_method_ref());
    m_method_refs_count++;
    always_assert(m_method_refs_count <= kMaxMethodRefs);
  }
};

bool account_for_added_split_method(
    const std::vector<const DexType*>& arg_types, DexState* dex_state) {
  if (!dex_state->can_insert_method_ref()) {
    return false;
  }

  UnorderedSet<const DexType*> arg_types_set(arg_types.begin(),
                                             arg_types.end());
  if (!dex_state->can_insert_type_refs(arg_types_set)) {
    return false;
  }

  dex_state->insert_method_ref();
  dex_state->insert_type_refs(arg_types_set);
  return true;
}

const DexString* get_split_method_name(
    const SplittableClosure& splittable_closure,
    const std::string& name_infix,
    size_t index) {
  auto* method = splittable_closure.method_closures->method;
  std::string_view base_name = method::is_init(method)     ? "$init$"
                               : method::is_clinit(method) ? "$clinit$"
                                                           : method->str();
  return DexString::make_string(base_name + "$split$" +
                                describe(splittable_closure.hot_split_kind) +
                                name_infix + std::to_string(index));
}

DexProto* get_split_proto(const DexMethod* method,
                          const std::vector<const DexType*>& arg_types) {
  return DexProto::make_proto(
      method->get_proto()->get_rtype(),
      // TODO: Remove overhead.
      DexTypeList::make_type_list(std::vector<const DexType*>(arg_types)));
}

ConcurrentSet<DexMethod*> split_splittable_closures(
    bool fix_new_hot_split_registration,
    const std::vector<DexClasses*>& dexen,
    int32_t min_sdk,
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects,
    size_t reserved_trefs,
    size_t reserved_mrefs,
    const ConcurrentMap<DexType*, std::vector<SplittableClosure>>&
        splittable_closures,
    const std::string& name_infix,
    AtomicMap<std::string, size_t>* uniquifiers,
    Stats* stats,
    UnorderedMap<DexClasses*, std::unique_ptr<DexState>>* dex_states,
    ConcurrentSet<DexMethod*>* concurrent_added_methods,
    ConcurrentSet<DexMethod*>* concurrent_split_methods,
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
    InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
        concurrent_new_hot_split_methods) {
  Timer t("split");
  ConcurrentSet<DexMethod*> concurrent_affected_methods;
  auto process_dex = [&](DexClasses* dex) {
    std::vector<const SplittableClosure*> ranked_splittable_closures;
    for (auto* cls : *dex) {
      auto it = splittable_closures.find(cls->get_type());
      if (it == splittable_closures.end()) {
        continue;
      }
      for (const auto& c : it->second) {
        ranked_splittable_closures.push_back(&c);
      }
    }
    if (ranked_splittable_closures.empty()) {
      return;
    }

    auto& dex_state = dex_states->at(dex);
    if (!dex_state) {
      dex_state =
          std::make_unique<DexState>(min_sdk, init_classes_with_side_effects,
                                     *dex, reserved_trefs, reserved_mrefs);
    }

    std::sort(ranked_splittable_closures.begin(),
              ranked_splittable_closures.end(), [](auto* c, auto* d) {
                if (c->rank != d->rank) {
                  return c->rank > d->rank;
                }
                auto* c_method = c->method_closures->method;
                auto* d_method = d->method_closures->method;
                if (c_method != d_method) {
                  return compare_dexmethods(c_method, d_method);
                }
                if (c->is_switch() != d->is_switch()) {
                  return c->is_switch() < d->is_switch();
                }
                return c->id() > d->id();
              });
    UnorderedSet<DexMethod*> affected_methods;
    auto record = [stats](const SplittableClosure& sc, CandidateFate fate,
                          const DexMethod* split = nullptr) {
      stats->record(
          SplitKind::Suffix, [&sc] { return sc.head_ids(); }, sc.net_terms,
          fate, sc.covered_code_units, split);
    };
    for (auto it = ranked_splittable_closures.begin();
         it != ranked_splittable_closures.end();
         ++it) {
      const auto* splittable_closure = *it;
      auto* method = splittable_closure->method_closures->method;
      std::string id =
          method->get_class()->str() + "." + method->get_name()->str();
      size_t index = uniquifiers->fetch_add(id, 1);
      auto arg_types = splittable_closure->get_arg_types();
      if (!account_for_added_split_method(arg_types, dex_state.get())) {
        stats->dex_limits_hit++;
        // This candidate and every one ranked after it in the dex.
        for (auto rest = it; rest != ranked_splittable_closures.end(); ++rest) {
          record(**rest, CandidateFate::Emission_DexLimit);
        }
        for (auto* m : UnorderedIterable(affected_methods)) {
          m->get_code()->cfg().remove_unreachable_blocks();
        }
        affected_methods.clear();
        break;
      }
      const auto* split_name =
          get_split_method_name(*splittable_closure, name_infix, index);
      // The name may belong to a method that is not a split of this one: a
      // split made by an earlier run, or a method whose name a constructor's
      // split shares, such as `$init$` for `<init>`. Reusing it would replace
      // that method's code. Unlike `DexMethod::get_unique_name`, which appends
      // its own suffix, this keeps the splits' index numbering.
      auto* split_proto = get_split_proto(method, arg_types);
      while (DexMethod::get_method(method->get_class(), split_name,
                                   split_proto) != nullptr) {
        split_name = get_split_method_name(*splittable_closure, name_infix,
                                           uniquifiers->fetch_add(id, 1));
      }
      auto split_method = SplitMethod::create(
          *splittable_closure, method->get_class(), split_name, arg_types);
      auto* new_method = split_method.get_new_method();

      new_method->rstate.set_dont_inline(); // Don't undo our work.
      if (method->rstate.too_large_for_inlining_into()) {
        new_method->rstate.set_too_large_for_inlining_into();
      }
      if (method->rstate.no_optimizations()) {
        new_method->rstate.set_no_optimizations();
      }

      split_method.add_to_target();
      split_method.apply_code_changes();

      if (splittable_closure->is_large_packed_switch) {
        if (splittable_closure->destroys_large_packed_switch) {
          stats->destroyed_large_packed_switches++;
        } else {
          stats->kept_large_packed_switches++;
        }
        if (splittable_closure->creates_large_sparse_switch) {
          stats->created_large_sparse_switches++;
        }
      }
      stats->added_code_size += splittable_closure->added_code_size;
      stats->split_code_size += new_method->get_code()->estimate_code_units();
      if (splittable_closure->closures.size() == 1) {
        stats->split_count_simple++;
      } else {
        stats->split_count_switches++;
        stats->split_count_switch_cases += splittable_closure->closures.size();
      }
      switch (splittable_closure->hot_split_kind.value()) {
      case HotSplitKind::Hot: {
        stats->hot_split_count++;
        if (concurrent_new_hot_split_methods != nullptr) {
          const auto* ptr = concurrent_new_hot_split_methods->get(method);
          auto* hot_root_method = ptr != nullptr ? *ptr : method;
          concurrent_new_hot_split_methods->emplace(new_method,
                                                    hot_root_method);
        }
        if ((concurrent_hot_methods != nullptr) &&
            (concurrent_hot_methods->count(method) != 0u)) {
          // The split inherits the root's profile stats via
          // `concurrent_new_hot_split_methods` above, so it is compiled too and
          // must join the hot set for later iterations to see it as one.
          // Re-inserting `method` (the historical behaviour, kept when the flag
          // is off) is a no-op: the guard has already proven it present.
          concurrent_hot_methods->insert(
              fix_new_hot_split_registration ? new_method : method);
        }
        break;
      }
      case HotSplitKind::HotCold:
        stats->hot_cold_split_count++;
        break;
      case HotSplitKind::Cold:
        stats->cold_split_count++;
        break;
      default:
        not_reached();
      }
      concurrent_split_methods->insert(method);
      affected_methods.insert(method);
      affected_methods.insert(new_method);
      concurrent_added_methods->insert(new_method);
      record(*splittable_closure, CandidateFate::Emitted, new_method);
      if (splittable_closure->below_legacy_floors) {
        stats->suffix_sub_floor_emitted++;
      }
    }
    insert_unordered_iterable(concurrent_affected_methods, affected_methods);
  };
  workqueue_run<DexClasses*>(process_dex, dexen);
  return concurrent_affected_methods;
}

// What splitting closures needs across the iterations of one run: the scope,
// per-dex reference accounting, and the uniquifiers that keep split names
// distinct.
class SplitRun {
 public:
  SplitRun(DexStoresVector& stores,
           int32_t min_sdk,
           bool create_init_class_insns,
           size_t reserved_mrefs,
           size_t reserved_trefs)
      : m_scope(build_class_scope(stores)),
        m_init_classes_with_side_effects(m_scope, create_init_class_insns),
        m_min_sdk(min_sdk),
        m_reserved_mrefs(reserved_mrefs),
        m_reserved_trefs(reserved_trefs) {
    for (auto& store : stores) {
      for (auto& dex : store.get_dexen()) {
        m_dexen.push_back(&dex);
        m_dex_states[&dex];
      }
    }
  }

  const Scope& scope() const { return m_scope; }

  struct Result {
    // The changed methods of the dexes that did not run out of references,
    // for another iteration.
    ConcurrentSet<DexMethod*> revisit;
    // The methods that got at least one split.
    ConcurrentSet<DexMethod*> split;
  };

  // Splits `splittable_closures`, keyed by the type of their method's class,
  // and appends every new split to `stats`.
  Result split(
      bool fix_new_hot_split_registration,
      const ConcurrentMap<DexType*, std::vector<SplittableClosure>>&
          splittable_closures,
      const std::string& name_infix,
      Stats* stats,
      InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
      InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
          concurrent_new_hot_split_methods) {
    Result result;
    ConcurrentSet<DexMethod*> concurrent_added_methods;
    result.revisit = split_splittable_closures(
        fix_new_hot_split_registration, m_dexen, m_min_sdk,
        m_init_classes_with_side_effects, m_reserved_trefs, m_reserved_mrefs,
        splittable_closures, name_infix, &m_uniquifiers, stats, &m_dex_states,
        &concurrent_added_methods, &result.split, concurrent_hot_methods,
        concurrent_new_hot_split_methods);
    // Transfer per-iteration newly-emitted splits into Stats. Sort by
    // method identity so the append order is deterministic across
    // runs (ConcurrentSet iteration is not).
    auto sorted =
        unordered_to_ordered(concurrent_added_methods, compare_dexmethods);
    stats->added_methods.reserve(stats->added_methods.size() + sorted.size());
    for (auto* m : sorted) {
      stats->added_methods.emplace_back(m, SplitKind::Suffix);
    }
    return result;
  }

 private:
  Scope m_scope;
  init_classes::InitClassesWithSideEffects m_init_classes_with_side_effects;
  int32_t m_min_sdk;
  size_t m_reserved_mrefs;
  size_t m_reserved_trefs;
  std::vector<DexClasses*> m_dexen;
  UnorderedMap<DexClasses*, std::unique_ptr<DexState>> m_dex_states;
  AtomicMap<std::string, size_t> m_uniquifiers;
};

} // namespace

namespace method_splitting_impl {

namespace {

// Entry block for a split method: load-param for each arg with a type, then
// const-def synthesis for the args without one.
cfg::Block* create_split_entry_block(
    cfg::ControlFlowGraph& split_cfg,
    const SplittableClosure& splittable_closure) {
  auto* split_entry_block = split_cfg.create_block();
  for (const auto& arg : splittable_closure.args) {
    if (arg.type != nullptr) {
      split_entry_block->push_back(
          (new IRInstruction(opcode::load_opcode(arg.type)))
              ->set_dest(arg.reg));
    }
  }
  for (const auto& arg : splittable_closure.args) {
    if (arg.type == nullptr) {
      if (arg.def->has_move_result_pseudo()) {
        split_entry_block->push_back(new IRInstruction(*arg.def));
        split_entry_block->push_back(
            (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                ->set_dest(arg.reg));
      } else {
        split_entry_block->push_back(
            (new IRInstruction(*arg.def))->set_dest(arg.reg));
      }
    }
  }
  split_cfg.set_entry_block(split_entry_block);
  return split_entry_block;
}

// The host method's CFG copied whole: positions, source blocks and try markers
// come across with their parent chains, and block ids are kept. The caller
// trims the copy down to the split's body.
std::unique_ptr<IRCode> clone_host_cfg(DexMethod* method) {
  auto split_code =
      std::make_unique<IRCode>(std::make_unique<cfg::ControlFlowGraph>());
  split_code->set_debug_item(std::make_unique<DexDebugItem>());
  // NOTE for callers building non-suffix splits (e.g. cold mid-method
  // regions): `deep_copy` preserves ALL edges of the original cfg --
  // including those crossing what the caller may consider a region
  // boundary. The split body will continue to execute past that
  // boundary unless the caller explicitly truncates it. For suffix
  // splits the boundary IS the original method's return so no
  // truncation is needed. For region splits, the caller must walk
  // the region's exit edges in `split_cfg`, delete them, and append
  // a `return-*` instruction -- otherwise the split body double-
  // executes the rejoin code AND the launchpad's `goto rejoin`
  // executes it again. See `apply_code_changes` below for the canonical
  // truncation pattern.
  method->get_code()->cfg().deep_copy(&split_code->cfg());
  return split_code;
}

// The private static split method with body `split_code`, made concrete.
DexMethod* make_split_method(DexType* target_type,
                             const DexString* split_name,
                             DexProto* split_proto,
                             std::unique_ptr<IRCode> split_code) {
  auto* split_method_ref =
      DexMethod::make_method(target_type, split_name, split_proto);
  DexAccessFlags split_access_flags =
      DexAccessFlags::ACC_PRIVATE | DexAccessFlags::ACC_STATIC;
  auto* split_method = split_method_ref->make_concrete(
      split_access_flags, std::move(split_code), /* is_virtual */ false);
  split_method->set_deobfuscated_name(show_deobfuscated(split_method));
  return split_method;
}

// A synthetic SourceBlock for `method`, modeled on `donor`'s, or null when the
// donor has none. A split of any kind other than Hot is cold, so its synthetic
// block gets the value 0. A Hot split keeps the donor's values, and so does a
// top-level switch case that a switch-outlining pass splits, which has no kind.
std::unique_ptr<SourceBlock> make_synthetic_sb(
    cfg::Block* donor,
    DexMethod* method,
    const std::optional<HotSplitKind>& kind) {
  auto* template_sb = source_blocks::get_first_source_block(donor);
  if (template_sb == nullptr) {
    return nullptr;
  }
  std::optional<SourceBlock::Val> opt_val;
  // TODO: For the hot case, compute "maximum" val over all closures.
  if (kind.has_value() && *kind != HotSplitKind::Hot) {
    opt_val = SourceBlock::Val{0, 0};
  }
  return source_blocks::clone_as_synthetic(template_sb, method, opt_val);
}

// A new host block that invokes `split` with the typed arguments, carrying
// `sb` and a generated position. The caller appends what follows the invoke.
cfg::Block* make_launchpad(cfg::ControlFlowGraph& cfg,
                           DexMethod* host,
                           DexMethod* split,
                           const std::vector<ClosureArgument>& args,
                           std::unique_ptr<SourceBlock> sb) {
  auto* launchpad = cfg.create_block();
  auto* invoke = (new IRInstruction(OPCODE_INVOKE_STATIC))
                     ->set_method(split)
                     ->set_srcs_size(split->get_proto()->get_args()->size());
  src_index_t i = 0;
  for (const auto& arg : args) {
    if (arg.type != nullptr) {
      invoke->set_src(i++, arg.reg);
    }
  }
  // srcs_size is the proto arg count, and get_arg_types() builds the proto
  // from the SAME `type != nullptr` filter this loop uses -- so the two counts
  // agree and every source register is initialized.
  always_assert(i == invoke->srcs_size());
  launchpad->push_back(invoke);
  // Add source-block and position to otherwise naked launchpad
  auto it = launchpad->get_first_insn();
  if (sb) {
    launchpad->insert_before(it, std::move(sb));
  }
  auto pos = std::make_unique<DexPosition>(
      DexString::make_string("RedexGenerated"), 0);
  pos->bind(DexString::make_string(show_deobfuscated(host)));
  cfg.insert_before(launchpad, it, std::move(pos));
  return launchpad;
}

// Turns the split's copy of the host switch `sw` into its dispatcher: strips
// everything before the switch instruction except positions (a later position
// may name one as its parent), and deletes every throw edge and every case
// edge to a block outside `keep`. Returns the default edge when its target is
// outside `keep` too, for the caller to dispose of.
//
// Unlike `ControlFlowGraph::remove_insn`, `Block::remove_mie` does not delete
// the throw edges that the stripped instructions justified. A `switch` cannot
// throw, so without this a dispatcher that sat in a `try` would keep throw
// successors although it has no throwing instruction.
cfg::Edge* strip_dispatcher(cfg::ControlFlowGraph& split_cfg,
                            cfg::Block* sw,
                            const UnorderedSet<cfg::BlockId>& keep) {
  auto switch_it = sw->get_last_insn();
  always_assert(switch_it != sw->end());
  always_assert(opcode::is_switch(switch_it->insn->opcode()));
  for (auto it = sw->begin(); it != switch_it;) {
    // Positions might be needed for parent references, we need to keep them
    if (it->type != MFLOW_POSITION) {
      it = sw->remove_mie(it);
    } else {
      it++;
    }
  }
  split_cfg.delete_succ_edge_if(sw, [&](const cfg::Edge* e) {
    return e->type() == cfg::EDGE_THROW ||
           (e->type() == cfg::EDGE_BRANCH && !keep.contains(e->target()->id()));
  });
  auto* default_edge = split_cfg.get_succ_edge_of_type(sw, cfg::EDGE_GOTO);
  return default_edge != nullptr && !keep.contains(default_edge->target()->id())
             ? default_edge
             : nullptr;
}

// The split's copy of a host switch, turned into the dispatcher over the case
// heads the split takes.
struct SplitDispatcher {
  cfg::Block* block;
  // The default edge when its target is not a taken head, for the caller to
  // dispose of; null otherwise.
  cfg::Edge* ungrouped_default;

  // Re-seeds the dispatcher's SourceBlock, which the strip removed, from the
  // host switch's, once the split method exists.
  void seed_source_block(const SplittableClosure& sc, DexMethod* split) const {
    if (auto sb =
            make_synthetic_sb(sc.switch_block, split, sc.hot_split_kind)) {
      block->insert_before(block->get_first_insn(), std::move(sb));
    }
  }
};

// Builds the dispatcher for `sc`, a split that takes several cases of the
// switch `sc.switch_block`. `split_cfg` is a clone of the host's cfg.
SplitDispatcher make_split_dispatcher(cfg::ControlFlowGraph& split_cfg,
                                      const SplittableClosure& sc) {
  auto* block = split_cfg.get_block(sc.switch_block->id());
  auto* ungrouped_default =
      strip_dispatcher(split_cfg, block, sc.grouped_heads);
  return SplitDispatcher{.block = block,
                         .ungrouped_default = ungrouped_default};
}

// Applies `edit` to the host switch `sw`; the split takes the switch's edges
// into `taken_heads`. Each edge gets the edit that `host_switch_edge_edit`
// gives it. An edge sent to a launchpad goes to the launchpad `launchpad_for`
// returns, and `launchpad_for` is called once per such edge.
void edit_host_switch(
    cfg::ControlFlowGraph& cfg,
    cfg::Block* sw,
    HostSwitchEdit edit,
    const UnorderedSet<cfg::BlockId>& taken_heads,
    const std::function<cfg::Block*(const cfg::Edge*)>& launchpad_for) {
  const auto edge_edit = [&](const cfg::Edge* e) {
    return host_switch_edge_edit(edit, taken_heads.contains(e->target()->id()),
                                 e->type() == cfg::EDGE_GOTO);
  };
  switch (edit) {
  case HostSwitchEdit::None:
    not_reached();
  case HostSwitchEdit::DeleteGrouped: {
    cfg.delete_succ_edge_if(sw, [&](const cfg::Edge* e) {
      return e->type() != cfg::EDGE_THROW &&
             edge_edit(e) == SwitchEdgeEdit::Delete;
    });
    auto* default_edge = cfg.get_succ_edge_of_type(sw, cfg::EDGE_GOTO);
    if (default_edge != nullptr &&
        edge_edit(default_edge) == SwitchEdgeEdit::ToLaunchpad) {
      cfg.set_edge_target(default_edge, launchpad_for(default_edge));
    }
    return;
  }
  }
}

} // namespace

SplitMethod SplitMethod::create(const SplittableClosure& splittable_closure,
                                DexType* target_type,
                                const DexString* split_name,
                                const std::vector<const DexType*>& arg_types) {
  auto* method = splittable_closure.method_closures->method;
  auto split_code = clone_host_cfg(method);
  auto& split_cfg = split_code->cfg();
  auto* split_entry_block =
      create_split_entry_block(split_cfg, splittable_closure);
  always_assert(!splittable_closure.closures.empty());
  cfg::Block* launchpad_template = splittable_closure.closures.front()->target;
  cfg::Block* split_landingpad;
  std::optional<SplitDispatcher> dispatcher;
  if (splittable_closure.closures.size() == 1) {
    always_assert(!splittable_closure.switch_block);
    split_landingpad = split_cfg.get_block(launchpad_template->id());
  } else {
    always_assert(splittable_closure.switch_block);
    dispatcher = make_split_dispatcher(split_cfg, splittable_closure);
    if (dispatcher->ungrouped_default != nullptr) {
      split_cfg.delete_edge(dispatcher->ungrouped_default);
    }
    split_landingpad = dispatcher->block;
  }
  split_cfg.add_edge(split_entry_block, split_landingpad, cfg::EDGE_GOTO);

  auto* split_method = make_split_method(target_type, split_name,
                                         get_split_proto(method, arg_types),
                                         std::move(split_code));

  // When splitting many cases out of a switch, we keep the positions of the
  // switch block, but not the source-block, so we insert a synthetic one here.
  if (dispatcher) {
    dispatcher->seed_source_block(splittable_closure, split_method);
  }
  // TODO: (Un)scale all source blocks in split method

  return SplitMethod{splittable_closure, split_method, launchpad_template,
                     make_synthetic_sb(launchpad_template, method,
                                       splittable_closure.hot_split_kind)};
}

void SplitMethod::add_to_target() {
  type_class(m_new_method->get_class())->add_method(m_new_method);
}

void SplitMethod::apply_code_changes() {
  auto* method = m_splittable_closure.method_closures->method;
  auto* proto = method->get_proto();
  auto* code = method->get_code();
  auto& cfg = code->cfg();
  auto* launchpad =
      make_launchpad(cfg, method, m_new_method, m_splittable_closure.args,
                     std::move(m_launchpad_sb));
  // A split taking several cases of a switch gets the switch's edges into its
  // case heads; one taking a single block gets every predecessor of that
  // block.
  const auto edit = m_splittable_closure.switch_block != nullptr
                        ? HostSwitchEdit::DeleteGrouped
                        : HostSwitchEdit::None;
  if (edit != HostSwitchEdit::None) {
    edit_host_switch(cfg, m_splittable_closure.switch_block, edit,
                     m_splittable_closure.grouped_heads,
                     [&](const cfg::Edge*) { return launchpad; });
  } else {
    auto copy = m_launchpad_template->preds();
    for (auto* e : copy) {
      cfg.set_edge_target(e, launchpad);
    }
  }
  if (proto->is_void()) {
    launchpad->push_back(new IRInstruction(OPCODE_RETURN_VOID));
  } else {
    auto* rtype = proto->get_rtype();
    reg_t min_registers_size = type::is_wide_type(rtype) ? 2 : 1;
    cfg.set_registers_size(
        std::max(cfg.get_registers_size(), min_registers_size));
    launchpad->push_back(
        (new IRInstruction(opcode::move_result_for_invoke(m_new_method)))
            ->set_dest(0));
    launchpad->push_back(
        (new IRInstruction(opcode::return_opcode(rtype)))->set_src(0, 0));
  }
}

void split_methods_in_stores(
    DexStoresVector& stores,
    const SplitEnvironment& env,
    const Config& config,
    Stats* stats,
    const std::string& name_infix,
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
    InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
        concurrent_new_hot_split_methods,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods) {
  SplitRun run(stores, env.min_sdk, env.create_init_class_insns,
               env.reserved_mrefs, env.reserved_trefs);
  const auto& scope = run.scope();

  ConcurrentSet<DexMethod*> methods;

  auto is_excluded = [&](DexMethod* method) {
    if (!config.split_clinits && method::is_clinit(method)) {
      return true;
    }
    auto name = method->get_deobfuscated_name_or_empty();
    for (const auto& prefix : config.excluded_prefices) {
      if (name.substr(0, prefix.size()) == prefix) {
        return true;
      }
    }
    return false;
  };
  walk::parallel::code(scope, [&](DexMethod* method, IRCode&) {
    if (is_excluded(method) || has_load_library_call(method)) {
      stats->excluded_methods++;
      return;
    }
    methods.insert(method);
  });

  size_t iteration{0};
  while (!methods.empty() && iteration < config.max_iteration) {
    TRACE(MS, 2, "=== iteration[%zu]", iteration);
    stats->iterations = iteration;
    Timer t("iteration " + std::to_string(iteration++));
    auto splittable_closures = select_splittable_closures_based_on_costs(
        methods, config, env.store_ref_checkers, concurrent_hot_methods,
        concurrent_splittable_no_optimizations_methods, *stats);
    auto split_count_before = stats->added_methods.size();
    methods =
        run.split(config.fix_new_hot_split_registration, splittable_closures,
                  name_infix, stats, concurrent_hot_methods,
                  concurrent_new_hot_split_methods)
            .revisit;
    TRACE(MS, 1, "[%zu] Split out %zu methods", iteration,
          stats->added_methods.size() - split_count_before);
  }
  stats->iterations = iteration;
  walk::code(scope, [&](DexMethod* method, IRCode&) {
    method->rstate.reset_too_large_for_inlining_into();
  });
}

SplitEnvironment make_split_environment(const DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  const auto& interdex_metrics = mgr.get_interdex_metrics();
  auto it = interdex_metrics.find(interdex::METRIC_RESERVED_MREFS);
  size_t reserved_mrefs = it == interdex_metrics.end() ? 0 : it->second;
  it = interdex_metrics.find(interdex::METRIC_RESERVED_TREFS);
  size_t reserved_trefs = it == interdex_metrics.end() ? 0 : it->second;
  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  const api::AndroidSDK* min_sdk_api{nullptr};
  if (conf.get_android_sdk_api_file(min_sdk)) {
    min_sdk_api = &conf.get_android_sdk_api(min_sdk);
  } else {
    mgr.incr_metric("min_sdk_no_file", 1);
  }
  return SplitEnvironment{
      min_sdk,
      StoreRefCheckers(stores, conf.normal_primary_dex(), min_sdk_api),
      conf.create_init_class_insns(),
      reserved_mrefs,
      reserved_trefs,
  };
}

SelectedSplits split_selected_closures(
    DexStoresVector& stores,
    const SplitEnvironment& env,
    const ConcurrentMap<DexType*, std::vector<SplittableClosure>>&
        splittable_closures,
    const std::string& name_infix,
    method_profiles::MethodProfiles& method_profiles,
    Stats* stats) {
  SplitRun run(stores, env.min_sdk, env.create_init_class_insns,
               env.reserved_mrefs, env.reserved_trefs);
  InsertOnlyConcurrentMap<DexMethod*, DexMethod*>
      concurrent_new_hot_split_methods;
  // The flag only matters with a hot-method set.
  auto result = run.split(/* fix_new_hot_split_registration */ false,
                          splittable_closures, name_infix, stats,
                          /* concurrent_hot_methods */ nullptr,
                          &concurrent_new_hot_split_methods);
  for (auto* method : UnorderedIterable(result.revisit)) {
    // Every revisited method is a host the splitter changed or a split it
    // built on a copy of its host's CFG, so its CFG is built.
    always_assert_log(method->get_code() != nullptr &&
                          method->get_code()->cfg_built(),
                      "%s", SHOW(method));
    method->get_code()->cfg().remove_unreachable_blocks();
  }
  return SelectedSplits{
      std::move(result.split),
      derive_hot_split_profiles(method_profiles,
                                concurrent_new_hot_split_methods),
  };
}

size_t derive_hot_split_profiles(
    method_profiles::MethodProfiles& method_profiles,
    const InsertOnlyConcurrentMap<DexMethod*, DexMethod*>&
        concurrent_new_hot_split_methods) {
  size_t derived_method_profile_stats{0};
  for (auto [new_method, root_method] :
       UnorderedIterable(concurrent_new_hot_split_methods)) {
    derived_method_profile_stats +=
        method_profiles.derive_stats(new_method, {root_method});
  }
  return derived_method_profile_stats;
}

} // namespace method_splitting_impl
