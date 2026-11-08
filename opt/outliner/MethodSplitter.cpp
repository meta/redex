/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodSplitter.h"

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexLimits.h"
#include "DexPosition.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "MethodClosures.h"
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

ConcurrentSet<DexMethod*> split_splittable_closures(
    const Config& config,
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
      auto split_method =
          SplitMethod::create(*splittable_closure, method->get_class(),
                              split_name, std::move(arg_types));
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
              config.fix_new_hot_split_registration ? new_method : method);
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
                             DexType* rtype,
                             std::vector<const DexType*> arg_types,
                             std::unique_ptr<IRCode> split_code) {
  auto* split_type_list = DexTypeList::make_type_list(
      // TODO: Remove overhead.
      [&]() {
        std::vector<const DexType*> non_const_args;
        non_const_args.reserve(arg_types.size());
        std::transform(arg_types.begin(), arg_types.end(),
                       std::back_inserter(non_const_args),
                       [](const auto* t) { return const_cast<DexType*>(t); });
        return non_const_args;
      }());
  auto* split_proto = DexProto::make_proto(rtype, split_type_list);
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
                                std::vector<const DexType*> arg_types) {
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

  auto* split_method = make_split_method(
      target_type, split_name, method->get_proto()->get_rtype(),
      std::move(arg_types), std::move(split_code));

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
    int32_t min_sdk,
    const Config& config,
    const StoreRefCheckers& store_ref_checkers,
    bool create_init_class_insns,
    size_t reserved_mrefs,
    size_t reserved_trefs,
    Stats* stats,
    const std::string& name_infix,
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
    InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
        concurrent_new_hot_split_methods,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods) {
  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, create_init_class_insns);

  ConcurrentSet<DexMethod*> methods;
  std::vector<DexClasses*> dexen;
  UnorderedMap<DexClasses*, std::unique_ptr<DexState>> dex_states;
  for (auto& store : stores) {
    for (auto& dex : store.get_dexen()) {
      dexen.push_back(&dex);
      dex_states[&dex];
    }
  }

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
  // Exclude methods containing loadLibrary/loadLibraryUnsafe calls from
  // splitting. Splitting these methods separates the const-string (library
  // name) from the invoke, which causes ReachableNativesPass to crash.
  auto has_load_library_call = [](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr || !code->cfg_built()) {
      return false;
    }
    for (auto* block : code->cfg().blocks()) {
      for (auto& mie : *block) {
        if (mie.type != MFLOW_OPCODE) {
          continue;
        }
        auto* insn = mie.insn;
        if (!insn->has_method() || !opcode::is_invoke_static(insn->opcode())) {
          continue;
        }
        auto callee_name = insn->get_method()->get_name()->str();
        if (callee_name != "loadLibrary" &&
            callee_name != "loadLibraryUnsafe") {
          continue;
        }
        auto cls_name = insn->get_method()->get_class()->str();
        if (cls_name == "Lcom/facebook/soloader/SoLoader;" ||
            cls_name == "Lcom/facebook/soloader/nativeloader/NativeLoader;") {
          return true;
        }
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
  AtomicMap<std::string, size_t> uniquifiers;
  while (!methods.empty() && iteration < config.max_iteration) {
    TRACE(MS, 2, "=== iteration[%zu]", iteration);
    stats->iterations = iteration;
    Timer t("iteration " + std::to_string(iteration++));
    auto splittable_closures = select_splittable_closures_based_on_costs(
        methods, config, store_ref_checkers, concurrent_hot_methods,
        concurrent_splittable_no_optimizations_methods, *stats);
    ConcurrentSet<DexMethod*> concurrent_added_methods;
    methods = split_splittable_closures(
        config, dexen, min_sdk, init_classes_with_side_effects, reserved_trefs,
        reserved_mrefs, splittable_closures, name_infix, &uniquifiers, stats,
        &dex_states, &concurrent_added_methods, concurrent_hot_methods,
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
    TRACE(MS, 1, "[%zu] Split out %zu methods", iteration,
          concurrent_added_methods.size());
  }
  stats->iterations = iteration;
  walk::code(scope, [&](DexMethod* method, IRCode&) {
    method->rstate.reset_too_large_for_inlining_into();
  });
}

} // namespace method_splitting_impl
