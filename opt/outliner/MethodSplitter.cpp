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
#include "DexStore.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"
#include "MethodClosures.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
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
    for (const auto* splittable_closure : ranked_splittable_closures) {
      auto* method = splittable_closure->method_closures->method;
      std::string id =
          method->get_class()->str() + "." + method->get_name()->str();
      size_t index = uniquifiers->fetch_add(id, 1);
      auto arg_types = splittable_closure->get_arg_types();
      if (!account_for_added_split_method(arg_types, dex_state.get())) {
        stats->dex_limits_hit++;
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
    }
    insert_unordered_iterable(concurrent_affected_methods, affected_methods);
  };
  workqueue_run<DexClasses*>(process_dex, dexen);
  return concurrent_affected_methods;
}

} // namespace

namespace method_splitting_impl {

SplitMethod SplitMethod::create(const SplittableClosure& splittable_closure,
                                DexType* target_type,
                                const DexString* split_name,
                                std::vector<const DexType*> arg_types) {
  auto* method = splittable_closure.method_closures->method;
  auto* code = method->get_code();
  auto& cfg = code->cfg();

  auto split_code =
      std::make_unique<IRCode>(std::make_unique<cfg::ControlFlowGraph>());
  auto& split_cfg = split_code->cfg();
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
  cfg.deep_copy(&split_cfg);
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
  cfg::Block* launchpad_template;
  cfg::Block* split_landingpad;
  if (splittable_closure.closures.size() == 1) {
    always_assert(!splittable_closure.switch_block);
    const auto* closure = splittable_closure.closures.front();
    launchpad_template = closure->target;
    split_landingpad = split_cfg.get_block(closure->target->id());
  } else {
    always_assert(splittable_closure.switch_block);
    split_landingpad =
        split_cfg.get_block(splittable_closure.switch_block->id());
    auto switch_it = split_landingpad->get_last_insn();
    always_assert(opcode::is_switch(switch_it->insn->opcode()));
    for (auto it = split_landingpad->begin(); it != switch_it;) {
      // Positions might be needed for parent references, we need to keep them
      if (it->type != MFLOW_POSITION) {
        it = split_landingpad->remove_mie(it);
      } else {
        it++;
      }
    }
    UnorderedSet<cfg::BlockId> split_target_ids;
    always_assert(!splittable_closure.closures.empty());
    launchpad_template = splittable_closure.closures.front()->target;
    for (const auto* closure : splittable_closure.closures) {
      split_target_ids.insert(closure->target->id());
    }
    split_cfg.delete_succ_edge_if(split_landingpad, [&](auto* e) {
      return !split_target_ids.contains(e->target()->id());
    });
    cfg.delete_succ_edge_if(splittable_closure.switch_block, [&](auto* e) {
      return e->type() == cfg::EDGE_BRANCH &&
             split_target_ids.contains(e->target()->id());
    });
  }
  split_cfg.add_edge(split_entry_block, split_landingpad, cfg::EDGE_GOTO);

  auto* proto = method->get_proto();
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
  auto* split_proto = DexProto::make_proto(proto->get_rtype(), split_type_list);
  auto* split_method_ref =
      DexMethod::make_method(target_type, split_name, split_proto);
  DexAccessFlags split_access_flags =
      DexAccessFlags::ACC_PRIVATE | DexAccessFlags::ACC_STATIC;
  auto* split_method = split_method_ref->make_concrete(
      split_access_flags, std::move(split_code), /* is_virtual */ false);

  split_method->set_deobfuscated_name(show_deobfuscated(split_method));

  auto make_new_sb = [&](auto* method, auto& template_sb) {
    std::optional<SourceBlock::Val> opt_val;
    // TODO: For the hot case, compute "maximum" val over all closures.
    if (splittable_closure.hot_split_kind.value() != HotSplitKind::Hot) {
      opt_val = SourceBlock::Val{0, 0};
    }
    return source_blocks::clone_as_synthetic(template_sb, method, opt_val);
  };
  // When splitting many cases out of a switch, we keep the positions of the
  // switch block, but not the source-block, so we insert a synthetic one here.
  if (splittable_closure.switch_block != nullptr) {
    if (auto* template_sb = source_blocks::get_first_source_block(
            splittable_closure.switch_block)) {
      auto split_landingpad_it = split_landingpad->get_first_insn();
      split_landingpad->insert_before(split_landingpad_it,
                                      make_new_sb(split_method, template_sb));
    }
  }
  // TODO: (Un)scale all source blocks in split method

  std::unique_ptr<SourceBlock> launchpad_sb;
  if (auto* template_sb =
          source_blocks::get_first_source_block(launchpad_template)) {
    launchpad_sb = make_new_sb(method, template_sb);
  }

  return SplitMethod{splittable_closure, split_method, launchpad_template,
                     std::move(launchpad_sb)};
}

void SplitMethod::add_to_target() {
  type_class(m_new_method->get_class())->add_method(m_new_method);
}

void SplitMethod::apply_code_changes() {
  auto* method = m_splittable_closure.method_closures->method;
  auto* proto = method->get_proto();
  auto* code = method->get_code();
  auto& cfg = code->cfg();
  auto* launchpad = cfg.create_block();
  auto copy = m_launchpad_template->preds();
  for (auto* e : copy) {
    if ((m_splittable_closure.switch_block == nullptr) ||
        e->src() == m_splittable_closure.switch_block) {
      cfg.set_edge_target(e, launchpad);
    }
  }
  auto* invoke_insn =
      (new IRInstruction(OPCODE_INVOKE_STATIC))
          ->set_method(m_new_method)
          ->set_srcs_size(m_new_method->get_proto()->get_args()->size());
  src_index_t i = 0;
  for (const auto& arg : m_splittable_closure.args) {
    if (arg.type != nullptr) {
      invoke_insn->set_src(i++, arg.reg);
    }
  }
  launchpad->push_back(invoke_insn);
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

  // Add source-block and position to otherwise naked launchpad
  auto launchpad_it = launchpad->get_first_insn();
  if (m_launchpad_sb) {
    launchpad->insert_before(launchpad_it, std::move(m_launchpad_sb));
  }
  auto new_pos = std::make_unique<DexPosition>(
      DexString::make_string("RedexGenerated"), 0);
  new_pos->bind(DexString::make_string(show_deobfuscated(method)));
  cfg.insert_before(launchpad, launchpad_it, std::move(new_pos));
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
    Timer t("iteration " + std::to_string(iteration++));
    auto splittable_closures = select_splittable_closures_based_on_costs(
        methods, config, store_ref_checkers, concurrent_hot_methods,
        concurrent_splittable_no_optimizations_methods,
        &stats->arg_type_illegal);
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
