/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveUnusedArgs.h"

#include <deque>
#include <map>
#include <mutex>
#include <set>
#include <vector>

#include "AnnoUtils.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "Liveness.h"
#include "MethodUtil.h"
#include "OptData.h"
#include "OptDataDefs.h"
#include "PassManager.h"
#include "Purity.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace opt_metadata;

/**
 * The RemoveUnusedArgsPass finds method arguments that are not live in the
 * method body, removes those unused arguments from the method signature, and
 * removes the corresponding argument registers from invocations of that
 * method.
 * As an extra bonus, it also removes unused result types, and it reorders
 * argument types to reduce the number of needed protos and shorty strings.
 */
namespace remove_unused_args {

constexpr const char* METRIC_CALLSITE_ARGS_REMOVED = "callsite_args_removed";
constexpr const char* METRIC_METHOD_PARAMS_REMOVED = "method_params_removed";
constexpr const char* METRIC_METHODS_UPDATED = "method_signatures_updated";
constexpr const char* METRIC_METHOD_RESULTS_REMOVED = "method_results_removed";
constexpr const char* METRIC_METHOD_PROTOS_REORDERED =
    "method_protos_reordered";
constexpr const char* METRIC_DEAD_INSTRUCTION_COUNT =
    "num_local_dce_dead_instruction_count";
constexpr const char* METRIC_UNREACHABLE_INSTRUCTION_COUNT =
    "num_local_dce_unreachable_instruction_count";
constexpr const char* METRIC_ITERATIONS = "iterations";

/**
 * Returns metrics as listed above from running RemoveArgs:
 * run() removes unused params from method signatures and param loads, then
 * updates all affected callsites accordingly.
 */
RemoveArgs::PassStats RemoveArgs::run(ConfigFiles& config) {
  RemoveArgs::PassStats pass_stats;
  gather_results_used();
  auto override_graph = mog::build_graph(m_scope);
  compute_reordered_protos(*override_graph);
  auto method_stats =
      update_method_protos(*override_graph, config.get_do_not_devirt_anon());
  pass_stats.method_params_removed_count =
      method_stats.method_params_removed_count;
  pass_stats.methods_updated_count = method_stats.methods_updated_count;
  auto callsites_stats = update_callsites();
  pass_stats.callsite_args_removed_count = callsites_stats.first;
  pass_stats.method_results_removed_count =
      method_stats.method_results_removed_count;
  pass_stats.method_protos_reordered_count =
      method_stats.method_protos_reordered_count;
  pass_stats.local_dce_stats = method_stats.local_dce_stats;
  pass_stats.local_dce_stats += callsites_stats.second;
  return pass_stats;
}

/**
 * Inspects all invoke instructions, and whether they are followed by
 * move-result instructions, and record this information for each method.
 */
void RemoveArgs::gather_results_used() {
  walk::parallel::code(
      m_scope, [&result_used = m_result_used](DexMethod*, IRCode& code) {
        always_assert(code.cfg_built());
        auto& cfg = code.cfg();
        auto ii = InstructionIterable(cfg);
        for (auto it = ii.begin(); it != ii.end(); ++it) {
          auto* insn = it->insn;
          if (!opcode::is_an_invoke(insn->opcode())) {
            continue;
          }
          auto move_result = cfg.move_result_of(it);
          if (move_result.is_end()) {
            continue;
          }
          auto* method = resolve_method_deprecated(
              insn->get_method(), opcode_to_search(insn->opcode()));
          // The above should return any callee for a virtual callsite. Because
          // we only remove results for groups of related methods where every
          // result can be removed, the logic works for true virtuals.
          if (method == nullptr) {
            continue;
          }
          result_used.insert(method);
        }
      });
}

// For normalization, we put primitive types last and thus all reference types
// first, as shorty strings take up space in a dex but don't distinguish arrays
// and classes.
static bool compare_dextypes_for_normalization(const DexType* a,
                                               const DexType* b) {
  int a_primitive = type::is_primitive(a) ? 1 : 0;
  int b_primitive = type::is_primitive(b) ? 1 : 0;
  if (a_primitive != b_primitive) {
    return a_primitive < b_primitive;
  }
  return compare_dexstrings(a->get_name(), b->get_name());
}

static DexProto* normalize_proto(DexProto* proto) {
  DexTypeList::ContainerType args_copy(proto->get_args()->begin(),
                                       proto->get_args()->end());
  std::stable_sort(args_copy.begin(), args_copy.end(),
                   compare_dextypes_for_normalization);
  DexType* rtype = proto->get_rtype();
  return DexProto::make_proto(
      rtype, DexTypeList::make_type_list(std::move(args_copy)));
}

static bool compare_weighted_dexprotos(const std::pair<DexProto*, size_t>& a,
                                       const std::pair<DexProto*, size_t>& b) {
  if (a.second != b.second) {
    return a.second > b.second;
  }
  return compare_dexprotos(a.first, b.first);
}

template <typename Collection>
static bool any_external(const Collection& methods) {
  for (auto* method_node : UnorderedIterable(methods)) {
    auto cls = type_class(method_node->method->get_class());
    if (cls == nullptr || cls->is_external()) {
      return true;
    }
  }
  return false;
}

/**
 * Inspects all methods and invoke instructions, building up a set of protos
 * that we should change. This is done by identifying all defined protos, and
 * then removing those from consideration that we should not change, e.g. those
 * that are externally defined or not-renamable.
 */
void RemoveArgs::compute_reordered_protos(const mog::Graph& override_graph) {
  AtomicMap<DexProto*, size_t> fixed_protos;
  ConcurrentSet<DexProto*> defined_protos;
  auto record_fixed_proto = [&fixed_protos](DexProto* proto, size_t increment) {
    fixed_protos.fetch_add(proto, increment);
  };
  walk::parallel::methods(
      m_scope,
      [&override_graph, &record_fixed_proto,
       &defined_protos](DexMethod* caller) {
        auto* caller_proto = caller->get_proto();
        defined_protos.insert(caller_proto);
        if (!method::can_change_signature(caller) ||
            has_any_parameter_annotation(caller)) {
          record_fixed_proto(caller_proto, 1);
        } else if (caller->is_virtual()) {
          auto is_interface_method =
              is_interface(type_class(caller->get_class()));
          if ((is_interface_method && (root(caller) || !can_rename(caller)))) {
            // We cannot rule out that there are dynamically added classes,
            // created via Proxy.newProxyInstance, that override this method. So
            // we assume the worst.
            record_fixed_proto(caller_proto, 0);
          } else {
            const auto& node = override_graph.get_node(caller);
            if (any_external(node.parents) ||
                (is_interface_method && any_external(node.children))) {
              // We can't change the signature of an overriding method when the
              // overridden method is external, or when an interface defines a
              // method whose only implementation is one that is inherited from
              // an external base class.
              record_fixed_proto(caller_proto, 0);
            }
          }
        }

        IRCode* code = caller->get_code();
        if (code == nullptr) {
          return;
        }
        always_assert(code->cfg_built());
        for (const auto& mie : InstructionIterable(code->cfg())) {
          if (mie.insn->has_method()) {
            auto* callee = mie.insn->get_method();
            auto* callee_proto = callee->get_proto();
            // We don't resolve here, but just check if the provided callee is
            // already resolved. If not, we are going to be conservative. (Note
            // that this matches what update_callsite does below.) We are also
            // going to record any external callees as fixed.
            DexMethod* callee_def = callee->as_def();
            if (callee_def == nullptr || callee_def->is_external()) {
              record_fixed_proto(callee_proto, 1);
            }
          }
        }
      });

  std::vector<std::pair<DexProto*, size_t>> ordered_fixed_protos;
  ordered_fixed_protos.reserve(fixed_protos.size());
  for (auto&& [proto, count] : UnorderedIterable(fixed_protos)) {
    ordered_fixed_protos.emplace_back(proto, count.load());
  }
  std::sort(ordered_fixed_protos.begin(), ordered_fixed_protos.end(),
            compare_weighted_dexprotos);
  UnorderedMap<DexProto*, DexProto*> fixed_representatives;
  for (auto p : ordered_fixed_protos) {
    auto* proto = p.first;
    auto* normalized_proto = normalize_proto(proto);
    // First one (with most references) wins
    fixed_representatives.emplace(normalized_proto, proto);
  }
  for (auto* proto : UnorderedIterable(defined_protos)) {
    if (fixed_protos.count(proto) != 0u) {
      continue;
    }
    auto* reordered_proto = normalize_proto(proto);
    auto it = fixed_representatives.find(reordered_proto);
    if (it != fixed_representatives.end()) {
      reordered_proto = it->second;
    }
    if (proto != reordered_proto) {
      m_reordered_protos.emplace(proto, reordered_proto);
    }
  }

  TRACE(ARGS, 1, "[compute_reordered_protos] can reorder %zu method protos",
        m_reordered_protos.size());
}

/**
 * Returns an updated argument type list for the given method with the given
 * live argument indices.
 */
DexTypeList::ContainerType RemoveArgs::get_live_arg_type_list(
    const DexMethod* method, const std::deque<uint16_t>& live_arg_idxs) {
  DexTypeList::ContainerType live_args;
  auto* args_list = method->get_proto()->get_args();

  for (uint16_t arg_num : live_arg_idxs) {
    if (!is_static(method)) {
      if (arg_num == 0) {
        continue;
      }
      arg_num--;
    }
    live_args.push_back(args_list->at(arg_num));
  }
  return live_args;
}

/**
 * Returns true on successful update to the given method's signature, where
 * the updated args list is specified by live_args.
 */
bool RemoveArgs::update_method_signature(DexMethod* method,
                                         DexProto* updated_proto,
                                         bool is_reordered) {
  auto* colliding_mref = DexMethod::get_method(
      method->get_class(), method->get_name(), updated_proto);
  if (colliding_mref != nullptr) {
    auto* colliding_method = colliding_mref->as_def();
    if ((colliding_method != nullptr) &&
        method::is_constructor(colliding_method)) {
      // We can't rename constructors, so we give up on removing args.
      return false;
    }
  }

  const auto* name = method->get_name();
  if (method->is_virtual()) {

    // When changing the proto, we need to worry about changes to virtual scopes
    // --- for this particular method change, but also across all other upcoming
    // method changes. To this end, we introduce unique names for each name and
    // arg list to avoid any such overlaps.

    NamedRenameMap& named_rename_map = m_rename_maps[name];
    size_t name_index;
    std::string kind;
    if (is_reordered) {
      // When we reorder protos, possibly for entire virtual scopes, we need to
      // make the name unique for each virtual scope, which is defined by the
      // pair (name, original proto args).

      // "rvp" stands for reordered virtual proto
      kind = "$rvp";
      auto* original_args = method->get_proto()->get_args();
      auto [it, emplaced] = named_rename_map.reordering_uniquifiers.emplace(
          original_args, named_rename_map.next_reordering_uniquifiers);
      if (emplaced) {
        named_rename_map.next_reordering_uniquifiers++;
      }
      name_index = it->second;
    } else {
      // We want everything in the same virtual scope to have the same name
      // but for it to not collide with any other method. We thus rename
      // every instance of a related method to the same name. We do this by
      // keeping a map from representative map to uniquifer.

      // "uva" stands for unused virtual args
      kind = "$uva";
      auto representative_method_it = m_method_representative_map.find(method);
      always_assert(representative_method_it !=
                    m_method_representative_map.end());
      auto [it, emplaced] = named_rename_map.removal_uniquifiers.emplace(
          representative_method_it->second,
          named_rename_map.next_removal_uniquifiers);
      if (emplaced) {
        named_rename_map.next_removal_uniquifiers++;
      }
      name_index = it->second;
    }

    std::stringstream ss;
    // This pass typically runs before the obfuscation pass, so we should not
    // need to be too concerned here about creating long method names.

    ss << name->str() << kind << std::to_string(m_iteration) << "$"
       << std::to_string(name_index);
    name = DexString::make_string(ss.str());
  }

  DexMethodSpec spec(nullptr, name, updated_proto);

  std::string tmp;
  if (traceEnabled(ARGS, 3)) {
    tmp = show(method);
  }

  method->change(spec, !method->is_virtual() /* rename on collision */);

  // We make virtual method names unique via $rvp / $uva name mangling; check
  // that this worked:
  always_assert(!method->is_virtual() || method->get_name() == name);

  TRACE(ARGS, 3, "Method signature %s updated to %s", tmp.c_str(),
        SHOW(method));
  log_opt(METHOD_PARAMS_REMOVED, method);
  return true;
}

std::deque<uint16_t> live_args(const DexMethod* method,
                               const std::set<uint16_t>& dead_args) {
  auto* proto = method->get_proto();
  auto num_args = proto->get_args()->size();
  if (!is_static(method)) {
    num_args++;
  }
  std::deque<uint16_t> live_args;
  for (uint16_t i = 0; i < num_args; i++) {
    if (dead_args.count(i) == 0u) {
      live_args.emplace_back(i);
    }
  }
  return live_args;
}

bool RemoveArgs::compute_remove_result(const DexMethod* method) {
  auto* proto = method->get_proto();
  return !proto->is_void() && (m_result_used.count_unsafe(method) == 0u);
}

/**
 * Takes in a method. Populates a mapping of dead args to
 * corresponding load instructions. This
 * function is not meant to be called on abstract methods.
 * For instance methods, the 'this' argument is always considered live.
 * e.g. We return {0:insn0, 2:insn2} for a method whose 0th and 2nd args are
 * dead.
 *
 * NOTE: In the IR, invoke instructions specify exactly one register
 *       for any param size.
 */
std::map<uint16_t, cfg::InstructionIterator> compute_dead_insns(
    const DexMethod* method, const IRCode& code) {
  auto* proto = method->get_proto();
  auto num_args = proto->get_args()->size();

  always_assert(method->get_code() != nullptr);

  std::map<uint16_t, cfg::InstructionIterator> dead_args_and_insns;

  // For instance methods, num_args does not count the 'this' argument.
  if (num_args == 0) {
    // Nothing to do if the method doesn't have args or result to remove.
    return dead_args_and_insns;
  }

  always_assert(code.cfg_built());
  const auto& cfg = code.cfg();
  LivenessFixpointIterator fixpoint_iter(cfg);
  fixpoint_iter.run(LivenessDomain());
  auto* entry_block = cfg.entry_block();
  bool is_instance_method = !is_static(method);
  size_t last_arg_idx = is_instance_method ? num_args : num_args - 1;
  auto* first_insn = entry_block->get_first_insn()->insn;
  // live_vars contains all the registers needed by entry_block's
  // successors.
  auto live_vars = fixpoint_iter.get_live_out_vars_at(entry_block);

  for (auto& mie : InstructionIterable(entry_block).reversed()) {
    auto* insn = mie.insn;
    if (opcode::is_a_load_param(insn->opcode())) {
      if (!live_vars.contains(insn->dest()) &&
          (!is_instance_method || mie.insn != first_insn)) {
        // Mark dead args as dead and never mark the "this" arg.
        dead_args_and_insns.emplace(
            last_arg_idx, entry_block->to_cfg_instruction_iterator(mie));
      }
      last_arg_idx--;
    }
    fixpoint_iter.analyze_instruction(insn, &live_vars);
  }

  return dead_args_and_insns;
}

// When reordering a method's proto, we need to update the method's load-param
// instructions accordingly. We return the accordingly reshuffled list of
// (live) argument indices.
static std::deque<uint16_t> update_method_body_for_reordered_proto(
    DexMethod* method, DexProto* original_proto, DexProto* reordered_proto) {
  // We store a copy of opcode, reg to enable re-assigning in permutated
  // order
  struct LoadParamInfo {
    IROpcode opcode;
    reg_t reg;
    IRInstruction* insn;
  };
  std::vector<LoadParamInfo> load_param_infos;
  std::optional<std::vector<LoadParamInfo>::iterator> load_param_infos_it;
  if (method->get_code() != nullptr) {
    auto param_insns = method->get_code()->cfg().get_param_instructions();
    for (const auto& mie : InstructionIterable(param_insns)) {
      load_param_infos.push_back(
          {mie.insn->opcode(), mie.insn->dest(), mie.insn});
    }
    load_param_infos_it = load_param_infos.begin();
  }

  std::deque<uint16_t> idxs;
  UnorderedMap<const DexType*, std::deque<uint16_t>> idxs_by_type;
  int idx = 0;
  if (!is_static(method)) {
    idxs.push_back(idx++);
    if (load_param_infos_it) {
      (*load_param_infos_it)++;
    }
  }
  for (const auto* t : *original_proto->get_args()) {
    idxs_by_type[t].push_back(idx++);
  }

  for (const auto* t : *reordered_proto->get_args()) {
    auto& deque = idxs_by_type.find(t)->second;
    auto new_idx = deque.front();
    deque.pop_front();

    idxs.push_back(new_idx);

    if (load_param_infos_it) {
      auto* load_param_insn = (*load_param_infos_it)++->insn;
      auto& info = load_param_infos.at(new_idx);
      load_param_insn->set_opcode(info.opcode);
      load_param_insn->set_dest(info.reg);
    }
  }

  return idxs;
}

namespace {

void run_cleanup(DexMethod* method,
                 cfg::ControlFlowGraph& cfg,
                 const init_classes::InitClassesWithSideEffects*
                     init_classes_with_side_effects,
                 const UnorderedSet<DexMethodRef*>& pure_methods,
                 std::mutex& mutex,
                 LocalDce::Stats& stats) {
  auto local_dce = LocalDce(init_classes_with_side_effects, pure_methods);
  local_dce.dce(cfg, /* normalize_new_instances */ true, method->get_class());
  const auto& local_stats = local_dce.get_stats();
  if ((local_stats.dead_instruction_count |
       local_stats.unreachable_instruction_count) != 0u) {
    std::lock_guard<std::mutex> lock(mutex);
    stats += local_stats;
  }
}

} // namespace

/**
 * Partitions the methods into related groups. A method is considered related
 * if it is connected in the method override graph. For each group, a
 * representative method is chosen. Populates m_methods_representative_map
 * with a mapping from each method to its representative. Populates
 * m_related_method_groups with a mapping from each representative method to
 * the group (including itself) of related methods.
 */
void RemoveArgs::populate_representative_ids(
    const mog::Graph& override_graph,
    const UnorderedSet<DexType*>& /*no_devirtualize_annos*/) {
  // Group methods that are related (somehow connect in override graph)
  // For each related group, assign a single representative method.
  walk::parallel::methods(m_scope, [&](DexMethod* method) {
    if (m_method_representative_map.count(method) != 0u) {
      return;
    }
    UnorderedSet<const DexMethod*> visited;
    visited.insert(method);
    override_graph.get_node(method).gather_connected_methods(&visited);
    const auto* representative =
        *unordered_min_element(visited, dexmethods_comparator());
    m_related_method_groups.get_or_emplace_and_assert_equal(representative,
                                                            visited);
    for (const auto* m : UnorderedIterable(visited)) {
      auto existing_representative =
          m_method_representative_map.emplace(m, representative);
      always_assert(*existing_representative.first == representative);
    }
  });
}

/* This function does the heavy lifting for computing updated protos and
 * whether we can update a method. When reordering/removing arguments from
 * virtual methods, the problem of whether we can update the method is a bit
 * more complex. We can only update a method if every method connected to it
 * in the method override graph can also be updated. Furthermore, we can only
 * remove the arguments that can be removed in all connected methods. This
 * function returns a list of entries for all methods that should be updated.
 */
void RemoveArgs::gather_updated_entries(
    const UnorderedSet<DexType*>& no_devirtualize_annos,
    InsertOnlyConcurrentMap<DexMethod*, Entry>* updated_entries) {
  // Loop over all related groups
  using MethodAndMethodSet =
      std::pair<const DexMethod* const, UnorderedSet<const DexMethod*>>;

  InsertOnlyConcurrentMap<const DexMethod*,
                          std::map<uint16_t, cfg::InstructionIterator>>
      all_dead_insns;

  // Fill in preliminary dead instruction data for methods.
  walk::parallel::code(m_scope, [&](DexMethod* method, IRCode& code) {
    all_dead_insns.emplace(method, compute_dead_insns(method, code));
  });

  auto kvp_workqueue = workqueue_foreach<const MethodAndMethodSet*>(
      [&](const MethodAndMethodSet* kvp) {
        bool remove_result = true;

        // First iteration, perform some basic checks for whether we can edit
        // this method.
        for (const auto* m : UnorderedIterable(kvp->second)) {
          // If we can't edit, just skip
          if (!method::can_change_signature(m) ||
              has_any_annotation(m, no_devirtualize_annos) ||
              has_any_parameter_annotation(m)) {
            return;
          }

          // Run other checks if we can edit
          const auto full_name = m->get_deobfuscated_name_or_empty();
          for (const auto& s : m_blocklist) {
            if (full_name.find(s) != std::string::npos) {
              return;
            }
          }

          // Compute remove result and && it with the remove result for the
          // whole group
          remove_result &= compute_remove_result(m);
        }

        // Second iteration, at this point we have all the dead args for the
        // related group. We need to iterate over the methods again and take the
        // intersection of the dead args
        auto num_args = kvp->first->get_proto()->get_args()->size();
        if (!is_static(kvp->first)) {
          num_args++;
        }
        // All method start out with all args dead except for `this`.
        std::set<uint16_t> running_dead_args;
        for (uint16_t i = (is_static(kvp->first) ? 0 : 1); i < num_args; i++) {
          running_dead_args.insert(i);
        }
        for (const auto* m : UnorderedIterable(kvp->second)) {
          if (m->get_code() != nullptr) {
            const auto& dead_insn_map = all_dead_insns.at(m);
            std::erase_if(running_dead_args,
                          [&](auto e) { return !dead_insn_map.count(e); });
          }
        }

        // Third iteration, delete all args/insns that aren't in
        // `running_dead_args`.
        for (const auto* m : UnorderedIterable(kvp->second)) {
          if (m->get_code() != nullptr) {
            auto& dead_insn_map = all_dead_insns.at_unsafe(m);
            std::erase_if(dead_insn_map, [&](const auto& e) {
              return !running_dead_args.count(e.first);
            });
          }
        }

        // Now we have enough to construct the proto for each
        // method. Also run some last checks that rely on having the proto
        // constructed.
        bool is_reordered;
        DexProto* updated_proto;
        std::deque<uint16_t> live_arg_idxs;
        auto reordered_it = m_reordered_protos.find(kvp->first->get_proto());
        if (reordered_it != m_reordered_protos.end()) {
          is_reordered = true;
          live_arg_idxs = live_args(kvp->first, {});
          updated_proto = reordered_it->second;
        } else {
          is_reordered = false;
          // Otherwise, try to construct the dead args proto
          live_arg_idxs = live_args(kvp->first, running_dead_args);
          auto live_args = get_live_arg_type_list(kvp->first, live_arg_idxs);
          auto* live_args_list =
              DexTypeList::make_type_list(std::move(live_args));
          DexType* rtype = remove_result ? type::_void()
                                         : kvp->first->get_proto()->get_rtype();
          updated_proto = DexProto::make_proto(rtype, live_args_list);
        }
        if (updated_proto == kvp->first->get_proto()) {
          return;
        }

        // Fourth iteration, check that none of the renamed methods collide.
        if (method::is_constructor(kvp->first)) {
          for (const auto* m : UnorderedIterable(kvp->second)) {
            auto* colliding_mref = DexMethod::get_method(
                m->get_class(), m->get_name(), updated_proto);
            if (colliding_mref != nullptr) {
              auto* colliding_method = colliding_mref->as_def();
              if (colliding_method != nullptr) {
                // We can't rename constructors, so we give up on removing args.
                return;
              }
            }
          }
        }

        // Fifth iteration, we loop one more time and add all the updated protos
        // to the final data structure.
        for (const auto* method : UnorderedIterable(kvp->second)) {
          std::vector<cfg::InstructionIterator> dead_insns;
          // Compile the list of dead instructions that we computed earlier
          if (!is_reordered) {
            auto dead_insns_it = all_dead_insns.find(method);
            if (dead_insns_it != all_dead_insns.end()) {
              for (const auto& dead_insn : dead_insns_it->second) {
                dead_insns.emplace_back(dead_insn.second);
              }
            }
          }
          always_assert(method->get_code() == nullptr ||
                        dead_insns.size() + updated_proto->get_args()->size() ==
                            method->get_proto()->get_args()->size());
          updated_entries->emplace(const_cast<DexMethod*>(method),
                                   (Entry){std::move(dead_insns), live_arg_idxs,
                                           remove_result, is_reordered,
                                           updated_proto, method->get_proto()});
        }
      });
  for (const auto& kvp : UnorderedIterable(m_related_method_groups)) {
    kvp_workqueue.add_item(&kvp);
  }
  kvp_workqueue.run_all();
}

/**
 * For methods that have unused arguments, record live argument registers.
 */
RemoveArgs::MethodStats RemoveArgs::update_method_protos(
    const mog::Graph& override_graph,
    const UnorderedSet<DexType*>& no_devirtualize_annos) {

  // Phase 1: Calculate exit blocks for all methods
  walk::parallel::methods(m_scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code != nullptr) {
      always_assert(code->cfg_built());
      auto& cfg = code->cfg();
      cfg.calculate_exit_block();
    }
  });

  // Phase 2: Removing args for virtual methods is slightly more complex
  // because we need to make sure that the args are unused across all
  // implementations of the method. In order to do this, we need to partition
  // the methods into related groups. A related group is a group of methods
  // that are connected in the method override graph. For each group, we
  // assign a single representative method as an identifier for the graph.
  populate_representative_ids(override_graph, no_devirtualize_annos);

  // Phase 3: Find all methods that we can potentially update
  InsertOnlyConcurrentMap<DexMethod*, Entry> unordered_entries;
  gather_updated_entries(no_devirtualize_annos, &unordered_entries);

  // Sort entries, so that we process all renaming operations in a
  // deterministic order.
  auto ordered_entries =
      unordered_to_ordered(unordered_entries,
                           [](const std::pair<DexMethod*, Entry>& a,
                              const std::pair<DexMethod*, Entry>& b) {
                             return compare_dexmethods(a.first, b.first);
                           });

  RemoveArgs::MethodStats method_stats;
  std::vector<DexClass*> classes;
  UnorderedMap<DexClass*, std::vector<std::pair<DexMethod*, Entry>>>
      class_entries;
  for (auto& p : ordered_entries) {
    DexMethod* method = p.first;
    const Entry& entry = p.second;
    always_assert(entry.updated_proto->get_args()->size() +
                      (is_static(method) ? 0 : 1) ==
                  entry.live_arg_idxs.size());
    if (!update_method_signature(method, entry.updated_proto,
                                 entry.is_reordered)) {
      continue;
    }

    // Remember entry for further processing, and log statistics
    DexClass* cls = type_class(method->get_class());
    classes.push_back(cls);
    class_entries[cls].push_back(p);
    method_stats.methods_updated_count++;
    method_stats.method_params_removed_count += entry.dead_insns.size();
    method_stats.method_results_removed_count += entry.remove_result ? 1 : 0;
    method_stats.method_protos_reordered_count += entry.is_reordered ? 1 : 0;
  }
  sort_unique(classes);

  // Phase 4: Update body of updated methods (in parallel)

  std::mutex local_dce_stats_mutex;
  auto& local_dce_stats = method_stats.local_dce_stats;
  walk::parallel::classes(classes, [&](DexClass* cls) {
    for (auto& p : class_entries.at(cls)) {
      DexMethod* method = p.first;
      const Entry& entry = p.second;

      if (!entry.is_reordered) {
        if (!entry.dead_insns.empty()) {
          always_assert(method->get_code()->cfg_built());
          auto& cfg = method->get_code()->cfg();
          // We update the method signature, so we must remove unused
          // OPCODE_LOAD_PARAM_* to satisfy IRTypeChecker.
          for (const auto& dead_insn : entry.dead_insns) {
            cfg.remove_insn(dead_insn);
          }
        }
        m_live_arg_idxs_map.emplace(method, entry.live_arg_idxs);
      }

      if (entry.remove_result && method->get_code() != nullptr) {
        always_assert(method->get_code()->cfg_built());
        auto& cfg = method->get_code()->cfg();
        for (const auto& mie : InstructionIterable(cfg)) {
          auto* insn = mie.insn;
          if (opcode::is_a_return_value(insn->opcode())) {
            insn->set_opcode(OPCODE_RETURN_VOID);
            insn->set_srcs_size(0);
          }
        }

        run_cleanup(method,
                    cfg,
                    &m_init_classes_with_side_effects,
                    m_pure_methods,
                    local_dce_stats_mutex,
                    local_dce_stats);
      }

      if (entry.is_reordered) {
        auto idxs = update_method_body_for_reordered_proto(
            method, entry.original_proto, entry.updated_proto);
        m_live_arg_idxs_map.emplace(method, std::move(idxs));
      }
    }
  });
  return method_stats;
}

/**
 * Removes dead arguments from the given invoke instr if applicable.
 * Returns the number of arguments removed.
 */
size_t RemoveArgs::update_callsite(IRInstruction* instr) {
  auto* method = instr->get_method()->as_def();
  if (method == nullptr) {
    // TODO: Properly resolve method.
    return 0;
  };

  auto kv_pair = m_live_arg_idxs_map.find(method);
  if (kv_pair == m_live_arg_idxs_map.end()) {
    // No removable arguments, so do nothing.
    return 0;
  }
  auto& updated_srcs = kv_pair->second;
  std::vector<reg_t> new_srcs;
  new_srcs.reserve(updated_srcs.size());
  for (size_t i = 0; i < updated_srcs.size(); ++i) {
    new_srcs.push_back(instr->src(updated_srcs.at(i)));
  }
  for (size_t i = 0; i < new_srcs.size(); ++i) {
    instr->set_src(i, new_srcs.at(i));
  }
  always_assert_log(instr->srcs_size() >= updated_srcs.size(),
                    "In RemoveArgs, callsites always update to fewer args, or "
                    "same in case of reordering\n");
  auto callsite_args_removed = instr->srcs_size() - updated_srcs.size();
  instr->set_srcs_size(updated_srcs.size());
  return callsite_args_removed;
}

/**
 * Removes unused arguments at callsites and returns the number of arguments
 * removed.
 */
std::pair<size_t, LocalDce::Stats> RemoveArgs::update_callsites() {
  // Walk through all methods to look for and edit callsites.
  std::mutex local_dce_stats_mutex;
  LocalDce::Stats local_dce_stats{};
  auto cnt = walk::parallel::methods<size_t>(
      m_scope, [&](DexMethod* method) -> size_t {
        auto* code = method->get_code();
        if (code == nullptr) {
          return 0;
        }
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();
        size_t callsite_args_removed = 0;
        for (const auto& mie : InstructionIterable(cfg)) {
          auto* insn = mie.insn;
          if (opcode::is_an_invoke(insn->opcode())) {
            size_t insn_args_removed = update_callsite(insn);
            if (insn_args_removed > 0) {
              log_opt(CALLSITE_ARGS_REMOVED, method, insn);
              callsite_args_removed += insn_args_removed;
            }
          }
        }

        if (callsite_args_removed != 0u) {
          run_cleanup(method,
                      cfg,
                      &m_init_classes_with_side_effects,
                      m_pure_methods,
                      local_dce_stats_mutex,
                      local_dce_stats);
        }

        return callsite_args_removed;
      });
  return std::make_pair(cnt, local_dce_stats);
}

void RemoveUnusedArgsPass::run_pass(DexStoresVector& stores,
                                    ConfigFiles& conf,
                                    PassManager& mgr) {
  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  size_t num_callsite_args_removed = 0;
  size_t num_method_params_removed = 0;
  size_t num_methods_updated = 0;
  size_t num_method_results_removed_count = 0;
  size_t num_method_protos_reordered_count = 0;
  size_t num_iterations = 0;
  LocalDce::Stats local_dce_stats;
  auto pure_methods = get_pure_methods();
  while (true) {
    num_iterations++;
    RemoveArgs rm_args(scope, init_classes_with_side_effects, m_blocklist,
                       pure_methods, m_total_iterations++);
    auto pass_stats = rm_args.run(conf);
    if (pass_stats.methods_updated_count == 0) {
      break;
    }
    num_callsite_args_removed += pass_stats.callsite_args_removed_count;
    num_method_params_removed += pass_stats.method_params_removed_count;
    num_methods_updated += pass_stats.methods_updated_count;
    num_method_results_removed_count += pass_stats.method_results_removed_count;
    num_method_protos_reordered_count +=
        pass_stats.method_protos_reordered_count;
    local_dce_stats += pass_stats.local_dce_stats;
  }

  TRACE(ARGS,
        1,
        "Removed %zu redundant callsite arguments",
        num_callsite_args_removed);
  TRACE(ARGS,
        1,
        "Removed %zu redundant method parameters",
        num_method_params_removed);
  TRACE(ARGS,
        1,
        "Removed %zu redundant method results",
        num_method_results_removed_count);
  TRACE(ARGS, 1, "Reordered %zu method protos",
        num_method_protos_reordered_count);
  TRACE(ARGS,
        1,
        "Updated %zu methods with redundant parameters",
        num_methods_updated);

  mgr.set_metric(METRIC_CALLSITE_ARGS_REMOVED, num_callsite_args_removed);
  mgr.set_metric(METRIC_METHOD_PARAMS_REMOVED, num_method_params_removed);
  mgr.set_metric(METRIC_METHODS_UPDATED, num_methods_updated);
  mgr.set_metric(METRIC_METHOD_RESULTS_REMOVED,
                 num_method_results_removed_count);
  mgr.set_metric(METRIC_METHOD_PROTOS_REORDERED,
                 num_method_protos_reordered_count);
  mgr.set_metric(METRIC_DEAD_INSTRUCTION_COUNT,
                 local_dce_stats.dead_instruction_count);
  mgr.set_metric(METRIC_UNREACHABLE_INSTRUCTION_COUNT,
                 local_dce_stats.unreachable_instruction_count);
  mgr.set_metric(METRIC_ITERATIONS, num_iterations);
}

static RemoveUnusedArgsPass s_pass;
} // namespace remove_unused_args
