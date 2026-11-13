/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LiftVirtualMethods.h"

#include <algorithm>
#include <map>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "ApiLevelChecker.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DedupVirtualMethods.h"
#include "DexUtil.h"
#include "LiveRange.h"
#include "MethodDedup.h"
#include "MethodFixup.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "SourceBlocks.h"
#include "TypeSystem.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace lift_virtual_methods {
namespace {

DexMethod* declared_method(const DexType* type,
                           const DexString* name,
                           const DexProto* proto) {
  auto* ref = DexMethod::get_method(type, name, proto);
  return ref == nullptr ? nullptr : ref->as_def();
}

bool is_lift_candidate(
    const DexMethod* method,
    const ConcurrentSet<DexMethodRef*>& super_invoked_methods) {
  return is_public(method) && dedup_vmethods::is_removable_copy(method) &&
         super_invoked_methods.count_unsafe(const_cast<DexMethod*>(method)) ==
             0;
}

/**
 * Moving a method into `target` changes the static type of its receiver to
 * `target`. Returns the cast that keeps every use of the receiver type
 * correct: nullptr when `target` already satisfies every use, std::nullopt
 * when no single cast does (or a use is not understood).
 *
 * A D8 forwarder passes its receiver as the interface whose default method it
 * forwards to, which a superclass that does not implement that interface
 * satisfies only after a cast to it.
 */
std::optional<const DexType*> receiver_cast(const DexMethod* method,
                                            const DexType* target) {
  auto demands = live_range::get_receiver_type_demands(method);
  if (!demands) {
    return std::nullopt;
  }
  if (unordered_all_of(*demands, [&](const DexType* demand) {
        return type::check_cast(target, demand);
      })) {
    return nullptr;
  }
  const auto* cast = live_range::reduce_type_demands(*demands);
  if (cast == nullptr) {
    return std::nullopt;
  }
  return cast;
}

void insert_receiver_cast(DexMethod* method, const DexType* cast) {
  auto& cfg = method->get_code()->cfg();
  auto receiver =
      InstructionIterable(cfg.get_param_instructions()).begin()->insn->dest();
  cfg.insert_after_param_loads(
      {(new IRInstruction(OPCODE_CHECK_CAST))
           ->set_type(const_cast<DexType*>(cast))
           ->set_src(0, receiver),
       (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
           ->set_dest(receiver)});
}

// Whether code in `ref_checker`'s store may reference everything that
// `method`'s code and prototype reference.
bool can_move(const RefChecker& ref_checker, const DexMethod* method) {
  return ref_checker.check_proto(method->get_proto()) &&
         ref_checker.check_code_refs(CodeRefs(method));
}

// An identical copy of the lifted method, with each block of the lifted
// method's code paired with its counterpart in the copy.
struct Copy {
  DexMethod* method;
  cfg::ControlFlowGraph::BlockPairing blocks;
};

// What adding `name:proto` to a class changes in the classes below it.
struct SubtreeEffect {
  // Identical copies that the lifted method replaces.
  std::vector<Copy> copies;
  // Classes that inherit the method without inheriting any version of it
  // today.
  std::vector<const DexType*> inheritors;
  // A class whose direct or weaker-access declaration would interact with an
  // inherited public method, or a reference that resolves to nothing today.
  bool conflict{false};
};

/**
 * Walks the classes below `target` down to the first public declaration of
 * `representative`'s signature on each path. An identical lift candidate is a
 * copy and the walk continues below it, since those classes already inherit
 * the method; any other public virtual declaration stays as an override and
 * shields its subtree.
 */
SubtreeEffect analyze_subtree(
    const TypeSystem& type_system,
    const DexClass* target,
    const DexMethod* representative,
    const ConcurrentSet<DexMethodRef*>& super_invoked_methods) {
  const auto* name = representative->get_name();
  const auto* proto = representative->get_proto();
  const auto& cfg = representative->get_code()->cfg();
  SubtreeEffect effect;
  // (class, whether a copy above it already gives it the method)
  std::vector<std::pair<const DexType*, bool>> work{
      {target->get_type(), false}};
  while (!work.empty()) {
    auto [type, below_copy] = work.back();
    work.pop_back();
    for (const auto* child : type_system.get_children(type)) {
      auto* ref = DexMethod::get_method(child, name, proto);
      auto* declared = ref == nullptr ? nullptr : ref->as_def();
      if (declared == nullptr) {
        if (!below_copy) {
          // A reference that resolves to nothing today would start resolving
          // to the lifted method.
          if (ref != nullptr) {
            effect.conflict = true;
            return effect;
          }
          effect.inheritors.push_back(child);
        }
        work.emplace_back(child, below_copy);
        continue;
      }
      if (!declared->is_virtual() || !is_public(declared)) {
        effect.conflict = true;
        return effect;
      }
      if (declared == representative) {
        work.emplace_back(child, true);
        continue;
      }
      // A method that cannot be removed, such as the target of an
      // invoke-super, stays as an override even when its code is identical.
      if (!is_lift_candidate(declared, super_invoked_methods)) {
        continue;
      }
      auto blocks = cfg.structural_block_pairing(declared->get_code()->cfg());
      if (blocks) {
        effect.copies.push_back({declared, std::move(*blocks)});
        work.emplace_back(child, true);
      }
    }
  }
  return effect;
}

/**
 * Whether one of `types` implements an interface that declares
 * `name:proto`, or one whose declarations are unknown. A class that newly
 * inherits the lifted method would otherwise stop reaching the interface's
 * default method through invoke-interface.
 */
bool implements_interface_with(const TypeSystem& type_system,
                               const std::vector<const DexType*>& types,
                               const DexString* name,
                               const DexProto* proto) {
  return std::any_of(types.begin(), types.end(), [&](const DexType* type) {
    const auto& intfs = type_system.get_implemented_interfaces(type);
    return std::any_of(intfs.begin(), intfs.end(), [&](const DexType* intf) {
      return type_class(intf) == nullptr ||
             declared_method(intf, name, proto) != nullptr;
    });
  });
}

/**
 * Whether every block of `representative` that carries source blocks has a
 * counterpart carrying as many in each copy, so that the lifted method can
 * carry the profile of every class that owned a copy. Blocks outside the
 * pairing (unreachable ones and a ghost exit block) carry no profile to merge.
 */
bool source_blocks_line_up(DexMethod* representative,
                           const std::vector<Copy>& copies) {
  auto& cfg = representative->get_code()->cfg();
  return std::all_of(copies.begin(), copies.end(), [&](const Copy& copy) {
    const auto& blocks = cfg.blocks();
    return std::all_of(blocks.begin(), blocks.end(), [&](cfg::Block* block) {
      auto it = copy.blocks.find(block);
      if (it == copy.blocks.end()) {
        return !source_blocks::has_source_blocks(block);
      }
      return source_blocks::have_same_source_block_counts(block, it->second);
    });
  });
}

/**
 * The largest group of identical methods, the first of them by method order
 * among groups of equal size.
 */
const MethodOrderedSet& largest_identical_group(
    const UnorderedBag<MethodOrderedSet>& groups) {
  return *unordered_max_element(groups, [](const auto& a, const auto& b) {
    return a.size() < b.size() ||
           (a.size() == b.size() && compare_dexmethods(*b.begin(), *a.begin()));
  });
}

} // namespace

const char* describe(Rejection rejection) {
  switch (rejection) {
  case Rejection::kFewerThanTwoIdentical:
    return "fewer_than_two_identical";
  case Rejection::kTargetHasMethod:
    return "target_has_method";
  case Rejection::kUnknownAncestor:
    return "unknown_ancestor";
  case Rejection::kAncestorDeclaresMethod:
    return "ancestor_declares_method";
  case Rejection::kApiLevel:
    return "api_level";
  case Rejection::kReceiverType:
    return "receiver_type";
  case Rejection::kRelocation:
    return "relocation";
  case Rejection::kCrossStore:
    return "cross_store";
  case Rejection::kSubtreeConflict:
    return "subtree_conflict";
  case Rejection::kTooManyInheritors:
    return "too_many_inheritors";
  case Rejection::kInterfaceDeclaresMethod:
    return "interface_declares_method";
  case Rejection::kSourceBlockMismatch:
    return "source_block_mismatch";
  case Rejection::kCount:
    break;
  }
  not_reached();
}

Stats lift(const DexStoresVector& stores,
           method_profiles::MethodProfiles& method_profiles,
           bool normal_primary_dex,
           const api::AndroidSDK* min_sdk_api,
           double max_inheritors_per_copy) {
  Stats stats;
  auto scope = build_class_scope(stores);
  TypeSystem type_system(scope);
  XStoreRefs xstores(stores, normal_primary_dex);
  ConcurrentSet<DexMethodRef*> super_invoked_methods;
  dedup_vmethods::collect_all_invoke_super_called(scope,
                                                  &super_invoked_methods);

  // Sibling candidates, grouped by their superclass and signature, in scope
  // order so that the lifting below is deterministic.
  using Key = std::tuple<DexClass*, const DexString*, DexProto*>;
  std::vector<std::pair<Key, std::vector<DexMethod*>>> groups;
  std::map<Key, size_t> group_index;
  for (auto* cls : scope) {
    if (is_interface(cls)) {
      continue;
    }
    auto* target = type_class(cls->get_super_class());
    if (target == nullptr || target->is_external() || is_interface(target)) {
      continue;
    }
    for (auto* method : cls->get_vmethods()) {
      if (!is_lift_candidate(method, super_invoked_methods)) {
        continue;
      }
      Key key{target, method->get_name(), method->get_proto()};
      auto [it, inserted] = group_index.emplace(key, groups.size());
      if (inserted) {
        groups.emplace_back(key, std::vector<DexMethod*>());
      }
      groups.at(it->second).second.push_back(method);
    }
  }

  // Lift into shallower classes first, so that one lift takes the identical
  // deeper copies with it instead of each level lifting its own.
  std::stable_sort(groups.begin(), groups.end(), [&](auto& a, auto& b) {
    return type_system.parent_chain(std::get<0>(a.first)->get_type()).size() <
           type_system.parent_chain(std::get<0>(b.first)->get_type()).size();
  });

  auto reject = [&](Rejection rejection) {
    stats.rejections[static_cast<size_t>(rejection)]++;
  };
  UnorderedMap<DexMethodRef*, DexMethodRef*> removed_vmethods;
  auto removed = [&](auto* m) { return removed_vmethods.count(m) != 0; };
  for (auto& [key, methods] : groups) {
    auto [target, name, proto] = key;
    // A lift into a shallower class may already have removed some of these.
    std::erase_if(methods, removed);
    if (methods.size() < 2) {
      continue;
    }
    const auto identical_groups = method_dedup::group_identical_methods(
        methods, /* dedup_fill_in_stack_trace */ true);
    const auto& identical = largest_identical_group(identical_groups);
    if (identical.size() < 2) {
      reject(Rejection::kFewerThanTwoIdentical);
      continue;
    }
    if (DexMethod::get_method(target->get_type(), name, proto) != nullptr) {
      reject(Rejection::kTargetHasMethod);
      continue;
    }
    // The chain starts at the first class Redex does not know, if any.
    const auto& parents = type_system.parent_chain(target->get_type());
    if (parents.empty() || parents.front() != type::java_lang_Object()) {
      reject(Rejection::kUnknownAncestor);
      continue;
    }
    if (resolve_method(type_class(target->get_super_class()), name, proto,
                       MethodSearch::Any) != nullptr) {
      reject(Rejection::kAncestorDeclaresMethod);
      continue;
    }
    auto* representative = *identical.begin();
    if (target->rstate.get_api_level() <
        api::LevelChecker::get_method_level(representative)) {
      reject(Rejection::kApiLevel);
      continue;
    }
    auto cast = receiver_cast(representative, target->get_type());
    if (!cast) {
      reject(Rejection::kReceiverType);
      continue;
    }
    const bool can_relocate =
        gather_invoked_methods_that_prevent_relocation(representative);
    if (!can_relocate) {
      reject(Rejection::kRelocation);
      continue;
    }
    if (!can_move(RefChecker(&xstores,
                             xstores.get_store_idx(target->get_type()),
                             min_sdk_api),
                  representative)) {
      reject(Rejection::kCrossStore);
      continue;
    }
    auto effect = analyze_subtree(type_system, target, representative,
                                  super_invoked_methods);
    if (effect.conflict) {
      reject(Rejection::kSubtreeConflict);
      continue;
    }
    // `identical` holds at least two direct subclasses of `target`; each one
    // besides the representative is a copy.
    always_assert(!effect.copies.empty());
    // `target` and every class that newly inherits the method gain a vtable
    // slot, which ART stores per class (in the app image for image classes).
    effect.inheritors.push_back(target->get_type());
    if (static_cast<double>(effect.inheritors.size()) >
        max_inheritors_per_copy * static_cast<double>(effect.copies.size())) {
      reject(Rejection::kTooManyInheritors);
      continue;
    }
    if (implements_interface_with(type_system, effect.inheritors, name,
                                  proto)) {
      reject(Rejection::kInterfaceDeclaresMethod);
      continue;
    }
    if (!source_blocks_line_up(representative, effect.copies)) {
      reject(Rejection::kSourceBlockMismatch);
      continue;
    }

    stats.new_vtable_slots += effect.inheritors.size();
    // The lifted method runs whenever one of the copies ran.
    std::vector<DexMethod*> sources{representative};
    for (auto& copy : effect.copies) {
      for (auto* block : representative->get_code()->cfg().blocks()) {
        auto it = copy.blocks.find(block);
        // `source_blocks_line_up` checked the counts.
        always_assert(
            it == copy.blocks.end() ||
            source_blocks::add_source_blocks_pairwise(block, it->second));
      }
      sources.push_back(copy.method);
    }
    method_profiles.substitute_stats(representative, sources);
    if (*cast != nullptr) {
      insert_receiver_cast(representative, *cast);
      stats.receiver_casts++;
    }
    // Also makes the receiver cast accessible from `target`. The relocation
    // check above passed, and the cast refers to a type, not a method.
    always_assert(
        relocate_method_if_no_changes(representative, target->get_type()));
    representative->set_access(representative->get_access() & ~ACC_FINAL);
    // Calls to the copies, from any package, now name `target`.
    set_public(target);
    stats.lifted_methods++;
    for (auto& copy : effect.copies) {
      auto* m = copy.method;
      type_class(m->get_class())->remove_method(m);
      removed_vmethods.emplace(m, representative);
      DexMethod::delete_method(m);
      stats.removed_methods++;
    }
  }

  method_fixup::fixup_references_to_removed_methods(scope, removed_vmethods);
  return stats;
}

} // namespace lift_virtual_methods

void LiftVirtualMethodsPass::bind_config() {
  // A removed copy saves an ArtMethod, which is about the size of four vtable
  // entries.
  bind("max_inheritors_per_copy", 4.0, m_max_inheritors_per_copy,
       "Skip a lift that would add more than this many vtable slots per "
       "removed copy: one in the superclass and one in each class that newly "
       "inherits the method.");
}

void LiftVirtualMethodsPass::run_pass(DexStoresVector& stores,
                                      ConfigFiles& conf,
                                      PassManager& mgr) {
  const auto min_sdk = mgr.get_redex_options().min_sdk;
  const api::AndroidSDK* min_sdk_api = conf.get_android_sdk_api_file(min_sdk)
                                           ? &conf.get_android_sdk_api(min_sdk)
                                           : nullptr;
  auto stats = lift_virtual_methods::lift(
      stores, conf.get_method_profiles(), conf.normal_primary_dex(),
      min_sdk_api, m_max_inheritors_per_copy);
  mgr.incr_metric("num_lifted_methods", stats.lifted_methods);
  mgr.incr_metric("num_removed_lifted_copies", stats.removed_methods);
  mgr.incr_metric("num_receiver_casts", stats.receiver_casts);
  mgr.incr_metric("num_new_vtable_slots", stats.new_vtable_slots);
  for (size_t i = 0; i < stats.rejections.size(); i++) {
    mgr.incr_metric(std::string("rejected.") +
                        lift_virtual_methods::describe(
                            static_cast<lift_virtual_methods::Rejection>(i)),
                    stats.rejections[i]);
  }
}

static LiftVirtualMethodsPass s_pass;
