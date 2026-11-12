/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "KotlinCompanionOptimizationPass.h"

#include "AtomicStatCounter.h"
#include "CFGMutation.h"
#include "ClassHierarchy.h"
#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "LiveRange.h"
#include "Mutators.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeInference.h"
#include "Walkers.h"

namespace {
void dump_cls(DexClass* cls, int trace_level = 5) {
  TRACE(KOTLIN_COMPANION, trace_level, "Class %s", SHOW(cls));
  std::vector<DexMethod*> methods = cls->get_all_methods();
  std::vector<DexField*> fields = cls->get_all_fields();
  for (auto* v : fields) {
    TRACE(KOTLIN_COMPANION, trace_level, "  Field %s", SHOW(v));
  }
  for (auto* v : methods) {
    TRACE(KOTLIN_COMPANION, trace_level, "  Method %s", SHOW(v));
    if (v->get_code() != nullptr) {
      TRACE(KOTLIN_COMPANION, trace_level, "  %s", SHOW(v->get_code()));
    }
  }
}

// Check if the method uses the first argument (i.e this pointer) in a
// meaningful way.  Uses of `this` solely to invoke virtual or direct methods on
// the same class are not considered meaningful because those call sites will be
// rewritten to static dispatch after relocation.
bool uses_this(const DexMethod* method) {
  const auto* code = method->get_code();
  always_assert(code->cfg_built());
  const auto& cfg = code->cfg();
  auto iterable = InstructionIterable(cfg.get_param_instructions());
  if (is_static(method)) {
    // MethodDevirtualizationPass may staticize companion methods, removing
    // the implicit `this` parameter.  However, @Synchronized companion
    // methods retain the companion instance as an explicit first parameter
    // (the proto changes to include the companion type).  We must still
    // analyze these methods for `this` usage (e.g., MONITOR_ENTER).
    //
    // Detect the kept companion instance by checking if the first proto
    // argument type matches the method's declaring class.
    if (iterable.empty()) {
      return false;
    }
    auto* first_insn = iterable.begin()->insn;
    if (first_insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT) {
      // First param is a primitive — can't be the companion instance.
      return false;
    }
    auto* args = method->get_proto()->get_args();
    if (args->empty() || args->at(0) != method->get_class()) {
      // First proto arg is not the companion type — `this` was truly removed.
      return false;
    }
    // First proto arg IS the companion type — companion instance is kept
    // as explicit first parameter.  Fall through to analyze.
  }
  always_assert(!iterable.empty());
  live_range::MoveAwareChains chains(cfg);
  live_range::Uses first_load_param_uses;

  auto* first_load_param = iterable.begin()->insn;
  first_load_param_uses =
      std::move(chains.get_def_use_chains()[first_load_param]);
  if (first_load_param_uses.empty()) {
    // "this" is not used.
    return false;
  }

  for (auto use : UnorderedIterable(first_load_param_uses)) {
    if ((use.insn->opcode() == OPCODE_INVOKE_VIRTUAL ||
         use.insn->opcode() == OPCODE_INVOKE_DIRECT) &&
        use.insn->get_method()->get_class() == method->get_class()) {
      continue;
    }
    return true;
  }

  return false;
}

// Rewrite same-class invoke-virtual/invoke-direct calls on `this` to
// invoke-static dispatch, stripping the `this` argument.  Dead move-object
// copies of `this` are left in place for LocalDcePass to clean up.
//
// Must be called for ALL companion methods BEFORE any are relocated, so that
// callee method refs still belong to the companion class.
//
// Precondition: `uses_this(method)` returned false, meaning the only uses of
// `this` are same-class invoke-virtual/invoke-direct calls.
void rewrite_this_calls_to_static(DexMethod* method) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return;
  }
  auto& cfg = code->cfg();
  auto param_insns = InstructionIterable(cfg.get_param_instructions());
  if (param_insns.empty()) {
    return;
  }
  auto* first_load_param = param_insns.begin()->insn;

  // Find all end-uses of `this` through move chains and rewrite same-class
  // invokes to static dispatch.
  live_range::MoveAwareChains chains(cfg);
  auto du_chains = chains.get_def_use_chains();
  auto du_it = du_chains.find(first_load_param);
  if (du_it == du_chains.end()) {
    return;
  }

  for (auto use : UnorderedIterable(du_it->second)) {
    auto* insn = use.insn;
    always_assert((insn->opcode() == OPCODE_INVOKE_VIRTUAL ||
                   insn->opcode() == OPCODE_INVOKE_DIRECT) &&
                  insn->get_method()->get_class() == method->get_class());
    insn->set_opcode(OPCODE_INVOKE_STATIC);
    auto nargs = insn->srcs_size();
    for (uint16_t i = 0; i < nargs - 1; i++) {
      insn->set_src(i, insn->src(i + 1));
    }
    insn->set_srcs_size(nargs - 1);
  }

  // Any dead move-object copies of `this` are left in place — they are
  // harmless and will be cleaned up by LocalDcePass.
}

// Make method static (if necessary) and relocate to TO_TYPE.
// Drops the `this` parameter because candidate filtering already rejected any
// companion whose methods use `this` in a meaningful way, and intra-companion
// `this` calls have been rewritten to static dispatch by the caller.
//
// When @JvmStatic creates a bridge on the outer class with the same name and
// proto, relocate_method would rename the companion method to avoid the
// collision.  To prevent this, we rename the colliding bridge out of the way
// first — it simply delegates to the companion and is dead code after
// relocation.  The companion method then takes its natural name on the outer
// class, and callers of the bridge's DexMethodRef are unaffected because the
// bridge retains its own (now renamed) DexMethodRef.
void make_static_and_relocate_method(DexMethod* method, DexType* to_type) {
  if (!is_static(method)) {
    mutators::make_static(method, mutators::KeepThis::No);
  }
  // Kotlin marks companion methods final, but interface methods must not be
  // final (JVMS 4.6).
  if (is_interface(type_class(to_type))) {
    method->set_access(method->get_access() & ~ACC_FINAL);
  }
  change_visibility(method, to_type);

  // @JvmStatic generates a static bridge on the outer class with the same
  // name and proto as the companion method.  After make_static(KeepThis::No),
  // the companion method has the same proto, so relocation would collide.
  // Rename the bridge to free the name for the companion method.
  // Non-static collisions (e.g., the outer class has its own virtual method
  // with the same name) are handled by relocate_method's rename_on_collision.
  auto* existing =
      DexMethod::get_method(to_type, method->get_name(), method->get_proto());
  if (existing != nullptr && existing->is_def() &&
      is_static(existing->as_def())) {
    auto* existing_def = existing->as_def();
    // Do not rename the bridge if it's native (JNI depends on the exact name)
    // or if it can't be renamed (e.g., kept by a proguard rule for reflection
    // like `-keepclassmembers ... parseFromJson`).
    if (is_native(existing_def) || !can_rename(existing_def)) {
      TRACE(KOTLIN_COMPANION,
            5,
            "Skip renaming bridge %s (native=%d, can_rename=%d)",
            SHOW(existing),
            is_native(existing_def),
            can_rename(existing_def));
      // Fall through to relocate_method which will rename the companion
      // method on collision instead.
    } else {
      TRACE(KOTLIN_COMPANION,
            5,
            "Renaming colliding @JvmStatic bridge %s",
            SHOW(existing));
      DexMethodSpec rename_spec;
      rename_spec.name = DexString::make_string(
          existing_def->get_name()->str() + "$companion_bridge");
      existing_def->change(rename_spec, true /* rename_on_collision */);
    }
  }

  relocate_method(method, to_type);
}

// \returns true if \p meth meets kotlin companion class <init> request.
// \returns false otherwise.
bool is_valid_init(DexMethod* meth) {
  if (!method::is_init(meth)) {
    return false;
  }
  DexType* return_type = meth->get_proto()->get_rtype();
  DexTypeList* args = meth->get_proto()->get_args();
  if (!type::is_void(return_type) || args->size() > 1) {
    return false;
  }

  TRACE(KOTLIN_COMPANION, 5, "Valid init: %s", SHOW(meth));
  // ()V
  if (args->empty()) {
    return true;
  }
  // (arg1)V
  // invoke-direct cls.<init>:()V or
  // invoke-direct Ljava/lang/Object;.<init>:()V
  // return-void
  auto& init_cfg = meth->get_code()->cfg();
  auto iterable = cfg::InstructionIterable(init_cfg);
  for (auto it = iterable.begin(); it != iterable.end(); it++) {
    auto* insn = it->insn;
    switch (insn->opcode()) {
    case OPCODE_MOVE_OBJECT:
    case OPCODE_RETURN_VOID:
    case IOPCODE_LOAD_PARAM_OBJECT:
      break;
    case OPCODE_INVOKE_DIRECT: {
      auto* cls = type_class(insn->get_method()->get_class());
      if (!method::is_init(insn->get_method()) ||
          (cls != type_class(meth->get_class()) &&
           cls->get_type() != type::java_lang_Object())) {
        return false;
      }
      break;
    }
    default:
      return false;
    }
  }
  return true;
}

// Check whether a companion's <clinit> only does field initialization.
// A "field-init-only" clinit contains only sput-*, const-*, new-instance,
// invoke-direct <init>, load-param, move-*, and return-void — the pattern
// Kotlin generates for `const val` properties.
bool is_clinit_field_init_only(DexMethod* clinit) {
  auto* code = clinit->get_code();
  if (code == nullptr) {
    return false;
  }
  auto& cfg = code->cfg();
  for (const auto& mie : cfg::InstructionIterable(cfg)) {
    auto op = mie.insn->opcode();
    if (opcode::is_a_load_param(op) || opcode::is_a_move(op) ||
        opcode::is_a_const(op) || opcode::is_an_sput(op) ||
        op == OPCODE_NEW_INSTANCE || op == OPCODE_RETURN_VOID ||
        op == OPCODE_INVOKE_DIRECT || op == OPCODE_NEW_ARRAY ||
        op == OPCODE_FILLED_NEW_ARRAY || op == OPCODE_CHECK_CAST ||
        op == OPCODE_SGET_OBJECT || op == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
      continue;
    }
    return false;
  }
  return true;
}

enum class RejectionReason {
  kAccepted,
  kRootedOrExternal,
  kNotCompanion,
  kHasSubclasses,
  kHasIfields,
  kHasInterfaces,
  kHasClinit,
  kHasSfields,
  kNonObjectSuper,
  kNoOuterClass,
  kMultipleCompanionSfields,
  kInvalidInit,
  kMethodNotRelocatable,
};

// Check if CLS is a companion object eligible for relocation.
// Requirements:
// 1. Inner Object class ending with "$Companion"
// 2. No <clinit>, OR clinit only initializes $$INSTANCE (the companion
//    singleton) with no other static fields
// 3. No instance fields; properties are lifted to the outer class
// 4. CLS has no subclasses (or is final) and extends java.lang.Object
// 5. Outer class exists and has at most one sfield of the companion type
// If eligible, return {kAccepted, outer_cls}; otherwise the rejection reason.
std::pair<RejectionReason, DexClass*> candidate_for_companion_relocation(
    DexClass* cls, const ClassHierarchy& ch) {
  if (root(cls) || !can_rename(cls) || !can_delete(cls) ||
      cls->rstate.is_referenced_by_resource_xml() || cls->is_external()) {
    return {RejectionReason::kRootedOrExternal, nullptr};
  }
  // Only consider classes whose name ends with "$Companion" — the default
  // Kotlin companion object naming convention.
  const auto cls_name = cls->get_name()->str();
  if (!cls_name.ends_with("$Companion;")) {
    return {RejectionReason::kNotCompanion, nullptr};
  }
  if (!is_final(cls) && !get_children(ch, cls->get_type()).empty()) {
    return {RejectionReason::kHasSubclasses, nullptr};
  }
  if (!cls->get_ifields().empty()) {
    return {RejectionReason::kHasIfields, nullptr};
  }
  if (!cls->get_interfaces()->empty()) {
    return {RejectionReason::kHasInterfaces, nullptr};
  }
  // Accept companions whose only static field is $$INSTANCE (the companion
  // singleton) and whose clinit only initializes it.  After all methods are
  // relocated and call sites rewritten, $$INSTANCE and the clinit become
  // dead code and are cleaned up by later passes.
  if (cls->get_clinit() != nullptr) {
    const auto& sfields = cls->get_sfields();
    bool instance_only = sfields.size() == 1 &&
                         sfields[0]->get_type() == cls->get_type() &&
                         is_clinit_field_init_only(cls->get_clinit());
    if (!instance_only) {
      TRACE(KOTLIN_COMPANION, 3, "Rejected (has_clinit):");
      dump_cls(cls, 3);
      return {RejectionReason::kHasClinit, nullptr};
    }
  } else if (!cls->get_sfields().empty()) {
    return {RejectionReason::kHasSfields, nullptr};
  }
  if (cls->get_super_class() != type::java_lang_Object()) {
    return {RejectionReason::kNonObjectSuper, nullptr};
  }
  // Derive the outer class by stripping the "$Companion;" suffix.
  auto outer_name = cls_name.substr(0, cls_name.rfind('$')) + ";";
  DexType* outer_type = DexType::get_type(outer_name);
  if (outer_type == nullptr) {
    return {RejectionReason::kNoOuterClass, nullptr};
  }
  DexClass* outer_cls = type_class(outer_type);
  if (outer_cls == nullptr || outer_cls->is_external()) {
    return {RejectionReason::kNoOuterClass, nullptr};
  }

  bool found = false;
  for (auto* sfield : outer_cls->get_sfields()) {
    if (sfield->get_type() == cls->get_type()) {
      if (found) {
        // Expect only one sfield in outer class to hold companion object
        // instance
        TRACE(KOTLIN_COMPANION, 5, "Rejected cls = %s", SHOW(cls));
        return {RejectionReason::kMultipleCompanionSfields, nullptr};
      }
      found = true;
    }
  }

  // Check each method for relocatability.  In addition to the class-level
  // root/can_rename/can_delete checks, individual methods may have keep rules
  // (e.g., @DoNotStrip) that prevent relocation.  Methods involved in JNI
  // bindings (fbjni HybridData pattern) are annotated @DoNotStrip, which makes
  // can_rename return false.
  for (auto* meth : cls->get_vmethods()) {
    // No need to check is_final(meth) — the class-level hierarchy check
    // already guarantees no subclasses, so no virtual method can be overridden.
    if (root(meth) || !can_rename(meth) || meth->rstate.no_optimizations() ||
        (meth->get_code() == nullptr) || uses_this(meth)) {
      TRACE(KOTLIN_COMPANION, 5, "Method not relocatable: %s", SHOW(meth));
      return {RejectionReason::kMethodNotRelocatable, nullptr};
    }
  }

  for (auto* meth : cls->get_dmethods()) {
    if (method::is_clinit(meth)) {
      continue; // Already handled above.
    }
    if (method::is_init(meth)) {
      if (!is_valid_init(meth)) {
        TRACE(KOTLIN_COMPANION, 5, "invalid init = %s", SHOW(meth));
        return {RejectionReason::kInvalidInit, nullptr};
      }
    } else if (root(meth) || !can_rename(meth) ||
               meth->rstate.no_optimizations() ||
               (meth->get_code() == nullptr) || uses_this(meth)) {
      TRACE(KOTLIN_COMPANION, 5, "Method not relocatable: %s", SHOW(meth));
      return {RejectionReason::kMethodNotRelocatable, nullptr};
    }
  }

  if (outer_cls->rstate.is_referenced_by_resource_xml()) {
    return {RejectionReason::kRootedOrExternal, nullptr};
  }
  return {RejectionReason::kAccepted, outer_cls};
}

void relocate(DexClass* comp_cls,
              DexClass* outer_cls,
              UnorderedSet<DexMethodRef*>& relocated_methods) {
  always_assert(comp_cls->get_ifields().empty());
  // Companion may have $$INSTANCE sfield (its own singleton); all other
  // sfields should have been rejected by candidate_for_companion_relocation.
  for (auto* sf : comp_cls->get_sfields()) {
    always_assert(sf->get_type() == comp_cls->get_type());
  }

  TRACE(KOTLIN_COMPANION, 5, "Before Relocating, the comp_cls is:");
  dump_cls(comp_cls);
  TRACE(KOTLIN_COMPANION, 5, "Before Relocating, the outer_cls is:");
  dump_cls(outer_cls);

  // NOTE: We intentionally do NOT remove the Companion sfield or clean up
  // the clinit here in Phase 3.  The renamed @JvmStatic bridge body still
  // references the field.  Phase 4 nullifies all sget-object reads first,
  // then Phase 5 safely removes the field and clinit construction.

  // Relocate methods from comp_cls to outer_cls.
  // Two passes are needed: first rewrite intra-companion `this` calls to static
  // dispatch across ALL methods, then make each method static and relocate.
  // This ordering is critical because `rewrite_this_calls_to_static` checks
  // that callee methods belong to the same class as the caller — if we
  // relocated some methods first, their class would already be the outer class,
  // causing the check to fail.
  std::vector<DexMethod*> methods = comp_cls->get_all_methods();
  for (auto* method : methods) {
    if (method::is_init(method) || method::is_clinit(method) ||
        is_static(method)) {
      continue;
    }
    rewrite_this_calls_to_static(method);
  }
  for (auto* method : methods) {
    if (method::is_init(method) || method::is_clinit(method)) {
      continue;
    }
    TRACE(KOTLIN_COMPANION,
          5,
          "Relocating :(%s)  %s -> %s",
          SHOW(method),
          SHOW(comp_cls),
          SHOW(outer_cls));
    make_static_and_relocate_method(method, outer_cls->get_type());
    relocated_methods.insert(method);
  }

  TRACE(KOTLIN_COMPANION, 5, "After relocating, the comp class is:");
  dump_cls(comp_cls);
  TRACE(KOTLIN_COMPANION, 5, "After relocating, the outer class is:");
  dump_cls(outer_cls);
}

bool is_def_trackable(IRInstruction* insn,
                      const DexClass* from,
                      const DexClass* outer,
                      live_range::MoveAwareChains& move_aware_chains) {
  auto du_chains_move_aware = move_aware_chains.get_def_use_chains();
  if (du_chains_move_aware.count(insn) == 0u) {
    // No use insns.
    return true;
  }
  const auto& use_set = du_chains_move_aware.at(insn);
  for (const auto& p : UnorderedIterable(use_set)) {
    auto* use_insn = p.insn;
    auto use_index = p.src_index;
    switch (use_insn->opcode()) {
    case OPCODE_MOVE_OBJECT:
      break;
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_VIRTUAL:
      if (use_index != 0 ||
          type_class(use_insn->get_method()->get_class()) != from) {
        TRACE(KOTLIN_COMPANION,
              2,
              "Adding cls %s to bad list due to insn %s",
              SHOW(from),
              SHOW(use_insn));
        return false;
      }
      break;
    case OPCODE_SPUT_OBJECT: {
      // Standard Kotlin clinit initialization pattern:
      //   sget-object v0, Companion.$INSTANCE
      //   sput-object v0, OuterClass.Companion
      // The companion instance is loaded and stored to the outer class's
      // Companion field.  This is safe — the SPUT_OBJECT case in
      // filter_untrackable_usages already validates clinit stores.
      auto* field = use_insn->get_field();
      if (type_class(field->get_class()) == outer &&
          field->get_type() == from->get_type()) {
        break;
      }
      TRACE(KOTLIN_COMPANION,
            2,
            "Adding cls %s to bad list due to insn %s",
            SHOW(from),
            SHOW(use_insn));
      return false;
    }
    default:
      TRACE(KOTLIN_COMPANION,
            2,
            "Adding cls %s to bad list due to insn %s",
            SHOW(from),
            SHOW(use_insn));
      return false;
    }
  }
  return true;
}

// Per-reason rejection counts from structural candidate checks.
struct RejectionCounts {
  AtomicStatCounter<size_t> rooted_or_external{0};
  AtomicStatCounter<size_t> not_companion{0};
  AtomicStatCounter<size_t> has_subclasses{0};
  AtomicStatCounter<size_t> has_sfields{0};
  AtomicStatCounter<size_t> has_clinit{0};
  AtomicStatCounter<size_t> has_interfaces{0};
  AtomicStatCounter<size_t> has_ifields{0};
  AtomicStatCounter<size_t> non_object_super{0};
  AtomicStatCounter<size_t> no_outer_class{0};
  AtomicStatCounter<size_t> multiple_companion_sfields{0};
  AtomicStatCounter<size_t> invalid_init{0};
  AtomicStatCounter<size_t> method_not_relocatable{0};
  AtomicStatCounter<size_t> cross_store{0};
};

// Phase 1: Structural candidate collection + duplicate outer class filtering.
// Fills `candidates` with companion->outer mappings that pass structural
// checks. Adds companions with duplicate outer classes to `rejected`. Populates
// `counts` with per-reason rejection tallies.
void collect_candidates(
    const Scope& scope,
    const DexStoresVector& stores,
    const UnorderedSet<DexType*>& do_not_relocate_set,
    InsertOnlyConcurrentMap<DexClass*, DexClass*>& candidates,
    ConcurrentSet<DexClass*>& rejected,
    RejectionCounts& counts) {
  ClassHierarchy ch = build_type_hierarchy(scope);
  // Build a type→store index map for cross-store checks.
  UnorderedMap<const DexType*, size_t> store_indices;
  for (size_t i = 0; i < stores.size(); ++i) {
    for (const auto& dex : stores[i].get_dexen()) {
      for (auto* cls : dex) {
        store_indices.emplace(cls->get_type(), i);
      }
    }
  }
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (do_not_relocate_set.count(cls->get_type()) != 0u) {
      return;
    }
    auto [reason, outer_cls] = candidate_for_companion_relocation(cls, ch);
    switch (reason) {
    case RejectionReason::kNotCompanion:
      ++counts.not_companion;
      return;
    case RejectionReason::kHasSubclasses:
      ++counts.has_subclasses;
      return;
    case RejectionReason::kHasSfields:
      ++counts.has_sfields;
      return;
    case RejectionReason::kHasClinit:
      ++counts.has_clinit;
      return;
    case RejectionReason::kHasInterfaces:
      ++counts.has_interfaces;
      return;
    case RejectionReason::kHasIfields:
      ++counts.has_ifields;
      return;
    case RejectionReason::kNonObjectSuper:
      ++counts.non_object_super;
      return;
    case RejectionReason::kNoOuterClass:
      ++counts.no_outer_class;
      return;
    case RejectionReason::kInvalidInit:
      ++counts.invalid_init;
      return;
    case RejectionReason::kMethodNotRelocatable:
      ++counts.method_not_relocatable;
      return;
    case RejectionReason::kRootedOrExternal:
      ++counts.rooted_or_external;
      return;
    case RejectionReason::kMultipleCompanionSfields:
      ++counts.multiple_companion_sfields;
      return;
    case RejectionReason::kAccepted:
      break;
    }
    if (do_not_relocate_set.count(outer_cls->get_type()) == 0u) {
      // Reject if companion and outer are in different stores — relocating
      // methods across stores would break OptimizeStores assumptions.
      auto cls_it = store_indices.find(cls->get_type());
      auto outer_it = store_indices.find(outer_cls->get_type());
      if (cls_it == store_indices.end() || outer_it == store_indices.end() ||
          cls_it->second != outer_it->second) {
        ++counts.cross_store;
        TRACE(KOTLIN_COMPANION, 2, "Rejected (cross_store): %s -> %s",
              SHOW(cls), SHOW(outer_cls));
        return;
      }
      // This is a candidate for relocation
      candidates.insert(std::make_pair(cls, outer_cls));
      TRACE(KOTLIN_COMPANION, 2, "Candidate cls : %s", SHOW(cls));
    }
  });

  // Filter out companions with duplicate outer classes.
  UnorderedMap<DexClass*, unsigned> outer_cls_count;
  for (auto& iter : UnorderedIterable(candidates)) {
    outer_cls_count[iter.second]++;
  }
  for (auto iter : UnorderedIterable(candidates)) {
    if (outer_cls_count.find(iter.second)->second != 1) {
      rejected.insert(iter.first);
    }
  }
}

// Phase 2: Full-program safety analysis.
// Scans all methods for unsafe uses of companion instances and adds them to
// `rejected`.
void filter_untrackable_usages(
    const Scope& scope,
    const InsertOnlyConcurrentMap<DexClass*, DexClass*>& candidates,
    ConcurrentSet<DexClass*>& rejected) {
  // Returns true if `from` is not a candidate or is already rejected.
  auto skip = [&](DexClass* from) {
    return from == nullptr || candidates.count(from) == 0u ||
           rejected.count(from) != 0u;
  };

  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr) {
      return;
    }

    // We cannot relocate returning companion object.
    auto* rtype = type_class(method->get_proto()->get_rtype());
    if ((rtype != nullptr) && (candidates.count(rtype) != 0u)) {
      rejected.insert(rtype);
      TRACE(KOTLIN_COMPANION,
            2,
            "Method %s returns companion object %s",
            SHOW(method),
            SHOW(rtype));
    }

    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    auto iterable = cfg::InstructionIterable(cfg);
    live_range::MoveAwareChains move_aware_chains(cfg);
    // TypeInference is expensive — only construct it lazily for APUT/AGET.
    std::unique_ptr<type_inference::TypeInference> type_inference;
    auto get_type_environments = [&]() -> const auto& {
      if (!type_inference) {
        type_inference = std::make_unique<type_inference::TypeInference>(cfg);
        type_inference->run(method);
      }
      return type_inference->get_type_environments();
    };

    // Helper: returns true if this method is a clinit of the companion's
    // outer class or the companion class itself.
    auto is_companion_clinit = [&](DexClass* companion) {
      if (!method::is_clinit(method)) {
        return false;
      }
      auto* method_cls = type_class(method->get_class());
      return method_cls == candidates.find(companion)->second ||
             method_cls == companion;
    };

    for (auto it = iterable.begin(); it != iterable.end(); it++) {
      auto* insn = it->insn;
      switch (insn->opcode()) {
      case OPCODE_SPUT_OBJECT: {
        auto* from = type_class(insn->get_field()->get_type());
        if (skip(from) || is_companion_clinit(from)) {
          break;
        }
        rejected.insert(from);
        break;
      }

      case OPCODE_IPUT_OBJECT:
      case OPCODE_IGET_OBJECT: {
        auto* from = type_class(insn->get_field()->get_type());
        if (skip(from)) {
          break;
        }
        rejected.insert(from);
        break;
      }

      case OPCODE_SGET_OBJECT: {
        auto* from = type_class(insn->get_field()->get_type());
        if (skip(from)) {
          break;
        }
        auto* outer = candidates.find(from)->second;
        if (!is_def_trackable(insn, from, outer, move_aware_chains)) {
          rejected.insert(from);
        }
        break;
      }

      case OPCODE_INSTANCE_OF: {
        auto* from = type_class(insn->get_type());
        if (skip(from) || is_companion_clinit(from)) {
          break;
        }
        rejected.insert(from);
        break;
      }

      case OPCODE_NEW_INSTANCE: {
        auto* from = type_class(insn->get_type());
        if (skip(from)) {
          break;
        }
        if (is_companion_clinit(from)) {
          // D8 may reuse the new-instance register after sput-object
          // (e.g., TAG = Companion.javaClass.simpleName compiles to
          // getClass() on the same register).  Reject if the register
          // has uses beyond <init> and sput-object — Phase 5 cannot
          // safely nullify the new-instance.
          auto* outer = candidates.find(from)->second;
          if (type_class(method->get_class()) == outer) {
            auto du = move_aware_chains.get_def_use_chains();
            auto mov_it = cfg.move_result_of(it);
            IRInstruction* def_insn = nullptr;
            if (!mov_it.is_end() && du.count(mov_it->insn) != 0u) {
              def_insn = mov_it->insn;
            } else if (du.count(insn) != 0u) {
              def_insn = insn;
            }
            if (def_insn != nullptr) {
              for (const auto& use : UnorderedIterable(du.at(def_insn))) {
                auto* u = use.insn;
                // Allow companion construction sequence.
                if ((opcode::is_an_invoke(u->opcode()) &&
                     method::is_init(u->get_method()) &&
                     u->get_method()->get_class() == from->get_type()) ||
                    (opcode::is_an_sput(u->opcode()) &&
                     u->get_field()->get_type() == from->get_type()) ||
                    opcode::is_a_move(u->opcode())) {
                  continue;
                }
                rejected.insert(from);
                TRACE(KOTLIN_COMPANION,
                      2,
                      "Reject %s: new-instance register reused in "
                      "clinit by %s",
                      SHOW(from),
                      SHOW(u));
                break;
              }
            }
          }
          break;
        }
        rejected.insert(from);
        break;
      }

      case OPCODE_INVOKE_DIRECT: {
        auto* from = type_class(insn->get_method()->get_class());
        if (!method::is_init(insn->get_method()) || skip(from)) {
          break;
        }
        if ((type_class(method->get_class()) == from &&
             method::is_init(method)) ||
            is_companion_clinit(from)) {
          break;
        }
        rejected.insert(from);
        break;
      }

      case OPCODE_APUT_OBJECT:
      case OPCODE_AGET_OBJECT: {
        const auto& env = get_type_environments().at(insn);
        auto dex_type = env.get_dex_type(insn->src(0));
        if (!dex_type) {
          break;
        }
        DexClass* from;
        if (insn->opcode() == OPCODE_AGET_OBJECT) {
          if (!type::is_array(*dex_type)) {
            break;
          }
          from = type_class(type::make_array_component_type(*dex_type));
        } else {
          from = type_class(*dex_type);
        }
        // Currently, we don't supporting tracking companion object usage in
        // aget/aput_object. Instead, simply insert it into bad list.
        if (skip(from)) {
          break;
        }
        rejected.insert(from);
        TRACE(KOTLIN_COMPANION,
              2,
              "Adding cls %s to bad list due to insn %s",
              SHOW(from),
              SHOW(insn));
        break;
      }
      default:
        if (insn->has_type()) {
          auto* from = type_class(insn->get_type());
          if (skip(from)) {
            break;
          }
          rejected.insert(from);
          TRACE(KOTLIN_COMPANION,
                2,
                "Adding cls %s to bad list due to insn %s",
                SHOW(from),
                SHOW(insn));
          break;
        }
        break;
      }
    }
  });
}

// Phase 3: Relocate companion methods to outer classes.
// Returns the set of relocated method refs, the set of companion types, and
// the count of relocated companions.
struct RelocationResult {
  UnorderedSet<DexMethodRef*> relocated_methods;
  UnorderedSet<DexFieldRef*> companion_fields;
  // Map from outer class to its relocated companion type, used for clinit
  // cleanup.
  UnorderedMap<DexClass*, DexType*> outer_to_companion;
  size_t relocated_count;
};

RelocationResult relocate_companions(
    const InsertOnlyConcurrentMap<DexClass*, DexClass*>& candidates,
    const ConcurrentSet<DexClass*>& rejected) {
  RelocationResult result;
  result.relocated_count = 0;
  for (const auto& p : UnorderedIterable(candidates)) {
    auto* comp_cls = p.first;
    auto* outer_cls = p.second;
    if (rejected.count(comp_cls) != 0u) {
      continue;
    }
    TRACE(KOTLIN_COMPANION,
          2,
          "Relocate : %s -> %s",
          SHOW(comp_cls),
          SHOW(outer_cls));
    relocate(comp_cls, outer_cls, result.relocated_methods);
    // Collect the Companion sfield on the outer class so Phase 4 can
    // nullify dead sget-object loads and clean up the clinit.
    for (auto* sfield : outer_cls->get_sfields()) {
      if (type_class(sfield->get_type()) == comp_cls) {
        result.companion_fields.insert(sfield);
      }
    }
    result.outer_to_companion.emplace(outer_cls, comp_cls->get_type());
    result.relocated_count++;
  }
  return result;
}

// Phase 4: Rewrite call sites from invoke-virtual/direct to invoke-static,
// then remove dead sget-object instructions that loaded companion instances.
void rewrite_call_sites(const Scope& scope,
                        const UnorderedSet<DexMethodRef*>& relocated_methods,
                        const UnorderedSet<DexFieldRef*>& companion_fields) {
  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    auto& cfg = code->cfg();
    auto iterable = cfg::InstructionIterable(cfg);
    bool changed = false;

    // Single pass: rewrite invoke-virtual/direct to invoke-static, and
    // nullify sget-object instructions that load relocated companion
    // instances.  The sget-object has a class-init side effect that prevents
    // LocalDcePass from removing it, so we replace it with const/0 to keep
    // the register defined while making the companion field unread.
    std::unique_ptr<cfg::CFGMutation> mutation;
    for (auto it = iterable.begin(); it != iterable.end(); it++) {
      auto* insn = it->insn;
      if ((insn->opcode() == OPCODE_INVOKE_VIRTUAL ||
           insn->opcode() == OPCODE_INVOKE_DIRECT) &&
          relocated_methods.count(insn->get_method()) != 0u) {
        // Rewrite to static dispatch and strip the companion `this` argument.
        insn->set_opcode(OPCODE_INVOKE_STATIC);
        auto nargs = insn->srcs_size();
        for (uint16_t i = 0; i < nargs - 1; i++) {
          insn->set_src(i, insn->src(i + 1));
        }
        insn->set_srcs_size(nargs - 1);
        changed = true;
      } else if (insn->opcode() == OPCODE_SGET_OBJECT &&
                 companion_fields.count(insn->get_field()) != 0u) {
        auto mov_it = cfg.move_result_of(it);
        if (!mov_it.is_end()) {
          if (!mutation) {
            mutation = std::make_unique<cfg::CFGMutation>(cfg);
          }
          auto* init_null = new IRInstruction(OPCODE_CONST);
          init_null->set_literal(0);
          init_null->set_dest(mov_it->insn->dest());
          TRACE(KOTLIN_COMPANION, 5, "Nullify sget-object %s", SHOW(insn));
          mutation->replace(it, {init_null});
        }
      }
    }
    if (mutation) {
      mutation->flush();
    }
    if (changed) {
      TRACE(KOTLIN_COMPANION, 5, "After : %s", SHOW(method));
      TRACE(KOTLIN_COMPANION, 5, "%s", SHOW(cfg));
    }
  });
}

// Phase 5: Clean up companion initialization in outer class clinits and remove
// the Companion sfield.  After Phase 4 nullified all sget-object reads of the
// companion field, the only remaining references are in the outer class's
// <clinit> (new-instance + invoke-direct <init> + sput-object).  Constructors
// are opaque to LocalDcePass, so we must clean them up explicitly.
void cleanup_clinits_and_fields(
    const UnorderedMap<DexClass*, DexType*>& outer_to_companion,
    const UnorderedSet<DexFieldRef*>& companion_fields) {
  for (const auto& [outer_cls, comp_type] :
       UnorderedIterable(outer_to_companion)) {
    // Clean up the outer class's <clinit>: remove the companion initialization
    // sequence.  Kotlin generates this pattern:
    //   new-instance      vN, Companion
    //   invoke-direct     vN, Companion.<init>:()V
    //   sput-object       vN, OuterClass.Companion
    // We replace new-instance with const/0 (to avoid dangling register uses),
    // and remove the invoke-direct and sput-object.
    if (outer_cls->get_clinit() != nullptr) {
      auto& clinit_cfg = outer_cls->get_clinit()->get_code()->cfg();

      auto is_companion_new_instance = [&](IRInstruction* insn) {
        return opcode::is_new_instance(insn->opcode()) &&
               insn->get_type() == comp_type;
      };
      auto is_companion_init = [&](IRInstruction* insn) {
        return opcode::is_an_invoke(insn->opcode()) &&
               method::is_init(insn->get_method()) &&
               insn->get_method()->get_class() == comp_type;
      };
      auto is_companion_sput = [&](IRInstruction* insn) {
        return opcode::is_an_sput(insn->opcode()) &&
               companion_fields.count(insn->get_field()) != 0u;
      };

      cfg::CFGMutation m(clinit_cfg);
      for (auto it = cfg::InstructionIterable(clinit_cfg).begin();
           it != cfg::InstructionIterable(clinit_cfg).end();
           it++) {
        auto* insn = it->insn;
        if (is_companion_new_instance(insn)) {
          auto mov_result_it = clinit_cfg.move_result_of(it);
          auto* init_null = new IRInstruction(OPCODE_CONST);
          init_null->set_literal(0);
          init_null->set_dest(mov_result_it->insn->dest());
          m.replace(it, {init_null});
          TRACE(KOTLIN_COMPANION, 5, "Nullify insn %s", SHOW(insn));
        } else if (is_companion_init(insn) || is_companion_sput(insn)) {
          m.remove(it);
          TRACE(KOTLIN_COMPANION, 5, "Remove insn %s", SHOW(insn));
        }
      }
      m.flush();
    }

    // Remove the Companion sfield from the outer class.
    std::vector<DexField*> to_remove;
    for (auto* sfield : outer_cls->get_sfields()) {
      if (companion_fields.count(sfield) != 0u) {
        to_remove.push_back(sfield);
      }
    }
    for (auto* f : to_remove) {
      TRACE(KOTLIN_COMPANION, 5, "Remove field %s", SHOW(f));
      outer_cls->remove_field(f);
    }
  }
}

} // namespace

void KotlinCompanionOptimizationPass::run_pass(DexStoresVector& stores,
                                               ConfigFiles&,
                                               PassManager& mgr) {
  const auto scope = build_class_scope(stores);

  UnorderedSet<DexType*> do_not_relocate_set;
  for (auto& p : m_do_not_relocate_list) {
    auto* t = DexType::get_type(p);
    if (t != nullptr) {
      TRACE(KOTLIN_COMPANION, 2, "do_not_relocate_cls  : %s", SHOW(t));
      do_not_relocate_set.insert(t);
    }
  }

  InsertOnlyConcurrentMap<DexClass*, DexClass*> candidates;
  ConcurrentSet<DexClass*> rejected;

  // Phase 1: Collect structurally eligible companion objects.
  RejectionCounts counts;
  collect_candidates(scope, stores, do_not_relocate_set, candidates, rejected,
                     counts);

  // Phase 2: Filter out companions with untrackable usages.
  filter_untrackable_usages(scope, candidates, rejected);

  // Phase 3: Relocate accepted companion methods to outer classes.
  auto relocation = relocate_companions(candidates, rejected);

  // Phase 4: Rewrite call sites to use static dispatch and nullify dead
  // sget-object instructions that loaded companion instances.
  rewrite_call_sites(scope, relocation.relocated_methods,
                     relocation.companion_fields);

  // Phase 5: Clean up companion initialization in outer class clinits and
  // remove the Companion sfield.  This runs after Phase 4 has nullified all
  // external sget-object reads, so the only remaining references are the
  // clinit construction sequence.
  cleanup_clinits_and_fields(relocation.outer_to_companion,
                             relocation.companion_fields);

  // Report stats.
  Stats stats;
  stats.kotlin_candidate_companion_objects = candidates.size();
  stats.kotlin_untrackable_companion_objects = rejected.size();
  stats.kotlin_companion_objects_relocated = relocation.relocated_count;
  stats.kotlin_rejected_rooted_or_external = counts.rooted_or_external;
  stats.kotlin_rejected_has_subclasses = counts.has_subclasses;
  stats.kotlin_rejected_not_companion = counts.not_companion;
  stats.kotlin_rejected_has_sfields = counts.has_sfields;
  stats.kotlin_rejected_has_clinit = counts.has_clinit;
  stats.kotlin_rejected_has_interfaces = counts.has_interfaces;
  stats.kotlin_rejected_has_ifields = counts.has_ifields;
  stats.kotlin_rejected_non_object_super = counts.non_object_super;
  stats.kotlin_rejected_no_outer_class = counts.no_outer_class;
  stats.kotlin_rejected_multiple_companion_sfields =
      counts.multiple_companion_sfields;
  stats.kotlin_rejected_invalid_init = counts.invalid_init;
  stats.kotlin_rejected_method_not_relocatable = counts.method_not_relocatable;
  stats.kotlin_rejected_cross_store = counts.cross_store;
  stats.report(mgr);
}

void KotlinCompanionOptimizationPass::Stats::report(PassManager& mgr) const {
  auto emit = [&](const std::string& name, size_t value) {
    mgr.incr_metric(name, value);
    TRACE(KOTLIN_COMPANION, 2, "%s = %zu", name.c_str(), value);
  };
  TRACE(KOTLIN_COMPANION, 2, "KotlinCompanionOptimizationPass Stats:");
  emit("kotlin_candidate_companion_objects",
       kotlin_candidate_companion_objects);
  emit("kotlin_untrackable_companion_objects",
       kotlin_untrackable_companion_objects);
  emit("kotlin_companion_objects_relocated",
       kotlin_companion_objects_relocated);
  emit("kotlin_rejected_rooted_or_external",
       kotlin_rejected_rooted_or_external);
  emit("kotlin_rejected_has_subclasses", kotlin_rejected_has_subclasses);
  emit("kotlin_rejected_not_companion", kotlin_rejected_not_companion);
  emit("kotlin_rejected_has_sfields", kotlin_rejected_has_sfields);
  emit("kotlin_rejected_has_clinit", kotlin_rejected_has_clinit);
  emit("kotlin_rejected_has_interfaces", kotlin_rejected_has_interfaces);
  emit("kotlin_rejected_has_ifields", kotlin_rejected_has_ifields);
  emit("kotlin_rejected_non_object_super", kotlin_rejected_non_object_super);
  emit("kotlin_rejected_no_outer_class", kotlin_rejected_no_outer_class);
  emit("kotlin_rejected_multiple_companion_sfields",
       kotlin_rejected_multiple_companion_sfields);
  emit("kotlin_rejected_invalid_init", kotlin_rejected_invalid_init);
  emit("kotlin_rejected_method_not_relocatable",
       kotlin_rejected_method_not_relocatable);
  emit("kotlin_rejected_cross_store", kotlin_rejected_cross_store);
}

static KotlinCompanionOptimizationPass s_pass;
