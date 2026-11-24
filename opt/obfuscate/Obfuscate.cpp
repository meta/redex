/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Obfuscate.h"
#include "ClassHierarchy.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "DexUtil.h"
#include "MethodHandleRewriter.h"
#include "ObfuscateUtils.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "VirtualRenamer.h"
#include "Walkers.h"

namespace {

static const char* METRIC_FIELD_TOTAL = "fields_total";
static const char* METRIC_FIELD_RENAMED = "fields_renamed";
static const char* METRIC_DMETHODS_TOTAL = "dmethods_total";
static const char* METRIC_DMETHODS_RENAMED = "dmethods_renamed";
static const char* METRIC_VMETHODS_TOTAL = "vmethods_total";
static const char* METRIC_VMETHODS_RENAMED = "vmethods_renamed";

/* Obfuscates a list of members
 * RenamingContext - the context that we need to be able to do renaming for this
 *   member. Will not be modified and will be shared between all members in a
 *   class.
 * ObfuscationState - keeps track of the new names we're trying to assign to
 *   members, we update this to show what name we chose for a member. Also
 *   contains a set of all used names in this class because that needs to be
 *   updated every time we choose a name.
 * returns the number of find_new_name calls done
 */
template <class T, class R, class S, class K>
int obfuscate_elems(const RenamingContext<T>& context,
                    DexElemManager<T, R, S, K>& name_mapping) {
  int num_renames = 0;
  for (T elem : context.elems) {
    if (!context.can_rename_elem(elem) ||
        !name_mapping[elem]->should_rename()) {
      TRACE(OBFUSCATE, 4, "Ignoring member %s because we shouldn't rename it",
            SHOW(elem->get_name()));
      continue;
    }
    context.name_gen.find_new_name(name_mapping[elem]);
    num_renames++;
  }
  return num_renames;
}

void debug_logging(std::vector<DexClass*>& classes) {
  for (DexClass* cls : classes) {
    TRACE_NO_LINE(OBFUSCATE, 4, "Applying new names:\n  List of ifields\t");
    for (DexField* f : cls->get_ifields()) {
      TRACE_NO_LINE(OBFUSCATE, 4, "%s\t", SHOW(f->get_name()));
    }
    TRACE(OBFUSCATE, 4, "");
    TRACE_NO_LINE(OBFUSCATE, 4, "  List of sfields\t");
    for (DexField* f : cls->get_sfields()) {
      TRACE_NO_LINE(OBFUSCATE, 4, "%s\t", SHOW(f->get_name()));
    }
    TRACE(OBFUSCATE, 4, "");
  }
  TRACE(OBFUSCATE, 3, "Finished applying new names to defs");
}

template <typename DexMember,
          typename DexMemberRef,
          typename DexMemberSpec,
          typename K>
DexMember* find_renamable_ref(
    DexMemberRef* ref,
    InsertOnlyConcurrentMap<DexMemberRef*, DexMember*>& ref_def_cache,
    DexElemManager<DexMember*, DexMemberRef*, DexMemberSpec, K>& name_mapping) {
  TRACE(OBFUSCATE, 4, "Found a ref opcode");
  return *ref_def_cache
              .get_or_create_and_assert_equal(
                  ref, [&](auto*) { return name_mapping.def_of_ref(ref); })
              .first;
}

void update_refs(Scope& scope,
                 DexFieldManager& field_name_mapping,
                 DexMethodManager& method_name_mapping,
                 size_t* classes_made_public) {
  InsertOnlyConcurrentMap<DexFieldRef*, DexField*> f_ref_def_cache;
  InsertOnlyConcurrentMap<DexMethodRef*, DexMethod*> m_ref_def_cache;

  auto maybe_publicize_class = [&](const DexMethod* referrer,
                                   DexClass* referree) {
    if (is_public(referree)) {
      return;
    }
    // TODO: Be more conservative here?
    if (!type::same_package(referrer->get_class(), referree->get_type()) ||
        is_private(referree)) {
      set_public(referree);
      ++(*classes_made_public);
    }
  };

  // A method handle is fixed up like the instruction it acts like.
  auto fix_method_handle =
      [&](const DexMethodHandle* method_handle,
          const DexMethod* m) -> std::optional<DexMethodHandle> {
    auto op = method_handle_opcode(method_handle);
    DexField* field_def = nullptr;
    DexMethod* method_def = nullptr;
    if (!opcode::is_a_method_invoke(op)) {
      // `method_handle_opcode` maps every invoke kind to an invoke, so this is
      // a field handle.
      auto* field_ref = method_handle->fieldref();
      auto* resolved = resolve_field_handle(method_handle);
      auto is_renamed = [&](DexFieldRef* ref) {
        return find_renamable_ref(ref, f_ref_def_cache, field_name_mapping) !=
               nullptr;
      };
      // Renaming changes what a handle resolves to when it renames the field
      // that the handle resolves to, or a definition of the other kind that
      // the handle names, which is renamed in place: a static-get handle of
      // `LChild;.x:I`, where `Child` declares an instance field `x`, resolves
      // to a static field `x` of a superclass. The handle then names the field
      // that it resolves to.
      if (resolved != nullptr && resolved != field_ref &&
          (is_renamed(resolved) ||
           (field_ref->is_def() && is_renamed(field_ref)))) {
        field_def = resolved;
      }
    } else if (opcode::is_invoke_direct(op) || opcode::is_invoke_static(op)) {
      auto* method_ref = method_handle->methodref();
      if (!method_ref->is_def()) {
        method_def = find_renamable_ref(method_ref, m_ref_def_cache,
                                        method_name_mapping);
      }
    }
    if (field_def == nullptr && method_def == nullptr) {
      return std::nullopt;
    }
    TRACE(OBFUSCATE, 4, "Found a method handle to fixup %s",
          SHOW(method_handle));
    maybe_publicize_class(m, type_class(field_def != nullptr
                                            ? field_def->get_class()
                                            : method_def->get_class()));
    return field_def != nullptr
               ? DexMethodHandle(method_handle->type(), field_def)
               : DexMethodHandle(method_handle->type(), method_def);
  };
  MethodHandleRewriter method_handle_rewriter({.handle = fix_method_handle});

  walk::parallel::opcodes(scope, [&](DexMethod* m, IRInstruction* instr) {
    method_handle_rewriter.rewrite(instr, m);
    auto op = instr->opcode();
    if (instr->has_field()) {
      DexFieldRef* field_ref = instr->get_field();
      if (field_ref->is_def()) {
        return;
      }
      DexField* field_def =
          find_renamable_ref(field_ref, f_ref_def_cache, field_name_mapping);
      if (field_def != nullptr) {
        TRACE(OBFUSCATE, 4, "Found a ref to fixup %s", SHOW(field_ref));
        instr->set_field(field_def);
        maybe_publicize_class(m, type_class(field_def->get_class()));
      }
    } else if (instr->has_method() &&
               (opcode::is_invoke_direct(op) || opcode::is_invoke_static(op))) {
      // We only check invoke-direct and invoke-static because the method def
      // we've renamed is a `dmethod`, not a `vmethod`.
      //
      // If we attempted to resolve invoke-virtual refs here, we would
      // conflate this virtual ref with a direct def that happens to have the
      // same name but isn't actually inherited.
      DexMethodRef* method_ref = instr->get_method();
      if (method_ref->is_def()) {
        return;
      }
      DexMethod* method_def =
          find_renamable_ref(method_ref, m_ref_def_cache, method_name_mapping);
      if (method_def != nullptr) {
        TRACE(OBFUSCATE, 4, "Found a ref to fixup %s", SHOW(method_ref));
        instr->set_method(method_def);
        maybe_publicize_class(m, type_class(method_def->get_class()));
      }
    }
  });
}

void get_totals(Scope& scope, RenameStats& stats) {
  for (const auto& cls : scope) {
    stats.fields_total += cls->get_ifields().size();
    stats.fields_total += cls->get_sfields().size();
    stats.vmethods_total += cls->get_vmethods().size();
    stats.dmethods_total += cls->get_dmethods().size();
  }
}

} // end namespace

void obfuscate(Scope& scope,
               RenameStats& stats,
               bool avoid_colliding_debug_name) {
  get_totals(scope, stats);
  ClassHierarchy ch = build_type_hierarchy(scope);

  DexFieldManager field_name_manager = new_dex_field_manager();
  DexMethodManager method_name_manager = new_dex_method_manager();

  UnorderedMap<const DexClass*, int> next_dmethod_seeds;
  for (DexClass* cls : scope) {
    always_assert_log(!cls->is_external(),
                      "Shouldn't rename members of external classes. %s",
                      SHOW(cls));
    // Checks to short-circuit expensive name-gathering logic (code is still
    // correct w/o this, but does unnecessary work)
    bool operate_on_ifields =
        contains_renamable_elem(cls->get_ifields(), field_name_manager);
    bool operate_on_sfields =
        contains_renamable_elem(cls->get_sfields(), field_name_manager);
    bool operate_on_dmethods =
        contains_renamable_elem(cls->get_dmethods(), method_name_manager);
    if (operate_on_ifields || operate_on_sfields) {
      FieldObfuscationState f_ob_state;
      FieldNameGenerator field_name_generator(f_ob_state.ids_to_avoid,
                                              f_ob_state.used_ids);

      TRACE(OBFUSCATE, 3, "Renaming the fields of class %s",
            SHOW(cls->get_name()));

      f_ob_state.populate_ids_to_avoid(cls, field_name_manager,
                                       /* unused */ ch);

      if (operate_on_ifields) {
        obfuscate_elems(
            FieldRenamingContext(cls->get_ifields(), field_name_generator),
            field_name_manager);
      }
      if (operate_on_sfields) {
        obfuscate_elems(
            FieldRenamingContext(cls->get_sfields(), field_name_generator),
            field_name_manager);
      }

      // Make sure to bind the new names otherwise not all generators will
      // assign names to the members
      field_name_generator.bind_names();
    }

    // =========== Obfuscate Methods Below ==========
    if (operate_on_dmethods) {
      MethodObfuscationState m_ob_state;
      MethodNameGenerator direct_method_name_gen(m_ob_state.ids_to_avoid,
                                                 m_ob_state.used_ids);

      TRACE(OBFUSCATE, 3, "Renaming the methods of class %s",
            SHOW(cls->get_name()));
      m_ob_state.populate_ids_to_avoid(cls, method_name_manager, ch);

      obfuscate_elems(MethodRenamingContext(cls->get_dmethods(),
                                            direct_method_name_gen,
                                            method_name_manager),
                      method_name_manager);

      direct_method_name_gen.bind_names();
      auto next_ctr = direct_method_name_gen.next_ctr();
      if (next_ctr != 0) {
        next_dmethod_seeds.emplace(cls, direct_method_name_gen.next_ctr());
      }
    }
  }
  field_name_manager.print_elements();
  method_name_manager.print_elements();

  TRACE(OBFUSCATE, 3, "Finished picking new names");

  // Update any instructions with a member that is a ref to the corresponding
  // def for any field that we are going to rename. This allows us to in-place
  // rename the field def and have that change seen everywhere.
  update_refs(scope, field_name_manager, method_name_manager,
              &stats.classes_made_public);

  TRACE(OBFUSCATE, 3, "Finished transforming refs");

  // Apply new names, recording what we're changing
  stats.fields_renamed = field_name_manager.commit_renamings_to_dex();
  stats.dmethods_renamed = method_name_manager.commit_renamings_to_dex();

  stats.vmethods_renamed =
      rename_virtuals(scope, avoid_colliding_debug_name, next_dmethod_seeds);

  debug_logging(scope);

  TRACE(OBFUSCATE, 1,
        "%s: %zu\n%s: %zu\n"
        "%s: %zu\n%s: %zu\n"
        "%s: %zu\n%s: %zu",
        METRIC_FIELD_TOTAL, stats.fields_total, METRIC_FIELD_RENAMED,
        stats.fields_renamed, METRIC_DMETHODS_TOTAL, stats.dmethods_total,
        METRIC_DMETHODS_RENAMED, stats.dmethods_renamed, METRIC_VMETHODS_TOTAL,
        stats.vmethods_total, METRIC_VMETHODS_RENAMED, stats.vmethods_renamed);
}

void ObfuscatePass::run_pass(DexStoresVector& stores,
                             ConfigFiles& /* conf */,
                             PassManager& mgr) {
  auto scope = build_class_scope(stores);
  RenameStats stats;
  auto debug_info_kind = mgr.get_redex_options().debug_info_kind;
  obfuscate(scope, stats, is_iodi(debug_info_kind));
  mgr.incr_metric(METRIC_FIELD_TOTAL, static_cast<int>(stats.fields_total));
  mgr.incr_metric(METRIC_FIELD_RENAMED, static_cast<int>(stats.fields_renamed));
  mgr.incr_metric(METRIC_DMETHODS_TOTAL,
                  static_cast<int>(stats.dmethods_total));
  mgr.incr_metric(METRIC_DMETHODS_RENAMED,
                  static_cast<int>(stats.dmethods_renamed));
  mgr.incr_metric(METRIC_VMETHODS_TOTAL,
                  static_cast<int>(stats.vmethods_total));
  mgr.incr_metric(METRIC_VMETHODS_RENAMED,
                  static_cast<int>(stats.vmethods_renamed));
}

static ObfuscatePass s_pass;
