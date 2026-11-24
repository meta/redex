/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <atomic>
#include <fstream>

#include "RemoveUnusedFields.h"

#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "FieldOpTracker.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Shrinker.h"
#include "Trace.h"
#include "Walkers.h"

using namespace remove_unused_fields;
using namespace shrinker;

namespace {

bool can_remove(DexField* field) {
  // XXX(jezng): why is can_rename not a subset of can_delete?
  return field != nullptr && !field->is_external() && can_delete(field) &&
         can_rename(field);
}

bool has_non_zero_static_value(DexField* field) {
  auto* ev = field->get_static_value();
  return ev != nullptr && !ev->is_zero();
}

// What the pass finds out about the fields of a scope before it changes any
// code.
class FieldAnalysis final {
 public:
  FieldAnalysis(const Config& config, const Scope& scope) : m_config(config) {
    analyze(scope);
  }

  const UnorderedSet<const DexField*>& unread_fields() const {
    return m_unread_fields;
  }

  const UnorderedSet<const DexField*>& unwritten_fields() const {
    return m_unwritten_fields;
  }

  const UnorderedSet<const DexField*>& zero_written_fields() const {
    return m_zero_written_fields;
  }

  const UnorderedSet<const DexField*>& vestigial_objects_written_fields()
      const {
    return m_vestigial_objects_written_fields;
  }

  bool can_remove_unread_field_put(const DexField* field) const {
    auto* t = field->get_type();
    // When no non-null value is ever written to a field, then it can never hold
    // a non-null reference
    if (m_zero_written_fields.count(field) != 0u) {
      return true;
    }

    // Certain types don't have lifetimes, or at least nobody should depend on
    // them.
    if (!m_type_lifetimes.has_lifetime(t)) {
      return true;
    }

    if (m_config.allowlist_types.count(t) != 0u) {
      return true;
    }

    // We don't have to worry about lifetimes of harmless objects
    if (m_vestigial_objects_written_fields.count(field) != 0u) {
      return true;
    }

    return false;
  }

 private:
  bool is_blocklisted(const DexField* field) const {
    return m_config.blocklist_types.count(field->get_type()) != 0 ||
           m_config.blocklist_classes.count(field->get_class()) != 0;
  }

  void analyze(const Scope& scope) {
    field_op_tracker::FieldStatsMap field_stats =
        field_op_tracker::analyze(scope);

    std::unique_ptr<field_op_tracker::FieldWrites> field_writes;
    if (m_config.remove_zero_written_fields ||
        m_config.remove_vestigial_objects_written_fields) {
      field_writes = std::make_unique<field_op_tracker::FieldWrites>();
      field_op_tracker::analyze_writes(
          scope, field_stats,
          m_config.remove_vestigial_objects_written_fields ? &m_type_lifetimes
                                                           : nullptr,
          field_writes.get());
    }

    for (auto& pair : UnorderedIterable(field_stats)) {
      auto* field = pair.first;
      auto& stats = pair.second;
      TRACE(RMUF,
            3,
            "%s: %zu %zu %d",
            SHOW(field),
            stats.reads,
            stats.writes,
            is_synthetic(field));
      if (can_remove(field) && !is_blocklisted(field)) {
        if (m_config.remove_unread_fields && stats.reads == 0) {
          m_unread_fields.emplace(field);
          if (m_config.remove_vestigial_objects_written_fields &&
              (field_writes->non_vestigial_objects_written_fields.count_unsafe(
                   field) == 0u)) {
            m_vestigial_objects_written_fields.emplace(field);
          }
        } else if (m_config.remove_unwritten_fields && stats.writes == 0 &&
                   !has_non_zero_static_value(field)) {
          m_unwritten_fields.emplace(field);
        } else if (m_config.remove_zero_written_fields &&
                   (field_writes->non_zero_written_fields.count_unsafe(field) ==
                    0u) &&
                   !has_non_zero_static_value(field)) {
          m_zero_written_fields.emplace(field);
        }
      }
    }
    TRACE(RMUF, 2, "unread_fields %zu", m_unread_fields.size());
    TRACE(RMUF, 2, "unwritten_fields %zu", m_unwritten_fields.size());
    TRACE(RMUF, 2, "zero written_fields %zu", m_zero_written_fields.size());
    TRACE(RMUF,
          2,
          "vestigial objects written_fields %zu",
          m_vestigial_objects_written_fields.size());
  }

  const Config& m_config;
  UnorderedSet<const DexField*> m_unread_fields;
  UnorderedSet<const DexField*> m_unwritten_fields;
  UnorderedSet<const DexField*> m_zero_written_fields;
  UnorderedSet<const DexField*> m_vestigial_objects_written_fields;
  field_op_tracker::TypeLifetimes m_type_lifetimes;
};

class RemoveUnusedFields final {
 public:
  RemoveUnusedFields(const Config& config,
                     const ConfigFiles& config_files,
                     const ShrinkerConfig& shrinker_config,
                     int min_sdk,
                     DexStoresVector& stores,
                     const Scope& scope)
      : m_scope(scope),
        m_analysis(config, scope),
        m_init_classes_with_side_effects(
            scope, config_files.create_init_class_insns()),
        m_shrinker(stores,
                   scope,
                   m_init_classes_with_side_effects,
                   config_files,
                   shrinker_config,
                   min_sdk) {
    transform();
  }

  const FieldAnalysis& analysis() const { return m_analysis; }

  size_t unremovable_unread_field_puts() const {
    return m_unremovable_unread_field_puts;
  }

  size_t init_classes() const { return m_init_classes; }

 private:
  void transform() {
    // Replace reads to unwritten fields with appropriate const-0 instructions,
    // and remove the writes to unread fields.
    walk::parallel::code(m_scope, [&](const DexMethod* method, IRCode& code) {
      if (method->rstate.no_optimizations()) {
        return;
      }
      always_assert(code.cfg_built());
      auto& cfg = code.cfg();
      cfg::CFGMutation m(cfg);
      auto iterable = cfg::InstructionIterable(cfg);
      bool any_changes = false;
      for (auto insn_it = iterable.begin(); insn_it != iterable.end();
           ++insn_it) {
        auto* insn = insn_it->insn;
        if (!insn->has_field()) {
          continue;
        }
        auto* field = resolve_field(insn->get_field());
        bool replace_insn = false;
        bool remove_insn = false;
        if (m_analysis.unread_fields().count(field) != 0u) {
          if (m_analysis.can_remove_unread_field_put(field)) {
            always_assert(opcode::is_an_iput(insn->opcode()) ||
                          opcode::is_an_sput(insn->opcode()));
            TRACE(RMUF, 5, "Removing %s", SHOW(insn));
            remove_insn = true;
          } else {
            m_unremovable_unread_field_puts++;
          }
        } else if (m_analysis.unwritten_fields().count(field) != 0u) {
          always_assert(opcode::is_an_iget(insn->opcode()) ||
                        opcode::is_an_sget(insn->opcode()));
          TRACE(RMUF, 5, "Replacing %s with const 0", SHOW(insn));
          replace_insn = true;
        } else if (m_analysis.zero_written_fields().count(field) != 0u) {
          if (opcode::is_an_iput(insn->opcode()) ||
              opcode::is_an_sput(insn->opcode())) {
            TRACE(RMUF, 5, "Removing %s", SHOW(insn));
            remove_insn = true;
          } else {
            always_assert(opcode::is_an_iget(insn->opcode()) ||
                          opcode::is_an_sget(insn->opcode()));
            TRACE(RMUF, 5, "Replacing %s with const 0", SHOW(insn));
            replace_insn = true;
          }
        }
        if (!replace_insn && !remove_insn) {
          continue;
        }
        std::vector<IRInstruction*> new_insns;
        if ((field != nullptr) && is_static(field)) {
          auto* init_class_insn =
              m_init_classes_with_side_effects.create_init_class_insn(
                  field->get_class());
          if (init_class_insn != nullptr) {
            new_insns.push_back(init_class_insn);
            m_init_classes++;
          }
        }
        if (replace_insn) {
          auto move_result = cfg.move_result_of(insn_it);
          if (move_result.is_end()) {
            continue;
          }
          auto* write_insn = move_result->insn;
          IRInstruction* const0 = new IRInstruction(
              write_insn->dest_is_wide() ? OPCODE_CONST_WIDE : OPCODE_CONST);
          const0->set_dest(write_insn->dest())->set_literal(0);
          new_insns.push_back(const0);
          any_changes = true;
        } else if (remove_insn) {
          any_changes = true;
        }
        m.replace(insn_it, new_insns);
      }
      m.flush();
      if (any_changes) {
        m_shrinker.shrink_method(const_cast<DexMethod*>(method));
      }
    });
  }

  const Scope& m_scope;
  FieldAnalysis m_analysis;
  const init_classes::InitClassesWithSideEffects
      m_init_classes_with_side_effects;
  Shrinker m_shrinker;
  std::atomic<size_t> m_unremovable_unread_field_puts{0};
  std::atomic<size_t> m_init_classes{0};
};

} // namespace

namespace remove_unused_fields {

UnorderedSet<const DexField*> fields_with_removable_unread_writes(
    const Config& config, const Scope& scope) {
  FieldAnalysis analysis(config, scope);
  InsertOnlyConcurrentSet<const DexField*> fields;
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode& code) {
    // The pass keeps this method's writes, but a field written here is still
    // listed if the pass removes one of its writes elsewhere.
    if (method->rstate.no_optimizations()) {
      return;
    }
    always_assert(code.cfg_built());
    for (const auto& mie : cfg::InstructionIterable(code.cfg())) {
      if (!mie.insn->has_field()) {
        continue;
      }
      const auto* field = resolve_field(mie.insn->get_field());
      if (analysis.unread_fields().count(field) != 0u &&
          analysis.can_remove_unread_field_put(field)) {
        fields.insert(field);
      }
    }
  });
  UnorderedSet<const DexField*> result;
  insert_unordered_iterable(result, fields);
  return result;
}

void PassImpl::run_pass(DexStoresVector& stores,
                        ConfigFiles& conf,
                        PassManager& mgr) {
  always_assert_log(
      !mgr.init_class_lowering_has_run(),
      "Implementation limitation: RemoveUnusedFieldsPass could introduce new "
      "init-class instructions.");
  auto scope = build_class_scope(stores);

  ShrinkerConfig shrinker_config;
  shrinker_config.run_const_prop = true;
  shrinker_config.run_cse = true;
  shrinker_config.run_copy_prop = true;
  shrinker_config.run_local_dce = true;
  shrinker_config.compute_pure_methods = false;

  int min_sdk = mgr.get_redex_options().min_sdk;
  RemoveUnusedFields rmuf(m_config, conf, shrinker_config, min_sdk, stores,
                          scope);
  mgr.set_metric("unread_fields", rmuf.analysis().unread_fields().size());
  mgr.set_metric("unwritten_fields", rmuf.analysis().unwritten_fields().size());
  mgr.set_metric("zero_written_fields",
                 rmuf.analysis().zero_written_fields().size());
  mgr.set_metric("vestigial_objects_written_fields",
                 rmuf.analysis().vestigial_objects_written_fields().size());
  mgr.set_metric("unremovable_unread_field_puts",
                 rmuf.unremovable_unread_field_puts());
  mgr.set_metric("init_classes", rmuf.init_classes());

  if (m_export_removed) {
    std::vector<const DexField*> removed_fields;
    insert_unordered_iterable(removed_fields, removed_fields.end(),
                              rmuf.analysis().unread_fields());
    insert_unordered_iterable(removed_fields, removed_fields.end(),
                              rmuf.analysis().unwritten_fields());
    sort_unique(removed_fields, compare_dexfields);
    auto path = conf.metafile(REMOVED_FIELDS_FILENAME);
    std::ofstream ofs(path, std::ofstream::out | std::ofstream::trunc);
    for (const auto* field : removed_fields) {
      ofs << show_deobfuscated(field) << "\n";
    }
  }
}

static PassImpl s_pass;

} // namespace remove_unused_fields
