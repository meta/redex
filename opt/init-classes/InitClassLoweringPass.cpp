/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InitClassLoweringPass.h"

#include <vector>

#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "InitClassPruner.h"
#include "InitClassesWithSideEffects.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace init_classes;

namespace {

constexpr const char* METRIC_METHODS_WITH_INIT_CLASS =
    "methods_with_init_class";
constexpr const char* METRIC_FIELDS_ADDED = "fields_added";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS =
    "init_class_instructions";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS_REMOVED =
    "init_class_instructions_removed";
constexpr const char* METRIC_INIT_CLASS_INSTRUCTIONS_REFINED =
    "init_class_instructions_refined";
constexpr const char* METRIC_SGET_INSTRUCTIONS_ADDED =
    "sget_instructions_added";
constexpr const char* METRIC_INIT_CLASSES = "init_classes";
constexpr const char* METRIC_FIELDS_MADE_PUBLIC = "fields_made_public";
constexpr const char* METRIC_TYPES_MADE_PUBLIC = "types_made_public";

static const char* redex_field_name = "$redex_init_class";

class InitClassFields {
 public:
  explicit InitClassFields(DexStoresVector& stores) {
    // For each dex, figure out which static fields it references, and which
    // classes belong to it.
    std::vector<std::pair<size_t, const DexClasses*>> dex_to_classes;
    for (auto& store : stores) {
      for (auto& dexen : store.get_dexen()) {
        dex_to_classes.emplace_back(dex_to_classes.size(), &dexen);
      }
    }
    m_dex_referenced_sfields.resize(dex_to_classes.size());
    workqueue_run<std::pair<size_t, const DexClasses*>>(
        [&](std::pair<size_t, const DexClasses*> p) {
          auto& dex_referenced_sfields = m_dex_referenced_sfields.at(p.first);
          for (auto* cls : *p.second) {
            cls->gather_fields(dex_referenced_sfields);
            m_class_dex_indices.emplace(cls->get_type(), p.first);
          }
          unordered_erase_if(dex_referenced_sfields, [](DexFieldRef* f) {
            return !f->is_def() || !is_static(f->as_def());
          });
        },
        dex_to_classes);
  }

  std::vector<IRInstruction*> get_replacements(
      const DexType* type,
      DexMethod* caller,
      const std::function<reg_t(DexField*)>& reg_getter) const {
    std::vector<IRInstruction*> insns;
    auto caller_dex_idx = m_class_dex_indices.at_unsafe(caller->get_class());
    auto* field = get(type, caller_dex_idx);
    auto reg = reg_getter(field);
    auto* sget_insn = (new IRInstruction(opcode::sget_opcode_for_field(field)))
                          ->set_field(field);
    auto* move_result_insn =
        (new IRInstruction(
             opcode::move_result_pseudo_for_sget(sget_insn->opcode())))
            ->set_dest(reg);
    insns.push_back(sget_insn);
    insns.push_back(move_result_insn);
    return insns;
  }

  size_t get_classes_size() { return m_init_class_fields.size(); }

  size_t get_fields_added() { return m_fields_added; }

  std::vector<std::pair<const DexType*, size_t>>
  get_ordered_init_class_reference_counts() {
    std::vector<std::pair<const DexType*, size_t>> res;
    for (auto& p : UnorderedIterable(m_init_class_fields)) {
      size_t count = 0;
      for (auto& q : UnorderedIterable(p.second)) {
        count += q.second.count;
      }
      res.emplace_back(p.first, count);
    }
    std::stable_sort(res.begin(), res.end(), [](const auto& a, const auto& b) {
      return a.second > b.second;
    });
    return res;
  }

  std::vector<DexField*> get_all() {
    UnorderedSet<DexField*> set;
    for (auto& p : UnorderedIterable(m_init_class_fields)) {
      for (auto& q : UnorderedIterable(p.second)) {
        set.insert(q.second.field);
      }
    }
    return unordered_to_ordered(set, compare_dexfields);
  }

 private:
  std::vector<UnorderedSet<DexFieldRef*>> m_dex_referenced_sfields;
  InsertOnlyConcurrentMap<DexType*, size_t> m_class_dex_indices;
  const DexString* m_field_name = DexString::make_string(redex_field_name);
  mutable std::atomic<size_t> m_fields_added{0};
  struct InitClassField {
    DexField* field{nullptr};
    size_t count{0};
  };
  mutable ConcurrentMap<const DexType*, UnorderedMap<size_t, InitClassField>>
      m_init_class_fields;

  DexField* get(const DexType* type, size_t dex_idx) const {
    DexField* res = nullptr;
    m_init_class_fields.update(
        type, [&](const DexType* type_, auto& map, bool) {
          auto& icf = map[dex_idx];
          if (icf.field == nullptr) {
            icf.field = make_init_class_field(type_, dex_idx);
            icf.field->rstate.set_init_class();
          }
          icf.count++;
          res = icf.field;
        });
    always_assert(res);
    return res;
  }

  static DexField* get_preferred_field(const std::vector<DexField*>& sfields) {
    always_assert(!sfields.empty());
    // 1. non-wide primitive, if any.
    for (auto* f : sfields) {
      if (!type::is_wide_type(f->get_type()) &&
          type::is_primitive(f->get_type())) {
        return f;
      }
    }
    // 2. non-wide, if any.
    for (auto* f : sfields) {
      if (!type::is_wide_type(f->get_type())) {
        return f;
      }
    }
    // 3. anything.
    return sfields.front();
  }

  DexField* make_init_class_field(const DexType* type, size_t dex_idx) const {
    auto* cls = type_class(type);
    always_assert(cls);
    const auto& dex_referenced_sfields = m_dex_referenced_sfields.at(dex_idx);
    const auto& sfields = cls->get_sfields();

    auto referenced_sfields = sfields;
    std::erase_if(referenced_sfields,
                  [&](auto* f) { return !dex_referenced_sfields.count(f); });
    if (!referenced_sfields.empty()) {
      // Ideally, we can pick from the filtered list of referenced sfields
      auto* f = get_preferred_field(referenced_sfields);
      always_assert(f->get_name() != m_field_name);
      return f;
    }

    auto pre_existing_sfields = sfields;
    std::erase_if(pre_existing_sfields,
                  [&](auto* f) { return f->get_name() == m_field_name; });
    if (!pre_existing_sfields.empty()) {
      // If there is no referenced sfield in this dex, but we have any
      // pre-existing sfields, then we pick one of them. This will effectively
      // add a field reference to this dex, but that's accounted for.
      return get_preferred_field(pre_existing_sfields);
    }

    // If we already created a new dummy field (for another dex), then we must
    // reuse that.
    for (auto* f : sfields) {
      if (f->get_name() == m_field_name) {
        return f;
      }
    }

    always_assert_log(DexField::get_field(type, m_field_name, type) == nullptr,
                      "field %s already exists!",
                      redex_field_name);
    auto* field = DexField::make_field(type, m_field_name, type)
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    field->rstate.set_root();
    insert_sorted(cls->get_sfields(), field, compare_dexfields);
    field->set_deobfuscated_name(show_deobfuscated(field));
    m_fields_added++;
    return field;
  }
};

void make_public(const std::vector<DexField*>& fields,
                 size_t* fields_made_public,
                 size_t* types_made_public) {
  UnorderedSet<DexType*> visited;
  std::function<void(DexType*)> visit;
  visit = [&](DexType* type) {
    auto* cls = type_class(type);
    if ((cls != nullptr) && !cls->is_external() && !is_public(cls)) {
      set_public(cls);
      (*types_made_public)++;
      visit(cls->get_super_class());
    }
  };
  for (const auto& f : fields) {
    if (!is_public(f)) {
      set_public(f);
      (*fields_made_public)++;
    }
    visit(f->get_class());
    visit(f->get_type());
  }
}

class LogCreator {
 private:
  DexMethodRef* m_log_e_method = DexMethod::make_method(
      "Landroid/util/Log;.e:(Ljava/lang/String;Ljava/lang/String;)I");

 public:
  std::vector<IRInstruction*> get_insns(cfg::ControlFlowGraph& cfg,
                                        const DexString* tag_str,
                                        const std::string& message) const {
    auto tmp0 = cfg.allocate_temp();
    auto* tag_insn =
        (new IRInstruction(OPCODE_CONST_STRING))->set_string(tag_str);
    auto* tag_result_insn =
        (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))->set_dest(tmp0);
    auto tmp1 = cfg.allocate_temp();
    auto* message_insn = (new IRInstruction(OPCODE_CONST_STRING))
                             ->set_string(DexString::make_string(message));
    auto* message_result_insn =
        (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))->set_dest(tmp1);
    auto* invoke_insn = (new IRInstruction(OPCODE_INVOKE_STATIC))
                            ->set_method(m_log_e_method)
                            ->set_srcs_size(2)
                            ->set_src(0, tmp0)
                            ->set_src(1, tmp1);
    return {tag_insn, tag_result_insn, message_insn, message_result_insn,
            invoke_insn};
  }
};

void log_in_clinits(const LogCreator& log_creator,
                    const Scope& scope,
                    const init_classes::InitClassesWithSideEffects&
                        init_classes_with_side_effects) {
  const auto* tag_str = DexString::make_string("clinit-with-side-effects");
  walk::parallel::classes(scope, [&](DexClass* cls) {
    auto* type = cls->get_type();
    if (init_classes_with_side_effects.refine(type) != type) {
      return;
    }
    auto* clinit = cls->get_clinit();
    if ((clinit == nullptr) || (clinit->get_code() == nullptr)) {
      return;
    }
    cfg::ScopedCFG cfg(clinit->get_code());
    auto insns = log_creator.get_insns(*cfg, tag_str, show_deobfuscated(type));
    cfg->insert_after_param_loads(insns);
    TRACE(ICL,
          6,
          "[InitClassLowering] added logging to %s:\n%s",
          SHOW(clinit),
          SHOW(*cfg));
  });
}

std::string get_init_class_message(DexMethod* method,
                                   const DexType* type,
                                   const cfg::InstructionIterator& cfg_it) {
  std::ostringstream oss;
  auto* pos = cfg_it.cfg().get_dbg_pos(cfg_it);
  if (pos != nullptr) {
    UnorderedSet<DexPosition*> visited;
    for (; pos != nullptr; pos = pos->parent) {
      if (!visited.insert(pos).second) {
        oss << "Cyclic";
        break;
      }
      if (pos->method != nullptr) {
        oss << *pos->method;
      } else {
        oss << "Unknown method";
      }
      oss << "(";
      if (pos->file == nullptr) {
        oss << "Unknown source";
      } else {
        oss << *pos->file;
      }
      oss << ":" << pos->line << ")";
      if (pos->parent != nullptr) {
        oss << ", parent: ";
      }
    }
  } else {
    oss << show_deobfuscated(method);
  }
  oss << " ==> " << show_deobfuscated(type);
  return oss.str();
}
} // namespace

void InitClassLoweringPass::bind_config() {
  bind(
      "drop", m_drop, m_drop,
      "Whether to drop the init-class instructions, instead of lowering them.");
  bind("log_init_classes", m_log_init_classes, m_log_init_classes,
       "Whether to insert log statements at all init-class instructions.");
  bind("log_in_clinits", m_log_in_clinits, m_log_in_clinits,
       "Whether to insert log statements in clinits with side-effects.");
}

void InitClassLoweringPass::run_pass(DexStoresVector& stores,
                                     ConfigFiles& conf,
                                     PassManager& mgr) {
  const auto scope = build_class_scope(stores);
  auto create_init_class_insns = conf.create_init_class_insns();
  TRACE(ICL, 1, "[InitClassLowering] create_init_class_insns: %d",
        create_init_class_insns);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, create_init_class_insns);
  LogCreator log_creator;
  if (m_log_in_clinits) {
    log_in_clinits(log_creator, scope, init_classes_with_side_effects);
  }
  const DexString* tag_str =
      m_log_in_clinits ? DexString::make_string("init-class") : nullptr;
  std::atomic<size_t> sget_instructions_added{0};
  std::atomic<size_t> methods_with_init_class{0};
  InitClassFields init_class_fields(stores);
  ConcurrentSet<DexMethod*> clinits;
  const auto stats =
      walk::parallel::methods<Stats>(scope, [&](DexMethod* method) {
        auto* code = method->get_code();
        if (code == nullptr) {
          return Stats();
        }
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();
        if (method::is_clinit(method)) {
          clinits.insert(method);
        }
        if (method::count_opcode_of_types(cfg, {IOPCODE_INIT_CLASS}) == 0u) {
          return Stats();
        }
        InitClassPruner pruner(init_classes_with_side_effects,
                               method->get_class(), cfg);
        pruner.apply();
        auto local_stats = pruner.get_stats();
        if (local_stats.init_class_instructions == 0) {
          return local_stats;
        }
        TRACE(ICL,
              6,
              "[InitClassLowering] method %s with %zu init-classes:\n%s",
              SHOW(method),
              local_stats.init_class_instructions,
              SHOW(cfg));
        methods_with_init_class++;
        std::optional<reg_t> tmp_reg;
        std::optional<reg_t> wide_tmp_reg;
        auto get_reg = [&](DexField* field) {
          if (type::is_wide_type(field->get_type())) {
            if (!wide_tmp_reg) {
              wide_tmp_reg = cfg.allocate_wide_temp();
            }
            return *wide_tmp_reg;
          }
          if (!tmp_reg) {
            tmp_reg = cfg.allocate_temp();
          }
          return *tmp_reg;
        };
        cfg::CFGMutation mutation(cfg);
        size_t local_sget_instructions_added = 0;
        for (auto* block : cfg.blocks()) {
          auto ii = InstructionIterable(block);
          for (auto it = ii.begin(); it != ii.end(); it++) {
            if (it->insn->opcode() != IOPCODE_INIT_CLASS) {
              continue;
            }
            always_assert(create_init_class_insns);
            const auto* type = it->insn->get_type();
            std::vector<IRInstruction*> replacements;
            if (!m_drop) {
              replacements =
                  init_class_fields.get_replacements(type, method, get_reg);
              local_sget_instructions_added++;
            }
            auto cfg_it = block->to_cfg_instruction_iterator(it);
            if (tag_str != nullptr) {
              auto message = get_init_class_message(method, type, cfg_it);
              auto log_insns = log_creator.get_insns(cfg, tag_str, message);
              replacements.insert(replacements.begin(), log_insns.begin(),
                                  log_insns.end());
            }
            mutation.replace(cfg_it, replacements);
          }
        }
        mutation.flush();
        if (local_sget_instructions_added != 0u) {
          sget_instructions_added += local_sget_instructions_added;
        }
        return local_stats;
      });

  // Remove clinits that are now trivial.
  for (auto* clinit : UnorderedIterable(clinits)) {
    if (method::is_trivial_clinit(*clinit->get_code())) {
      type_class(clinit->get_class())->remove_method(clinit);
    }
  }

  TRACE(ICL, 1,
        "[InitClassLowering] %zu methods have %zu sget instructions; %zu "
        "classes with clinits with side effects needed initialization with "
        "%zu added fields",
        (size_t)methods_with_init_class, (size_t)sget_instructions_added,
        init_class_fields.get_classes_size(),
        init_class_fields.get_fields_added());

  if (traceEnabled(ICL, 5)) {
    for (auto& p :
         init_class_fields.get_ordered_init_class_reference_counts()) {
      auto* cls = type_class(p.first);
      auto count = p.second;
      auto* clinit = cls->get_clinit();
      always_assert(clinit);
      auto& cfg = clinit->get_code()->cfg();
      TRACE(ICL, 5,
            "[InitClassLowering] clinit of %s referenced by %zu init-class "
            "instructions:\n%s",
            SHOW(cls), count, SHOW(cfg));
    }
  }

  size_t fields_made_public = 0;
  size_t types_made_public = 0;
  make_public(init_class_fields.get_all(), &fields_made_public,
              &types_made_public);
  TRACE(ICL, 5,
        "[InitClassLowering] made %zu existing fields and %zu classes public",
        fields_made_public, types_made_public);

  mgr.incr_metric(METRIC_METHODS_WITH_INIT_CLASS, methods_with_init_class);
  mgr.incr_metric(METRIC_FIELDS_ADDED, init_class_fields.get_fields_added());
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS,
                  stats.init_class_instructions);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS_REMOVED,
                  stats.init_class_instructions_removed);
  mgr.incr_metric(METRIC_INIT_CLASS_INSTRUCTIONS_REFINED,
                  stats.init_class_instructions_refined);
  mgr.incr_metric(METRIC_INIT_CLASSES, init_class_fields.get_classes_size());
  mgr.incr_metric(METRIC_SGET_INSTRUCTIONS_ADDED, sget_instructions_added);
  mgr.incr_metric(METRIC_FIELDS_MADE_PUBLIC, fields_made_public);
  mgr.incr_metric(METRIC_TYPES_MADE_PUBLIC, types_made_public);

  mgr.record_init_class_lowering();
}

static InitClassLoweringPass s_pass;
