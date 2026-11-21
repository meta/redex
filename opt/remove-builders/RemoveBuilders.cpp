/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveBuilders.h"

#include "ConfigFiles.h"
#include "Dataflow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "PassManager.h"
#include "RemoveBuildersHelper.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

constexpr const char* METRIC_CLASSES_REMOVED = "classes_removed";
constexpr const char* METRIC_FIELDS_REMOVED = "fields_removed";
constexpr const char* METRIC_METHODS_REMOVED = "methods_removed";
constexpr const char* METRIC_METHODS_CLEARED = "methods_cleared";

struct builder_counters {
  size_t classes_removed;
  size_t fields_removed;
  size_t methods_removed;
  size_t methods_cleared;
};

builder_counters b_counter;

// checks if the `this` argument on an instance method ever gets passed to
// a method that doesn't belong to the same instance, or if it gets stored
// in a field, or if it escapes as a return value.
bool this_arg_escapes(DexMethod* method, bool enable_buildee_constr_change) {
  always_assert(method != nullptr);
  always_assert(!(method->get_access() & ACC_STATIC));

  auto* code = method->get_code();
  auto& cfg = code->cfg();
  auto* this_insn = cfg.get_first_param_instruction();
  always_assert(this_insn != nullptr &&
                this_insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT);
  auto regs_size = cfg.get_registers_size();
  auto* this_cls = method->get_class();
  const auto& blocks = cfg.blocks_reverse_post_deprecated();
  std::function<void(cfg::InstructionIterator, TaintedRegs*)> trans =
      [&](const cfg::InstructionIterator& it, TaintedRegs* tregs) {
        auto* insn = it->insn;
        if (insn == this_insn) {
          tregs->m_reg_set[insn->dest()] = true;
        } else {
          transfer_object_reach(this_cls, regs_size, insn, tregs->m_reg_set);
        }
      };
  auto taint_map =
      forwards_dataflow(cfg.entry_block(),
                        blocks,
                        TaintedRegs(static_cast<int>(regs_size + 1)),
                        trans);
  return tainted_reg_escapes(
      this_cls, method, *taint_map, enable_buildee_constr_change);
}

bool this_arg_escapes(DexClass* cls, bool enable_buildee_constr_change) {
  always_assert(cls != nullptr);

  bool result = false;
  for (DexMethod* m : cls->get_dmethods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (((m->get_access() & ACC_STATIC) == 0u) &&
        this_arg_escapes(m, enable_buildee_constr_change)) {
      TRACE(BUILDERS,
            3,
            "this escapes in %s",
            m->get_deobfuscated_name().c_str());
      result = true;
    }
  }
  for (DexMethod* m : cls->get_vmethods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (this_arg_escapes(m, enable_buildee_constr_change)) {
      TRACE(BUILDERS,
            3,
            "this escapes in %s",
            m->get_deobfuscated_name().c_str());
      result = true;
    }
  }
  return result;
}

std::vector<DexMethod*> get_static_methods(
    const std::vector<DexMethod*>& dmethods) {
  std::vector<DexMethod*> static_methods;

  for (const auto& dmethod : dmethods) {
    if (is_static(dmethod)) {
      static_methods.emplace_back(dmethod);
    }
  }

  return static_methods;
}

/**
 * First pass through what "trivial builder" means:
 *  - is a builder
 *  - it doesn't escape stack
 *  - has no static methods
 *  - has no static fields
 */
UnorderedSet<DexClass*> get_trivial_builders(
    const UnorderedSet<const DexType*>& builders,
    const UnorderedSet<const DexType*>& stack_only_builders) {

  UnorderedSet<DexClass*> trivial_builders;

  for (const DexType* builder_type : UnorderedIterable(builders)) {
    DexClass* builder_class = type_class(builder_type);

    // Filter out builders that escape the stack.
    if (stack_only_builders.find(builder_type) == stack_only_builders.end()) {
      continue;
    }

    // Filter out builders that do "extra work".
    bool has_static_methods =
        !get_static_methods(builder_class->get_dmethods()).empty();

    if (has_static_methods || !builder_class->get_sfields().empty()) {
      continue;
    }

    DexType* buildee_type = get_buildee(builder_class->get_type());
    if (buildee_type == nullptr) {
      continue;
    }

    trivial_builders.emplace(builder_class);
  }

  return trivial_builders;
}

void gather_removal_builder_stats(
    const UnorderedSet<DexClass*>& builders,
    const UnorderedSet<DexClass*>& kept_builders) {

  for (DexClass* builder : UnorderedIterable(builders)) {
    if (kept_builders.find(builder) == kept_builders.end()) {
      b_counter.classes_removed++;
      b_counter.methods_removed +=
          builder->get_vmethods().size() + builder->get_dmethods().size();
      b_counter.fields_removed += builder->get_ifields().size();
    }
  }
}

UnorderedSet<DexClass*> get_builders_with_subclasses(Scope& classes) {
  UnorderedSet<DexClass*> builders_with_subclasses;

  for (const auto& cls : classes) {
    DexType* super_type = cls->get_super_class();
    if (super_type == nullptr) {
      continue;
    }

    DexClass* super_cls = type_class(super_type);
    if (super_cls == nullptr) {
      continue;
    }

    if (has_builder_name(super_type)) {
      builders_with_subclasses.emplace(super_cls);
    }
  }

  return builders_with_subclasses;
}

} // namespace

std::vector<const DexType*> RemoveBuildersPass::created_builders(DexMethod* m) {
  always_assert(m != nullptr);

  std::vector<const DexType*> builders;
  auto* code = m->get_code();
  if (code == nullptr) {
    return builders;
  }
  auto& cfg = code->cfg();
  for (auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_NEW_INSTANCE) {
      const DexType* cls = insn->get_type();
      if (m_builders.find(cls) != m_builders.end()) {
        builders.emplace_back(cls);
      }
    }
  }
  return builders;
}

// checks if any instances of :builder that get created in the method ever get
// passed to a method (aside from when its own instance methods get invoked),
// or if they get stored in a field, or if they escape as a return value.
bool RemoveBuildersPass::escapes_stack(const DexType* builder,
                                       DexMethod* method) {
  always_assert(builder != nullptr);
  always_assert(method != nullptr);

  auto* code = method->get_code();
  auto& cfg = code->cfg();
  const auto& blocks = cfg.blocks_reverse_post_deprecated();
  auto regs_size = cfg.get_registers_size();
  auto taint_map = get_tainted_regs(cfg, regs_size, blocks, builder);
  return tainted_reg_escapes(
      builder, method, *taint_map, m_enable_buildee_constr_change);
}

void RemoveBuildersPass::run_pass(DexStoresVector& stores,
                                  ConfigFiles& conf,
                                  PassManager& mgr) {
  // Initialize couters.
  b_counter = {0, 0, 0, 0};

  auto* obj_type = type::java_lang_Object();
  auto scope = build_class_scope(stores);
  for (DexClass* cls : scope) {
    if (is_annotation(cls) || is_interface(cls) ||
        cls->get_super_class() != obj_type) {
      continue;
    }

    if (has_builder_name(cls->get_type())) {
      m_builders.emplace(cls->get_type());
    }
  }

  UnorderedSet<const DexType*> escaped_builders;
  walk::methods(scope, [&](DexMethod* m) {
    auto builders = created_builders(m);
    for (const DexType* builder : builders) {
      if (escapes_stack(builder, m)) {
        TRACE(BUILDERS,
              3,
              "%s escapes in %s",
              SHOW(builder),
              m->get_deobfuscated_name().c_str());
        escaped_builders.emplace(builder);
      }
    }
  });

  UnorderedSet<const DexType*> stack_only_builders;
  for (const DexType* builder : UnorderedIterable(m_builders)) {
    if (escaped_builders.find(builder) == escaped_builders.end()) {
      stack_only_builders.emplace(builder);
    }
  }

  UnorderedSet<const DexType*> builders_and_supers;
  for (const DexType* builder : UnorderedIterable(stack_only_builders)) {
    const DexType* cls = builder;
    while (cls != nullptr && cls != obj_type) {
      builders_and_supers.emplace(cls);
      cls = type_class(cls)->get_super_class();
    }
  }

  UnorderedSet<const DexType*> this_escapes;
  for (const DexType* cls_ty : UnorderedIterable(builders_and_supers)) {
    DexClass* cls = type_class(cls_ty);
    if (cls->is_external() ||
        this_arg_escapes(cls, m_enable_buildee_constr_change)) {
      this_escapes.emplace(cls_ty);
    }
  }

  // set of builders that neither escape the stack nor pass their 'this' arg
  // to another function
  UnorderedSet<const DexType*> no_escapes;
  for (const DexType* builder : UnorderedIterable(stack_only_builders)) {
    const DexType* cls = builder;
    bool hierarchy_has_escape = false;
    while (cls != nullptr) {
      if (this_escapes.find(cls) != this_escapes.end()) {
        hierarchy_has_escape = true;
        break;
      }
      cls = type_class(cls)->get_super_class();
    }
    if (!hierarchy_has_escape) {
      no_escapes.emplace(builder);
    }
  }

  size_t dmethod_count = 0;
  size_t vmethod_count = 0;
  size_t build_count = 0;
  for (const DexType* builder : UnorderedIterable(no_escapes)) {
    auto* cls = type_class(builder);
    auto* buildee = get_buildee(builder);
    dmethod_count += cls->get_dmethods().size();
    vmethod_count += cls->get_vmethods().size();
    for (DexMethod* m : cls->get_vmethods()) {
      if (m->get_proto()->get_rtype() == buildee) {
        build_count++;
      }
    }
  }

  UnorderedSet<DexClass*> trivial_builders =
      get_trivial_builders(m_builders, no_escapes);

  UnorderedSet<DexClass*> kept_builders = get_builders_with_subclasses(scope);

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());
  BuilderTransform b_transform(
      init_classes_with_side_effects,
      *conf.get_global_config().get_config_by_name<InlinerConfig>("inliner"),
      scope,
      stores,
      conf,
      false);

  // Inline non init methods.
  UnorderedSet<DexClass*> removed_builders;
  walk::methods(scope, [&](DexMethod* method) {
    auto builders = created_builders(method);

    for (const DexType* builder : builders) {
      if (method->get_class() == builder) {
        continue;
      }

      DexClass* builder_cls = type_class(builder);

      // Filter out builders that we cannot remove.
      if (kept_builders.find(builder_cls) != kept_builders.end()) {
        continue;
      }
      if (m_blocklist.find(builder) != m_blocklist.end()) {
        TRACE(BUILDERS, 2, "Skipping excluded type %s", SHOW(builder));
        continue;
      }

      // Check it is a trivial one.
      if (trivial_builders.find(builder_cls) != trivial_builders.end()) {

        DexMethod* method_copy = DexMethod::make_method_from(
            method,
            method->get_class(),
            DexString::make_string(method->get_name()->str() +
                                   "$redex_builders"));
        bool was_not_removed =
            !b_transform.inline_methods(
                method, builder, &get_non_init_methods) ||
            !remove_builder_from(method, builder_cls, b_transform);

        if (was_not_removed) {
          kept_builders.emplace(builder_cls);
          method->set_code(method_copy->release_code());
        } else {
          b_counter.methods_cleared++;
          removed_builders.emplace(builder_cls);
        }

        DexMethod::delete_method_DO_NOT_USE(method_copy);
      }
    }
  });

  // No need to remove the builders here, since `RemoveUnreachable` will
  // take care of it.
  gather_removal_builder_stats(removed_builders, kept_builders);

  mgr.set_metric("total_builders", m_builders.size());
  mgr.set_metric("stack_only_builders", stack_only_builders.size());
  mgr.set_metric("no_escapes", no_escapes.size());
  mgr.incr_metric(METRIC_CLASSES_REMOVED, b_counter.classes_removed);
  mgr.incr_metric(METRIC_METHODS_REMOVED, b_counter.methods_removed);
  mgr.incr_metric(METRIC_FIELDS_REMOVED, b_counter.fields_removed);
  mgr.incr_metric(METRIC_METHODS_CLEARED, b_counter.methods_cleared);

  TRACE(BUILDERS, 1, "Total builders: %zu", m_builders.size());
  TRACE(BUILDERS, 1, "Stack-only builders: %zu", stack_only_builders.size());
  TRACE(BUILDERS,
        1,
        "Stack-only builders that don't let `this` escape: %zu",
        no_escapes.size());
  TRACE(BUILDERS, 1, "Stats for unescaping builders:");
  TRACE(BUILDERS, 1, "\tdmethods: %zu", dmethod_count);
  TRACE(BUILDERS, 1, "\tvmethods: %zu", vmethod_count);
  TRACE(BUILDERS, 1, "\tbuild methods: %zu", build_count);
  TRACE(BUILDERS, 1, "Trivial builders: %zu", trivial_builders.size());
  TRACE(BUILDERS, 1, "Classes removed: %zu", b_counter.classes_removed);
  TRACE(BUILDERS, 1, "Methods removed: %zu", b_counter.methods_removed);
  TRACE(BUILDERS, 1, "Fields removed: %zu", b_counter.fields_removed);
  TRACE(BUILDERS, 1, "Methods cleared: %zu", b_counter.methods_cleared);

  b_transform.flush();
}

static RemoveBuildersPass s_pass;
