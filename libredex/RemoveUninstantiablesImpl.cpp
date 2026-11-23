/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveUninstantiablesImpl.h"

#include <cinttypes>

#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "MethodFixup.h"
#include "NullPointerExceptionUtil.h"
#include "PassManager.h"
#include "ScopedCFG.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {

/// \return a new \c IRInstruction representing a `const` operation writing
/// literal \p lit into register \p dest.
IRInstruction* ir_const(uint32_t dest, int64_t lit) {
  auto* insn = new IRInstruction(OPCODE_CONST);
  insn->set_dest(dest);
  insn->set_literal(lit);
  return insn;
}

/// \return a new \c IRInstruction representing a `unreachable` operation
/// writing the impossible value into register \p dest.
IRInstruction* ir_unreachable(uint32_t dest) {
  auto* insn = new IRInstruction(IOPCODE_UNREACHABLE);
  insn->set_dest(dest);
  return insn;
}

/// \return a new \c IRInstruction representing a `throw` operation, throwing
/// the contents of register \p src.
IRInstruction* ir_throw(uint32_t src) {
  auto* insn = new IRInstruction(OPCODE_THROW);
  insn->set_src(0, src);
  return insn;
}

/// \return a new \c IRInstruction representing a `check-cast` operation,
/// verifying that \p src is compatible with \p type.
IRInstruction* ir_check_cast(uint32_t src, DexType* type) {
  auto* insn = new IRInstruction(OPCODE_CHECK_CAST);
  insn->set_src(0, src);
  insn->set_type(type);
  return insn;
}

/// \return a new \c IRInstruction representing a `move-result-pseudo-object`
/// operation.
IRInstruction* ir_move_result_pseudo_object(uint32_t dest) {
  auto* insn = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  insn->set_dest(dest);
  return insn;
}

} // namespace

namespace remove_uninstantiables_impl {

Stats& Stats::operator+=(const Stats& that) {
  this->instance_ofs += that.instance_ofs;
  this->invokes += that.invokes;
  this->field_accesses_on_uninstantiable +=
      that.field_accesses_on_uninstantiable;
  this->throw_null_methods += that.throw_null_methods;
  this->abstracted_classes += that.abstracted_classes;
  this->abstracted_vmethods += that.abstracted_vmethods;
  this->removed_vmethods += that.removed_vmethods;
  this->get_uninstantiables += that.get_uninstantiables;
  this->invoke_uninstantiables += that.invoke_uninstantiables;
  this->check_casts += that.check_casts;
  return *this;
}

Stats Stats::operator+(const Stats& that) const {
  auto copy = *this;
  copy += that;
  return copy;
}

void Stats::report(PassManager& mgr) const {
#define REPORT(STAT)                                                           \
  do {                                                                         \
    mgr.incr_metric(#STAT, STAT);                                              \
    TRACE(                                                                     \
        RMUNINST, 2, "  " #STAT ": %d/%" PRId64, STAT, mgr.get_metric(#STAT)); \
  } while (0)

  TRACE(RMUNINST, 2, "RemoveUninstantiablesImpl Stats:");

  REPORT(instance_ofs);
  REPORT(invokes);
  REPORT(field_accesses_on_uninstantiable);
  REPORT(throw_null_methods);
  REPORT(abstracted_classes);
  REPORT(abstracted_vmethods);
  REPORT(removed_vmethods);
  REPORT(get_uninstantiables);
  REPORT(invoke_uninstantiables);
  REPORT(check_casts);

#undef REPORT
}

Stats replace_uninstantiable_refs(
    const UnorderedSet<const DexType*>& scoped_uninstantiable_types,
    cfg::ControlFlowGraph& cfg) {
  cfg::CFGMutation m(cfg);

  Stats stats;
  auto ii = InstructionIterable(cfg);
  npe::NullPointerExceptionCreator npe_creator(&cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    auto op = insn->opcode();
    switch (op) {
    case OPCODE_INSTANCE_OF:
      if (scoped_uninstantiable_types.count(insn->get_type()) != 0u) {
        auto dest = cfg.move_result_of(it)->insn->dest();
        m.replace(it, {ir_const(dest, 0)});
        stats.instance_ofs++;
      }
      continue;

    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_SUPER:
      // Note that we don't want to call resolve_method here: The most precise
      // class information is already present in the supplied method reference,
      // which gives us the best chance of finding an uninstantiable type.
      if (scoped_uninstantiable_types.count(insn->get_method()->get_class()) !=
          0u) {
        auto* sb = source_blocks::get_last_source_block_before(it.block(),
                                                               it.unwrap());
        m.replace_mie(it, npe_creator.get_insns(insn, sb));
        stats.invokes++;
      }
      continue;

    case OPCODE_CHECK_CAST:
      if (scoped_uninstantiable_types.count(insn->get_type()) != 0u) {
        auto src = insn->src(0);
        auto dest = cfg.move_result_of(it)->insn->dest();
        m.replace(it,
                  {ir_check_cast(src, type::java_lang_Void()),
                   ir_move_result_pseudo_object(dest), ir_const(src, 0),
                   ir_const(dest, 0)});
        stats.check_casts++;
      }
      continue;

    default:
      break;
    }

    if (opcode::is_an_iget(op) && (scoped_uninstantiable_types.count(
                                       insn->get_field()->get_class()) != 0u)) {
      auto* sb =
          source_blocks::get_last_source_block_before(it.block(), it.unwrap());
      m.replace_mie(it, npe_creator.get_insns(insn, sb));
      stats.field_accesses_on_uninstantiable++;
      continue;
    }

    if (opcode::is_an_iput(op) && (scoped_uninstantiable_types.count(
                                       insn->get_field()->get_class()) != 0u)) {
      auto* sb =
          source_blocks::get_last_source_block_before(it.block(), it.unwrap());
      m.replace_mie(it, npe_creator.get_insns(insn, sb));
      stats.field_accesses_on_uninstantiable++;
      continue;
    }

    if ((opcode::is_an_iget(op) || opcode::is_an_sget(op)) &&
        (scoped_uninstantiable_types.count(insn->get_field()->get_type()) !=
         0u)) {
      auto dest = cfg.move_result_of(it)->insn->dest();
      m.replace(it, {ir_const(dest, 0)});
      stats.get_uninstantiables++;
      continue;
    }

    if (opcode::is_a_method_invoke(op) &&
        (scoped_uninstantiable_types.count(
             insn->get_method()->get_proto()->get_rtype()) != 0u)) {
      auto move_result_it = cfg.move_result_of(it);
      if (!move_result_it.is_end()) {
        auto dest = move_result_it->insn->dest();
        m.replace(move_result_it, {ir_const(dest, 0)});
        stats.invoke_uninstantiables++;
      }
      continue;
    }
  }

  m.flush();
  return stats;
}

Stats replace_all_with_unreachable_throw(cfg::ControlFlowGraph& cfg) {
  auto* entry = cfg.entry_block();
  always_assert_log(entry, "Expect an entry block");

  auto it = entry->to_cfg_instruction_iterator(
      entry->get_first_non_param_loading_insn());
  always_assert_log(!it.is_end(), "Expecting a non-param loading instruction");

  auto tmp = cfg.allocate_temp();
  cfg.insert_before(it, {ir_unreachable(tmp), ir_throw(tmp)});

  Stats stats;
  stats.throw_null_methods++;
  return stats;
}

Stats reduce_uncallable_instance_methods(
    const Scope& scope,
    const ConcurrentSet<DexMethod*>& uncallable_instance_methods,
    const std::function<bool(const DexMethod*)>& is_implementation_method) {
  // We perform structural changes, i.e. whether a method has a body and
  // removal, as a post-processing step, to streamline the main operations
  struct ClassPostProcessing {
    UnorderedMap<DexMethod*, DexMethod*> remove_vmethods;
    UnorderedSet<DexMethod*> abstract_vmethods;
  };
  ConcurrentMap<DexClass*, ClassPostProcessing> class_post_processing;
  std::mutex stats_mutex;
  Stats stats;
  workqueue_run<DexMethod*>(
      [&](DexMethod* method) {
        auto* overridden_method =
            method->is_virtual()
                ? resolve_method_deprecated(method, MethodSearch::Super, method)
                : nullptr;
        auto* method_cls = type_class(method->get_class());
        if (overridden_method == nullptr && method->is_virtual() &&
            !is_implementation_method(method)) {
          class_post_processing.update(
              method_cls, [method](DexClass*, ClassPostProcessing& cpp, bool) {
                cpp.abstract_vmethods.insert(method);
              });
          std::lock_guard<std::mutex> lock_guard(stats_mutex);
          stats.abstracted_vmethods++;
        } else if (overridden_method != nullptr && can_delete(method) &&
                   get_visibility(method) ==
                       get_visibility(overridden_method) &&
                   !is_implementation_method(method)) {
          // We require same visibility, as we are going to remove the method
          // and rewrite all references to the overridden method. TODO: Consider
          // upgrading the visibility of the overridden method.
          always_assert(overridden_method != method);
          class_post_processing.update(
              method_cls,
              [method,
               overridden_method](DexClass*, ClassPostProcessing& cpp, bool) {
                cpp.remove_vmethods.emplace(method, overridden_method);
              });
          std::lock_guard<std::mutex> lock_guard(stats_mutex);
          stats.removed_vmethods++;
        } else {
          cfg::ScopedCFG cfg(method->get_code());
          auto method_stats =
              remove_uninstantiables_impl::replace_all_with_unreachable_throw(
                  *cfg);
          std::lock_guard<std::mutex> lock_guard(stats_mutex);
          stats += method_stats;
        }
      },
      uncallable_instance_methods);

  // Post-processing:
  // 1. make methods abstract (pretty straightforward), and
  // 2. remove methods (per class in parallel for best performance, and rewrite
  // all invocation references)
  std::vector<DexClass*> classes_with_removed_vmethods;
  UnorderedMap<DexMethodRef*, DexMethodRef*> removed_vmethods;
  for (auto& p : UnorderedIterable(class_post_processing)) {
    auto* cls = p.first;
    auto& cpp = p.second;
    if (!cpp.abstract_vmethods.empty()) {
      if (!is_abstract(cls)) {
        stats.abstracted_classes++;
        cls->set_access((cls->get_access() & ~ACC_FINAL) | ACC_ABSTRACT);
      }
      for (auto* method : UnorderedIterable(cpp.abstract_vmethods)) {
        method->set_access(
            (DexAccessFlags)((method->get_access() & ~ACC_FINAL) |
                             ACC_ABSTRACT));
        method->set_code(nullptr);
      }
    }
    if (!cpp.remove_vmethods.empty()) {
      classes_with_removed_vmethods.push_back(cls);
      insert_unordered_iterable(removed_vmethods, cpp.remove_vmethods);
    }
  }

  walk::parallel::classes(
      classes_with_removed_vmethods, [&class_post_processing](DexClass* cls) {
        auto& cpp = class_post_processing.at_unsafe(cls);
        for (auto& p : UnorderedIterable(cpp.remove_vmethods)) {
          cls->remove_method(p.first);
          DexMethod::delete_method(p.first);
        }
      });

  // Forward chains.
  method_fixup::fixup_references_to_removed_methods(scope, removed_vmethods);

  return stats;
}

} // namespace remove_uninstantiables_impl
