/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "KotlinInstanceRewriter.h"
#include "AtomicStatCounter.h"
#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "KotlinLambdaAnalyzer.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SourceBlocksUtils.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
DexField* has_instance_field(DexClass* cls, const DexString* instance) {
  for (auto* filed : cls->get_sfields()) {
    if (filed->get_name() == instance && filed->get_type() == cls->get_type()) {
      return filed;
    }
  }
  return nullptr;
}

} // namespace

KotlinInstanceRewriter::Stats KotlinInstanceRewriter::collect_instance_usage(
    const Scope& scope,
    ConcurrentMap<DexFieldRef*,
                  std::set<std::pair<IRInstruction*, DexMethod*>>>&
        concurrent_instance_map) {
  // Collect all the types which are of Kotlin classes which sets INSTANCE
  // variable.
  // Get all the uses of the INSTANCE variables whose <init> does not have
  // side effects
  KotlinInstanceRewriter::Stats stats{};
  AtomicStatCounter<size_t> lambda_without_instance_count{0};
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (!can_rename(cls) || !can_delete(cls)) {
      return;
    }
    if (auto analyzer = KotlinLambdaAnalyzer::for_class(cls);
        !analyzer || !analyzer->is_non_capturing()) {
      return;
    }
    auto* instance = has_instance_field(cls, m_instance);
    if (instance == nullptr) {
      lambda_without_instance_count++;
      return;
    }
    if (concurrent_instance_map.count(instance) != 0u) {
      return;
    }
    std::set<std::pair<IRInstruction*, DexMethod*>> insns;
    concurrent_instance_map.emplace(instance, insns);
  });
  stats.kotlin_new_instance = concurrent_instance_map.size();
  stats.kotlin_lambda_without_instance = lambda_without_instance_count;
  return stats;
}

KotlinInstanceRewriter::Stats KotlinInstanceRewriter::remove_escaping_instance(
    const Scope& scope,
    ConcurrentMap<DexFieldRef*,
                  std::set<std::pair<IRInstruction*, DexMethod*>>>&
        concurrent_instance_map) {
  ConcurrentSet<DexFieldRef*> remove_list;
  // A method handle that gets or puts INSTANCE cannot be rewritten into a new
  // instance, and would name the removed field. Code, static field values and
  // annotations can hold one.
  const auto named_by_method_handles =
      method::gather_fields_named_by_method_handles(scope);
  for (const auto& [field, _] : UnorderedIterable(concurrent_instance_map)) {
    if (named_by_method_handles.count(field->as_def()) != 0u) {
      remove_list.insert(field);
    }
  }
  // Get all the single uses of the INSTANCE variables
  KotlinInstanceRewriter::Stats total_stats =
      walk::parallel::methods<KotlinInstanceRewriter::Stats>(
          scope, [&](DexMethod* method) {
            KotlinInstanceRewriter::Stats stats{};
            auto* code = method->get_code();
            if (code == nullptr) {
              return stats;
            }

            always_assert(method->get_code()->cfg_built());
            auto& cfg = method->get_code()->cfg();
            auto iterable = cfg::InstructionIterable(cfg);
            for (auto it = iterable.begin(); it != iterable.end(); it++) {
              auto* insn = it->insn;
              for_each_field_access(insn, [&](IROpcode op, DexFieldRef* field,
                                              const DexMethodHandle*) {
                if (!opcode::is_an_sget(op) && !opcode::is_an_sput(op)) {
                  return;
                }
                if (concurrent_instance_map.count(field) == 0u) {
                  return;
                }
                if (remove_list.count(field) != 0u) {
                  return;
                }
                // If there is more SPUT otherthan the initial one.
                if (opcode::is_an_sput(op)) {
                  if (method::is_clinit(method) &&
                      method->get_class() == field->get_type()) {
                    return;
                  }
                  // Erase if the field is written elsewhere.
                  remove_list.insert(field);
                  return;
                }

                concurrent_instance_map.update(
                    field,
                    [&](DexFieldRef*,
                        std::set<std::pair<IRInstruction*, DexMethod*>>& s,
                        bool /* exists */) {
                      s.insert(std::make_pair(insn, method));
                    });
              });
            }
            return stats;
          });
  for (auto* field : UnorderedIterable(remove_list)) {
    concurrent_instance_map.erase(field);
  }
  return total_stats;
}

KotlinInstanceRewriter::Stats KotlinInstanceRewriter::transform(
    ConcurrentMap<DexFieldRef*,
                  std::set<std::pair<IRInstruction*, DexMethod*>>>&
        concurrent_instance_map) {
  // Among the Kotlin classes which sets INSTANCE and whose use is cleary
  // defined, select singles use INSTANCEs. Remove the INSTANCE initialization
  // in <clinit> and replace the SGET INSTANCE with a new INSTANCE.
  std::vector<DexFieldRef*> fields_to_rewrite;
  KotlinInstanceRewriter::Stats stats = {};
  for (const auto& it : UnorderedIterable(concurrent_instance_map)) {
    if (it.second.size() > max_no_of_instance) {
      continue;
    }
    const std::set<std::pair<IRInstruction*, DexMethod*>>& insns = it.second;
    if (insns.empty()) {
      continue;
    }
    auto* field = it.first;
    fields_to_rewrite.push_back(field);
  }
  std::sort(fields_to_rewrite.begin(), fields_to_rewrite.end(),
            compare_dexfields);

  for (auto* field : fields_to_rewrite) {
    stats.kotlin_instances_with_single_use++;
    // Remove instance from cls
    auto* cls = type_class(field->get_class());
    auto dmethods = cls->get_dmethods();
    for (auto* meth : dmethods) {
      if (method::is_clinit(meth)) {
        auto& cfg = meth->get_code()->cfg();
        cfg::CFGMutation m(cfg);
        TRACE(KOTLIN_INSTANCE, 5, "%s <clinit> before\n%s", SHOW(cls),
              SHOW(cfg));
        auto iterable = cfg::InstructionIterable(cfg);
        for (auto insn_it = iterable.begin(); insn_it != iterable.end();
             insn_it++) {
          auto* insn = insn_it->insn;
          if (!opcode::is_an_sput(insn->opcode()) ||
              insn->get_field() != field) {
            continue;
          }

          m.remove(insn_it);
          stats.kotlin_instance_fields_removed++;
        }
        m.flush();
        TRACE(KOTLIN_INSTANCE, 5, "%s <clinit> after\n%s", SHOW(cls),
              SHOW(cfg));
        break;
      }
    }

    // Convert INSTANCE read to new instance creation
    for (const auto& method_it : concurrent_instance_map.find(field)->second) {
      auto* meth = method_it.second;
      auto& cfg = meth->get_code()->cfg();
      cfg::CFGMutation m(cfg);
      TRACE(KOTLIN_INSTANCE, 5, "%s before\n%s", SHOW(meth), SHOW(cfg));
      DexMethodRef* init = DexMethod::get_method(
          cls->get_type(), DexString::make_string("<init>"),
          DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})));
      always_assert(init);
      // Make this constructor publcic
      set_public(init->as_def());
      std::vector<IRInstruction*> init_insns_to_fix;
      auto iterable = cfg::InstructionIterable(cfg);
      for (auto insn_it = iterable.begin(); insn_it != iterable.end();
           insn_it++) {
        auto* insn = insn_it->insn;
        if (!opcode::is_an_sget(insn->opcode()) || insn->get_field() != field) {
          continue;
        }
        auto move_result_it = cfg.move_result_of(insn_it);
        IRInstruction* new_isn = new IRInstruction(OPCODE_NEW_INSTANCE);
        new_isn->set_type(cls->get_type());
        IRInstruction* mov_result =
            new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
        mov_result->set_dest(move_result_it->insn->dest());
        IRInstruction* init_isn = new IRInstruction(OPCODE_INVOKE_DIRECT);
        init_isn->set_method(init)->set_srcs_size(1)->set_src(
            0, move_result_it->insn->dest());
        auto* sb = source_blocks::get_last_source_block_before(
            insn_it.block(), insn_it.unwrap());
        std::vector<MethodItemEntry> replacement;
        replacement.emplace_back(new_isn);
        replacement.emplace_back(mov_result);
        if (sb != nullptr) {
          replacement.emplace_back(source_blocks::clone_as_synthetic(sb));
        }
        replacement.emplace_back(init_isn);
        if (sb != nullptr) {
          replacement.emplace_back(source_blocks::clone_as_synthetic(sb));
        }
        init_insns_to_fix.push_back(init_isn);
        m.replace_mie(insn_it, std::move(replacement));
        m.remove(move_result_it);
        stats.kotlin_new_inserted++;
      }
      m.flush();
      for (auto* block : cfg.blocks()) {
        auto last_insn_it = block->get_last_insn();
        if (last_insn_it == block->end()) {
          continue;
        }
        for (auto* tracked_init : init_insns_to_fix) {
          if (last_insn_it->insn == tracked_init) {
            auto* sb_ptr = source_blocks::get_first_source_block(block);
            if (sb_ptr != nullptr) {
              source_blocks::impl::BlockAccessor::insert_source_block_after(
                  block, last_insn_it,
                  source_blocks::clone_as_synthetic(sb_ptr));
            }
            break;
          }
        }
      }
      TRACE(KOTLIN_INSTANCE, 5, "%s after\n%s", SHOW(meth), SHOW(cfg));
    }
    cls->remove_field(resolve_field(field));
  }
  return stats;
}

void KotlinInstanceRewriter::Stats::report(PassManager& mgr) const {
  mgr.incr_metric("kotlin_new_instance", kotlin_new_instance);
  mgr.incr_metric("kotlin_new_instance_which_escapes",
                  kotlin_new_instance_which_escapes);
  mgr.incr_metric("kotlin_instances_with_single_use",
                  kotlin_instances_with_single_use);
  mgr.incr_metric("kotlin_instance_fields_removed",
                  kotlin_instance_fields_removed);
  mgr.incr_metric("kotlin_new_inserted", kotlin_new_inserted);
  mgr.incr_metric("kotlin_lambda_without_instance",
                  kotlin_lambda_without_instance);

  TRACE(KOTLIN_INSTANCE, 1, "kotlin_new_instance = %zu", kotlin_new_instance);
  TRACE(KOTLIN_INSTANCE, 1, "kotlin_new_instance_which_escapes = %zu",
        kotlin_new_instance_which_escapes);
  TRACE(KOTLIN_INSTANCE, 1, "kotlin_instances_with_single_use = %zu",
        kotlin_instances_with_single_use);
  TRACE(KOTLIN_INSTANCE, 1, "kotlin_instance_fields_removed = %zu",
        kotlin_instance_fields_removed);
  TRACE(KOTLIN_INSTANCE, 1, "kotlin_new_inserted = %zu", kotlin_new_inserted);
  TRACE(KOTLIN_INSTANCE, 1, "kotlin_lambda_without_instance = %zu",
        kotlin_lambda_without_instance);
}
