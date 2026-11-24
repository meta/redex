/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveNullcheckStringArg.h"

#include "CFGMutation.h"
#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ReachingDefinitions.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace kotlin_nullcheck_wrapper;

void RemoveNullcheckStringArg::run_pass(DexStoresVector& stores,
                                        ConfigFiles& /*conf*/,
                                        PassManager& mgr) {
  TransferMapForParam transfer_map_param;
  TransferMapForExpr transfer_map_expr;

  UnorderedSet<DexMethod*> new_methods;
  if (!setup(transfer_map_param, transfer_map_expr, new_methods)) {
    TRACE(NULLCHECK, 2, "RemoveNullcheckStringArgPass: setup failed");
    return;
  }

  Scope scope = build_class_scope(stores);
  Stats stats = walk::parallel::methods<Stats>(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (!method::is_optimizable(method) || (new_methods.count(method) != 0u)) {
      return Stats();
    }
    always_assert(code->cfg_built());
    auto local_stats = change_in_cfg(code->cfg(), transfer_map_param,
                                     transfer_map_expr, is_static(method));
    return local_stats;
  });

  stats.report(mgr);
}

bool RemoveNullcheckStringArg::setup(TransferMapForParam& transfer_map_param,
                                     TransferMapForExpr& transfer_map_expr,
                                     UnorderedSet<DexMethod*>& new_methods) {

  DexMethodRef* builtin_param_V1_3 =
      DexMethod::get_method(CHECK_PARAM_NULL_SIGNATURE_V1_3);
  DexMethodRef* builtin_param_V1_4 =
      DexMethod::get_method(CHECK_PARAM_NULL_SIGNATURE_V1_4);
  DexMethodRef* builtin_expr_V1_3 =
      DexMethod::get_method(CHECK_EXPR_NULL_SIGNATURE_V1_3);
  DexMethodRef* builtin_expr_V1_4 =
      DexMethod::get_method(CHECK_EXPR_NULL_SIGNATURE_V1_4);
  if (builtin_param_V1_3 != nullptr) {
    auto* new_check_param_method = get_wrapper_method_with_int_index(
        NEW_CHECK_PARAM_NULL_SIGNATURE_V1_3,
        WRAPPER_CHECK_PARAM_NULL_METHOD_V1_3, builtin_param_V1_3);
    if (new_check_param_method != nullptr) {
      transfer_map_param[builtin_param_V1_3] = new_check_param_method;
      new_methods.insert(new_check_param_method);
    }
  }
  if (builtin_param_V1_4 != nullptr) {
    auto* new_check_param_method = get_wrapper_method_with_int_index(
        NEW_CHECK_PARAM_NULL_SIGNATURE_V1_4,
        WRAPPER_CHECK_PARAM_NULL_METHOD_V1_4, builtin_param_V1_4);
    if (new_check_param_method != nullptr) {
      transfer_map_param[builtin_param_V1_4] = new_check_param_method;
      new_methods.insert(new_check_param_method);
    }
  }

  if (builtin_expr_V1_3 != nullptr) {
    for (auto err : all_NullErrSrc) {
      auto err_msg = get_err_msg(err);
      auto* new_check_expr_method = get_wrapper_method_with_msg(
          NEW_CHECK_EXPR_NULL_SIGNATURE_V1_3_PRE,
          WRAPPER_CHECK_EXPR_NULL_METHOD_V1_3_PRE, err_msg, builtin_expr_V1_3);
      if (new_check_expr_method != nullptr) {
        transfer_map_expr[builtin_expr_V1_3].emplace(err,
                                                     new_check_expr_method);
        new_methods.insert(new_check_expr_method);
      }
    }
  }

  if (builtin_expr_V1_4 != nullptr) {
    for (auto err : all_NullErrSrc) {
      auto err_msg = get_err_msg(err);
      auto* new_check_expr_method = get_wrapper_method_with_msg(
          NEW_CHECK_EXPR_NULL_SIGNATURE_V1_4_PRE,
          WRAPPER_CHECK_EXPR_NULL_METHOD_V1_4_PRE, err_msg, builtin_expr_V1_4);
      if (new_check_expr_method != nullptr) {
        transfer_map_expr[builtin_expr_V1_4].emplace(err,
                                                     new_check_expr_method);
        new_methods.insert(new_check_expr_method);
      }
    }
  }
  /* If we could not generate suitable wrapper method, giveup. */
  if (new_methods.empty()) {
    return false;
  }

  return true;
}

DexMethod* RemoveNullcheckStringArg::get_wrapper_method_with_msg(
    const char* signature,
    const char* name,
    const std::string& msg,
    DexMethodRef* builtin) {
  std::string wrapper_signature;
  wrapper_signature.append(signature);
  wrapper_signature.append(msg);
  wrapper_signature.append(NEW_CHECK_EXPR_NULL_SIGNATURE_POST);
  std::string wrapper_name;
  wrapper_name.append(name);
  wrapper_name.append(msg);
  if (DexMethod::get_method(wrapper_signature) != nullptr) {
    /* Wrapper method already exist. */
    return nullptr;
  }

  auto* host_cls = type_class(builtin->get_class());
  if ((host_cls == nullptr) || host_cls->is_external()) {
    return nullptr;
  }

  DexTypeList* arg_signature =
      DexTypeList::make_type_list({type::java_lang_Object()});
  auto* const proto = DexProto::make_proto(type::_void(), arg_signature);
  MethodCreator method_creator(host_cls->get_type(),
                               DexString::make_string(wrapper_name),
                               proto,
                               ACC_PUBLIC | ACC_STATIC);
  auto obj_arg = method_creator.get_local(0);

  auto* main_block = method_creator.get_main_block();
  auto* if_block = main_block->if_testz(OPCODE_IF_NEZ, obj_arg);
  auto* str_type = DexType::get_type("Ljava/lang/String;");
  if (str_type == nullptr) {
    return nullptr;
  }

  auto str_const = method_creator.make_local(str_type);

  // const-string v2, msg
  if_block->load_const(str_const, DexString::make_string(msg));

  if_block->invoke(OPCODE_INVOKE_STATIC, builtin, {obj_arg, str_const});
  if_block->ret_void();
  main_block->ret_void();

  auto* new_method = method_creator.create();
  new_method->get_code()->build_cfg();
  TRACE(NULLCHECK, 5, "Created Method : %s", SHOW(new_method->get_code()));
  host_cls->add_method(new_method);
  return new_method;
}

DexMethod* RemoveNullcheckStringArg::get_wrapper_method_with_int_index(
    const char* wrapper_signature,
    const char* wrapper_name,
    DexMethodRef* builtin) {

  if (DexMethod::get_method(wrapper_signature) != nullptr) {
    /* Wrapper method already exist. */
    return nullptr;
  }

  auto* host_cls = type_class(builtin->get_class());
  if (host_cls == nullptr) {
    return nullptr;
  }

  DexTypeList* arg_signature =
      DexTypeList::make_type_list({type::java_lang_Object(), type::_int()});
  auto* const proto = DexProto::make_proto(type::_void(), arg_signature);
  MethodCreator method_creator(host_cls->get_type(),
                               DexString::make_string(wrapper_name),
                               proto,
                               ACC_PUBLIC | ACC_STATIC);
  auto obj_arg = method_creator.get_local(0);

  // If the wrapper is going to print the index of the param as a string, we
  // will have to construct a string from the index with additional
  // information as part of the wrapper method.
  auto* main_block = method_creator.get_main_block();
  auto int_ind = method_creator.get_local(1);
  auto* str_type = DexType::get_type("Ljava/lang/String;");
  auto* str_builder_type = DexType::get_type("Ljava/lang/StringBuilder;");
  if ((str_type == nullptr) || (str_builder_type == nullptr)) {
    return nullptr;
  }

  auto* to_str_method = DexMethod::get_method(
      "Ljava/lang/Integer;.toString:(I)Ljava/lang/String;");
  auto* str_builder_init_method =
      DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:()V");
  auto* append_method = method::java_lang_StringBuilder_append_String();
  auto* str_builder_to_str_method = method::java_lang_StringBuilder_toString();

  if (to_str_method == nullptr) {
    return nullptr;
  }
  auto str_ind = method_creator.make_local(str_type);
  auto str_builder = method_creator.make_local(str_builder_type);
  auto str_const = method_creator.make_local(str_type);
  auto str_res = method_creator.make_local(str_type);
  auto* if_block = main_block->if_testz(OPCODE_IF_NEZ, obj_arg);

  // invoke-static {v3}, Ljava/lang/Integer;.toString:(I)Ljava/lang/String;
  if_block->invoke(OPCODE_INVOKE_STATIC, to_str_method, {int_ind});
  // move-result-object v3
  if_block->move_result(str_ind, str_type);
  // new-instance v1, Ljava/lang/StringBuilder;
  if_block->new_instance(str_builder_type, str_builder);
  // invoke-direct {v1}, Ljava/lang/StringBuilder;.<init>:()V
  if_block->invoke(OPCODE_INVOKE_DIRECT, str_builder_init_method,
                   {str_builder});
  // const-string v2, "param index = "
  if_block->load_const(str_const, DexString::make_string("param at index = "));
  // invoke-virtual {v1, v2},
  // Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
  if_block->invoke(OPCODE_INVOKE_VIRTUAL, append_method,
                   {str_builder, str_const});
  // invoke-virtual {v1, v3},
  // Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
  if_block->invoke(OPCODE_INVOKE_VIRTUAL, append_method,
                   {str_builder, str_ind});
  // invoke-virtual {v1},
  // Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;
  if_block->invoke(OPCODE_INVOKE_VIRTUAL, str_builder_to_str_method,
                   {str_builder});
  // move-result-object v3
  if_block->move_result(str_res, str_type);

  if_block->invoke(OPCODE_INVOKE_STATIC, builtin, {obj_arg, str_res});
  if_block->ret_void();
  main_block->ret_void();

  auto* new_method = method_creator.create();
  new_method->get_code()->build_cfg();
  TRACE(NULLCHECK, 5, "Created Method : %s", SHOW(new_method->get_code()));
  host_cls->add_method(new_method);
  return new_method;
}

RemoveNullcheckStringArg::Stats RemoveNullcheckStringArg::change_in_cfg(
    cfg::ControlFlowGraph& cfg,
    const TransferMapForParam& transfer_map_param,
    const TransferMapForExpr& transfer_map_expr,
    bool is_static) {
  Stats stats{};
  cfg::CFGMutation m(cfg);
  auto params = cfg.get_param_instructions();
  UnorderedMap<size_t, int> param_index;
  int arg_index = is_static ? 0 : -1;

  reaching_defs::MoveAwareFixpointIterator reaching_defs_iter(cfg);
  reaching_defs_iter.run({});

  for (const auto& mie : InstructionIterable(params)) {
    auto* load_insn = mie.insn;
    always_assert(opcode::is_a_load_param(load_insn->opcode()));
    param_index.insert(std::make_pair(load_insn->dest(), arg_index++));
  }

  live_range::MoveAwareChains chains(
      cfg, /* ignore_unreachable */ false,
      [&](auto* insn) { return opcode::is_a_load_param(insn->opcode()); });
  live_range::DefUseChains du_chains = chains.get_def_use_chains();

  for (cfg::Block* block : cfg.blocks()) {
    auto env = reaching_defs_iter.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end();
         reaching_defs_iter.analyze_instruction(it++->insn, &env)) {
      auto* insn = it->insn;
      if (insn->opcode() != OPCODE_INVOKE_STATIC) {
        continue;
      }
      auto iter_param = transfer_map_param.find(insn->get_method());
      auto iter_expr = transfer_map_expr.find(insn->get_method());
      if (iter_param == transfer_map_param.end() &&
          iter_expr == transfer_map_expr.end()) {
        continue;
      }
      auto new_insn = std::make_unique<IRInstruction>(OPCODE_INVOKE_STATIC);
      auto defs = env.get(insn->src(0));
      always_assert(!defs.is_bottom() && !defs.is_top());
      if (iter_param != transfer_map_param.end()) {
        // We could have params copied via intermediate registers.
        IRInstruction* param_load_insn = nullptr;
        for (auto* def : defs.elements()) {
          if (!opcode::is_a_load_param(def->opcode())) {
            continue;
          }
          if (param_load_insn != nullptr) {
            /* Multiple param load insns. Should never happen.*/
            param_load_insn = nullptr;
            break;
          }
          param_load_insn = def;
        }
        if (param_load_insn == nullptr) {
          /* No param load insn. Should never happen. In any case, skipping this
           * insn is OK. */
          stats.null_check_insns_unchanged++;
          continue;
        }
        auto param_iter = param_index.find(param_load_insn->dest());
        always_assert(param_iter != param_index.end());

        auto use_set = du_chains[param_load_insn];
        if (use_set.size() == 1) {
          for (const auto& p : UnorderedIterable(use_set)) {
            always_assert(p.insn == insn);
          }
          // If we have single use which is null check, remove null check.
          m.remove(cfg.find_insn(insn));
          continue;
        }

        auto index = param_iter->second;
        // If for any reason we have assertion on this pointer
        if (index == -1) {
          stats.null_check_insns_unchanged++;
          continue;
        }
        auto tmp_reg = cfg.allocate_temp();
        IRInstruction* cst_insn = new IRInstruction(OPCODE_CONST);
        cst_insn->set_literal(index)->set_dest(tmp_reg);
        new_insn->set_method(iter_param->second)
            ->set_srcs_size(2)
            ->set_src(0, insn->src(0))
            ->set_src(1, tmp_reg);
        m.replace(cfg.find_insn(insn), {cst_insn, new_insn.release()});
      } else {
        // Handle null check for expr. Get the proper wrapper function to throw
        // more accurate exception message.
        always_assert(!defs.empty());
        auto* def = *defs.elements().begin();
        NullErrSrc err_msg;
        if (defs.size() > 1) {
          // Should never happened based on the way that null_check is inserted
          // by Kotlin compiler.
          // https://github.com/JetBrains/kotlin/blob/1e5fc1c3aa1e682f9ae2ef6b61d373d74e51bc11/compiler/backend/src/org/jetbrains/kotlin/codegen/optimization/nullCheck/RedundantNullCheckMethodTransformer.kt
          // In this case, we still do the opt, but mark the error msg as
          // UNKNOWN.
          TRACE(
              NULLCHECK, 2,
              "[Remove null check] defs.size() = %zu of the dest of insn %s \n",
              defs.size(), SHOW(insn));
          err_msg = NullErrSrc::UNKNOWN_SRC;
        } else {
          err_msg = get_wrapper_code(def->opcode());
        }
        auto new_it = iter_expr->second.find(err_msg);
        if (new_it == iter_expr->second.end()) {
          // This means the wrapper method is not created.
          stats.null_check_insns_unchanged++;
          continue;
        }
        if (err_msg == NullErrSrc::UNKNOWN_SRC) {
          stats.null_check_src_unknown++;
        }
        new_insn->set_method(new_it->second)
            ->set_srcs_size(1)
            ->set_src(0, insn->src(0));
        m.replace(cfg.find_insn(insn), {new_insn.release()});
      }
      stats.null_check_insns_changed++;
    }
  }

  m.flush();
  return stats;
}

void RemoveNullcheckStringArg::Stats::report(PassManager& mgr) const {
  mgr.incr_metric("null_check_insns_changed", null_check_insns_changed);
  mgr.incr_metric("null_check_insns_unchanged", null_check_insns_unchanged);
  mgr.incr_metric("null_check_src_unknown", null_check_src_unknown);
  TRACE(NULLCHECK, 2, "RemoveNullcheckStringArgPass Stats:");
  TRACE(NULLCHECK, 2,
        "RemoveNullcheckStringArgPass insns changed = %zu; unchanged = %zu; "
        "src_unknown_changed= %zu\n",
        null_check_insns_changed, null_check_insns_unchanged,
        null_check_src_unknown);
}

// Computes set of uninstantiable types, also looking at the type system to
// find non-external (and non-native)...
static RemoveNullcheckStringArg s_pass;
