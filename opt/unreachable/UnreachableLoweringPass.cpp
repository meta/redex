/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "UnreachableLoweringPass.h"

#include "BaselineProfile.h"
#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "Debug.h"
#include "DexUtil.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "Show.h"
#include "Trace.h"
#include "TypedNonReturningMethods.h"
#include "UnreachableDefUseChains.h"
#include "Walkers.h"
#include <DexStructure.h>

namespace {

constexpr const char* METRIC_UNREACHABLE_INSTRUCTIONS =
    "unreachable_instructions";
constexpr const char* METRIC_UNREACHABLE_METHODS = "unreachable_methods";
constexpr const char* METRIC_REACHABLE_METHODS_WITH_UNREACHABLE_INSTRUCTIONS =
    "reachable_methods_with_unreachable_instructions";

constexpr const char* UNREACHABLE_EXCEPTION_CLASS_NAME =
    "Lcom/redex/UnreachableException;";
constexpr const char* UNREACHABLE_EXCEPTION_CREATE_AND_THROW_METHOD_NAME =
    "createAndThrow";

void report(const typed_nonreturning_methods::Stats& stats, PassManager& mgr) {
  mgr.incr_metric("typed_nonreturning_method_candidates",
                  stats.candidate_methods);
  mgr.incr_metric("typed_nonreturning_methods_rejected",
                  stats.rejected_methods);
  mgr.incr_metric("typed_nonreturning_methods_unprofitable",
                  stats.unprofitable_methods);
  mgr.incr_metric("typed_nonreturning_methods", stats.typed_methods);
  mgr.incr_metric("typed_nonreturning_method_call_sites",
                  stats.typed_call_sites);
  mgr.incr_metric("typed_nonreturning_method_compiled_call_sites",
                  stats.compiled_call_sites);
}

} // namespace

void UnreachableLoweringPass::bind_config() {
  bind("typed_nonreturning_methods", false, m_typed_nonreturning_methods,
       "Where a static method that cannot return normally is called right "
       "before an unreachable throw, change the method's return type in place "
       "to com.redex.UnreachableException and throw the call's result, rather "
       "than lowering the unreachable instruction to a second call. Only call "
       "sites in callers that the baseline profile does not compile, or in "
       "try regions, are converted, and instrumented builds are left alone.");
}

void UnreachableLoweringPass::eval_pass(DexStoresVector& stores,
                                        ConfigFiles&,
                                        PassManager& mgr) {
  always_assert(!stores.empty());
  auto& root_store = stores.front();
  auto& primary_dex = root_store.get_dexen().at(0);
  const auto* cls_name =
      DexString::make_string(UNREACHABLE_EXCEPTION_CLASS_NAME);
  auto* type = DexType::make_type(cls_name);
  ClassCreator cls_creator(type);
  cls_creator.set_access(ACC_PUBLIC | ACC_FINAL);
  cls_creator.set_super(type::java_lang_RuntimeException());
  auto* cls = cls_creator.create();
  cls->rstate.set_generated();
  cls->rstate.set_root();
  cls->set_perf_sensitive(PerfSensitiveGroup::UNREACHABLE);
  primary_dex.push_back(cls);

  DexMethod* init_method;

  {
    MethodCreator method_creator(
        cls->get_type(),
        DexString::make_string("<init>"),
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})),
        ACC_PUBLIC | ACC_CONSTRUCTOR);
    auto this_arg = method_creator.get_local(0);
    auto string_var = method_creator.make_local(type::java_lang_String());
    method_creator.make_local(type::java_lang_RuntimeException());
    auto* main_block = method_creator.get_main_block();

    main_block->load_const(
        string_var,
        DexString::make_string(
            "Redex: Unreachable code. This should never get triggered."));
    main_block->invoke(
        OPCODE_INVOKE_DIRECT,
        DexMethod::make_method(
            type::java_lang_RuntimeException(),
            DexString::make_string("<init>"),
            DexProto::make_proto(
                type::_void(),
                DexTypeList::make_type_list({type::java_lang_String()}))),
        {this_arg, string_var});
    main_block->ret_void();
    init_method = method_creator.create();
    cls->add_method(init_method);
    init_method->get_code()->build_cfg();
    init_method->rstate.set_generated();
    init_method->set_deobfuscated_name(show_deobfuscated(init_method));
  }

  {
    MethodCreator method_creator(
        cls->get_type(),
        DexString::make_string(
            UNREACHABLE_EXCEPTION_CREATE_AND_THROW_METHOD_NAME),
        DexProto::make_proto(type, DexTypeList::make_type_list({})),
        ACC_STATIC | ACC_PUBLIC);
    auto var = method_creator.make_local(type);
    auto* main_block = method_creator.get_main_block();
    main_block->new_instance(type, var);
    main_block->invoke(init_method, {var});
    main_block->throwex(var);
    m_create_and_throw_method = method_creator.create();
    cls->add_method(m_create_and_throw_method);
    m_create_and_throw_method->get_code()->build_cfg();
    m_create_and_throw_method->rstate.set_generated();
    m_create_and_throw_method->rstate.set_root();
    m_create_and_throw_method->set_deobfuscated_name(
        show_deobfuscated(m_create_and_throw_method));
  }

  m_reserved_refs_handle = mgr.reserve_refs(name(),
                                            ReserveRefsInfo(/* frefs */ 0,
                                                            /* trefs */ 1,
                                                            /* mrefs */ 1));
}

void UnreachableLoweringPass::run_pass(DexStoresVector& stores,
                                       ConfigFiles& conf,
                                       PassManager& mgr) {
  always_assert(m_reserved_refs_handle);
  mgr.release_reserved_refs(*m_reserved_refs_handle);
  m_reserved_refs_handle = std::nullopt;

  const auto scope = build_class_scope(stores);
  // Like other code-shape optimizations, not under instrumentation.
  if (m_typed_nonreturning_methods &&
      !mgr.get_redex_options().instrument_pass_enabled) {
    report(typed_nonreturning_methods::type_nonreturning_methods(
               stores, scope, m_create_and_throw_method->get_class(),
               baseline_profiles::get_default_baseline_profile(scope, conf),
               baseline_profiles::get_huge_method_max(conf)),
           mgr);
  }

  std::atomic<size_t> unreachable_instructions{0};
  std::atomic<size_t> unreachable_methods{0};
  std::atomic<size_t> reachable_methods_with_unreachable_instructions{0};
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    auto& cfg = code.cfg();
    bool is_unreachable_method = cfg.entry_block()->is_unreachable();
    if (is_unreachable_method) {
      unreachable_methods++;
    }
    size_t local_unreachable_instructions{0};
    Lazy<live_range::DefUseChains> duchains(
        [&cfg]() { return unreachable::get_def_use_chains(cfg); });
    auto ii = InstructionIterable(cfg);
    std::unique_ptr<cfg::CFGMutation> mutation;
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto& mie = *it;
      if (!opcode::is_unreachable(mie.insn->opcode())) {
        continue;
      }
      local_unreachable_instructions++;

      // We want to enforce that the (dummy) value produced by the "unreachable"
      // instruction is only used by a "throw" instruction.
      // TODO: In practice, the InstrumentPass might also squeeze in an
      // (unreachable) DynamicAnalysis.onMethodExit invocation in between the
      // "unreachable" instruction and the "throw". This should be avoided, and
      // then we can assert even stricter code patterns here.
      const auto& uses = (*duchains)[mie.insn];
      for (const auto& use : UnorderedIterable(uses)) {
        auto* insn = use.insn;
        if (opcode::is_move_object(insn->opcode())) {
          continue;
        }
        always_assert_log(opcode::is_throw(insn->opcode()),
                          "only unreachable instruction {%s} use {%s} must be "
                          "throw in %s:\n%s",
                          SHOW(mie.insn), SHOW(insn), SHOW(method), SHOW(cfg));
      }

      // TODO: Consider other transformations, e.g. just return if there are no
      // monitor instructions, or embed a descriptive message.
      // `baseline_profiles::lowered_unreachable_extra_code_units` sizes this
      // replacement for passes that run before this one.
      if (!mutation) {
        mutation = std::make_unique<cfg::CFGMutation>(cfg);
      }
      mutation->replace(it,
                        {
                            (new IRInstruction(OPCODE_INVOKE_STATIC))
                                ->set_method(m_create_and_throw_method),
                            (new IRInstruction(OPCODE_MOVE_RESULT_OBJECT))
                                ->set_dest(mie.insn->dest()),
                        });
    }

    if (mutation) {
      always_assert(local_unreachable_instructions > 0);
      mutation->flush();
      cfg.remove_unreachable_blocks();
      unreachable_instructions += local_unreachable_instructions;
      if (!is_unreachable_method) {
        reachable_methods_with_unreachable_instructions++;
      }
    } else {
      always_assert(local_unreachable_instructions == 0);
    }
  });
  mgr.incr_metric(METRIC_UNREACHABLE_INSTRUCTIONS,
                  (size_t)unreachable_instructions);
  mgr.incr_metric(METRIC_UNREACHABLE_METHODS, (size_t)unreachable_methods);
  mgr.incr_metric(METRIC_REACHABLE_METHODS_WITH_UNREACHABLE_INSTRUCTIONS,
                  (size_t)reachable_methods_with_unreachable_instructions);
  TRACE(UNREACHABLE, 1,
        "%zu unreachable instructions, %zu unreachable methods, %zu reachable "
        "methods with unreachable instructions",
        (size_t)unreachable_instructions, (size_t)unreachable_methods,
        (size_t)reachable_methods_with_unreachable_instructions);
}

static UnreachableLoweringPass s_pass;
