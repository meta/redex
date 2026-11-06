/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringBuilderOutliner.h"

#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "Debug.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "Walkers.h"

using namespace stringbuilder_outliner;

Outliner::Outliner(Config config)
    : m_config(config),
      m_append_str(DexString::get_string("append")),
      m_stringbuilder(DexType::get_type("Ljava/lang/StringBuilder;")),
      m_stringbuilder_default_ctor(
          DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:()V")),
      m_stringbuilder_capacity_ctor(
          DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:(I)V")),
      m_stringbuilder_tostring(method::java_lang_StringBuilder_toString()) {
  always_assert(m_append_str);
  always_assert(m_stringbuilder);
  always_assert(m_stringbuilder_default_ctor);
  always_assert(m_stringbuilder_capacity_ctor);
}

/*
 * Gather the types of the values that the StringBuilder instance is
 * concatenating.
 */
const DexTypeList* Outliner::typelist_from_state(
    const BuilderState& state) const {
  DexTypeList::ContainerType args;
  for (const auto* insn : state) {
    auto* method = insn->get_method();
    args.emplace_back(method->get_proto()->get_args()->at(0));
  }
  return DexTypeList::make_type_list(std::move(args));
}

void Outliner::gather_outline_candidate_typelists(
    const BuilderStateMap& tostring_instruction_to_state) {
  for (const auto& p : tostring_instruction_to_state) {
    const auto& state = p.second;
    const auto* typelist = typelist_from_state(state);
    m_outline_typelists.fetch_add(typelist, 1);
  }
}

void Outliner::analyze(IRCode& code) {
  always_assert(code.cfg_built());
  auto& cfg = code.cfg();

  cfg.calculate_exit_block();

  // Do a quick one-pass scan to see if the method has any instructions that may
  // be outlinable. Only do the more expensive fixpoint calculations if the
  // method passes this check.
  auto tostring_instructions =
      stringbuilder_analysis::find_tostring_instructions(
          cfg, m_stringbuilder_tostring);
  if (tostring_instructions.empty()) {
    return;
  }

  auto tostring_instruction_to_state =
      stringbuilder_analysis::gather_builder_states(cfg, tostring_instructions);

  gather_outline_candidate_typelists(tostring_instruction_to_state);

  m_builder_state_maps.emplace(&code, std::move(tostring_instruction_to_state));
}

/*
 * Don't create helpers if:
 * 1) They only have a few use sites -- the performance/size overheads of
 * outlining may not be worth it.
 * 2) A long list of parameters would be required. Calls to these methods could
 * significantly increase register pressure in the caller.
 */
void Outliner::create_outline_helpers(DexStoresVector* stores) {
  auto* outline_helper_cls =
      DexType::make_type("Lcom/redex/OutlinedStringBuilders;");
  const auto* concat_str = DexString::make_string("concat");
  auto* string_ty = DexType::make_type("Ljava/lang/String;");

  ClassCreator cc(outline_helper_cls);
  cc.set_super(type::java_lang_Object());
  bool did_create_helper{false};
  for (const auto& p : UnorderedIterable(m_outline_typelists)) {
    const auto* typelist = p.first;
    auto count = p.second.load();

    if (count < m_config.min_outline_count ||
        typelist->size() > m_config.max_outline_length) {
      // TODO: filter out length zero/one states?
      continue;
    }
    TRACE(STRBUILD, 3,
          "Outlining %zu StringBuilders of length %zu with typelist %s", count,
          typelist->size(), SHOW(typelist));
    m_stats.stringbuilders_removed += count;
    m_stats.operations_removed += count * typelist->size();

    if (m_outline_helpers.count(typelist) != 0) {
      continue;
    }
    m_stats.helper_methods_created += 1;

    auto* helper =
        DexMethod::make_method(outline_helper_cls, concat_str,
                               DexProto::make_proto(string_ty, typelist))
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    helper->set_code(create_outline_helper_code(helper));
    helper->set_deobfuscated_name(show(helper));
    cc.add_method(helper);
    did_create_helper = true;
    m_outline_helpers.emplace(typelist, helper);
  }

  if (did_create_helper) {
    auto& dexen = (*stores)[0].get_dexen()[0];
    dexen.push_back(cc.create());
  }
}

/*
 * Given a method with a proto like `concat(String, int, String)`, generate
 * IRCode equivalent to the following Java:
 *
 *   String concat(String a, int b, String c) {
 *     StringBuilder sb = new StringBuilder();
 *     sb.append(a);
 *     sb.append(b);
 *     sb.append(c);
 *     return sb.toString();
 *   }
 */
std::unique_ptr<IRCode> Outliner::create_outline_helper_code(
    DexMethod* method) const {
  using namespace dex_asm;

  auto* typelist = method->get_proto()->get_args();
  auto code = std::make_unique<IRCode>(method, 1);
  code->push_back(dasm(OPCODE_NEW_INSTANCE, m_stringbuilder));
  code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {0_v}));
  code->push_back(
      dasm(OPCODE_INVOKE_DIRECT, m_stringbuilder_default_ctor, {0_v}));
  auto param_insns_it =
      InstructionIterable(code->get_param_instructions()).begin();
  for (size_t i = 0; i < typelist->size(); ++i, ++param_insns_it) {
    auto* ty = typelist->at(i);
    auto reg = param_insns_it->insn->dest();
    auto* append_method = DexMethod::get_method(
        m_stringbuilder, m_append_str,
        DexProto::make_proto(m_stringbuilder,
                             DexTypeList::make_type_list({ty})));
    always_assert_log(append_method, "Could not find append for %s", SHOW(ty));
    code->push_back((new IRInstruction(OPCODE_INVOKE_VIRTUAL))
                        ->set_method(append_method)
                        ->set_srcs_size(2)
                        ->set_src(0, 0)
                        ->set_src(1, reg));
  }
  code->push_back(dasm(OPCODE_INVOKE_VIRTUAL, m_stringbuilder_tostring, {0_v}));
  code->push_back(dasm(OPCODE_MOVE_RESULT_OBJECT, {0_v}));
  code->push_back(dasm(OPCODE_RETURN_OBJECT, {0_v}));
  code->build_cfg();
  return code;
}

static IROpcode move_for_type(const DexType* ty) {
  if (!type::is_primitive(ty)) {
    return OPCODE_MOVE_OBJECT;
  } else if (type::is_wide_type(ty)) {
    return OPCODE_MOVE_WIDE;
  } else {
    return OPCODE_MOVE;
  }
}

static IROpcode invoke_for_method(const DexMethod* method) {
  if (is_static(method)) {
    return OPCODE_INVOKE_STATIC;
  } else if (method->is_virtual()) {
    return OPCODE_INVOKE_VIRTUAL;
  } else {
    return OPCODE_INVOKE_DIRECT;
  }
}

/*
 * Convert a sequence of instructions like
 *
 *   invoke-virtual {v0, v1} StringBuilder.append(String)
 *   invoke-virtual {v0, v2} StringBuilder.append(String)
 *   ...
 *   invoke-virtual {v0, vN} StringBuilder.append(String)
 *   invoke-virtual {v0} StringBuilder.toString()
 *
 * into
 *
 *   move-object v1, vN + 1
 *   invoke-virtual {v0, v1} StringBuilder.append(String)
 *   move-object v2, vN + 2
 *   invoke-virtual {v0, v2} StringBuilder.append(String)
 *   ...
 *   move-object v2, vN + N
 *   invoke-virtual {v0, vN} StringBuilder.append(String)
 *   invoke-static {vN + 1, vN + 2, ..., vN + N} OutlinedStringBuilders.concat()
 *
 * It is anticipated that the now-redundant StringBuilder.append() calls will
 * be removed by a later run of ObjectSensitiveDcePass, and that most of the
 * move instructions created here will be eliminated as part of move coalescing
 * during register allocation.
 */
void Outliner::transform(const DexMethod* source_method, IRCode* code) {
  if (m_builder_state_maps.count(code) == 0) {
    return;
  }
  const auto& tostring_instruction_to_state = m_builder_state_maps.at(code);
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  UnorderedMap<const IRInstruction*, IRInstruction*> insns_to_insert;
  UnorderedMap<const IRInstruction*, IRInstruction*> insns_to_replace;
  for (const auto& p : tostring_instruction_to_state) {
    const auto* tostring_insn = p.first;
    const auto& state = p.second;
    const auto* typelist = typelist_from_state(state);
    if (m_outline_helpers.count(typelist) == 0) {
      continue;
    }
    auto tostring_it = cfg.find_insn(tostring_insn);
    if (source_blocks::is_hot(tostring_it.block())) {
      ++m_stats.tostring_outlined_hot;
    }
    auto* outline_helper = m_outline_helpers.at(typelist);
    auto* callsite_sb = source_blocks::get_last_source_block_before(
        tostring_it.block(), tostring_it.unwrap());
    if (callsite_sb != nullptr) {
      auto snapshot =
          source_blocks::clone_as_synthetic(callsite_sb, nullptr, std::nullopt);
      m_target_to_callsite_source_blocks.update(
          outline_helper, [&snapshot](auto*, auto& sources, bool) {
            sources.push_back(std::move(snapshot));
          });
    }
    auto* invoke_outlined =
        new IRInstruction(invoke_for_method(outline_helper));
    invoke_outlined->set_method(outline_helper);
    invoke_outlined->set_srcs_size(typelist->size());

    if (source_method != nullptr) {
      m_target_to_source_map.update(
          outline_helper,
          [source_method](const DexMethod*, std::vector<DexMethod*>& sources,
                          bool /*exists*/) {
            sources.push_back(const_cast<DexMethod*>(source_method));
          });
    }

    size_t idx{0};
    for (const auto* insn : state) {
      reg_t reg;
      if (insns_to_insert.count(insn) != 0u) {
        // An instruction can occur in more than one BuilderState if the
        // corresponding StringBuilder instance is used in both sides of a
        // conditional branch.
        reg = insns_to_insert.at(insn)->dest();
      } else {
        auto* ty = insn->get_method()->get_proto()->get_args()->at(0);
        reg = type::is_wide_type(ty) ? cfg.allocate_wide_temp()
                                     : cfg.allocate_temp();
        auto* move = (new IRInstruction(move_for_type(ty)))
                         ->set_src(0, insn->src(1))
                         ->set_dest(reg);
        insns_to_insert.emplace(insn, move);
      }

      invoke_outlined->set_src(idx, reg);
      ++idx;
    }

    insns_to_replace.emplace(tostring_insn, invoke_outlined);
  }

  apply_changes(insns_to_insert, insns_to_replace, code);
}

/*
 * The StringBuilder analysis tracks and describes transformations in terms of
 * IRInstructions, but efficient insertion / removal of IRInstructions requires
 * knowing their corresponding IRList iterators. This method does one pass to
 * obtain those iterators before doing the appropriate transforms.
 */
void Outliner::apply_changes(
    const UnorderedMap<const IRInstruction*, IRInstruction*>& insns_to_insert,
    const UnorderedMap<const IRInstruction*, IRInstruction*>& insns_to_replace,
    IRCode* code) {
  auto& cfg = code->cfg();
  std::vector<std::pair<cfg::InstructionIterator, IRInstruction*>> to_insert;
  std::vector<std::pair<cfg::InstructionIterator, IRInstruction*>> to_replace;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      auto it = block->to_cfg_instruction_iterator(mie);
      if (insns_to_insert.count(mie.insn) != 0u) {
        to_insert.emplace_back(it, insns_to_insert.at(insn));
      }
      if (insns_to_replace.count(insn) != 0u) {
        to_replace.emplace_back(it, insns_to_replace.at(insn));
      }
    }
  }
  cfg::CFGMutation m(code->cfg());
  for (const auto& p : to_insert) {
    m.insert_before(p.first, {p.second});
  }
  m.flush();

  for (const auto& p : to_replace) {
    delete p.first->insn;
    p.first->insn = p.second;
  }
}

void Outliner::set_hot_method_from_callsite() {
  for (const auto& [target, snapshots] :
       UnorderedIterable(m_target_to_callsite_source_blocks)) {
    std::vector<SourceBlock*> source_blocks_callsites;
    source_blocks_callsites.reserve(snapshots.size());
    for (const auto& snapshot : snapshots) {
      source_blocks_callsites.push_back(snapshot.get());
    }

    if (!source_blocks_callsites.empty()) {
      always_assert(target->get_code());
      auto* template_sb = source_blocks_callsites[0];
      source_blocks::insert_synthetic_source_blocks_in_method(
          target, [target, template_sb, &source_blocks_callsites]() {
            // The outlined `target` is reached from every call site, so
            // its synthetic count is the SUM of those sites' counts, not the
            // max.
            return source_blocks::clone_as_synthetic_summing(
                template_sb, target, source_blocks_callsites);
          });
    }
  }
}

size_t derive_method_profiles_stats(
    ConfigFiles& config, const Outliner::OutlinedMethods& outlined_methods) {
  auto& method_profiles = config.get_method_profiles();
  size_t res = 0;
  for (const auto& [target, sources] : UnorderedIterable(outlined_methods)) {
    std::vector<DexMethod*> sorted_sources = sources;
    std::sort(sorted_sources.begin(), sorted_sources.end(),
              dexmethods_comparator());
    res += method_profiles.derive_stats(target, sorted_sources);
  }
  return res;
}

void StringBuilderOutlinerPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles& config,
                                         PassManager& mgr) {
  auto scope = build_class_scope(stores);
  Outliner outliner(m_config);
  // 1) Determine which methods have candidates for outlining.
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode& code) {
    if (!method->rstate.no_optimizations()) {
      outliner.analyze(code);
    }
  });
  // 2) Determine which candidates occur frequently enough to be worth
  // outlining. Build the corresponding outline helper functions.
  outliner.create_outline_helpers(&stores);
  // 3) Actually do the outlining.
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode& code) {
    if (!method->rstate.no_optimizations()) {
      outliner.transform(method, &code);
    }
  });
  // 4) mark the new outlined string methods as hot if the call site was hot
  outliner.set_hot_method_from_callsite();

  if (m_config.derive_method_profiles_stats) {
    size_t derived_method_profile_stats =
        derive_method_profiles_stats(config, outliner.get_outlined_methods());
    mgr.incr_metric("num_derived_method_profile_stats",
                    derived_method_profile_stats);
  }

  mgr.incr_metric("stringbuilders_removed",
                  outliner.get_stats().stringbuilders_removed);
  mgr.incr_metric("operations_removed",
                  outliner.get_stats().operations_removed);
  mgr.incr_metric("helper_methods_created",
                  outliner.get_stats().helper_methods_created);
  mgr.incr_metric("tostring_outlined_hot",
                  outliner.get_stats().tostring_outlined_hot);
}

static StringBuilderOutlinerPass s_pass;
