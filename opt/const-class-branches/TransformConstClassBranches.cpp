/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TransformConstClassBranches.h"

#include <algorithm>
#include <mutex>

#include "CFGMutation.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "Creators.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexStructure.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "StringTreeSet.h"
#include "SwitchEquivFinder.h"
#include "SwitchEquivPrerequisites.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {

constexpr const char* METRIC_METHODS_TRANSFORMED = "num_methods_transformed";
constexpr const char* METRIC_CONST_CLASS_INSTRUCTIONS_REMOVED =
    "num_const_class_instructions_removed";
constexpr const char* METRIC_TOTAL_STRING_SIZE = "total_string_size";

// Holder for the pass's configuration options.
struct PassState {
  DexMethodRef* lookup_method;
  bool consider_external_classes;
  size_t min_cases;
  size_t max_cases;
  std::mutex& transforms_mutex;
};

// Denotes a branch and successor blocks within a method that can be
// successfully represented/transformed.
struct BranchTransform {
  cfg::Block* block;
  IRInstruction* insn;
  reg_t determining_reg;
  std::unique_ptr<SwitchEquivFinder> switch_equiv;
};

// Denotes a method that will have one or many transforms.
struct MethodTransform {
  DexMethod* method;
  std::unique_ptr<IRCode> code_copy;
  std::unique_ptr<cfg::ScopedCFG> scoped_cfg;
  std::vector<BranchTransform> transforms;
};

struct Stats {
  size_t methods_transformed{0};
  size_t const_class_instructions_removed{0};
  size_t string_tree_size{0};
  Stats& operator+=(const Stats& that) {
    methods_transformed += that.methods_transformed;
    const_class_instructions_removed += that.const_class_instructions_removed;
    string_tree_size += that.string_tree_size;
    return *this;
  }
};

size_t num_const_class_opcodes(const cfg::ControlFlowGraph* cfg) {
  size_t result{0};
  for (const auto& mie : InstructionIterable(*cfg)) {
    if (mie.insn->opcode() == OPCODE_CONST_CLASS) {
      result++;
    }
  }
  return result;
}

// This pass cares about comparing objects, so only eq, ne are relevant at the
// end of a block.
bool ends_in_if_statment(const cfg::Block* b) {
  auto it = b->get_last_insn();
  if (it == b->end()) {
    return false;
  }
  auto op = it->insn->opcode();
  return opcode::is_if_eq(op) || opcode::is_if_ne(op);
}

// Meant to be a quick guess, to skip some of the preliminary work in deciding
// for real if the method should be operated upon if nothing looks relevant.
bool should_consider_method(const PassState& pass_state, DexMethod* method) {
  if (!method::is_optimizable(method)) {
    return false;
  }
  auto* code = method->get_code();
  auto& cfg = code->cfg();
  bool found_branch = false;
  for (const auto* b : cfg.blocks()) {
    // Note: SwitchEquivFinder assumes the non-leaf blocks (the blocks that
    // perform equals checks) have no throw edges. Avoid considering such a
    // method early on.
    if (b->is_catch()) {
      return false;
    }
    if (ends_in_if_statment(b)) {
      found_branch = true;
      break;
    }
  }
  return found_branch && num_const_class_opcodes(&cfg) >= pass_state.min_cases;
}

// True if the finder is successful, has a default block and does not have some
// edge cases we don't wanna deal with right now.
bool finder_results_are_supported(SwitchEquivFinder* finder) {
  return finder->success() &&
         finder->are_keys_uniform(SwitchEquivFinder::KeyKind::CLASS) &&
         finder->extra_loads().empty() && finder->default_case();
}

// Rather than looping over the cfg blocks, explicitly start from the entry
// block and bfs through the graph. Makes sure that even if the cfg got
// manipulated such that entry block is not the smallest id, we will start
// looking for eligible transforms roughly from that point.
void order_blocks(const cfg::ControlFlowGraph& cfg,
                  std::vector<cfg::Block*>* out) {
  std::stack<cfg::Block*> to_visit;
  UnorderedSet<cfg::BlockId> visited;
  to_visit.push(cfg.entry_block());
  while (!to_visit.empty()) {
    cfg::Block* b = to_visit.top();
    to_visit.pop();

    if (visited.count(b->id()) > 0) {
      continue;
    }
    visited.emplace(b->id());
    out->emplace_back(b);
    for (cfg::Edge* e : b->succs()) {
      to_visit.push(e->target());
    }
  }
}

// "simple" in this case means it does not exist, or it has an easily
// identifiable exit block.
bool has_simple_clinit(DexClass* cls) {
  auto* clinit = cls->get_clinit();
  if (clinit == nullptr) {
    return true;
  }
  auto& cfg = clinit->get_code()->cfg();
  cfg.calculate_exit_block();
  auto* exit_block = cfg.exit_block();
  for (const auto& edge : exit_block->preds()) {
    if (edge->type() == cfg::EDGE_GHOST) {
      return false;
    }
  }
  auto last = exit_block->get_last_insn();
  return last != exit_block->end() &&
         last->insn->opcode() == OPCODE_RETURN_VOID;
}

namespace cp = constant_propagation;

void gather_possible_transformations(
    const PassState& pass_state,
    DexMethod* method,
    std::vector<MethodTransform>* method_transforms) {
  // First step is to operate on a simplified copy of the code. If the transform
  // is applicable, this copy will take effect.
  auto code_copy = std::make_unique<IRCode>(*method->get_code());
  SwitchEquivEditor::simplify_moves(code_copy.get());
  auto scoped_cfg = std::make_unique<cfg::ScopedCFG>(code_copy.get());
  auto& cfg = **scoped_cfg;

  std::vector<BranchTransform> transforms;

  TRACE(CCB, 3, "Checking for const-class branching in %s", SHOW(method));
  auto fixpoint = std::make_shared<cp::intraprocedural::FixpointIterator>(
      cfg, SwitchEquivFinder::Analyzer());
  fixpoint->run(ConstantEnvironment());

  std::vector<cfg::Block*> blocks;
  order_blocks(cfg, &blocks);
  UnorderedSet<cfg::Block*> blocks_considered;
  for (const auto& b : blocks) {
    if (blocks_considered.count(b) > 0) {
      continue;
    }
    blocks_considered.emplace(b);
    reg_t determining_reg;
    if (ends_in_if_statment(b) &&
        find_determining_reg(*fixpoint, b, &determining_reg)) {
      // Keep going, maybe this block is a useful starting point.
      TRACE(CCB, 2, "determining_reg is %u for B%zu", determining_reg, b->id());
      auto* last_insn = b->get_last_insn()->insn;
      auto root_branch = cfg.find_insn(last_insn);
      auto finder = std::make_unique<SwitchEquivFinder>(
          &cfg, root_branch, determining_reg,
          SwitchEquivFinder::NO_LEAF_DUPLICATION, fixpoint,
          SwitchEquivFinder::EXECUTION_ORDER);
      if (finder_results_are_supported(finder.get())) {
        TRACE(CCB, 2, "SwitchEquivFinder succeeded on B%zu for branch at: %s",
              b->id(), SHOW(last_insn));
        auto visited = finder->visited_blocks();
        insert_unordered_iterable(blocks_considered, visited);
        const auto& key_to_case = finder->key_to_case();
        size_t relevant_case_count{0};
        for (auto&& [key, leaf] : key_to_case) {
          if (!SwitchEquivFinder::is_default_case(key)) {
            const auto* dtype = boost::get<const DexType*>(key);
            auto* case_class = type_class(dtype);
            if (pass_state.consider_external_classes ||
                (case_class != nullptr && !case_class->is_external())) {
              relevant_case_count++;
            }
          }
        }
        if (relevant_case_count > pass_state.max_cases ||
            relevant_case_count < pass_state.min_cases) {
          TRACE(CCB, 2, "Not considering branch due to number of cases.");
          continue;
        }
        // Part of this method should conform to expectations, note this.
        BranchTransform transform{b, last_insn, determining_reg,
                                  std::move(finder)};
        transforms.emplace_back(std::move(transform));
      }
    }
  }
  if (!transforms.empty()) {
    std::lock_guard<std::mutex> lock(pass_state.transforms_mutex);
    MethodTransform mt{method, std::move(code_copy), std::move(scoped_cfg),
                       std::move(transforms)};
    method_transforms->emplace_back(std::move(mt));
  }
}

Stats apply_transform(const PassState& pass_state,
                      const size_t& const_string_max_size,
                      MethodTransform& mt,
                      size_t transform_count) {
  Stats result;
  auto* method = mt.method;
  auto* cls = type_class(method->get_class());

  // Injects code into the <clinit> of the method's class, to set up a new
  // static final field containing the given string, built up from pieces no
  // larger than a certain size.
  auto* void_void_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto ensure_clinit = [&]() {
    auto* clinit = cls->get_clinit();
    if (clinit != nullptr && clinit->get_code() != nullptr) {
      return clinit;
    }
    MethodCreator mc{method->get_class(), DexString::make_string("<clinit>"),
                     void_void_proto, ACC_CONSTRUCTOR | ACC_STATIC};
    auto* block = mc.get_main_block();
    block->ret_void();
    auto* new_clinit = mc.create();
    new_clinit->get_code()->build_cfg();
    cls->add_method(new_clinit);
    return new_clinit;
  };
  auto create_static_field_for_string = [&](const std::string& encoded_str) {
    const auto* field_name =
        DexString::make_string("$RDX$tree" + std::to_string(transform_count));
    auto* field_def = DexField::make_field(method->get_class(), field_name,
                                           type::java_lang_String())
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    field_def->set_deobfuscated_name(show_deobfuscated(field_def));
    cls->add_field(field_def);

    auto* clinit = ensure_clinit();
    auto& cfg = clinit->get_code()->cfg();
    TRACE(CCB, 5, "BASELINE CLINIT: %s", SHOW(cfg));

    cfg.calculate_exit_block();
    auto* exit_block = cfg.exit_block();
    cfg::CFGMutation mutation(cfg);
    std::vector<IRInstruction*> instructions;
    auto sb_reg = cfg.allocate_temp();
    auto extra_reg = cfg.allocate_temp();
    auto* new_instance =
        (new IRInstruction(OPCODE_NEW_INSTANCE))
            ->set_type(DexType::get_type("Ljava/lang/StringBuilder;"));
    instructions.push_back(new_instance);
    auto* instance_move_pseudo =
        (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
            ->set_dest(sb_reg);
    instructions.push_back(instance_move_pseudo);
    auto* invoke_ctor = (new IRInstruction(OPCODE_INVOKE_DIRECT))
                            ->set_srcs_size(1)
                            ->set_src(0, sb_reg)
                            ->set_method(DexMethod::get_method(
                                "Ljava/lang/StringBuilder;.<init>:()V"));
    instructions.push_back(invoke_ctor);
    for (size_t idx = 0; idx < encoded_str.size();
         idx += const_string_max_size) {
      auto chunk = encoded_str.substr(idx, const_string_max_size);
      auto* const_string = (new IRInstruction(OPCODE_CONST_STRING))
                               ->set_string(DexString::make_string(chunk));
      instructions.push_back(const_string);
      auto* move_result_pseudo =
          (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
              ->set_dest(extra_reg);
      instructions.push_back(move_result_pseudo);
      auto* append =
          (new IRInstruction(OPCODE_INVOKE_VIRTUAL))
              ->set_srcs_size(2)
              ->set_src(0, sb_reg)
              ->set_src(1, extra_reg)
              ->set_method(method::java_lang_StringBuilder_append_String());
      instructions.push_back(append);
    }
    auto* to_string =
        (new IRInstruction(OPCODE_INVOKE_VIRTUAL))
            ->set_srcs_size(1)
            ->set_src(0, sb_reg)
            ->set_method(method::java_lang_StringBuilder_toString());
    instructions.push_back(to_string);
    auto* move_result =
        (new IRInstruction(OPCODE_MOVE_RESULT_OBJECT))->set_dest(sb_reg);
    instructions.push_back(move_result);
    auto* sput_object = (new IRInstruction(OPCODE_SPUT_OBJECT))
                            ->set_field(field_def)
                            ->set_src(0, sb_reg);
    instructions.push_back(sput_object);

    auto it = cfg.find_insn(exit_block->get_last_insn()->insn);
    mutation.insert_before(it, instructions);
    mutation.flush();

    TRACE(CCB, 5, "NEW CLINIT: %s", SHOW(cfg));
    return field_def;
  };

  auto& cfg = **mt.scoped_cfg;
  auto before_const_class_count = num_const_class_opcodes(&cfg);
  TRACE(CCB, 3,
        "Processing const-class branching in %s (transform size = %zu) %s",
        SHOW(method), mt.transforms.size(), SHOW(cfg));

  for (auto& transform : mt.transforms) {
    // Determine stable order of the types that are being switched on.
    std::set<const DexType*, dextypes_comparator> ordered_types;
    const auto& key_to_case = transform.switch_equiv->key_to_case();
    cfg::Block* default_case{nullptr};
    for (auto&& [key, block] : key_to_case) {
      if (!SwitchEquivFinder::is_default_case(key)) {
        const auto* dtype = boost::get<const DexType*>(key);
        ordered_types.emplace(dtype);
      } else {
        TRACE(CCB, 3, "DEFAULT -> B%zu\n%s", block->id(), SHOW(block));
        default_case = block;
      }
    }
    // Create ordinals for each type being switched on, reserving zero to denote
    // an explicit default case.
    std::map<std::string, int16_t> string_tree_items;
    std::vector<std::pair<int32_t, cfg::Block*>> new_edges;
    constexpr int16_t STRING_TREE_NO_ENTRY = 0;
    int16_t counter = STRING_TREE_NO_ENTRY + 1;
    for (const auto& type : ordered_types) {
      auto string_name = java_names::internal_to_external(type->str());
      int16_t ordinal = counter++;
      string_tree_items.emplace(string_name, ordinal);
      auto* block = key_to_case.at(type);
      new_edges.emplace_back(ordinal, block);
      TRACE(CCB, 3, "%s (%s) -> B%zu\n%s", SHOW(type), string_name.c_str(),
            block->id(), SHOW(block));
    }

    auto encoded_str =
        StringTreeMap<int16_t>::encode_string_tree_map(string_tree_items);
    result.string_tree_size = encoded_str.size();

    // Fiddle with the block's last instruction and install an actual switch
    TRACE(CCB, 2, "Removing B%zu's last instruction: %s", transform.block->id(),
          SHOW(transform.insn));

    std::vector<IRInstruction*> replacements;
    auto encoded_str_reg = cfg.allocate_temp();
    if (encoded_str.size() > const_string_max_size && has_simple_clinit(cls)) {
      auto* field_def = create_static_field_for_string(encoded_str);
      auto* sget_object =
          (new IRInstruction(OPCODE_SGET_OBJECT))->set_field(field_def);
      replacements.push_back(sget_object);
    } else {
      const auto* encoded_dex_str = DexString::make_string(encoded_str);
      auto* const_string_insn =
          (new IRInstruction(OPCODE_CONST_STRING))->set_string(encoded_dex_str);
      replacements.push_back(const_string_insn);
    }
    auto* move_string_insn =
        (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
            ->set_dest(encoded_str_reg);
    replacements.push_back(move_string_insn);

    auto default_value_reg = cfg.allocate_temp();
    auto* default_value_const = new IRInstruction(OPCODE_CONST);
    default_value_const->set_literal(STRING_TREE_NO_ENTRY);
    default_value_const->set_dest(default_value_reg);
    replacements.push_back(default_value_const);

    auto* invoke_string_tree = new IRInstruction(OPCODE_INVOKE_STATIC);
    invoke_string_tree->set_method(pass_state.lookup_method);
    invoke_string_tree->set_srcs_size(3);
    invoke_string_tree->set_src(0, transform.determining_reg);
    invoke_string_tree->set_src(1, encoded_str_reg);
    invoke_string_tree->set_src(2, default_value_reg);
    replacements.push_back(invoke_string_tree);

    // Just reuse a reg we don't need anymore
    auto switch_result_reg = default_value_reg;
    auto* move_lookup_result = new IRInstruction(OPCODE_MOVE_RESULT);
    move_lookup_result->set_dest(switch_result_reg);
    replacements.push_back(move_lookup_result);

    auto* new_switch = new IRInstruction(OPCODE_SWITCH);
    new_switch->set_src(0, switch_result_reg);
    // Note: it seems instruction "new_switch" gets appended via create_branch;
    // no need to push to replacements

    cfg.replace_insns(cfg.find_insn(transform.insn), replacements);
    // We are explicitly covering the default block via the default return value
    // from the string tree. Not needed here.
    cfg.create_branch(transform.block, new_switch, nullptr, new_edges);

    // Reset successor of last prologue block to implement the default case.
    // Make copy of succs to enable modification within loop
    auto succs_copy = transform.block->succs();
    for (auto* edge : succs_copy) {
      if (edge->type() == cfg::EDGE_GOTO) {
        cfg.set_edge_target(edge, default_case);
      }
    }
    transform_count++;
  }
  // Last step is to prune leaf blocks which are now unreachable. Do this
  // before computing metrics (so we know if this pass is doing anything
  // useful) but be sure to not dereference any Block ptrs from here on out!
  cfg.remove_unreachable_blocks();
  TRACE(CCB, 3, "POST EDIT %s", SHOW(cfg));
  result.methods_transformed = 1;
  // Metric is not entirely accurate as we don't do dce on the first block that
  // starts the if chain (eehhh close enough).
  result.const_class_instructions_removed =
      before_const_class_count - num_const_class_opcodes(&cfg);
  always_assert(result.const_class_instructions_removed >= 0);

  // Make the copy take effect.
  method->set_code(std::move(mt.code_copy));
  return result;
}

} // namespace

void TransformConstClassBranchesPass::bind_config() {
  bind("consider_external_classes", false, m_consider_external_classes);
  // Probably not worthwhile for tiny methods.
  bind("min_cases", 5, m_min_cases);
  // Arbitrary default values to avoid creating unbounded amounts of encoded
  // string data.
  bind("max_cases", 2000, m_max_cases);
  bind("string_tree_lookup_method", "", m_string_tree_lookup_method);
  // Applying runtime workarounds per string generated, at the moment, will
  // involve generating extra helper methods. Put some sensible cap on number of
  // transforms to give the ability to reserve refs
  bind("transforms_per_dex", 10, m_max_transforms_per_dex);
  // Emit const-string opcodes with size no greater than X. Larger strings will
  // have codegen to build a static field in chunks.
  bind("const_string_max_size", 8000, m_const_string_max_size);
  trait(Traits::Pass::unique, true);
}

void TransformConstClassBranchesPass::eval_pass(DexStoresVector&,
                                                ConfigFiles&,
                                                PassManager& mgr) {
  // Every transform may involve a large string that might be split up and built
  // in pieces, culminating in a static field. Reserve enough space for this to
  // pessimistically happen each time. Per transform that would net 1 field, and
  // each transform would add 4 method refs (1 for the lookup call, and 3 for
  // building a big string with a StringBuilder; <init>, append, toString).
  m_reserved_refs_handle =
      mgr.reserve_refs(name(),
                       ReserveRefsInfo(/* frefs */ m_max_transforms_per_dex,
                                       /* trefs */ 0,
                                       /* mrefs */ 4));
}

void TransformConstClassBranchesPass::run_pass(DexStoresVector& stores,
                                               ConfigFiles& /* unused */,
                                               PassManager& mgr) {
  always_assert(m_reserved_refs_handle);
  mgr.release_reserved_refs(*m_reserved_refs_handle);
  m_reserved_refs_handle = std::nullopt;

  auto scope = build_class_scope(stores);
  if (m_string_tree_lookup_method.empty()) {
    TRACE(CCB, 1, "Pass not configured; returning.");
    return;
  }
  auto* string_tree_lookup_method =
      DexMethod::get_method(m_string_tree_lookup_method);
  if (string_tree_lookup_method == nullptr) {
    TRACE(CCB, 1, "Lookup method not found; returning.");
    return;
  }

  std::vector<MethodTransform> method_transforms;
  std::mutex transforms_mutex;
  PassState pass_state{string_tree_lookup_method, m_consider_external_classes,
                       m_min_cases, m_max_cases, transforms_mutex};
  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (should_consider_method(pass_state, method)) {
      gather_possible_transformations(pass_state, method, &method_transforms);
    }
  });

  UnorderedMap<DexClass*, std::vector<MethodTransform*>> per_class_transforms;
  for (auto& transform : method_transforms) {
    auto* cls = type_class(transform.method->get_class());
    per_class_transforms[cls].emplace_back(&transform);
  }

  Stats stats;
  // Apply at most N transforms per dex, because of reserved refs.
  auto apply_transforms_dex = [&](DexClasses& dex_file) {
    std::vector<MethodTransform*> per_dex_transforms;
    for (auto* cls : dex_file) {
      auto search = per_class_transforms.find(cls);
      if (search != per_class_transforms.end()) {
        per_dex_transforms.insert(per_dex_transforms.end(),
                                  search->second.begin(), search->second.end());
      }
    }
    std::sort(per_dex_transforms.begin(), per_dex_transforms.end(),
              [](const MethodTransform* a, const MethodTransform* b) {
                return compare_dexmethods(a->method, b->method);
              });
    size_t transform_count{0};
    for (auto it = per_dex_transforms.rbegin(); it != per_dex_transforms.rend();
         ++it) {
      auto& mt = *it;
      auto size = mt->transforms.size();
      if (transform_count + size > m_max_transforms_per_dex) {
        break;
      }
      stats += apply_transform(pass_state, m_const_string_max_size, *mt,
                               transform_count);
      transform_count += size;
    }
  };

  for (auto& store : stores) {
    auto& dex_files = store.get_dexen();
    for (auto& dex_file : dex_files) {
      apply_transforms_dex(dex_file);
    }
  }
  mgr.incr_metric(METRIC_METHODS_TRANSFORMED, stats.methods_transformed);
  mgr.incr_metric(METRIC_CONST_CLASS_INSTRUCTIONS_REMOVED,
                  stats.const_class_instructions_removed);
  mgr.incr_metric(METRIC_TOTAL_STRING_SIZE, stats.string_tree_size);
  TRACE(CCB, 1,
        "[transform const-class branches] Altered %zu method(s) to remove %zu "
        "const-class instructions; %zu bytes of character data created.",
        stats.methods_transformed, stats.const_class_instructions_removed,
        stats.string_tree_size);
}

static TransformConstClassBranchesPass s_pass;
