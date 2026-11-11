/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResourcesInliningPass.h"

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "Debug.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"
#include "androidfw/ResourceTypes.h"

namespace {

// get_type_names() describes the application package only, while id_to_name and
// a resource id read out of bytecode can name any package in the table, so the
// type id is not an index this vector is guaranteed to hold. Type id 0 would
// underflow the documented "element i is type id i + 1" numbering.
std::optional<std::string_view> get_type_name(
    const std::vector<std::string>& type_names, uint32_t id) {
  uint32_t type_id = (id & TYPE_MASK_BIT) >> TYPE_INDEX_BIT_SHIFT;
  if (type_id == 0 || type_id > type_names.size()) {
    return std::nullopt;
  }
  return type_names[type_id - 1];
}

} // namespace

UnorderedMap<uint32_t, resources::InlinableValue>
ResourcesInliningPass::filter_inlinable_resources(
    ResourceTableFile* res_table,
    const UnorderedMap<uint32_t, resources::InlinableValue>&
        inlinable_resources,
    const UnorderedSet<std::string>& resource_type_names,
    const UnorderedSet<std::string>& resource_entry_names) {
  auto type_ids = res_table->get_types_by_name(resource_type_names);

  std::vector<std::string> type_names;
  res_table->get_type_names(&type_names);

  uint32_t num_colors = 0;
  uint32_t num_ints = 0;
  uint32_t num_bools = 0;
  const auto& id_to_name = res_table->id_to_name;
  if (traceEnabled(RIP, 1)) {
    for (const auto& val : id_to_name) {
      auto type_name = get_type_name(type_names, val.first);
      if (type_name == std::nullopt) {
        continue;
      }
      if (*type_name == "color") {
        num_colors++;
      } else if (*type_name == "integer") {
        num_ints++;
      } else if (*type_name == "bool") {
        num_bools++;
      }
    }
    TRACE(RIP, 1, "num_ints: %u", num_ints);
    TRACE(RIP, 1, "num_bools: %u", num_bools);
    TRACE(RIP, 1, "num_colors: %u", num_colors);
  }

  UnorderedMap<uint32_t, resources::InlinableValue> refined_inlinable_resources;

  for (const auto& pair : UnorderedIterable(inlinable_resources)) {
    const auto& id = pair.first;
    const auto& value = pair.second;

    auto masked_type = id & TYPE_MASK_BIT;
    const auto& id_name = id_to_name.at(id);

    auto type_name = get_type_name(type_names, id);
    if (type_name == std::nullopt) {
      continue;
    }
    std::string entry_name_formatted = std::string(*type_name) + "/" + id_name;

    if (type_ids.find(masked_type) != type_ids.end() ||
        resource_entry_names.find(entry_name_formatted) !=
            resource_entry_names.end()) {
      refined_inlinable_resources.insert({id, value});
    }
  }

  return refined_inlinable_resources;
}

void ResourcesInliningPass::run_pass(DexStoresVector& stores,
                                     ConfigFiles& conf,
                                     PassManager& mgr) {
  std::string zip_dir;
  conf.get_json_config().get("apk_dir", "", zip_dir);
  always_assert(!zip_dir.empty());
  auto resources = create_resource_reader(zip_dir);
  auto res_table = resources->load_res_table();
  auto inlinable = res_table->get_inlinable_resource_values();
  UnorderedMap<uint32_t, resources::InlinableValue> inlinable_resources =
      filter_inlinable_resources(res_table.get(),
                                 inlinable,
                                 m_resource_type_names,
                                 m_resource_entry_names);

  const Scope scope = build_class_scope(stores);
  const auto& id_to_name = res_table->id_to_name;
  std::vector<std::string> type_names;
  res_table->get_type_names(&type_names);
  auto package_name = resources->get_manifest_package_name();

  MethodTransformsMap possible_transformations =
      ResourcesInliningPass::find_transformations(
          scope, inlinable_resources, id_to_name, type_names, package_name);

  for (auto& pair : UnorderedIterable(possible_transformations)) {
    auto* method = pair.first;
    auto& transforms = pair.second;
    ResourcesInliningPass::inline_resource_values_dex(method, transforms, mgr);
  }
}

/*
 This method generates a map of the valid APIs that can be inlined to the
 range of valid types
 that can be inlined. The DexMethodRef* represents the method that is being
 called and the first component of the tuple
 represents the lower bound of the type that can be inlined and the second
 component represents the upper bound of the type that can be inlined. Per the
 following Android source links, these methods are performing no further logic
 beyond retrieving the raw data from the resource table and thus should be
 easily representable with dex instructions.
 https://cs.android.com/android/platform/superproject/+/android-14.0.0_r1:frameworks/base/core/java/android/content/res/Resources.java;l=1180
 https://cs.android.com/android/platform/superproject/+/android-14.0.0_r1:frameworks/base/core/java/android/content/res/Resources.java;l=1073
 https://cs.android.com/android/platform/superproject/+/android-14.0.0_r1:frameworks/base/core/java/android/content/res/Resources.java;l=1206
*/
UnorderedMap<DexMethodRef*, std::tuple<uint8_t, uint8_t>>
generate_valid_method_refs() {
  UnorderedMap<DexMethodRef*, std::tuple<uint8_t, uint8_t>> usable_apis;

  DexMethodRef* bool_method =
      DexMethod::get_method("Landroid/content/res/Resources;.getBoolean:(I)Z");
  std::tuple<uint8_t, uint8_t> bool_range =
      std::make_tuple(android::Res_value::TYPE_INT_BOOLEAN,
                      android::Res_value::TYPE_INT_BOOLEAN);
  usable_apis.insert({bool_method, bool_range});

  DexMethodRef* color_method =
      DexMethod::get_method("Landroid/content/res/Resources;.getColor:(I)I");
  std::tuple<uint8_t, uint8_t> color_range =
      std::make_tuple(android::Res_value::TYPE_FIRST_COLOR_INT,
                      android::Res_value::TYPE_LAST_COLOR_INT);
  usable_apis.insert({color_method, color_range});

  DexMethodRef* int_method =
      DexMethod::get_method("Landroid/content/res/Resources;.getInteger:(I)I");
  std::tuple<uint8_t, uint8_t> int_range = std::make_tuple(
      android::Res_value::TYPE_FIRST_INT, android::Res_value::TYPE_LAST_INT);
  usable_apis.insert({int_method, int_range});

  DexMethodRef* string_method = DexMethod::get_method(
      "Landroid/content/res/Resources;.getString:(I)Ljava/lang/String;");
  std::tuple<uint8_t, uint8_t> string_range = std::make_tuple(
      android::Res_value::TYPE_STRING, android::Res_value::TYPE_LAST_INT);
  usable_apis.insert({string_method, string_range});
  return usable_apis;
}

bool exists_possible_transformation(
    const cfg::ControlFlowGraph& cfg,
    const UnorderedMap<DexMethodRef*, std::tuple<uint8_t, uint8_t>>&
        value_method_refs,
    const UnorderedSet<DexMethodRef*>& name_method_refs) {
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_INVOKE_VIRTUAL &&
          (value_method_refs.find(insn->get_method()) !=
               value_method_refs.end() ||
           name_method_refs.find(insn->get_method()) !=
               name_method_refs.end())) {
        return true;
      }
    }
  }
  return false;
}

MethodTransformsMap ResourcesInliningPass::find_transformations(
    const Scope& scope,
    const UnorderedMap<uint32_t, resources::InlinableValue>&
        inlinable_resources,
    const std::map<uint32_t, std::string>& id_to_name,
    const std::vector<std::string>& type_names,
    const std::optional<std::string>& package_name) {
  DexMethodRef* getResourceEntryName = DexMethod::get_method(
      "Landroid/content/res/Resources;.getResourceEntryName:(I)Ljava/lang/"
      "String;");
  DexMethodRef* getResourceName = DexMethod::get_method(
      "Landroid/content/res/Resources;.getResourceName:(I)Ljava/lang/"
      "String;");
  UnorderedSet<DexMethodRef*> name_method_refs = {getResourceEntryName,
                                                  getResourceName};

  UnorderedMap<DexMethodRef*, std::tuple<uint8_t, uint8_t>> value_method_refs =
      generate_valid_method_refs();

  MethodTransformsMap possible_transformations;

  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (method->rstate.no_optimizations()) {
      return;
    }

    namespace cp = constant_propagation;
    using CombinedAnalyzer =
        InstructionAnalyzerCombiner<cp::ResourceIdAnalyzer,
                                    cp::StaticFinalFieldAnalyzer,
                                    cp::HeapEscapeAnalyzer,
                                    cp::PrimitiveAnalyzer>;

    // Retrieving cfg
    auto* get_code = method->get_code();
    if (get_code == nullptr) {
      return;
    }
    auto& cfg = get_code->cfg();

    if (!exists_possible_transformation(cfg, value_method_refs,
                                        name_method_refs)) {
      return;
    }

    TRACE(RIP, 1, "Found possible transformations for %s", SHOW(method));
    cp::intraprocedural::FixpointIterator intra_cp(
        cfg, CombinedAnalyzer(nullptr, nullptr, nullptr, nullptr));
    // Runing the combined analyzer initially
    intra_cp.run(ConstantEnvironment());

    std::vector<InlinableOptimization> transforms;
    auto check_register = [](ConstantEnvironment& env,
                             reg_t reg) -> std::optional<int64_t> {
      const auto& register_env = env.get_register_environment();
      const auto& value = register_env.get(reg);
      auto constant_domain = value.maybe_get<SignedConstantDomain>();
      if (constant_domain != std::nullopt && !constant_domain->is_top() &&
          !constant_domain->is_bottom()) {
        return constant_domain->get_constant();
      }
      auto r_domain = value.maybe_get<ConstantResourceIdDomain>();
      if (r_domain != std::nullopt && r_domain->is_value()) {
        auto id = r_domain->get_constant();
        return std::optional<int64_t>(id->id);
      }
      return std::nullopt;
    };
    auto handle_instruction = [&](ConstantEnvironment& env,
                                  IRInstruction* insn) {
      if (insn->opcode() != OPCODE_INVOKE_VIRTUAL) {
        return;
      }
      DexMethodRef* method_ref = insn->get_method();
      auto value_method_comp =
          value_method_refs.find(method_ref) != value_method_refs.end();
      auto name_method_comp =
          name_method_refs.find(method_ref) != name_method_refs.end();
      if (!value_method_comp && !name_method_comp) {
        return;
      }
      auto const_value = check_register(env, insn->src(1));
      if (const_value != std::nullopt &&
          inlinable_resources.find(static_cast<uint32_t>(
              const_value.value())) != inlinable_resources.end() &&
          value_method_comp) {
        // Adding to list of possible optimizations if it is
        auto insertable = InlinableOptimization();
        insertable.insn = insn;
        insertable.inlinable =
            inlinable_resources.at(static_cast<uint32_t>(const_value.value()));
        transforms.push_back(insertable);
      } else if (const_value != std::nullopt && name_method_comp) {
        auto elem_id = static_cast<uint32_t>(const_value.value());
        auto insertable = InlinableOptimization();
        insertable.insn = insn;
        if (id_to_name.find(elem_id) == id_to_name.end()) {
          return;
        }
        if (method_ref == getResourceEntryName) {
          insertable.inlinable = id_to_name.at(elem_id);
        } else {
          auto type_name = get_type_name(type_names, elem_id);
          if (type_name == std::nullopt || package_name == std::nullopt) {
            return;
          }
          insertable.inlinable = *package_name + ":" + std::string(*type_name) +
                                 "/" + id_to_name.at(elem_id);
        }
        transforms.push_back(insertable);
      }
    };

    // Looping through each block and replaying
    for (auto* block : cfg.blocks()) {
      auto env = intra_cp.get_entry_state_at(block);
      auto last_insn = block->get_last_insn();
      // Going through each instruction in the block and checking for invoke
      // virtual, if it is inlinable and if it is a valid API call
      for (auto& mie : InstructionIterable(block)) {
        auto* insn = mie.insn;
        handle_instruction(env, insn);
        intra_cp.analyze_instruction(insn, &env, insn == last_insn->insn);
      }
    }
    // For each method, adding all possible transformations to the map
    if (!transforms.empty()) {
      possible_transformations.emplace(method, std::move(transforms));
    }
  });
  return possible_transformations;
}

void ResourcesInliningPass::inline_resource_values_dex(
    DexMethod* method,
    const std::vector<InlinableOptimization>& insn_inlinable,
    PassManager& mgr) {
  auto& cfg = method->get_code()->cfg();
  cfg::CFGMutation mutator(cfg);

  UnorderedMap<DexMethodRef*, std::tuple<uint8_t, uint8_t>> usable_apis =
      generate_valid_method_refs();

  IRInstruction* new_insn;
  for (const auto& elem : insn_inlinable) {
    auto* insn = elem.insn;
    cfg::InstructionIterator it_invoke = cfg.find_insn(insn);

    if (std::holds_alternative<resources::InlinableValue>(elem.inlinable)) {
      auto inlinable_value = get<resources::InlinableValue>(elem.inlinable);
      DexMethodRef* method_ref = insn->get_method();
      if (usable_apis.find(method_ref) != usable_apis.end()) {
        auto method_bounds = usable_apis.at(method_ref);
        auto method_lower_bound = get<0>(method_bounds);
        auto method_upper_bound = get<1>(method_bounds);

        if (method_lower_bound > inlinable_value.type ||
            method_upper_bound < inlinable_value.type) {
          continue;
        }
      }

      auto move_insn_it = cfg.move_result_of(it_invoke);
      if (move_insn_it.is_end()) {
        mgr.incr_metric("removed_unused_invokes", 1);
        mutator.remove(it_invoke);
        continue;
      }
      auto* move_insn = move_insn_it->insn;

      if (move_insn->opcode() == OPCODE_MOVE_RESULT) {
        new_insn = new IRInstruction(OPCODE_CONST);
        if (inlinable_value.type == android::Res_value::TYPE_INT_BOOLEAN) {
          if (method_ref ==
              DexMethod::get_method(
                  "Landroid/content/res/Resources;.getInteger:(I)I")) {
            if (static_cast<int>(inlinable_value.bool_value) == 1) {
              new_insn->set_literal((int32_t)0xffffffff);
            } else {
              new_insn->set_literal(0);
            }
          } else {
            new_insn->set_literal(
                static_cast<int64_t>(inlinable_value.bool_value));
          }
          mgr.incr_metric("inlined_booleans", 1);
        } else {
          new_insn->set_literal((int32_t)inlinable_value.uint_value);
          mgr.incr_metric("inlined_integers", 1);
        }
        always_assert_log(move_insn->has_dest(),
                          "The move instruction has no destination");
        new_insn->set_dest(move_insn->dest());
        mutator.replace(it_invoke, {new_insn});
      }

      else if (move_insn->opcode() == OPCODE_MOVE_RESULT_OBJECT) {
        new_insn = new IRInstruction(OPCODE_CONST_STRING);
        if (inlinable_value.type == android::Res_value::TYPE_STRING) {
          new_insn->set_string(
              DexString::make_string(inlinable_value.string_value));
        } else if (inlinable_value.type ==
                   android::Res_value::TYPE_INT_BOOLEAN) {
          new_insn->set_string(DexString::make_string(
              inlinable_value.bool_value ? "true" : "false"));
        } else if (inlinable_value.type == android::Res_value::TYPE_INT_HEX) {
          std::stringstream stream;
          stream << "0x" << std::hex << inlinable_value.uint_value;
          new_insn->set_string(DexString::make_string(stream.str()));
        } else if (inlinable_value.type >=
                       android::Res_value::TYPE_FIRST_COLOR_INT &&
                   inlinable_value.type <=
                       android::Res_value::TYPE_LAST_COLOR_INT) {
          std::stringstream stream;
          stream << "#" << std::hex << inlinable_value.uint_value;
          new_insn->set_string(DexString::make_string(stream.str()));
        } else if (inlinable_value.type >= android::Res_value::TYPE_FIRST_INT &&
                   inlinable_value.type <= android::Res_value::TYPE_LAST_INT) {
          new_insn->set_string(DexString::make_string(std::to_string(
              static_cast<int32_t>(inlinable_value.uint_value))));
        } else {
          continue;
        }
        IRInstruction* new_insn_pseudo_move =
            new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
        always_assert_log(move_insn->has_dest(),
                          "The move instruction has no destination");
        new_insn_pseudo_move->set_dest(move_insn->dest());
        mutator.replace(it_invoke, {new_insn, new_insn_pseudo_move});
        mgr.incr_metric("inlined_strings", 1);
      }
      mutator.remove(move_insn_it);
    } else {
      auto move_insn_it = cfg.move_result_of(it_invoke);
      if (move_insn_it.is_end()) {
        mgr.incr_metric("removed_unused_invokes", 1);
        mutator.remove(it_invoke);
        continue;
      }
      auto* move_insn = move_insn_it->insn;
      new_insn = new IRInstruction(OPCODE_CONST_STRING);
      new_insn->set_string(
          DexString::make_string(get<std::string>(elem.inlinable)));
      IRInstruction* new_insn_pseudo_move =
          new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
      always_assert_log(move_insn->has_dest(),
                        "The move instruction has no destination");
      new_insn_pseudo_move->set_dest(move_insn->dest());
      mutator.replace(it_invoke, {new_insn, new_insn_pseudo_move});
      mgr.incr_metric("inlined_strings", 1);
    }
    mgr.incr_metric("inlined_total", 1);
  }
  mutator.flush();
}

static ResourcesInliningPass s_pass;
