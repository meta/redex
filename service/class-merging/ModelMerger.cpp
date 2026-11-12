/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ModelMerger.h"

#include "CFGMutation.h"
#include "ClassAssemblingUtils.h"
#include "ConfigFiles.h"
#include "Creators.h" // NOLINT
#include "Debug.h"
#include "Inliner.h"
#include "MethodReference.h"
#include "ModelMethodMerger.h"
#include "Resolver.h"
#include "Show.h"
#include "TypeReference.h"
#include "TypeStringRewriter.h"
#include "TypeTagUtils.h"
#include "Walkers.h"

#include <fstream>
#include <sstream>

using namespace class_merging;

namespace {

using CallSites = std::vector<std::pair<DexMethod*, IRInstruction*>>;

const std::string CM_MAP_FILE_NAME = "redex-class-merging-map.txt";

TypeTags gen_type_tags(const std::vector<const MergerType*>& mergers) {
  TypeTags res;
  for (const auto& merger : mergers) {
    uint32_t val = 0;
    for (const auto* const type : merger->mergeables) {
      res.set_type_tag(type, val++);
    }
  }
  return res;
}

TypeTags collect_type_tags(const std::vector<const MergerType*>& mergers) {
  TypeTags type_tags;
  for (const auto* merger : mergers) {
    for (const auto* const type : merger->mergeables) {
      auto type_tag = type_tag_utils::parse_model_type_tag(type_class(type));
      always_assert_log(type_tag != std::nullopt,
                        "Type tag is missing from %s\n", SHOW(type));
      type_tags.set_type_tag(type, *type_tag);
    }
  }
  return type_tags;
}

DexField* scan_type_tag_field(const char* type_tag_field_name,
                              const DexType* type) {
  DexField* field = nullptr;
  while (field == nullptr && type != type::java_lang_Object()) {
    auto* cls = type_class(type);
    field = cls->find_ifield(type_tag_field_name, type::_int());
    type = cls->get_super_class();
  }

  always_assert_log(field, "Failed to find type tag field!");
  return field;
}

// If no type tags, the result is empty.
MergerToField get_type_tag_fields(const std::vector<const MergerType*>& mergers,
                                  bool input_has_type_tag,
                                  bool generate_type_tags) {
  MergerToField merger_to_type_tag_field;
  for (const auto* merger : mergers) {
    DexField* field = nullptr;
    if (input_has_type_tag) {
      field = scan_type_tag_field(EXTERNAL_TYPE_TAG_FIELD_NAME, merger->type);
      always_assert(field);
      set_public(field);
      merger_to_type_tag_field[merger] = field;
    } else if (generate_type_tags) {
      field = scan_type_tag_field(INTERNAL_TYPE_TAG_FIELD_NAME, merger->type);
      merger_to_type_tag_field[merger] = field;
    }
    TRACE(CLMG,
          5,
          "type tag field: merger->type %s field %s",
          SHOW(merger->type),
          SHOW(field));
  }
  return merger_to_type_tag_field;
}

/*
 * INSTANCE_OF needs special treatment involving the type tag.
 */
bool is_simple_type_ref(IRInstruction* insn) {
  if (!insn->has_type()) {
    return false;
  }
  return opcode::is_new_instance(insn->opcode()) ||
         opcode::is_check_cast(insn->opcode()) ||
         opcode::is_const_class(insn->opcode()) ||
         opcode::is_new_array(insn->opcode());
}

void update_code_type_refs(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger) {
  TRACE(CLMG, 8,
        "  Updating NEW_INSTANCE, NEW_ARRAY, CHECK_CAST & CONST_CLASS");
  UnorderedTypeSet mergeables;
  for (const auto& pair : UnorderedIterable(mergeable_to_merger)) {
    mergeables.insert(pair.first);
  }
  auto patcher = [&](DexMethod* meth, IRCode& code) {
    auto& cfg = code.cfg();
    auto ii = cfg::InstructionIterable(cfg);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;

      /////////////////////////////////////////////////////
      // Resolve method refs referencing a mergeable to defs
      /////////////////////////////////////////////////////
      if (insn->has_method()) {
        auto* meth_ref = insn->get_method();
        if (meth_ref == nullptr || meth_ref->is_def() ||
            meth_ref->is_external() || meth_ref->is_concrete()) {
          continue;
        }
        auto* proto = meth_ref->get_proto();
        if (!type_reference::proto_has_reference_to(proto, mergeables)) {
          continue;
        }
        bool resolved_virtual_to_interface;
        /*const auto meth_def =*/
        resolve_invoke_method_deprecated(insn, meth,
                                         &resolved_virtual_to_interface);
        // This is a very tricky case where ResolveRefs cannot resolve a
        // MethodRef to MethodDef. It is a invoke-virtual with a MethodRef
        // referencing an interface method implementation defined in a subclass
        // of the referenced type. To resolve the actual def we need to go
        // through another interface method search. Maybe we should fix it in
        // ResolveRefs.
        always_assert_log(resolved_virtual_to_interface,
                          "Found mergeable referencing MethodRef %s\n",
                          SHOW(meth_ref));
        always_assert(insn->opcode() == OPCODE_INVOKE_VIRTUAL);
        auto* new_proto =
            type_reference::get_new_proto(proto, mergeable_to_merger);
        DexMethodSpec spec;
        spec.proto = new_proto;
        meth_ref->change(spec, true /*rename on collision*/);
        continue;
      }
      ////////////////////////////////////////
      // Update simple type refs
      ////////////////////////////////////////
      if (!is_simple_type_ref(insn)) {
        continue;
      }
      auto* const ref_type = insn->get_type();
      const auto* type = type::make_element_type_if_array(ref_type);
      if (mergeable_to_merger.count(type) == 0) {
        continue;
      }
      always_assert(type_class(type));
      auto* merger_type = mergeable_to_merger.at(type);
      if (type::is_array(ref_type)) {
        auto* array_merger_type =
            type::make_array_type(merger_type, type::get_array_level(ref_type));
        insn->set_type(array_merger_type);
        TRACE(CLMG,
              9,
              "  replacing %s (%s -> %s) referencing array type of %s",
              SHOW(insn),
              SHOW(ref_type),
              SHOW(array_merger_type),
              SHOW(type));
      } else {
        insn->set_type(const_cast<DexType*>(merger_type));
        TRACE(CLMG, 9, "  replacing %s referencing %s", SHOW(insn), SHOW(type));
      }
    }
  };

  walk::parallel::code(scope, patcher);
}

void update_refs_to_mergeable_fields(
    const Scope& scope,
    const std::vector<const MergerType*>& mergers,
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger,
    MergerFields& merger_fields,
    bool disable_violation_fixes) {
  UnorderedMap<DexField*, DexField*> fields_lookup;
  for (const auto& merger : mergers) {
    cook_merger_fields_lookup(merger_fields.at(merger->type), merger->field_map,
                              fields_lookup);
  }
  TRACE(CLMG, 8, "  Updating field refs");
  walk::parallel::code(scope, [&](DexMethod* /*meth*/, IRCode& code) {
    auto& cfg = code.cfg();
    auto ii = cfg::InstructionIterable(cfg);
    UnorderedMap<IRInstruction*, SourceBlock*> sb_before_igets;

    for (auto* block : cfg.blocks()) {
      SourceBlock* prev_sb = nullptr;
      for (auto& mie : *block) {
        if (mie.type == MFLOW_SOURCE_BLOCK) {
          prev_sb = mie.src_block.get();
        }
        if (mie.type == MFLOW_OPCODE) {
          auto* insn = mie.insn;
          if (opcode::is_an_iget(insn->opcode())) {
            sb_before_igets[insn] = prev_sb;
          }
        }
      }
    }

    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;
      if (!insn->has_field()) {
        continue;
      }
      auto* const field = resolve_field(insn->get_field(),
                                        opcode::is_an_ifield_op(insn->opcode())
                                            ? FieldSearch::Instance
                                            : FieldSearch::Static);
      if (field == nullptr) {
        continue;
      }
      auto fields_it = fields_lookup.find(field);
      if (fields_it == fields_lookup.end()) {
        continue;
      }
      auto* const new_field = fields_it->second;
      insn->set_field(new_field);
      TRACE(CLMG,
            9,
            "  replacing %s field ref %s (defined on mergeable)",
            SHOW(insn),
            SHOW(field));

      if (field->get_type() == new_field->get_type()) {
        continue;
      }
      if (opcode::is_an_iget(insn->opcode())) {
        auto* field_type = field->get_type();
        auto merger_it = mergeable_to_merger.find(field_type);
        field_type = merger_it != mergeable_to_merger.end() ? merger_it->second
                                                            : field_type;
        auto sb_it = sb_before_igets.find(insn);
        patch_iget(cfg, it, field_type,
                   sb_it != sb_before_igets.end() ? sb_it->second : nullptr,
                   disable_violation_fixes);
      } else if (opcode::is_an_iput(insn->opcode())) {
        patch_iput(it);
      }
    }
  });
}

DexMethod* create_instanceof_method(const DexType* merger_type,
                                    DexField* type_tag_field) {
  auto* arg_list =
      DexTypeList::make_type_list({type::java_lang_Object(), type::_int()});
  auto* proto = DexProto::make_proto(type::_boolean(), arg_list);
  auto access = ACC_PUBLIC | ACC_STATIC;
  auto mc = MethodCreator(const_cast<DexType*>(merger_type),
                          DexString::make_string(INSTANCE_OF_STUB_NAME),
                          proto,
                          access);
  auto obj_loc = mc.get_local(0);
  auto type_tag_loc = mc.get_local(1);
  // first type check result loc.
  auto check_res_loc = mc.make_local(type::_boolean());
  auto* mb = mc.get_main_block();
  mb->instance_of(obj_loc, check_res_loc, const_cast<DexType*>(merger_type));
  // ret slot.
  auto ret_loc = mc.make_local(type::_boolean());
  // first check and branch off. Zero means fail.
  auto* instance_of_block = mb->if_testz(OPCODE_IF_EQZ, check_res_loc);

  // Fall through. Check succeed.
  auto itype_tag_loc = mc.make_local(type::_int());
  // CHECK_CAST obj to merger type.
  instance_of_block->check_cast(obj_loc, const_cast<DexType*>(merger_type));
  instance_of_block->iget(type_tag_field, obj_loc, itype_tag_loc);
  // Second type check
  auto* tag_match_block =
      instance_of_block->if_test(OPCODE_IF_NE, itype_tag_loc, type_tag_loc);
  // Second check succeed
  tag_match_block->load_const(ret_loc, 1);
  tag_match_block->ret(ret_loc);
  // Fall through, check failed.
  instance_of_block->load_const(ret_loc, 0);
  instance_of_block->ret(ret_loc);

  return mc.create();
}

void update_instance_of(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger,
    const UnorderedMap<const DexType*, DexMethod*>& merger_to_instance_of_meth,
    const TypeTags& type_tags,
    const bool is_intra_dex) {
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    always_assert(code.cfg_built());
    auto& cfg = code.cfg();
    cfg::CFGMutation mutation(cfg);
    auto ii = cfg::InstructionIterable(cfg);
    std::vector<IRInstruction*> instance_of_invokes;
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;
      if (!insn->has_type() || insn->opcode() != OPCODE_INSTANCE_OF) {
        continue;
      }
      auto* const type = insn->get_type();
      if (mergeable_to_merger.count(type) == 0) {
        continue;
      }

      always_assert(type_class(type));
      TRACE(CLMG, 9, " patching INSTANCE_OF at %s %s", SHOW(insn),
            SHOW(caller));
      // Load type_tag.
      auto type_tag = type_tags.get_type_tag(type);
      auto type_tag_reg = cfg.allocate_temp();
      auto* load_type_tag =
          method_reference::make_load_const(type_tag_reg, type_tag);
      // Replace INSTANCE_OF with INVOKE_STATIC to instance_of_meth.
      auto* merger_type = mergeable_to_merger.at(type);
      auto* instance_of_meth = merger_to_instance_of_meth.at(merger_type);
      std::vector<reg_t> args;
      args.push_back(insn->src(0));
      args.push_back(type_tag_reg);
      auto* invoke = method_reference::make_invoke(instance_of_meth,
                                                   OPCODE_INVOKE_STATIC, args);
      // MOVE_RESULT to dst of INSTANCE_OF.
      auto* move_res = new IRInstruction(OPCODE_MOVE_RESULT);
      move_res->set_dest(std::next(it)->insn->dest());
      mutation.insert_after(
          it, std::vector<IRInstruction*>{load_type_tag, invoke, move_res});
      // remove original INSTANCE_OF.
      mutation.remove(it);
      instance_of_invokes.push_back(invoke);

      TRACE(CLMG, 9, " patched INSTANCE_OF in \n%s", SHOW(cfg));
    }
    mutation.flush();

    if (!is_intra_dex) {
      return;
    }
    for (auto* invoke : instance_of_invokes) {
      // Inline the invoke to INSTANCE_OF method.
      auto* callee = resolve_invoke_method_deprecated(invoke, caller);
      bool is_inlined = inliner::inline_with_cfg(
          caller, callee, invoke, nullptr, nullptr, cfg.get_registers_size());
      TRACE(CLMG, 9, " inlined (%d) INSTANCE_OF in \n%s", is_inlined,
            SHOW(cfg));
    }
  });
}

void update_instance_of_no_type_tag(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger) {
  walk::parallel::code(scope, [&](DexMethod* /*caller*/, IRCode& code) {
    always_assert(code.cfg_built());
    auto& cfg = code.cfg();
    auto ii = cfg::InstructionIterable(cfg);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;
      if (!insn->has_type() || insn->opcode() != OPCODE_INSTANCE_OF) {
        continue;
      }
      auto* const type = insn->get_type();
      if (mergeable_to_merger.count(type) == 0) {
        continue;
      }

      always_assert(type_class(type));
      auto* merger_type = mergeable_to_merger.at(type);
      insn->set_type(merger_type);
      TRACE(CLMG, 9, " patched INSTANCE_OF no type tag in \n%s", SHOW(cfg));
    }
  });
}

void update_refs_to_mergeable_types(
    const Scope& scope,
    const SubtypeMaps& subtype_maps,
    const std::vector<const MergerType*>& mergers,
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger,
    const TypeTags& type_tags,
    const MergerToField& type_tag_fields,
    UnorderedMap<DexMethod*, std::string>& method_debug_map,
    bool has_type_tags,
    const bool is_intra_dex) {
  // Update simple type referencing instructions to instantiate merger type.
  update_code_type_refs(scope, mergeable_to_merger);
  type_reference::update_method_signature_type_references(
      scope,
      mergeable_to_merger,
      subtype_maps,
      std::optional<
          std::reference_wrapper<UnorderedMap<DexMethod*, std::string>>>(
          method_debug_map));
  type_reference::update_field_type_references(scope, mergeable_to_merger);
  // Fix INSTANCE_OF
  if (!has_type_tags) {
    always_assert(type_tag_fields.empty());
    update_instance_of_no_type_tag(scope, mergeable_to_merger);
    return;
  }
  UnorderedMap<const DexType*, DexMethod*> merger_to_instance_of_meth;
  for (const auto* merger : mergers) {
    const auto* type = merger->type;
    auto* type_tag_field = type_tag_fields.at(merger);
    auto* instance_of_meth = create_instanceof_method(type, type_tag_field);
    instance_of_meth->get_code()->build_cfg();
    merger_to_instance_of_meth[type] = instance_of_meth;
    type_class(type)->add_method(instance_of_meth);
  }
  update_instance_of(scope,
                     mergeable_to_merger,
                     merger_to_instance_of_meth,
                     type_tags,
                     is_intra_dex);
}

std::string merger_info(const MergerType& merger) {
  std::ostringstream ss;
  ss << " assembling merger " << SHOW(merger.type) << " - mergeables "
     << merger.mergeables.size() << ", dmethods " << merger.dmethods.size()
     << ", non_virt_methods " << merger.non_virt_methods.size()
     << ", virt_methods " << merger.vmethods.size() << "\n";
  for (const auto& imeths : merger.intfs_methods) {
    ss << "  interface methods " << imeths.methods.size() << "\n";
  }
  ss << " Field maps \n";
  for (const auto& fmap : UnorderedIterable(merger.field_map)) {
    ss << "  type " << SHOW(fmap.first) << "\n";
    size_t num_empty_fields = 0;
    for (auto* const field : fmap.second) {
      if (field != nullptr) {
        ss << "    field " << field->c_str() << " " << SHOW(field->get_type())
           << "\n";
      } else {
        ss << "    field -- empty due to imprecise shaping\n";
        num_empty_fields++;
      }
    }
    ss << "    Total empty fields = " << num_empty_fields << "\n";
  }
  return ss.str();
}

// Trim the debug map to only contain mergeable methods.
void trim_method_debug_map(
    const UnorderedMap<const DexType*, DexType*>& mergeable_to_merger,
    UnorderedMap<DexMethod*, std::string>& method_debug_map) {
  TRACE(CLMG, 5, "Method debug map un-trimmed %zu", method_debug_map.size());
  size_t trimmed_cnt = 0;
  unordered_erase_if(method_debug_map, [&](auto& p) {
    if (mergeable_to_merger.count(p.first->get_class())) {
      ++trimmed_cnt;
      return true;
    }
    return false;
  });

  TRACE(CLMG, 5, "Method debug map trimmed %zu", trimmed_cnt);
}

void write_out_type_mapping(const ConfigFiles& conf,
                            const TypeTags& type_tags,
                            const std::vector<const MergerType*>& mergers,
                            const TypeToMethodMap& method_dedup_map) {
  std::string mapping_file = conf.metafile(CM_MAP_FILE_NAME);
  std::ofstream os(mapping_file, std::ios_base::app);
  if (!os.is_open()) {
    return;
  }

  std::ostringstream out;
  for (const auto* merger : mergers) {
    for (const auto* mergeable : merger->mergeables) {
      out << SHOW(mergeable) << " -> " << SHOW(merger->type) << " "
          << type_tags.get_type_tag(mergeable) << '\n';

      if (method_dedup_map.count(mergeable) != 0u) {
        for (const auto& symbol_map : method_dedup_map.at(mergeable)) {
          out << "  " << symbol_map.first << " -> " << SHOW(symbol_map.second)
              << '\n';
        }
      }
    }
  }
  out << '\n';

  os << out.str();
  TRACE(CLMG,
        4,
        "Dumped type mapping (%zu) to %s",
        out.str().size(),
        mapping_file.c_str());
}

} // namespace

namespace class_merging {

const std::vector<DexField*> ModelMerger::empty_fields =
    std::vector<DexField*>();

void ModelMerger::update_merger_fields(const MergerType& merger) {
  auto merger_fields = merger.has_fields()
                           ? create_merger_fields(merger.type, merger.field_map)
                           : empty_fields;
  m_merger_fields[merger.type] = merger_fields;
}

void ModelMerger::update_stats(const std::string& model_name,
                               const std::vector<const MergerType*>& mergers,
                               ModelMethodMerger& mm) {
  for (const auto* merger : mergers) {
    m_stats.m_num_classes_merged += merger->mergeables.size();
  }
  // Print method stats
  mm.print_method_stats(model_name, m_stats.m_num_classes_merged);
  m_stats += mm.get_stats();
}

std::vector<DexClass*> ModelMerger::merge_model(
    Scope& scope,
    DexStoresVector& stores,
    ConfigFiles& conf,
    Model& model,
    bool update_method_profiles_stats) {
  Timer t("merge_model");
  std::vector<const MergerType*> to_materialize;
  std::vector<DexClass*> merger_classes;
  const auto model_spec = model.get_model_spec();
  bool input_has_type_tag = model_spec.input_has_type_tag();

  model.walk_hierarchy([&](const MergerType& merger) {
    // a model hierarchy is walked top down BFS style.
    // The walker is passed only merger that need computation.
    // A set of properties in the MergerType define the operation to
    // perform on the given type.

    auto* cls = type_class(merger.type);
    const auto& intfs = model.get_interfaces(merger.type);
    TRACE(CLMG, 3, "%s", merger_info(merger).c_str());
    always_assert_log(cls == nullptr,
                      "Shape type %s already names a class",
                      SHOW(merger.type));

    update_merger_fields(merger);
    cls = create_merger_class(merger.type,
                              model.get_parent(merger.type),
                              m_merger_fields.at(merger.type),
                              intfs,
                              model_spec.generate_type_tag(),
                              !merger.has_mergeables());
    // When inferring the interdex grouping using coldstart_pct markers, we do
    // not persist that grouping to the rstate. Doing that will inferfere with
    // the InterDex pass logic. InterDex pass does not recognize those markers
    // as DexEndMarker. To avoid more complications, convert the grouping idx to
    // two groups setup when setting up the rstate grouping idx as if we do not
    // recognize those coldstart_pct markers.
    bool uses_coldstart_pct_marker = conf.get_recognize_coldstart_pct_marker();
    auto subgroup_idx = merger.interdex_subgroup;
    if (uses_coldstart_pct_marker && subgroup_idx != std::nullopt) {
      if (*subgroup_idx < conf.get_num_interdex_groups() - 1) {
        subgroup_idx = 0;
      } else {
        subgroup_idx = 1;
      }
    }
    cls->rstate.set_interdex_subgroup(subgroup_idx);
    cls->rstate.set_generated();
    if (subgroup_idx) {
      TRACE(CLMG, 5, "Set interdex subgroup %u (%u) for %s", *subgroup_idx,
            *merger.interdex_subgroup, SHOW(merger.type));
    }

    add_class(cls, scope, stores, merger.dex_id);
    merger_classes.push_back(cls);

    if (!merger.has_mergeables()) {
      return;
    }
    // Bail out if we should not generate type tags and there are vmethods
    // or intfs_methods.
    if (model_spec.no_type_tag()) {
      if (!merger.vmethods.empty() || !merger.intfs_methods.empty()) {
        TRACE(CLMG,
              5,
              "Bailing out: no type tag merger %s w/ true virtuals",
              SHOW(merger.type));
        return;
      }
    }
    to_materialize.emplace_back(&merger);
  });

  // Merging transformations.
  UnorderedMap<const DexType*, DexType*> mergeable_to_merger;
  for (const auto* merger : to_materialize) {
    auto* type = const_cast<DexType*>(merger->type);
    for (const auto* mergeable : merger->mergeables) {
      auto* cls = type_class(mergeable);
      // Count source instance fields, not coalesced slots or shape
      // placeholders.
      for (auto* field : cls->get_ifields()) {
        if (is_volatile(field)) {
          ++m_stats.m_num_merged_volatile_fields;
        }
        if (is_final(field)) {
          ++m_stats.m_num_merged_final_fields;
        }
      }
      loosen_access_modifier_except_vmethods(cls);
      mergeable_to_merger[mergeable] = type;
    }
  }

  TypeTags type_tags = input_has_type_tag ? collect_type_tags(to_materialize)
                                          : gen_type_tags(to_materialize);
  auto type_tag_fields = get_type_tag_fields(to_materialize, input_has_type_tag,
                                             model_spec.generate_type_tag());
  UnorderedMap<DexMethod*, std::string> method_debug_map;
  const auto& subtype_maps = model.get_type_system().get_subtype_maps();
  update_refs_to_mergeable_types(
      scope, subtype_maps, to_materialize, mergeable_to_merger, type_tags,
      type_tag_fields, method_debug_map, model_spec.has_type_tag(),
      m_is_intra_dex_merging);
  trim_method_debug_map(mergeable_to_merger, method_debug_map);
  update_refs_to_mergeable_fields(scope, to_materialize, mergeable_to_merger,
                                  m_merger_fields,
                                  conf.disable_violation_fixes());

  // Merge methods
  method_profiles::MethodProfiles& method_profile = conf.get_method_profiles();
  ModelMethodMerger mm(
      scope,
      to_materialize,
      type_tag_fields,
      &type_tags,
      method_debug_map,
      model.get_model_spec(),
      model.get_model_spec().max_num_dispatch_target,
      update_method_profiles_stats
          ? std::optional<method_profiles::MethodProfiles*>(&method_profile)
          : std::nullopt);
  auto mergeable_to_merger_ctor = mm.merge_methods();
  update_stats(model.get_name(), to_materialize, mm);

  // Rewrite strings in annotation dalvik.annotation.Signature
  rewriter::TypeStringMap type_str_mapping(mergeable_to_merger);
  rewriter::rewrite_dalvik_annotation_signature(scope, type_str_mapping);

  if (model_spec.replace_type_like_strings()) {
    rewriter::rewrite_string_literal_instructions(scope, type_str_mapping);
  }

  // Write out mapping files
  auto method_dedup_map = mm.get_method_dedup_map();
  write_out_type_mapping(conf, type_tags, to_materialize, method_dedup_map);
  if (!to_materialize.empty()) {
    post_process(model, type_tags, mergeable_to_merger_ctor);
  }

  // Properly update merged classes or even remove them.
  auto* no_interface = DexTypeList::make_type_list({});
  scope.erase(
      std::remove_if(scope.begin(),
                     scope.end(),
                     [&mergeable_to_merger, &no_interface](DexClass* cls) {
                       if (mergeable_to_merger.count(cls->get_type()) != 0u) {
                         cls->set_interfaces(no_interface);
                         cls->set_super_class(type::java_lang_Object());
                         redex_assert(CONSTP(cls)->get_vmethods().empty());
                         if ((cls->get_clinit() == nullptr) &&
                             cls->get_sfields().empty()) {
                           // Purge merged cls w/o static fields.
                           return true;
                         } else {
                           // Purge dmethods other than the clinit.
                           // For the original dmethods on the merged classes,
                           // we dedup them and relocate the selected ones to
                           // the merger. We remove the replaced ones in
                           // `ModelMethodMerger::dedup_non_ctor_non_virt_methods`.
                           // What's left here are staticized virtual methods
                           // left by the virtual method merging process. We did
                           // inline their entries in the merged dispatch or
                           // relocate if inlining failed. So what's left here
                           // are not reachable anymore, and safe to be purged.
                           auto dmethods = cls->get_dmethods();
                           for (auto* m : dmethods) {
                             if (!method::is_clinit(m)) {
                               cls->remove_method(m);
                               DexMethod::delete_method(m);
                             }
                           }
                         }
                       }
                       return false;
                     }),
      scope.end());

  TRACE(CLMG, 3, "created %zu merger classes", merger_classes.size());
  m_stats.m_num_generated_classes =
      static_cast<uint32_t>(merger_classes.size());
  return merger_classes;
}

} // namespace class_merging
