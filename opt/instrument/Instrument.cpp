/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Instrument.h"

#include <boost/algorithm/string.hpp>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "BlockInstrument.h"
#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexStructure.h"
#include "DexUtil.h"
#include "IRList.h"
#include "InitClassesWithSideEffects.h"
#include "InterDexPassPlugin.h"
#include "JsonWrapper.h"
#include "Match.h"
#include "MethodReference.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Shrinker.h"
#include "ShrinkerConfig.h"
#include "Timer.h"
#include "Trace.h"
#include "TypeSystem.h"
#include "Walkers.h"

using namespace instrument;

/*
 * This pass performs instrumentation for dynamic (runtime) analysis.
 *
 * Analysis code, which should be a static public method, is written in Java.
 * Its class and method names are specified in the config. This pass then
 * inserts the method to points of interest. For a starting example, we
 * implement the "onMethodBegin" instrumentation.
 */
namespace {

constexpr bool instr_debug = false;

constexpr const char* SIMPLE_METHOD_TRACING = "simple_method_tracing";
constexpr const char* BASIC_BLOCK_TRACING = "basic_block_tracing";
constexpr const char* BASIC_BLOCK_HIT_COUNT = "basic_block_hit_count";
constexpr const char* METHOD_REPLACEMENT = "methods_replacement";

// For example, say that "Lcom/facebook/debug/" is in the set. We match either
// "^Lcom/facebook/debug/*" or "^Lcom/facebook/debug;".
bool match_class_name(std::string cls_name,
                      const UnorderedSet<std::string>& set) {
  always_assert(cls_name.back() == ';');
  // We also support exact class name (e.g., "Lcom/facebook/Debug;")
  if (set.count(cls_name) != 0u) {
    return true;
  }
  cls_name.back() = '/';
  size_t pos = cls_name.find('/', 0);
  while (pos != std::string::npos) {
    if (set.count(cls_name.substr(0, pos + 1)) != 0u) {
      return true;
    }
    pos = cls_name.find('/', pos + 1);
  }
  return false;
}

void instrument_onMethodBegin(DexMethod* method,
                              int index,
                              DexMethod* method_onMethodBegin) {
  IRCode* code = method->get_code();
  assert(code != nullptr);
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();

  IRInstruction* const_inst = new IRInstruction(OPCODE_CONST);
  const_inst->set_literal(index);
  const auto reg_dest = cfg.allocate_temp();
  const_inst->set_dest(reg_dest);

  IRInstruction* invoke_inst = new IRInstruction(OPCODE_INVOKE_STATIC);
  invoke_inst->set_method(method_onMethodBegin);
  invoke_inst->set_srcs_size(1);
  invoke_inst->set_src(0, reg_dest);

  // Try to find a right insertion point: the entry point of the method.
  // We skip any fall throughs and IOPCODE_LOAD_PARAM*.
  auto* entry_block = cfg.entry_block();
  auto insert_point = entry_block->get_first_non_param_loading_insn();
  auto cfg_insert_point =
      entry_block->to_cfg_instruction_iterator(insert_point);
  cfg.insert_before(cfg_insert_point, {const_inst, invoke_inst});

  if (instr_debug) {
    auto ii = cfg::InstructionIterable(cfg);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      if (it == cfg_insert_point) {
        TRACE(INSTRUMENT, 9, "<==== insertion");
        TRACE(INSTRUMENT, 9, "%s", SHOW(*it));
        ++it;
        if (it != ii.end()) {
          TRACE(INSTRUMENT, 9, "%s", SHOW(*it));
          ++it;
          if (it != ii.end()) {
            TRACE(INSTRUMENT, 9, "%s", SHOW(*it));
          }
        }
        TRACE(INSTRUMENT, 9, "");
        break;
      }
      TRACE(INSTRUMENT, 9, "%s", SHOW(*it));
    }
  }
}

void do_simple_method_tracing(DexClass* analysis_cls,
                              DexStoresVector& stores,
                              ConfigFiles& cfg,
                              PassManager& pm,
                              const InstrumentPass::Options& options) {
  const size_t NUM_SHARDS = options.num_shards;
  const auto& array_fields =
      InstrumentPass::patch_sharded_arrays(analysis_cls, NUM_SHARDS);
  always_assert(array_fields.size() == NUM_SHARDS);
  const auto& analysis_methods =
      InstrumentPass::generate_sharded_analysis_methods(
          analysis_cls, options.analysis_method_name, array_fields, NUM_SHARDS);
  const auto& analysis_method_map = analysis_methods.first;
  const auto& analysis_method_names = analysis_methods.second;

  // Write metadata file with more information.
  const auto& file_name = cfg.metafile(options.metadata_file_name);
  std::ofstream ofs(file_name, std::ofstream::out | std::ofstream::trunc);

  // Write meta info of the meta file: the type of the meta file and version.
  ofs << "#,simple-method-tracing,1.0\n";

  size_t method_id = 0;
  size_t excluded = 0;
  UnorderedSet<std::string> method_names;
  std::vector<DexMethod*> to_instrument;

  auto worker = [&](DexMethod* method, size_t& total_size) -> int {
    std::string name = method->get_deobfuscated_name_or_empty_copy();
    always_assert_log(
        !name.empty(),
        "Deobfuscated method name can't be empty: obfuscated "
        "name: %s, class: \'%s\'(%s)",
        SHOW(method->get_name()),
        type_class(method->get_class())->get_deobfuscated_name().c_str(),
        SHOW(method->get_class()->get_name()));
    always_assert_log(
        !method_names.count(name),
        "Deobfuscated method names must be unique, but found duplicate: \'%s\'",
        SHOW(name));
    method_names.insert(name);

    if (method->get_code() == nullptr) {
      ofs << "M,-1," << name << ",0,\"" << vshow(method->get_access(), true)
          << "\"\n";
      return 0;
    }

    const size_t sum_opcode_sizes =
        method->get_code()->cfg().sum_opcode_sizes();
    total_size += sum_opcode_sizes;

    // Excluding analysis methods myselves.
    if ((analysis_method_names.count(method->get_name()->str_copy()) != 0u) ||
        method == analysis_cls->get_clinit()) {
      ++excluded;
      TRACE(INSTRUMENT, 2, "Excluding analysis method: %s", SHOW(method));
      ofs << "M,-1," << name << "," << sum_opcode_sizes << ",\"" << "MYSELF "
          << vshow(method->get_access(), true) << "\"\n";
      return 0;
    }

    // Handle allowlist and blocklist.
    if (!options.allowlist.empty()) {
      if (InstrumentPass::is_included(method, options.allowlist)) {
        TRACE(INSTRUMENT, 8, "Allowlist: included: %s", SHOW(method));
      } else {
        ++excluded;
        TRACE(INSTRUMENT, 9, "Allowlist: excluded: %s", SHOW(method));
        return 0;
      }
    }

    // In case of a conflict, when an entry is present in both blocklist
    // and allowlist, the blocklist is given priority and the entry
    // is not instrumented.
    if (InstrumentPass::is_included(method, options.blocklist)) {
      ++excluded;
      TRACE(INSTRUMENT, 8, "Blocklist: excluded: %s", SHOW(method));
      ofs << "M,-1," << name << "," << sum_opcode_sizes << ",\"" << "BLOCKLIST "
          << vshow(method->get_access(), true) << "\"\n";
      return 0;
    }

    TRACE(INSTRUMENT, 8, "%zu: %s", method_id, SHOW(method));
    assert(to_instrument.size() == method_id);
    to_instrument.push_back(method);

    // Emit metadata to the file.
    ofs << "M," << method_id << "," << name << "," << sum_opcode_sizes << ",\""
        << vshow(method->get_access(), true /*is_method*/) << "\"\n";
    ++method_id;
    return 1;
  };

  auto scope = build_class_scope(stores);
  TypeSystem ts(scope);

  // We now have sharded method stats arrays. We interleave methods into
  // multiple arrays. Say we instrument 11 methods and have 3 arrays. Each array
  // may have up to floor(11/3) + 1 = 4 methods. Their distributions look like:
  //
  //                0                   1
  //   method id    0 1 2 3 4 5 6 7 8 9 0
  //   array id     0 1 2 0 1 2 0 1 2 0 1  <= i % 3
  //   array index  0 0 0 1 1 1 2 2 2 3 3  <= i / 3
  //
  //                  arrays[0]     arrays[1]    arrays[2]
  //   method id    [0, 3, 6, 9]  [1, 4, 7, 10]  [2, 5, 8]
  //
  // Be extremely careful when handling indexes. The Java-side uploader needs to
  // untangle the arrays. The WWW endpoints do not need to know this complexity.
  // So, only devices handle this sharding.
  //
  // In order to do that, we need to know the total number of methods to be
  // instrumented. We don't know this number until iterating all methods while
  // processing exclusions. We take a two-pass approach:
  //  1) For all methods, collect (method id, method) pairs and write meta data.
  //  2) Do actual instrumentation.
  for (const auto& cls : scope) {
    std::string cls_name = cls->get_deobfuscated_name_or_empty_copy();
    always_assert_log(
        !method_names.count(cls_name),
        "Deobfuscated class names must be unique, but found duplicate: %s",
        SHOW(cls_name));
    method_names.insert(cls_name);

    int instrumented = 0;
    size_t total_size = 0;
    for (auto* dmethod : cls->get_dmethods()) {
      instrumented += worker(dmethod, total_size);
    }
    for (auto* vmethod : cls->get_vmethods()) {
      instrumented += worker(vmethod, total_size);
    }

    ofs << "C," << cls_name << "," << total_size << ","
        << (instrumented == 0 ? "NONE" : std::to_string(instrumented)) << ","
        << cls->get_dmethods().size() << "," << cls->get_vmethods().size()
        << ",\"" << vshow(cls->get_access(), false /*is_method*/) << "\"\n";

    // Enumerate all super and interface classes for this class.
    const auto& obj_type = DexType::get_type("Ljava/lang/Object;");
    std::stringstream ss_parents;
    for (const auto& e : ts.parent_chain(cls->get_type())) {
      // Exclude myself and obvious java.lang.Object.
      if (e != obj_type && e != cls->get_type()) {
        ss_parents << show_deobfuscated(e) << " ";
      }
    }
    if (ss_parents.tellp() > 0) {
      ofs << "P," << cls_name << ",\"" << ss_parents.str() << "\"\n";
    }

    std::stringstream ss_interfaces;
    for (const auto& e : ts.get_all_super_interfaces(cls->get_type())) {
      ss_interfaces << show_deobfuscated(e) << " ";
    }
    if (ss_interfaces.tellp() > 0) {
      ofs << "I," << cls_name << ",\"" << ss_interfaces.str() << "\"\n";
    }
  }

  // Now we know the total number of methods to be instrumented. Do some
  // computations and actual instrumentation.
  const size_t kTotalSize = to_instrument.size();
  TRACE(INSTRUMENT, 2, "%zu methods to be instrumented; shard size: %zu (+1)",
        kTotalSize, kTotalSize / NUM_SHARDS);
  for (size_t i = 0; i < kTotalSize; ++i) {
    TRACE(INSTRUMENT, 6, "Sharded %zu => [%zu][%zu] %s", i, (i % NUM_SHARDS),
          (i / NUM_SHARDS), SHOW(to_instrument[i]));
    instrument_onMethodBegin(
        to_instrument[i],
        static_cast<int>((i / NUM_SHARDS) * options.num_stats_per_method),
        analysis_method_map.at(static_cast<int>(i % NUM_SHARDS) + 1));
  }

  TRACE(INSTRUMENT,
        1,
        "%zu methods were instrumented (%zu methods were excluded)",
        method_id,
        excluded);

  // Patch stat array sizes.
  for (size_t i = 0; i < NUM_SHARDS; ++i) {
    size_t n = kTotalSize / NUM_SHARDS + (i < kTotalSize % NUM_SHARDS ? 1 : 0);
    // Get obfuscated name corresponding to each sMethodStat[1-N] field.
    const auto field_name =
        array_fields.at(static_cast<int>(i) + 1)->get_name()->str();
    InstrumentPass::patch_array_size(
        analysis_cls, field_name,
        static_cast<int>(options.num_stats_per_method) * static_cast<int>(n));
  }

  // Patch method count constant.
  always_assert(method_id == kTotalSize);
  auto* field = analysis_cls->find_field_from_simple_deobfuscated_name(
      "sNumStaticallyInstrumented");
  always_assert(field != nullptr);
  InstrumentPass::patch_static_field(analysis_cls, field->get_name()->str(),
                                     static_cast<int>(kTotalSize));

  field =
      analysis_cls->find_field_from_simple_deobfuscated_name("sProfileType");
  always_assert(field != nullptr);
  InstrumentPass::patch_static_field(
      analysis_cls, field->get_name()->str(),
      static_cast<int>(ProfileTypeFlags::SimpleMethodTracing));

  ofs.close();
  TRACE(INSTRUMENT, 2, "Index file was written to: %s", SHOW(file_name));

  pm.incr_metric("Instrumented", method_id);
  pm.incr_metric("Excluded", excluded);
}

UnorderedSet<std::string> load_blocklist_file(const std::string& file_name) {
  // Assume the file simply enumerates blocklisted names.
  UnorderedSet<std::string> ret;
  std::ifstream ifs(file_name);
  assert_log(ifs, "Can't open blocklist file: %s\n", SHOW(file_name));

  std::string line;
  while (ifs >> line) {
    ret.insert(line);
  }

  TRACE(INSTRUMENT, 3, "Loaded %zu blocklist entries from %s", ret.size(),
        SHOW(file_name));
  return ret;
}

void count_source_block_chain_length(DexStoresVector& stores, PassManager& pm) {
  std::atomic<size_t> longest_list{0};
  std::atomic<size_t> sum{0};
  std::atomic<size_t> count{0};
  walk::parallel::methods(build_class_scope(stores), [&](DexMethod* m) {
    auto* code = m->get_code();
    if (code == nullptr) {
      return;
    }
    std::optional<size_t> last_known = std::nullopt;
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    for (const auto* b : cfg.blocks()) {
      for (const auto& mie : *b) {
        if (mie.type == MFLOW_SOURCE_BLOCK) {
          size_t len = 0;
          for (auto* sb = mie.src_block.get(); sb != nullptr;
               sb = sb->next.get()) {
            ++len;
          }
          count.fetch_add(1);
          sum.fetch_add(len);

          if (last_known && *last_known >= len) {
            continue;
          }
          for (;;) {
            auto cur = longest_list.load();
            if (cur >= len) {
              last_known = cur;
              break;
            }
            if (longest_list.compare_exchange_strong(cur, len)) {
              last_known = len;
              break;
            }
          }
        }
      }
    }
  });
  pm.set_metric("longest_sb_chain", longest_list.load());
  pm.set_metric("average100_sb_chain",
                count.load() > 0 ? 100 * sum.load() / count.load() : 0);
}

} // namespace

InstrumentPass::InstrumentPass() : Pass("InstrumentPass") {}
InstrumentPass::~InstrumentPass() {}

// Find a sequence of opcode that creates a static array. Patch the array size.
void InstrumentPass::patch_array_size(DexClass* analysis_cls,
                                      const std::string_view array_name,
                                      const int array_size) {
  DexMethod* clinit = analysis_cls->get_clinit();
  always_assert(clinit != nullptr);

  auto* code = clinit->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  bool patched = false;
  walk::matching_opcodes_in_block(
      *clinit,
      // Don't find OPCODE_CONST. It might be deduped with others, or changing
      // this const can affect other instructions. (Well, we might have a
      // unique const number though.) So, just create a new const load
      // instruction. LocalDCE can clean up the redundant instructions.
      std::make_tuple(/* m::const_(), */
                      m::new_array_(),
                      m::move_result_pseudo_object_(),
                      m::sput_object_()),
      [&](DexMethod* method,
          cfg::Block*,
          const std::vector<IRInstruction*>& insts) {
        assert(method == clinit);
        if (insts[2]->get_field()->get_name()->str() != array_name) {
          return;
        }

        IRInstruction* const_inst = new IRInstruction(OPCODE_CONST);
        const_inst->set_literal(array_size);
        const auto reg_dest = cfg.allocate_temp();
        const_inst->set_dest(reg_dest);
        insts[0]->set_src(0, reg_dest);
        auto ii = cfg::InstructionIterable(cfg);
        for (auto it = ii.begin(); it != ii.end(); ++it) {
          if (it->insn == insts[0]) {
            cfg.insert_before(it, const_inst);
            patched = true;
            return;
          }
        }
      });

  if (!patched) {
    std::cerr << "[InstrumentPass] error: cannot patch array size.\n";
    std::cerr << show(clinit->get_code()->cfg()) << '\n';
    exit(1);
  }

  TRACE(INSTRUMENT, 2, "%s array was patched: %d", SHOW(array_name),
        array_size);
}

void InstrumentPass::patch_static_field(DexClass* analysis_cls,
                                        const std::string_view field_name,
                                        const int new_number) {
  DexMethod* clinit = analysis_cls->get_clinit();
  always_assert(clinit != nullptr);

  // Find the sput with the given field name.
  auto* code = clinit->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* sput_inst = it->insn;
    if (sput_inst->opcode() != OPCODE_SPUT ||
        sput_inst->get_field()->get_name()->str() != field_name) {
      continue;
    }
    // Find the SPUT.
    // Create a new const instruction just like patch_stat_array_size.
    IRInstruction* const_inst = new IRInstruction(OPCODE_CONST);
    const_inst->set_literal(new_number);
    const auto reg_dest = cfg.allocate_temp();
    const_inst->set_dest(reg_dest);
    sput_inst->set_src(0, reg_dest);
    cfg.insert_before(it, const_inst);
    TRACE(INSTRUMENT, 2, "%s was patched: %d", SHOW(field_name), new_number);
    return;
  }
  // SPUT can be null if the original field value was encoded in the
  // static_values_off array. And consider simplifying using make_concrete.
  TRACE(INSTRUMENT, 2, "sput %s was deleted; creating it", SHOW(field_name));
  auto* sput_inst = new IRInstruction(OPCODE_SPUT);
  sput_inst->set_field(
      DexField::make_field(DexType::make_type(analysis_cls->get_name()),
                           DexString::make_string(field_name),
                           DexType::make_type("I")));
  IRInstruction* const_inst = new IRInstruction(OPCODE_CONST);
  const_inst->set_literal(new_number);
  const auto reg_dest = cfg.allocate_temp();
  const_inst->set_dest(reg_dest);
  sput_inst->set_src(0, reg_dest);
  auto* entry_block = cfg.entry_block();
  auto last_param = entry_block->get_last_param_loading_insn();
  // always_assert(last_param != entry_block->end());
  if (last_param != entry_block->end()) {
    auto cfg_last_param = entry_block->to_cfg_instruction_iterator(last_param);
    cfg.insert_after(cfg_last_param, {const_inst, sput_inst});
  } else {
    auto first_insn = entry_block->get_first_non_param_loading_insn();
    auto cfg_first_insn = entry_block->to_cfg_instruction_iterator(first_insn);
    cfg.insert_before(cfg_first_insn, {const_inst, sput_inst});
  }
  TRACE(INSTRUMENT, 2, "%s was patched: %d", SHOW(field_name), new_number);
}

void InstrumentPass::bind_config() {
  bind("instrumentation_strategy", "", m_options.instrumentation_strategy);
  bind("analysis_class_name", "", m_options.analysis_class_name);
  bind("analysis_method_name", "", m_options.analysis_method_name);
  bind("blocklist", {}, m_options.blocklist);
  bind("allowlist", {}, m_options.allowlist);
  bind("blocklist_file_name", "", m_options.blocklist_file_name);
  bind("metadata_file_name", "redex-instrument-metadata.txt",
       m_options.metadata_file_name);
  bind("num_stats_per_method", 1, m_options.num_stats_per_method);
  bind("num_shards", 1, m_options.num_shards);
  // Note: only_cold_start_class is only used for block tracing.
  bind("only_cold_start_class", false, m_options.only_cold_start_class);
  bind("methods_replacement", {}, m_options.methods_replacement,
       "Replacing instance method call with static method call.",
       Configurable::bindflags::methods::error_if_unresolvable);
  bind("analysis_method_names", {}, m_options.analysis_method_names);
  // 0 means the block tracing is effectively method-only tracing.
  bind("max_num_blocks", 0, m_options.max_num_blocks);
  bind("instrument_catches", true, m_options.instrument_catches);
  bind("instrument_blocks_without_source_block", true,
       m_options.instrument_blocks_without_source_block);
  bind("instrument_only_root_store", false,
       m_options.instrument_only_root_store);
  bind("inline_onBlockHit", false, m_options.inline_onBlockHit);
  bind("inline_onNonLoopBlockHit", false, m_options.inline_onNonLoopBlockHit);
  bind("apply_CSE_CopyProp", false, m_options.apply_CSE_CopyProp);
  bind("analysis_package_prefix", std::nullopt,
       m_options.analysis_package_prefix);

  trait(Traits::Pass::unique, true);

  after_configuration([this] {
    // Currently we only support instance call to static call.
    for (auto& pair : UnorderedIterable(m_options.methods_replacement)) {
      always_assert(!is_static(pair.first));
      always_assert(is_static(pair.second));
    }
    if (m_options.instrumentation_strategy == METHOD_REPLACEMENT) {
      always_assert_log(
          !m_options.methods_replacement.empty(),
          "Invalid configuration, `methods_replacement` should not be empty\n");
    }
  });
}

namespace {

// Possible finalize some fields to help Redex clean up unused instrumentation.
void maybe_unset_dynamic_analysis(
    DexStoresVector& stores,
    const std::string& analysis_class_name,
    const std::optional<std::string>& analysis_package_prefix) {
  auto undo_rename_delete = [](auto* cls) {
    // Undo all can_rename and can_delete on it.
    cls->rstate.unset_root();
    for (auto* m : cls->get_all_methods()) {
      m->rstate.unset_root();
    }
    for (auto* f : cls->get_all_fields()) {
      f->rstate.unset_root();
    }

    // We don't care about running its clinit
    cls->rstate.set_clinit_has_no_side_effects();
  };

  [&]() {
    auto* analysis_type = DexType::get_type(analysis_class_name);
    if (analysis_type == nullptr) {
      return;
    }
    auto* analysis_cls = type_class(analysis_type);
    if (analysis_cls == nullptr) {
      return;
    }

    undo_rename_delete(analysis_cls);

    auto* field = analysis_cls->find_field_from_simple_deobfuscated_name(
        "sNumStaticallyInstrumented");
    if (field != nullptr) {
      // Make it final. The default value should be 0, and may lead to other
      // optimizations, e.g., by FinalInline.
      field->set_access(field->get_access() | DexAccessFlags::ACC_FINAL);

      always_assert(field->get_type() == type::_int());
      field->set_value(std::unique_ptr<DexEncodedValue>(
          new DexEncodedValuePrimitive(DexEncodedValueTypes::DEVT_INT, 0)));

      // Look through all methods and remove accesses.
      walk::code(std::vector<DexClass*>{analysis_cls},
                 [&](auto* /*method*/, auto& code) {
                   cfg::ScopedCFG c{&code};
                   cfg::CFGMutation mut{*c};
                   bool found = false;
                   auto iterable = cfg::InstructionIterable(*c);
                   auto end = iterable.end();
                   for (auto it = iterable.begin(); it != end; ++it) {
                     auto* insn = it->insn;
                     if (insn->opcode() != OPCODE_SPUT) {
                       continue;
                     }
                     if (insn->get_field() == field) {
                       found = true;
                       mut.remove(it);
                     }
                   }
                   if (found) {
                     mut.flush();
                   } else {
                     mut.clear();
                   }
                 });
    }
  }();

  if (analysis_package_prefix) {
    walk::parallel::classes(build_class_scope(stores), [&](auto* cls) {
      if (cls->get_name()->str().find(*analysis_package_prefix) == 0) {
        undo_rename_delete(cls);
      }
    });
  }
}

void set_no_opt_flag_on_analysis_methods(
    bool value,
    const std::string& analysis_class_name,
    const std::vector<std::string>& analysis_method_names) {

  // Set the 'no_optimizations' flag for analysis methods (onMethodBeginGated,
  // onMethodExit). Primarily so we do not outline from them.

  auto* analysis_type = DexType::get_type(analysis_class_name);
  if (analysis_type == nullptr) {
    return;
  }

  auto* analysis_cls = type_class(analysis_type);
  if (analysis_cls == nullptr) {
    return;
  }

  for (auto* m : analysis_cls->get_all_methods()) {
    if (std::find(analysis_method_names.begin(), analysis_method_names.end(),
                  m->get_name()->str()) != analysis_method_names.end()) {
      if (value) {
        m->rstate.set_no_optimizations();
      } else {
        m->rstate.reset_no_optimizations();
      }
    }
  }
}

size_t check_integrity(DexStoresVector& stores, const std::string& prefix) {
  auto scope = build_class_scope(stores);
  InsertOnlyConcurrentSet<const DexType*> checked_types;
  auto check_type = [&prefix, &checked_types](const DexType* type) {
    if (type->get_name()->str().find(prefix) != 0) {
      return true;
    }
    checked_types.insert(type);
    return type_class(type) != nullptr;
  };
  walk::parallel::classes(scope, [&](DexClass* cls) {
    check_type(cls->get_type()); // Just for counting purposes.
    check_type(cls->get_super_class());
    if (cls->get_interfaces() != nullptr) {
      for (auto* intf : *cls->get_interfaces()) {
        check_type(intf);
      }
    }
    for (auto* field : cls->get_all_fields()) {
      always_assert_log(check_type(field->get_type()), "%s", SHOW(field));
    }
  });
  walk::parallel::methods(scope, [&](DexMethod* m) {
    auto* code = m->get_code();
    if (code == nullptr) {
      return;
    }
    cfg::ScopedCFG cfg{code};
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      std::vector<const DexType*> types;
      insn->gather_types(types);
      for (const auto* type : types) {
        always_assert_log(check_type(type), "%s", SHOW(insn));
      }
    }
  });
  return checked_types.size();
}

} // namespace

void InstrumentPass::eval_pass(DexStoresVector& stores,
                               ConfigFiles& conf,
                               PassManager& mgr) {
  if (!conf.get_json_config().get("instrument_pass_enabled", false) &&
      !mgr.get_redex_options().instrument_pass_enabled) {
    maybe_unset_dynamic_analysis(stores, m_options.analysis_class_name,
                                 m_options.analysis_package_prefix);
    return;
  }

  if (m_options.analysis_package_prefix) {
    m_integrity_types =
        check_integrity(stores, *m_options.analysis_package_prefix);
  }

  // Note: Could do the inverse and protect necessary members here.

  set_no_opt_flag_on_analysis_methods(true, m_options.analysis_class_name,
                                      m_options.analysis_method_names);

  // Make a small room for additional method refs during InterDex. We may
  // introduce a new field. We introduce a type reference to the analysis class
  // in each dex. We will introduce more method refs from analysis methods.

  size_t max_analysis_methods;
  if (m_options.instrumentation_strategy == SIMPLE_METHOD_TRACING) {
    max_analysis_methods = m_options.num_shards;
  } else if (m_options.instrumentation_strategy == BASIC_BLOCK_TRACING ||
             m_options.instrumentation_strategy == BASIC_BLOCK_HIT_COUNT) {
    // TODO: Derive this from the source.
    // Our current DynamicAnalysis has 2 * 7 onMethodExits and 1 onMethodBegin.
    max_analysis_methods = 15;
  } else {
    max_analysis_methods = 1;
  }

  m_reserved_refs_handle =
      mgr.reserve_refs(name(),
                       ReserveRefsInfo(/* frefs */ 1,
                                       /* trefs */ 1,
                                       /* mrefs */ max_analysis_methods));
}

// Check for inclusion in allow/block lists of methods/classes. It supports:
// - "Lcom/fb/foo/" matches "^Lcom/fb/foo/*" or "^Lcom/facebook/debug;"
// - "Lcom/fb/foo;.bar()V" matches exact full method names.
// - "Lcom/fb/foo;.bar*" matches method name prefixes.
bool InstrumentPass::is_included(const DexMethod* method,
                                 const UnorderedSet<std::string>& set) {
  if (set.empty()) {
    return false;
  }

  // Try to check for method by its full name.
  std::string full_method_name = method->get_deobfuscated_name_or_empty_copy();
  if (set.count(full_method_name) != 0u) {
    return true;
  }

  // Prefix method name matching.
  for (const auto& pattern : UnorderedIterable(set)) {
    if (pattern.back() == '*') {
      if (full_method_name.find(pattern.substr(0, pattern.length() - 1)) !=
          std::string::npos) {
        return true;
      }
    }
  }

  return match_class_name(show_deobfuscated(method->get_class()), set);
}

std::pair<UnorderedMap<int /*shard_num*/, DexMethod*>,
          UnorderedSet<std::string>>
InstrumentPass::generate_sharded_analysis_methods(
    DexClass* cls,
    const std::string& template_method_full_name,
    const UnorderedMap<int /*shard_num*/, DexFieldRef*>& array_fields,
    const size_t num_shards) {
  DexMethod* template_method =
      cls->find_method_from_simple_deobfuscated_name(template_method_full_name);

  if (template_method == nullptr) {
    std::cerr << "[InstrumentPass] error: failed to find template method \'"
              << template_method_full_name << "\' in " << show(*cls) << '\n';
    for (const auto& m : cls->get_dmethods()) {
      std::cerr << " " << show(m) << '\n';
    }
    exit(1);
  }

  const auto template_method_name = template_method->get_name()->str();

  UnorderedMap<int /*shard_num*/, DexMethod*> new_analysis_methods;
  UnorderedSet<std::string> method_names;

  // Even if one shard, we create a new method from the template method.
  for (size_t i = 1; i <= num_shards; ++i) {
    const auto new_name = template_method_name + std::to_string(i);
    std::string deobfuscated_name =
        template_method->get_deobfuscated_name_or_empty_copy();
    boost::replace_first(deobfuscated_name, template_method_name, new_name);

    DexMethod* new_method =
        DexMethod::make_method_from(template_method,
                                    template_method->get_class(),
                                    DexString::make_string(new_name));
    new_method->set_deobfuscated_name(str_copy(deobfuscated_name));
    cls->add_method(new_method);

    // Patch the array name in newly created method.
    bool patched = false;
    walk::matching_opcodes_in_block(
        *new_method,
        std::make_tuple(m::sget_object_()),
        [&](DexMethod* /*method*/,
            cfg::Block*,
            const std::vector<IRInstruction*>& insts) {
          DexField* field = dynamic_cast<DexField*>(insts[0]->get_field());
          if (field->get_simple_deobfuscated_name() ==
              InstrumentPass::STATS_FIELD_NAME) {
            // Set the new field created from patch_sharded_arrays.
            insts[0]->set_field(array_fields.at(static_cast<int>(i)));
            patched = true;
            return;
          }
        });

    always_assert_log(patched, "Failed to patch sMethodStats1 in %s\n",
                      SHOW(new_method));
    method_names.insert(new_name);
    new_method->get_code()->build_cfg();
    new_analysis_methods[static_cast<int>(i)] = new_method;
    TRACE(INSTRUMENT, 2, "Created %s with %s", SHOW(new_method),
          SHOW(array_fields.at(i)));
  }

  // Remove template method.
  cls->remove_method(template_method);
  return std::make_pair(new_analysis_methods, method_names);
}

UnorderedMap<int /*shard_num*/, DexFieldRef*>
InstrumentPass::patch_sharded_arrays(
    DexClass* cls,
    const size_t num_shards,
    const std::map<int /*shard_num*/, std::string>& suggested_names) {
  // Insert additional sMethodStatsN into the clinit
  //
  // private static short[] sMethodStats1 = new short[0];
  // private static short[] sMethodStats2 = new short[0]; <= Add
  // ...
  // private static short[] sMethodStatsN = new short[0]; <= Add
  //
  //        OPCODE: CONST v0, 0
  //        OPCODE: NEW_ARRAY v0, [S
  //        OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT v1
  //        OPCODE: SPUT_OBJECT v1, Lcom/foo/Bar;.sMethodStats1:[S
  // Add => OPCODE: NEW_ARRAY v0, [S
  // Add => OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT v1
  // Add => OPCODE: SPUT_OBJECT v1, Lcom/foo/Bar;.sMethodStats2:[S
  always_assert(num_shards > 0);
  DexMethod* clinit = cls->get_clinit();
  IRCode* code = clinit->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  UnorderedMap<int /*shard_num*/, DexFieldRef*> fields;
  bool patched = false;
  walk::matching_opcodes_in_block(
      *clinit,
      std::make_tuple(m::new_array_(), m::move_result_pseudo_object_(),
                      m::sput_object_()),
      [&](DexMethod* /*method*/,
          cfg::Block*,
          const std::vector<IRInstruction*>& insts) {
        DexField* template_field =
            dynamic_cast<DexField*>(insts[2]->get_field());
        if (template_field->get_simple_deobfuscated_name() !=
            InstrumentPass::STATS_FIELD_NAME) {
          return;
        }

        // Create new sMethodStatsN fields. Even if num_shard is 1, we create
        // new field from the template field. Regarding obfuscation, the rename
        // module runs after InstrumentPass. So, we just need to assign
        // human-readable names here.
        for (size_t i = 1; i <= num_shards; i++) {
          const auto new_name =
              suggested_names.count(static_cast<int>(i)) != 0u
                  ? suggested_names.at(static_cast<int>(i))
                  : InstrumentPass::STATS_FIELD_NAME + std::to_string(i);
          auto deobfuscated_name = template_field->get_deobfuscated_name();
          boost::replace_first(deobfuscated_name,
                               InstrumentPass::STATS_FIELD_NAME, new_name);

          DexField* new_field = dynamic_cast<DexField*>(
              DexField::make_field(template_field->get_class(),
                                   DexString::make_string(new_name),
                                   template_field->get_type()));
          new_field->set_deobfuscated_name(deobfuscated_name);
          new_field->make_concrete(
              template_field->get_access(),
              template_field->get_static_value() == nullptr
                  ? nullptr
                  : template_field->get_static_value()->clone());
          fields[static_cast<int>(i)] = new_field;
          TRACE(INSTRUMENT, 2, "Created array: %s", SHOW(new_field));
          cls->add_field(new_field);
        }

        // Clone the matched three instructions, but with new field names.
        for (size_t i = num_shards; i >= 1; --i) {
          auto pos_it = cfg.find_insn(insts[2]);
          auto new_insts = {
              (new IRInstruction(OPCODE_NEW_ARRAY))
                  ->set_type(insts[0]->get_type())
                  ->set_src(0, insts[0]->src(0)),
              (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                  ->set_dest(insts[1]->dest()),
              (new IRInstruction(OPCODE_SPUT_OBJECT))
                  ->set_src(0, insts[2]->src(0))
                  ->set_field(fields.at(static_cast<int>(i)))};
          if (i == 1) {
            cfg.replace_insns(pos_it, new_insts);
          } else {
            cfg.insert_after(pos_it, new_insts);
          }
        }
        patched = true;
        cls->remove_field(template_field);
      });

  always_assert_log(patched, "Failed to insert sMethodStatsN:\n%s",
                    SHOW(clinit->get_code()->cfg()));

  // static short[][] sMethodStatsArray = new short[][] {
  //   sMethodStats1, <== Add
  //   sMethodStats2, <== Add
  //   ...
  // }
  //
  //        OPCODE: NEW_ARRAY v0, [[S  <== Patch
  //        OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT vX
  //        OPCODE: SPUT_OBJECT vX, Lcom/foo;.sMethodStatsArray:[[S
  // Add => OPCODE: SGET_OBJECT Lcom/foo;.sMethodStats1:[S
  // Add => OPCODE: IOPCODE_MOVE_RESULT_PSEUDO_OBJECT vY
  // Add => OPCODE: CONST vN, index
  // Add => OPCODE: APUT_OBJECT vY, vX, vN
  //        ...
  // Add => OPCODE: APUT_OBJECT vY, vX, vN
  auto* field =
      cls->find_field_from_simple_deobfuscated_name("sMethodStatsArray");
  always_assert(field != nullptr);
  InstrumentPass::patch_array_size(cls, field->get_name()->str(),
                                   static_cast<int>(num_shards));
  patched = false;
  walk::matching_opcodes_in_block(
      *clinit,
      std::make_tuple(m::new_array_(), m::move_result_pseudo_object_(),
                      m::sput_object_()),
      [&](DexMethod* /*method*/,
          cfg::Block*,
          const std::vector<IRInstruction*>& insts) {
        DexField* inst_field = dynamic_cast<DexField*>(insts[2]->get_field());
        if (inst_field->get_simple_deobfuscated_name() != "sMethodStatsArray") {
          return;
        }

        const reg_t vX = insts[1]->dest();
        const reg_t vY = cfg.allocate_temp();
        const reg_t vN = cfg.allocate_temp();
        for (size_t i = num_shards; i >= 1; --i) {
          auto pos_it = cfg.find_insn(insts[2]);
          cfg.insert_after(
              pos_it,
              {(new IRInstruction(OPCODE_SGET_OBJECT))
                   ->set_field(fields.at(static_cast<int>(i))),
               (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                   ->set_dest(vY),
               (new IRInstruction(OPCODE_CONST))
                   ->set_literal(static_cast<int64_t>(i - 1))
                   ->set_dest(vN),
               (new IRInstruction(OPCODE_APUT_OBJECT))
                   ->set_srcs_size(3)
                   ->set_src(0, vY)
                   ->set_src(1, vX)
                   ->set_src(2, vN)});
        }
        patched = true;
      });

  always_assert_log(patched,
                    "Failed to insert sMethodStatsN to sMethodStatsArray:\n%s",
                    SHOW(clinit->get_code()->cfg()));

  return fields;
}

void InstrumentPass::run_pass(DexStoresVector& stores,
                              ConfigFiles& cfg,
                              PassManager& pm) {
  if (m_reserved_refs_handle) {
    pm.release_reserved_refs(*m_reserved_refs_handle);
  }

  // TODO(fengliu): We may need change this but leave it here for local test.
  if (m_options.instrumentation_strategy == METHOD_REPLACEMENT) {
    bool exclude_primary_dex = !pm.get_redex_options().is_art_build;
    auto num_wrapped_invocations =
        method_reference::wrap_instance_call_with_static(
            stores, m_options.methods_replacement, exclude_primary_dex);
    pm.set_metric("wrapped_invocations", num_wrapped_invocations);
    m_reserved_refs_handle = std::nullopt;
    return;
  }

  count_source_block_chain_length(stores, pm);

  if (!cfg.get_json_config().get("instrument_pass_enabled", false) &&
      !pm.get_redex_options().instrument_pass_enabled) {
    TRACE(INSTRUMENT, 1,
          "--enable-instrument-pass (or \"instrument_pass_enabled\": true) is "
          "not specified.");
    pm.set_metric("skipped_pass", 1);
    return;
  }

  always_assert(m_reserved_refs_handle);
  m_reserved_refs_handle = std::nullopt;

  // Append block listed classes from the file, if exists.
  if (!m_options.blocklist_file_name.empty()) {
    insert_unordered_iterable(
        m_options.blocklist,
        load_blocklist_file(m_options.blocklist_file_name));
  }
  pm.set_metric("blocklist_size", m_options.blocklist.size());

  if (m_options.analysis_class_name.empty()) {
    std::cerr << "[InstrumentPass] error: empty analysis class name.\n";
    exit(1);
  }

  // Get the analysis class.
  DexType* analysis_class_type =
      g_redex->get_type(DexString::get_string(m_options.analysis_class_name));
  if (analysis_class_type == nullptr) {
    std::cerr << "[InstrumentPass] error: cannot find analysis class: "
              << m_options.analysis_class_name << '\n';
    exit(1);
  }

  DexClass* analysis_cls = g_redex->type_class(analysis_class_type);
  always_assert(analysis_cls != nullptr);

  // Check whether the analysis class is in the primary dex. We use a heuristic
  // that looks the last 12 characters of the location of the given dex.
  // Skip this check if InterDexPass normal_primary_dex is enabled.
  bool normal_primary_dex = true; // Default value
  Json::Value interdex_pass_config;
  cfg.get_json_config().get("InterDexPass", Json::nullValue,
                            interdex_pass_config);
  if (!interdex_pass_config.empty()) {
    JsonWrapper interdex_jw(interdex_pass_config);
    interdex_jw.get("normal_primary_dex", true, normal_primary_dex);
  }

  if (!normal_primary_dex) {
    auto dex_loc = analysis_cls->get_location()->get_file_name();
    if (dex_loc.size() < 12 /* strlen("/classes.dex") == 12 */ ||
        dex_loc.substr(dex_loc.size() - 12) != "/classes.dex") {
      std::cerr
          << "[InstrumentPass] Analysis class must be in the primary dex. "
             "It was in "
          << dex_loc << '\n';
      exit(1);
    }
  }

  // Just do the very minimal common work here: load the analysis class.
  // Each instrumentation strategy worker function will do its own job.
  TRACE(INSTRUMENT,
        3,
        "Loaded analysis class: %s (%s)",
        SHOW(m_options.analysis_class_name),
        SHOW(analysis_cls->get_location()->get_file_name()));

  if (m_options.instrumentation_strategy == SIMPLE_METHOD_TRACING) {
    do_simple_method_tracing(analysis_cls, stores, cfg, pm, m_options);
  } else if (m_options.instrumentation_strategy == BASIC_BLOCK_TRACING ||
             m_options.instrumentation_strategy == BASIC_BLOCK_HIT_COUNT) {
    BlockInstrumentHelper::do_basic_block_tracing(analysis_cls, stores, cfg, pm,
                                                  m_options);
  } else {
    std::cerr << "[InstrumentPass] Unknown instrumentation strategy.\n";
    exit(1);
  }

  // Be nice and immediately destruct some painful block overhead.

  auto scope = build_class_scope(stores);

  // We're done and have inserted our instrumentation. Allow further cleanup.
  g_redex->instrument_mode = false;

  // Allow optimizations in analysis methods while the Shrinker runs
  set_no_opt_flag_on_analysis_methods(false, m_options.analysis_class_name,
                                      m_options.analysis_method_names);

  // Simple config.
  shrinker::ShrinkerConfig shrinker_config;
  shrinker_config.run_const_prop = true;
  shrinker_config.run_local_dce = true;
  shrinker_config.compute_pure_methods = false;
  if (m_options.apply_CSE_CopyProp) {
    shrinker_config.run_cse = true;
    shrinker_config.run_copy_prop = true;
  }

  UnorderedSet<const DexField*> finalish_fields;
  if (m_options.apply_CSE_CopyProp) {
    auto* field =
        analysis_cls->find_field_from_simple_deobfuscated_name("sHitStats");
    finalish_fields.insert(field);
    field->rstate.unset_root();
    always_assert(field->rstate.can_delete() && field->rstate.can_rename());

    field =
        analysis_cls->find_field_from_simple_deobfuscated_name("sIsEnabled");
    finalish_fields.insert(field);
    field->rstate.unset_root();
    always_assert(field->rstate.can_delete() && field->rstate.can_rename());

    field = analysis_cls->find_field_from_simple_deobfuscated_name(
        "sNumStaticallyHitsInstrumented");
    finalish_fields.insert(field);
    field->rstate.unset_root();
    always_assert(field->rstate.can_delete() && field->rstate.can_rename());

    field = analysis_cls->find_field_from_simple_deobfuscated_name(
        "sNumStaticallyInstrumented");
    finalish_fields.insert(field);
    field->rstate.unset_root();
    always_assert(field->rstate.can_delete() && field->rstate.can_rename());
  }

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, cfg.create_init_class_insns());

  int min_sdk = pm.get_redex_options().min_sdk;
  shrinker::Shrinker shrinker(stores, scope, init_classes_with_side_effects,
                              cfg, shrinker_config, min_sdk, {}, {},
                              finalish_fields);

  {
    Timer cleanup{"Parallel Cleanup"};

    walk::parallel::methods(scope, [&](auto* m) {
      if (m->get_code() == nullptr) {
        return;
      }

      shrinker.shrink_method(m);
    });
  }

  // Probably shouldn't need to do this, as the outliner shouldn't run after
  // InstrumentPass, but let's be defensive, in case pass order changes in
  // future.
  set_no_opt_flag_on_analysis_methods(true, m_options.analysis_class_name,
                                      m_options.analysis_method_names);

  if (m_integrity_types) {
    pm.set_metric("integrity_checked_types", *m_integrity_types);
  }
}

static InstrumentPass s_pass;
