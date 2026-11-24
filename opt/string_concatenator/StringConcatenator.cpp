/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringConcatenator.h"

#include <map>
#include <mutex>
#include <utility>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

/* This pass finds <clinit> methods with lots of string concatenations of
 * compile-time-known strings and concatenates those strings. This way, at
 * runtime, we only need to load the string.
 *
 * Here's an example <clinit> method that this method will optimize:
 *
 *   public static final String PREFIX = "foo";
 *   public static final String CONCATENATED = PREFIX + "bar";
 *
 * The output code should be equivalent to:
 *
 *   public static final PREFIX = "foo";
 *   public static final CONCATENATED = "foobar";
 *
 * The final values of the string fields are stored in the Dex file as
 * DexEncodedValues
 *
 * This should be done after FinalInlineV2 pass to make sure input strings are
 * resolved.
 *
 * TODO: someday, this should probably be subsumed by a more general purpose
 * optimization, possibly StringSimplificationPass.
 */

namespace {
using StrBuilderId = uint32_t;

class RegMap {
  using RegStrMap = UnorderedMap<reg_t, std::string>;
  using RegBuilderMap = UnorderedMap<reg_t, StrBuilderId>;
  RegStrMap m_strings;
  RegBuilderMap m_builders;

 public:
  void put_string(reg_t r, const std::string& s) {
    m_builders.erase(r);
    m_strings[r] = s;
  }

  void put_builder(reg_t r, StrBuilderId b) {
    m_strings.erase(r);
    m_builders[r] = b;
  }

  std::optional<std::string> find_string(reg_t r) {
    const auto& search = m_strings.find(r);
    return (search == m_strings.end())
               ? std::nullopt
               : std::optional<std::string>(search->second);
  }

  std::optional<StrBuilderId> find_builder(reg_t r) {
    const auto& search = m_builders.find(r);
    return (search == m_builders.end())
               ? std::nullopt
               : std::optional<StrBuilderId>(search->second);
  }
};

struct Stats {
  uint32_t insns_removed{0};
  uint32_t clinits_emptied{0};
  uint32_t string_fields_resolved{0};

  Stats& operator+=(const Stats& that) {
    insns_removed += that.insns_removed;
    clinits_emptied += that.clinits_emptied;
    string_fields_resolved += that.string_fields_resolved;
    return *this;
  }

  void report(PassManager& mgr) {
    mgr.set_metric("insns_removed", insns_removed);
    mgr.set_metric("clinits_emptied", clinits_emptied);
    mgr.set_metric("string_fields_resolved", string_fields_resolved);
    TRACE(STR_CAT, 1,
          "insns removed: %u, methods rewritten %u, string fields resolved %u",
          insns_removed, clinits_emptied, string_fields_resolved);
  }
};

struct ConcatenatorConfig {
  const DexType* string_builder;
  const DexType* string;
  const DexMethodRef* init_void;
  const DexMethodRef* init_string;
  const DexMethodRef* append;
  const DexMethodRef* to_string;

  ConcatenatorConfig() {
    string_builder = DexType::get_type("Ljava/lang/StringBuilder;");
    always_assert(string_builder != nullptr);
    string = DexType::get_type("Ljava/lang/String;");
    always_assert(string != nullptr);
    init_void = DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:()V");
    always_assert(init_void != nullptr);
    init_string = DexMethod::get_method(
        "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V");
    always_assert(init_string != nullptr);
    append = method::java_lang_StringBuilder_append_String();
    to_string = method::java_lang_StringBuilder_toString();
  }
};

struct LockedMethodSet {
  using Map = std::set<DexMethod*, dexmethods_comparator>;
  std::mutex mutex;
  Map map;

  void insert(DexMethod* method) {
    std::lock_guard<std::mutex> lock(mutex);
    map.insert(method);
  }

  Map& get() { return map; }
};

class Concatenator {

  using BuilderStrMap = UnorderedMap<StrBuilderId, std::string>;
  using FieldMap = std::map<DexFieldRef*, std::string, dexfields_comparator>;

  const ConcatenatorConfig& m_config;

  /* match this (and similar) patterns:
   *
   *  new-instance v1, Ljava/lang/StringBuilder;
   *  const-string v0, "fb"
   *  invoke-direct {v1, v0}, Ljava/lang/StringBuilder;.<init>
   *  const-string v0, "://"
   *  invoke-virtual {v1, v0}, Ljava/lang/StringBuilder;.append
   *  move-result-object v0
   *  invoke-virtual {v0}, Ljava/lang/StringBuilder;.toString
   *  move-result-object v0
   *  sput-object v0, LFoo;.PREFIX:Ljava/lang/String;
   *
   *  new-instance v1, Ljava/lang/StringBuilder;
   *  invoke-direct {v1}, Ljava/lang/StringBuilder;.<init>:()V
   *  sget-object v0, LFoo;.PREFIX:Ljava/lang/String;
   *  invoke-virtual {v1, v0}, Ljava/lang/StringBuilder;.append
   *  move-result-object v1
   *  const-string v0, "bar"
   *  move-result-object v0
   *  invoke-virtual {v0}, Ljava/lang/StringBuilder;.toString
   *  move-result-object v0
   *  sput-object v0, LFoo;.CONCATENATED:Ljava/lang/String;
   *
   * And fill `fields_ptr` with the final values of these string fields
   */
  bool analyze(cfg::Block* block,
               const DexType* this_type,
               FieldMap* fields_ptr) {
    RegMap registers;
    BuilderStrMap builder_str;
    FieldMap& fields = *fields_ptr;
    always_assert_log(fields.empty(), "should start with fresh field map");

    bool has_string_builder = false;
    bool has_to_string = false;
    for (auto& mie : ir_list::InstructionIterable(block)) {
      auto* insn = mie.insn;
      auto op = insn->opcode();

      const auto& move = [&registers](reg_t dest, reg_t source) {
        const auto& str_search = registers.find_string(source);
        const auto& builder_search = registers.find_builder(source);
        if (str_search != std::nullopt) {
          always_assert(builder_search == std::nullopt);
          registers.put_string(dest, *str_search);
          return true;
        } else if (builder_search != std::nullopt) {
          always_assert(str_search == std::nullopt);
          registers.put_builder(dest, *builder_search);
          return true;
        }
        return false;
      };

      // The bottom of this switch statement has a `return false`. This way, any
      // instructions that we don't expect force us to safely abort the
      // analysis. A successful analysis of an instruction should immediately
      // be followed by a `continue` statement.
      //
      // TODO: allow static initializers that have other unrelated code
      switch (op) {
      case OPCODE_MOVE_OBJECT: {
        bool success = move(insn->dest(), insn->src(0));
        if (success) {
          continue;
        }
        break;
      }
      case OPCODE_MOVE_RESULT_OBJECT:
      case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT: {
        bool success = move(insn->dest(), RESULT_REGISTER);
        if (success) {
          continue;
        }
        break;
      }
      case OPCODE_CONST_STRING:
        registers.put_string(RESULT_REGISTER, insn->get_string()->str_copy());
        continue;
      case OPCODE_NEW_INSTANCE:
        if (insn->get_type() == m_config.string_builder) {
          StrBuilderId new_id = static_cast<StrBuilderId>(builder_str.size());
          builder_str[new_id] = "";
          registers.put_builder(RESULT_REGISTER, new_id);

          has_string_builder = true;
          continue;
        }
        break;
      case OPCODE_SGET_OBJECT: {
        const auto& field_search = fields.find(insn->get_field());
        if (field_search != fields.end()) {
          registers.put_string(RESULT_REGISTER, field_search->second);
          continue;
        }
        break;
      }
      case OPCODE_SPUT_OBJECT: {
        const auto& field_ref = insn->get_field();
        if (field_ref->get_type() == m_config.string &&
            field_ref->get_class() == this_type) {
          const auto& field_def = resolve_field(field_ref, FieldSearch::Static);
          if (field_def != nullptr && is_final(field_def)) {
            const auto& str_search = registers.find_string(insn->src(0));
            if (str_search != std::nullopt) {
              fields[field_ref] = *str_search;
              continue;
            }
          }
        }
        break;
      }
      case OPCODE_INVOKE_VIRTUAL:
      case OPCODE_INVOKE_DIRECT: {
        auto* method = insn->get_method();
        if (method == m_config.init_void) {
          continue;
        } else if (method == m_config.init_string) {
          const auto& str_search = registers.find_string(insn->src(1));
          if (str_search != std::nullopt) {
            StrBuilderId new_id = static_cast<StrBuilderId>(builder_str.size());
            builder_str[new_id] = *str_search;
            registers.put_builder(insn->src(0), new_id);
            continue;
          }
        } else if (method == m_config.append) {
          auto builder_search = registers.find_builder(insn->src(0));
          const auto& string_search = registers.find_string(insn->src(1));
          if (builder_search != std::nullopt && string_search != std::nullopt) {
            builder_str[*builder_search] += *string_search;
            registers.put_builder(RESULT_REGISTER, *builder_search);
            continue;
          }
        } else if (method == m_config.to_string) {
          const auto& builder_search = registers.find_builder(insn->src(0));
          if (builder_search != std::nullopt) {
            registers.put_string(RESULT_REGISTER, builder_str[*builder_search]);

            has_to_string = true;
            continue;
          }
        }
        break;
      }
      case OPCODE_RETURN_VOID:
        continue;
      default:
        break;
      }
      // reject any method with any other instruction
      return false;
    }
    // filter out methods that had a few instructions we analyzed but didn't
    // actually have a field loaded by a concatenated string
    return has_string_builder && has_to_string && !fields.empty();
  }

  /* Encode these string fields as `DexEncodedValue`s
   */
  static void encode(const FieldMap& fields) {
    for (const auto& entry : fields) {
      DexField* field = resolve_field(entry.first, FieldSearch::Static);
      always_assert(field != nullptr);
      const std::string& str = entry.second;
      field->set_value(std::unique_ptr<DexEncodedValue>(
          new DexEncodedValueString(DexString::make_string(str))));
    }
  }

  /* Clear out the code inside and remove the method from the class.
   */
  static void clear_method(cfg::ControlFlowGraph* cfg, cfg::Block* b) {
    cfg->set_registers_size(0);
    b->push_front(new IRInstruction(OPCODE_RETURN_VOID));
  }

 public:
  explicit Concatenator(const ConcatenatorConfig& config) : m_config(config) {}

  Stats run(cfg::ControlFlowGraph* cfg,
            DexMethod* method,
            LockedMethodSet* methods_to_remove) {
    Stats stats;
    const auto& blocks = cfg->blocks();
    if (blocks.size() != 1) {
      // We're interested in the massive initialization functions for classes
      // with compile-time-known strings. These methods don't usually have more
      // than one block.
      return stats;
    }
    cfg::Block* block = blocks[0];

    FieldMap fields;

    bool can_opt = analyze(block, method->get_class(), &fields);

    if (!can_opt) {
      return stats;
    }

    const auto before_size = block->num_opcodes();
    encode(fields);
    clear_method(cfg, block);
    methods_to_remove->insert(method);
    const auto after_size = block->num_opcodes();

    stats.insns_removed += before_size - after_size;
    stats.clinits_emptied += 1;
    stats.string_fields_resolved += fields.size();

    TRACE(STR_CAT, 2, "optimize %s from %u to %u", SHOW(method), before_size,
          block->num_opcodes());
    return stats;
  }
};

} // namespace

void StringConcatenatorPass::run_pass(DexStoresVector& stores,
                                      ConfigFiles& /* unused */,
                                      PassManager& mgr) {
  constexpr bool kDebug = false;
  const auto& scope = build_class_scope(stores);
  const ConcatenatorConfig config{};
  LockedMethodSet methods_to_remove;
  Stats stats = walk::parallel::methods<Stats>(
      scope,
      [&config, &methods_to_remove](DexMethod* m) {
        auto* code = m->get_code();
        if (!method::is_optimizable(m)) {
          return Stats{};
        }
        if (!method::is_clinit(m)) {
          // TODO maybe later? If we expand to non-clinit methods, `analyze()`
          // will have to consider StringBuilders passed in as arguments.
          return Stats{};
        }

        always_assert(code->cfg_built());
        // This legacy pass cannot deal with goto-chains. Force-linearize the
        // cfg.
        code->clear_cfg();
        code->build_cfg();
        Stats method_stats =
            Concatenator{config}.run(&code->cfg(), m, &methods_to_remove);

        return method_stats;
      },
      kDebug ? 1 : redex_parallel::default_num_threads());

  for (DexMethod* method : methods_to_remove.get()) {
    // We can delete the method without finding callsites because these are all
    // <clinit> methods, which don't have explicit callsites
    auto* cls = type_class(method->get_class());
    always_assert_log(cls != nullptr, "%s comes from an unknown class",
                      SHOW(method));
    cls->remove_method(method);
  }

  stats.report(mgr);
}

static StringConcatenatorPass s_pass;
