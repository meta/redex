/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "FieldOpTracker.h"

#include <optional>

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "Lazy.h"
#include "ReachingDefinitions.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "TypeInference.h"
#include "Walkers.h"

namespace {

// How a value can escape
struct Escapes {
  // Fields in which the value was stored
  UnorderedSet<DexField*> put_value_fields;
  // Constructors to which the value was passed as the first argument
  UnorderedSet<DexMethod*> invoked_ctors;
  // Value may have a (relevant) lifetime and escaped otherwise, or an object /
  // array in which a field / array element with a (relevant) lifetime type was
  // written to with a non-zero value.
  bool other{false};
};

// Escape information for instructions define a value
using InstructionEscapes = UnorderedMap<IRInstruction*, Escapes>;

bool operator==(const Escapes& a, const Escapes& b) {
  return a.put_value_fields == b.put_value_fields &&
         a.invoked_ctors == b.invoked_ctors && a.other == b.other;
}

// InstructionEscapes (an UnorderedMap) is compared with the wrapper's built-in
// order-independent operator==, which matches keys and compares per-key
// `Escapes` values via the operator== above.

class WritesAnalyzer {
 private:
  const field_op_tracker::TypeLifetimes* m_type_lifetimes;
  const field_op_tracker::FieldStatsMap& m_field_stats;
  mutable InsertOnlyConcurrentMap<const DexMethod*, InstructionEscapes>
      m_method_insn_escapes;

  bool has_lifetime(const DexType* t) const {
    return ((m_type_lifetimes == nullptr) && type::is_object(t)) ||
           m_type_lifetimes->has_lifetime(t);
  }

  const InstructionEscapes& get_insn_escapes(const DexMethod* method) const {
    return *m_method_insn_escapes
                .get_or_create_and_assert_equal(
                    method, [&](auto*) { return compute_insn_escapes(method); })
                .first;
  }

  // Compute information about which values (represented by
  // instructions that create them) escape by being stored in fields, array
  // elements, passed as the first argument to a constructor, or escape
  // otherwise. We also record writing a non-zero value to a field / array
  // element with a (relevant) lifetime type as an "other" escape.
  InstructionEscapes compute_insn_escapes(const DexMethod* method) const {
    const auto& cfg = method->get_code()->cfg();
    Lazy<type_inference::TypeInference> type_inference([&cfg, method] {
      auto res = std::make_unique<type_inference::TypeInference>(cfg);
      res->run(method);
      return res;
    });

    reaching_defs::MoveAwareFixpointIterator fp_iter(cfg);
    fp_iter.run({});
    InstructionEscapes insn_escapes;
    auto escape = [&insn_escapes](
                      const sparta::PatriciaTreeSet<IRInstruction*>& defs,
                      DexField* put_value_field, DexMethod* invoked_ctor,
                      bool other) {
      always_assert_log(
          !!put_value_field + !!invoked_ctor + other == 1,
          "One and only one of put_value_field, invoked_ctor, other is set.");
      for (auto* def : defs) {
        auto& escapes = insn_escapes[def];
        if (invoked_ctor != nullptr) {
          escapes.invoked_ctors.insert(invoked_ctor);
        } else if (put_value_field != nullptr) {
          escapes.put_value_fields.insert(put_value_field);
        } else {
          escapes.other = true;
        }
      }
    };
    for (auto* block : cfg.blocks()) {
      auto env = fp_iter.get_entry_state_at(block);
      if (env.is_bottom()) {
        continue;
      }
      auto get_non_zero_defs = [&env](reg_t reg) {
        const auto& src_defs = env.get(reg);
        always_assert(!src_defs.is_bottom());
        always_assert(!src_defs.is_top());
        auto copy = src_defs.elements();
        for (auto* def : src_defs.elements()) {
          if ((def->opcode() == OPCODE_CONST ||
               def->opcode() == OPCODE_CONST_WIDE) &&
              def->get_literal() == 0) {
            copy.remove(def);
          }
        }
        return copy;
      };
      auto insns = InstructionIterable(block);
      for (auto it = insns.begin(); it != insns.end();
           fp_iter.analyze_instruction(it++->insn, &env)) {
        auto* insn = it->insn;
        // Helper function to check if the formal type and the inferred type
        // have a (relevant) lifetime.
        auto has_lifetime =
            [this, &type_inference, insn](
                reg_t reg, const std::optional<const DexType*>& formal_type) {
              if (formal_type && !this->has_lifetime(*formal_type)) {
                // If the formal type has no lifetime, then we can stop here.
                // More precise type information of the value actually flowing
                // in, i.e. a subtype, cannot change this.
                return false;
              }
              const auto& type_env =
                  type_inference->get_type_environments().at(insn);
              const auto& inferred_type = type_env.get_dex_type(reg);
              return !inferred_type || this->has_lifetime(*inferred_type);
            };
        auto op = insn->opcode();
        if (opcode::is_an_iput(op) || opcode::is_an_sput(op)) {
          auto non_zero_value_defs = get_non_zero_defs(insn->src(0));
          if (non_zero_value_defs.empty()) {
            continue;
          }
          DexField* field;
          bool other = (field = resolve_field(insn->get_field())) == nullptr;
          escape(non_zero_value_defs, field, nullptr, other);
          if (op != OPCODE_IPUT_OBJECT ||
              !has_lifetime(insn->src(0), insn->get_field()->get_type())) {
            continue;
          }
          if (opcode::is_an_iput(op)) {
            // All (non-zero) definitions whose fields are written to are
            // considered to have escaped to ensure that an object that may be
            // relevant for lifetime purposes is not discarded.
            auto non_zero_obj_defs = get_non_zero_defs(insn->src(1));
            escape(non_zero_obj_defs, nullptr, nullptr, true);
          }
          continue;
        }
        if (op == OPCODE_APUT_OBJECT) {
          auto non_zero_value_defs = get_non_zero_defs(insn->src(0));
          if (non_zero_value_defs.empty()) {
            continue;
          }
          const auto& type_env =
              type_inference->get_type_environments().at(insn);
          const auto& array_type = type_env.get_dex_type(insn->src(1));
          std::optional<const DexType*> component_type;
          if (array_type && type::is_array(*array_type)) {
            component_type = type::make_array_component_type(*array_type);
          }
          if (!has_lifetime(insn->src(0), component_type)) {
            continue;
          }
          escape(non_zero_value_defs, nullptr, nullptr, true);
          // All (non-zero) definitions whose fields are written to are
          // considered to have escaped to ensure that an object that may be
          // relevant for lifetime purposes is not discarded.
          auto non_zero_obj_defs = get_non_zero_defs(insn->src(1));
          escape(non_zero_obj_defs, nullptr, nullptr, true);
          continue;
        }
        if (insn->has_method()) {
          const auto* type_list = insn->get_method()->get_proto()->get_args();
          bool is_instance = op != OPCODE_INVOKE_STATIC;
          for (size_t src_idx = 0; src_idx < insn->srcs_size(); src_idx++) {
            auto non_zero_value_defs = get_non_zero_defs(insn->src(src_idx));
            if (non_zero_value_defs.empty()) {
              continue;
            }
            const DexType* arg_type;
            if (src_idx == 0 && is_instance) {
              arg_type = insn->get_method()->get_class();
            } else {
              arg_type = type_list->at(src_idx -
                                       static_cast<unsigned long>(is_instance));
            }
            if (!has_lifetime(insn->src(src_idx), arg_type)) {
              continue;
            }
            DexMethod* invoked_ctor{nullptr};
            bool other =
                src_idx != 0 || op != OPCODE_INVOKE_DIRECT ||
                !method::is_init(insn->get_method()) ||
                ((invoked_ctor = resolve_method_deprecated(
                      insn->get_method(), MethodSearch::Direct)) == nullptr);
            escape(non_zero_value_defs, nullptr, invoked_ctor, other);
          }
          continue;
        }
        if (op == OPCODE_RETURN_OBJECT) {
          auto non_zero_value_defs = get_non_zero_defs(insn->src(0));
          if (non_zero_value_defs.empty()) {
            continue;
          }
          auto* rtype = method->get_proto()->get_rtype();
          if (!has_lifetime(insn->src(0), rtype)) {
            continue;
          }
          escape(non_zero_value_defs, nullptr, nullptr, true);
          continue;
        }
      }
    }
    return insn_escapes;
  }

  // Whether a constructor can store any values with (relevant) lifetimes
  bool may_capture(const sparta::PatriciaTreeSet<const DexMethod*>& active,
                   const DexMethodRef* method) const {
    always_assert(method::is_init(method));
    auto* type = method->get_class();
    if (type == type::java_lang_Object()) {
      return false;
    }
    if (method->is_external()) {
      return true;
    }
    auto* cls = type_class(type);
    if (cls == nullptr || cls->is_external()) {
      return true;
    }
    bool any_non_vestigial_objects_written_fields{false};
    UnorderedSet<DexMethod*> invoked_base_ctors;
    bool other_escapes{false};
    if (!get_writes(active, method->as_def(),
                    /* non_zero_written_fields */ nullptr,
                    /* non_vestigial_objects_written_fields */ nullptr,
                    &any_non_vestigial_objects_written_fields,
                    &invoked_base_ctors, &other_escapes)) {
      // mutual recursion across constructor invocations, which can happen when
      // a constructor creates a new object of some other type
      return true;
    }
    if (other_escapes || any_non_vestigial_objects_written_fields ||
        (unordered_any_of(invoked_base_ctors,
                          [&](DexMethod* invoked_base_ctor) {
                            return may_capture(active, invoked_base_ctor);
                          }))) {
      return true;
    }
    return false;
  }

  // Whether a newly created object may capture any values with (relevant)
  // lifetimes, or itself, as part of its creation
  bool may_capture(const sparta::PatriciaTreeSet<const DexMethod*>& active,
                   const IRInstruction* insn,
                   const UnorderedSet<DexMethod*>& invoked_ctors) const {
    switch (insn->opcode()) {
    case OPCODE_NEW_ARRAY:
      return false;
    case OPCODE_FILLED_NEW_ARRAY: {
      auto* component_type = type::make_array_component_type(insn->get_type());
      return insn->srcs_size() > 0 && has_lifetime(component_type);
    }
    case OPCODE_NEW_INSTANCE:
      always_assert(!invoked_ctors.empty());
      return unordered_any_of(invoked_ctors, [&](DexMethod* method) {
        always_assert(type::is_subclass(method->get_class(), insn->get_type()));
        return may_capture(active, method);
      });
    default:
      not_reached();
    }
  }

 public:
  explicit WritesAnalyzer(const Scope& /*scope*/,
                          const field_op_tracker::FieldStatsMap& field_stats,
                          const field_op_tracker::TypeLifetimes* type_lifetimes)
      : m_type_lifetimes(type_lifetimes), m_field_stats(field_stats) {}

  bool any_read(const UnorderedSet<DexField*>& fields) const {
    return unordered_any_of(fields, [&](DexField* field) {
      return m_field_stats.at(field).reads != 0;
    });
  }

  // Result indicates whether we ran into a recursive case.
  bool get_writes(
      const sparta::PatriciaTreeSet<const DexMethod*>& old_active,
      const DexMethod* method,
      ConcurrentSet<DexField*>* non_zero_written_fields,
      ConcurrentSet<DexField*>* non_vestigial_objects_written_fields,
      bool* any_non_vestigial_objects_written_fields,
      UnorderedSet<DexMethod*>* invoked_base_ctors,
      bool* other_escapes) const {
    auto active = old_active;
    active.insert(method);
    if (active.reference_equals(old_active)) {
      return false;
    }
    const auto& insn_escapes = get_insn_escapes(method);
    auto* init_load_param_this =
        method::is_init(method)
            ? method->get_code()->cfg().get_param_instructions().front().insn
            : nullptr;

    // We'll determine which fields are being written to with
    // (potentially) non-zero values, and which fields are being written to with
    // an non-vestigial value. Right now, we only consider as vestigial values
    // newly created objects and arrays which escape only to unread fields and
    // contain no non-vestigial objects.
    for (const auto& p : UnorderedIterable(insn_escapes)) {
      auto* insn = p.first;
      const auto& escapes = p.second;
      auto is_vestigial_object =
          opcode::is_a_new(insn->opcode()) &&
          !(any_read(escapes.put_value_fields) || escapes.other) &&
          !(has_lifetime(insn->get_type()) &&
            may_capture(active, insn, escapes.invoked_ctors));
      for (auto* field : UnorderedIterable(escapes.put_value_fields)) {
        always_assert(field != nullptr);
        if (non_zero_written_fields != nullptr) {
          non_zero_written_fields->insert(field);
        }
        if (!is_vestigial_object && has_lifetime(field->get_type())) {
          if (non_vestigial_objects_written_fields != nullptr) {
            non_vestigial_objects_written_fields->insert(field);
          }
          if (any_non_vestigial_objects_written_fields != nullptr) {
            *any_non_vestigial_objects_written_fields = true;
          }
        }
      }
      if (!escapes.invoked_ctors.empty() && (invoked_base_ctors != nullptr) &&
          insn == init_load_param_this) {
        insert_unordered_iterable(*invoked_base_ctors, escapes.invoked_ctors);
      }
      if ((other_escapes != nullptr) && escapes.other) {
        *other_escapes = true;
      }
    }
    return true;
  }
};

} // namespace

namespace field_op_tracker {

TypeLifetimes::TypeLifetimes()
    : m_ignored_types({type::java_lang_String(), type::java_lang_Class(),
                       type::java_lang_Boolean(), type::java_lang_Byte(),
                       type::java_lang_Short(), type::java_lang_Character(),
                       type::java_lang_Integer(), type::java_lang_Long(),
                       type::java_lang_Float(), type::java_lang_Double()}),
      m_java_lang_Enum(type::java_lang_Enum()) {}

bool TypeLifetimes::has_lifetime(const DexType* t) const {
  // Fields of primitive types can never hold on to references
  if (type::is_primitive(t)) {
    return false;
  }

  // Nobody should ever rely on the lifetime of strings, classes, boxed
  // values, or enum values
  if (m_ignored_types.count(t) != 0u) {
    return false;
  }
  if (type::is_subclass(m_java_lang_Enum, t)) {
    return false;
  }

  return true;
}

void analyze_writes(const Scope& scope,
                    const FieldStatsMap& field_stats,
                    const TypeLifetimes* type_lifetimes,
                    FieldWrites* res) {
  WritesAnalyzer analyzer(scope, field_stats, type_lifetimes);
  walk::parallel::code(scope, [&](const DexMethod* method, const IRCode&) {
    auto success = analyzer.get_writes(
        /*active*/ {}, method, &res->non_zero_written_fields,
        &res->non_vestigial_objects_written_fields,
        /* any_non_vestigial_objects_written_fields */ nullptr,
        /* invoked_base_ctors */ nullptr,
        /* other_escapes */ nullptr);
    always_assert(success);
  });
};

FieldStatsMap analyze(const Scope& scope) {
  ConcurrentMap<DexField*, FieldStats> concurrent_field_stats;
  // Gather the read/write counts from instructions.
  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (method->get_code() == nullptr) {
      return;
    }
    UnorderedMap<DexField*, FieldStats> field_stats;
    if (method::is_init(method)) {
      // compute init_writes by checking receiver of each iput
      cfg::ScopedCFG cfg(method->get_code());
      reaching_defs::MoveAwareFixpointIterator reaching_definitions(*cfg);
      reaching_definitions.run(reaching_defs::Environment());
      auto* first_load_param = cfg->get_param_instructions().begin()->insn;
      always_assert(first_load_param->opcode() == IOPCODE_LOAD_PARAM_OBJECT);
      for (cfg::Block* block : cfg->blocks()) {
        auto env = reaching_definitions.get_entry_state_at(block);
        auto insns = InstructionIterable(block);
        for (auto it = insns.begin(); it != insns.end();
             reaching_definitions.analyze_instruction(it++->insn, &env)) {
          IRInstruction* insn = it->insn;
          if (!opcode::is_an_iput(insn->opcode())) {
            continue;
          }
          auto* field = resolve_field(insn->get_field());
          if (field == nullptr || field->get_class() != method->get_class()) {
            continue;
          }
          // We only consider for init_writes those iputs where the obj is the
          // receiver. I cannot see where the JVM spec this would be enforced,
          // we'll be conservative to be safe.
          auto obj_defs = env.get(insn->src(1));
          if (!obj_defs.is_top() && !obj_defs.is_bottom() &&
              obj_defs.elements().size() == 1 &&
              *obj_defs.elements().begin() == first_load_param) {
            ++field_stats[field].init_writes;
          }
        }
      }
    }
    bool is_clinit = method::is_clinit(method);
    cfg_adapter::iterate(method->get_code(), [&](const MethodItemEntry& mie) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (!insn->has_field()) {
        return cfg_adapter::LOOP_CONTINUE;
      }
      auto* field = resolve_field(insn->get_field());
      if (field == nullptr) {
        return cfg_adapter::LOOP_CONTINUE;
      }
      if (opcode::is_an_sget(op) || opcode::is_an_iget(op)) {
        ++field_stats[field].reads;
      } else if (opcode::is_an_sput(op) || opcode::is_an_iput(op)) {
        ++field_stats[field].writes;
        if (is_clinit && is_static(field) &&
            field->get_class() == method->get_class()) {
          ++field_stats[field].init_writes;
        }
      }
      return cfg_adapter::LOOP_CONTINUE;
    });
    for (auto& p : UnorderedIterable(field_stats)) {
      concurrent_field_stats.update(
          p.first, [&](DexField*, FieldStats& fs, bool) { fs += p.second; });
    }
  });

  FieldStatsMap field_stats;
  insert_unordered_iterable(field_stats, concurrent_field_stats);

  // Gather field reads from annotations.
  walk::annotations(scope, [&](DexAnnotation* anno) {
    std::vector<DexFieldRef*> fields_in_anno;
    anno->gather_fields(fields_in_anno);
    for (const auto& field_ref : fields_in_anno) {
      auto* field = resolve_field(field_ref);
      if (field != nullptr) {
        ++field_stats[field].reads;
      }
    }
  });
  return field_stats;
}

} // namespace field_op_tracker
