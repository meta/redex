/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "WrappedPrimitives.h"

#include <inttypes.h>

#include "CFGMutation.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationWholeProgramState.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "RedexContext.h"
#include "Show.h"
#include "Trace.h"
#include "TypeSystem.h"

namespace wrapped_primitives {
static std::unique_ptr<WrappedPrimitives> s_instance{nullptr};
WrappedPrimitives* get_instance() { return s_instance.get(); }

void initialize(const std::vector<Spec>& wrapper_specs) {
  s_instance.reset(new WrappedPrimitives(wrapper_specs));
  // In tests, we create and destroy g_redex repeatedly. So we need to reset
  // the singleton.
  g_redex->add_destruction_task([]() { s_instance.reset(nullptr); });
}

void WrappedPrimitives::mark_roots() {
  for (auto& spec : m_wrapper_specs) {
    for (auto&& [from, to] : spec.allowed_invokes) {
      auto* def = to->as_def();
      if (def != nullptr && def->rstate.can_delete()) {
        TRACE(WP, 2, "Setting %s as root", SHOW(def));
        def->rstate.set_root();
        m_marked_root_methods.emplace(def);
        auto* cls = type_class(def->get_class());
        if (cls->rstate.can_delete()) {
          TRACE(WP, 2, "Setting %s as root", SHOW(cls));
          cls->rstate.set_root();
          m_marked_root_classes.emplace(cls);
        }
      }
    }
    for (auto& method : spec.wrapper_type_constructors()) {
      if (!method->rstate.dont_inline()) {
        method->rstate.set_dont_inline();
        TRACE(WP, 2, "Disallowing inlining for %s", SHOW(method));
      }
    }
  }
}

void WrappedPrimitives::unmark_roots() {
  for (const auto& def : UnorderedIterable(m_marked_root_methods)) {
    TRACE(WP, 2, "Unsetting %s as root", SHOW(def));
    def->rstate.unset_root();
  }
  for (const auto& cls : UnorderedIterable(m_marked_root_classes)) {
    TRACE(WP, 2, "Unsetting %s as root", SHOW(cls));
    cls->rstate.unset_root();
  }
}

namespace {
bool contains_relevant_invoke(
    const UnorderedSet<const DexMethodRef*>& wrapped_apis, DexMethod* method) {
  if (wrapped_apis.empty()) {
    return false;
  }
  auto& cfg = method->get_code()->cfg();
  auto iterable = cfg::InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    IRInstruction* insn = it->insn;
    if (insn->has_method() && wrapped_apis.count(insn->get_method()) > 0) {
      return true;
    }
  }
  return false;
}

// Checks if the value is a known ObjectWithImmutAttr with a single known
// attribute value. Makes assumptions that there is only 1, as is consistent
// with the other assumptions in the pass.
std::optional<std::pair<const DexType*, int64_t>>
extract_object_with_attr_value(const ConstantValue& value) {
  auto obj_or_none = value.maybe_get<ObjectWithImmutAttrDomain>();
  if (obj_or_none != std::nullopt &&
      obj_or_none->get_constant() != std::nullopt) {
    auto object = *obj_or_none->get_constant();
    auto signed_value =
        only(object.attributes).value.maybe_get<SignedConstantDomain>();
    if (signed_value && signed_value.value().get_constant() != std::nullopt) {
      auto primitive_value = *signed_value.value().get_constant();
      return std::pair<const DexType*, int64_t>(object.type, primitive_value);
    } else {
      TRACE(WP, 2, "  No SignedConstantDomain value");
    }
  } else {
    TRACE(WP, 2, "  Not a known ObjectWithImmutAttrDomain");
  }

  return std::nullopt;
}

bool needs_cast(const TypeSystem& type_system,
                DexMethodRef* from_ref,
                DexMethodRef* to_ref) {
  auto* from = from_ref->get_class();
  auto* to = to_ref->get_class();
  if (from == to) {
    return false;
  }
  if (is_interface(type_class(from))) {
    auto supers = type_system.get_all_super_interfaces(from);
    return supers.count(to) == 0;
  } else {
    if (is_interface(type_class(to))) {
      return !type_system.implements(from, to);
    } else {
      return !type_system.is_subtype(to, from);
    }
  }
}

// For definitions of a wrapper type that flow into an invoke, makes sure they
// are all known ObjectWithImmutAttr instances and they agree on the type of
// the object. Empty return value will signal an invalid state that should not
// be transformed.
template <typename T>
std::vector<KnownDef> validate_known_defs(
    const UnorderedMap<IRInstruction*, KnownDef>& known_defs,
    const T& actual_defs) {
  std::vector<KnownDef> known_vec;
  UnorderedSet<const DexType*> type_set;
  for (auto& d : actual_defs) {
    auto is_known_search = known_defs.find(d);
    if (is_known_search != known_defs.end()) {
      auto& kd = is_known_search->second;
      known_vec.push_back(kd);
      type_set.emplace(kd.wrapper_type);
    }
  }
  if (known_vec.size() == actual_defs.size() && type_set.size() == 1) {
    return known_vec;
  } else {
    // Return empty to signal that validation did not pass.
    return {};
  }
}
} // namespace

bool WrappedPrimitives::is_wrapped_method_ref(const DexType* wrapper_type,
                                              DexMethodRef* ref) {
  auto search = m_type_to_spec.find(const_cast<DexType*>(wrapper_type));
  if (search != m_type_to_spec.end()) {
    return search->second.allowed_invokes.count(ref) > 0;
  }
  return false;
};

DexMethodRef* WrappedPrimitives::unwrapped_method_ref_for(
    const DexType* wrapper_type, DexMethodRef* ref) {
  auto spec = m_type_to_spec.at(const_cast<DexType*>(wrapper_type));
  return spec.allowed_invokes.at(ref);
};

void WrappedPrimitives::increment_consts() { m_consts_inserted++; }

void WrappedPrimitives::increment_casts() { m_casts_inserted++; }

// The initial phase of analyzing a method; for a known ObjectWithImmutAttr
// instance, keep track of the sget-object instruction that defines it, the
// register they get moved into, and the primitive value that is stored.
// Computing this up front can make subsequent transformations easier.
UnorderedMap<IRInstruction*, KnownDef>
WrappedPrimitives::build_known_definitions(
    const cp::intraprocedural::FixpointIterator& intra_cp,
    cfg::ControlFlowGraph& cfg) {
  UnorderedMap<IRInstruction*, KnownDef> known_defs;
  for (const auto& block : cfg.blocks()) {
    auto env = intra_cp.get_entry_state_at(block);
    // This block is unreachable
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* insn = it->insn;
      intra_cp.analyze_instruction(insn, &env, insn == last_insn->insn);
      if (insn->opcode() != IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
        continue;
      }
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      auto primary_it = cfg.primary_instruction_of_move_result(cfg_it);
      always_assert(!primary_it.is_end());
      if (primary_it->insn->opcode() != OPCODE_SGET_OBJECT) {
        continue;
      }
      auto* primary_insn = primary_it->insn;
      auto search = m_type_to_spec.find(primary_insn->get_field()->get_type());
      if (search != m_type_to_spec.end()) {
        const auto& reg_env = env.get_register_environment();
        auto dest_reg = insn->dest();
        const auto& value = reg_env.get(dest_reg);
        auto maybe_pair = extract_object_with_attr_value(value);
        if (maybe_pair != std::nullopt) {
          // Store a mapping of primary instruction to its dest register and
          // value. This may be useful later for ambiguous data flow into a
          // wrapped API method.
          KnownDef kd{maybe_pair->first, primary_insn, dest_reg,
                      maybe_pair->second};
          known_defs.emplace(primary_insn, kd);
        }
      }
    }
  }
  return known_defs;
}

void WrappedPrimitives::optimize_method(
    const TypeSystem& type_system,
    const cp::intraprocedural::FixpointIterator& intra_cp,
    const cp::WholeProgramState& /*wps*/,
    DexMethod* method,
    cfg::ControlFlowGraph& cfg) {
  if (method->get_code() == nullptr || method->rstate.no_optimizations()) {
    return;
  }
  if (!contains_relevant_invoke(m_all_wrapped_apis, method)) {
    return;
  }

  TRACE(WP, 2, "optimize_method: %s", SHOW(method));
  TRACE(WP, 8, "Initial %s", SHOW(cfg));
  // Initial replay of the analysis, to build up an understanding of sget-object
  // instructions, their possible known value and the registers they populate.
  auto known_defs = build_known_definitions(intra_cp, cfg);
  // Subsequent replay of analysis, which will set up mutations as needed.
  Lazy<live_range::LazyLiveRanges> live_ranges(
      [&]() { return std::make_unique<live_range::LazyLiveRanges>(cfg); });
  cfg::CFGMutation mutation(cfg);
  for (const auto& block : cfg.blocks()) {
    auto env = intra_cp.get_entry_state_at(block);
    // This block is unreachable
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      auto move_result_it = cfg.move_result_of(cfg_it);

      auto* insn = cfg_it->insn;
      if (insn->has_method() &&
          m_all_wrapped_apis.count(insn->get_method()) > 0) {
        TRACE(WP, 2, "Relevant invoke: %s in B%zu", SHOW(insn), block->id());
        auto* ref = insn->get_method();

        // Inline the wrapped constant value and change method ref, if all
        // information is known.
        auto srcs_size = insn->srcs_size();
        const auto& reg_env = env.get_register_environment();

        bool updated_ref{false};
        auto updated_insn = std::make_unique<IRInstruction>(*insn);
        // HELPER FUNCTIONS
        auto perform_unwrapping = [&](const DexType* wrapper_type,
                                      src_index_t idx, reg_t literal_reg) {
          updated_insn->set_src(idx, literal_reg);
          auto* unwrapped_ref = unwrapped_method_ref_for(wrapper_type, ref);
          if (!updated_ref) {
            if (needs_cast(type_system, ref, unwrapped_ref)) {
              auto* to_type = unwrapped_ref->get_class();
              auto opcode = is_interface(type_class(to_type))
                                ? OPCODE_INVOKE_INTERFACE
                                : OPCODE_INVOKE_VIRTUAL;
              auto obj_reg = cfg.allocate_temp();
              auto* cast = (new IRInstruction(OPCODE_CHECK_CAST))
                               ->set_type(to_type)
                               ->set_src(0, insn->src(0));
              auto* move_pseudo =
                  (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                      ->set_dest(obj_reg);
              updated_insn->set_method(unwrapped_ref);
              updated_insn->set_opcode(opcode);
              updated_insn->set_src(0, obj_reg);
              mutation.insert_before(cfg_it, {cast, move_pseudo});
              increment_casts();
            } else {
              updated_insn->set_method(unwrapped_ref);
            }
            updated_ref = true;
          }
        };
        auto inject_const = [&](const cfg::InstructionIterator& anchor,
                                int64_t literal, reg_t literal_reg,
                                bool is_wide) {
          auto* const_insn =
              (new IRInstruction(is_wide ? OPCODE_CONST_WIDE : OPCODE_CONST))
                  ->set_literal(literal)
                  ->set_dest(literal_reg);

          mutation.insert_before(anchor, {const_insn});
          increment_consts();
        };

        for (size_t i = 0; i < srcs_size; i++) {
          auto current_reg = insn->src(i);
          TRACE(WP, 2, "  Checking v%u", current_reg);
          const auto& value = reg_env.get(current_reg);
          auto maybe_pair = extract_object_with_attr_value(value);
          if (maybe_pair != std::nullopt) {
            const auto* wrapper_type = maybe_pair->first;
            auto literal = maybe_pair->second;
            TRACE(WP,
                  2,
                  " ** Instruction %s uses a known object with constant "
                  "value %" PRId64,
                  SHOW(insn),
                  literal);

            auto search =
                m_type_to_spec.find(const_cast<DexType*>(wrapper_type));
            if (search != m_type_to_spec.end()) {
              auto spec = search->second;
              if (is_wrapped_method_ref(wrapper_type, ref)) {
                auto is_wide = type::is_wide_type(spec.primitive);
                auto literal_reg =
                    is_wide ? cfg.allocate_wide_temp() : cfg.allocate_temp();
                inject_const(cfg_it, literal, literal_reg, is_wide);
                perform_unwrapping(wrapper_type, i, literal_reg);
              }
            }
          } else {
            // Check if the src idx is a wrapper type in the proto. If so, do a
            // fallback to check if N known ObjectWithImmutAttr instances are
            // flowing into this call.
            TRACE(WP, 2,
                  "  v%u is not a known object (i = %zu); will fall back and "
                  "look for "
                  "multiple incoming definitions",
                  current_reg, i);
            live_range::Use use{insn, (src_index_t)i};
            auto f = live_ranges->use_def_chains->find(use);
            if (f != live_ranges->use_def_chains->end() &&
                f->second.size() > 1) {
              // Only check if there are multiple defs; a single def that was
              // not understood in the environment will have no value taking
              // this fallback path.
              auto valid_defs = validate_known_defs(known_defs, f->second);
              if (!valid_defs.empty()) {
                TRACE(WP, 2,
                      " ** Should be able to patch dataflow to this invoke!!");
                const auto* wrapper_type =
                    valid_defs.at(0).wrapper_type; // all types in vec will be
                                                   // the same, per validation
                                                   // step
                auto search =
                    m_type_to_spec.find(const_cast<DexType*>(wrapper_type));
                if (search != m_type_to_spec.end()) {
                  auto spec = search->second;
                  if (is_wrapped_method_ref(wrapper_type, ref)) {
                    // Perform unwrapping as above, but with an injected const
                    // alongside each definition.
                    auto is_wide = type::is_wide_type(spec.primitive);
                    auto literal_reg = is_wide ? cfg.allocate_wide_temp()
                                               : cfg.allocate_temp();
                    for (auto& kd : valid_defs) {
                      inject_const(cfg.find_insn(kd.primary_insn),
                                   kd.primitive_value, literal_reg, is_wide);
                    }
                    perform_unwrapping(wrapper_type, i, literal_reg);
                  }
                }
              }
            }
          }
        } // END SRCS FOR LOOP
        if (updated_ref) {
          std::vector<IRInstruction*> replacements{updated_insn.release()};
          if (!move_result_it.is_end()) {
            replacements.push_back(new IRInstruction(*move_result_it->insn));
          }
          mutation.replace(cfg_it, replacements);
        }
      }
      intra_cp.analyze_instruction(insn, &env, insn == last_insn->insn);
    }
  }
  mutation.flush();
  TRACE(WP, 8, "Post edit %s %s", SHOW(method), SHOW(cfg));
}

bool is_wrapped_api(const DexMethodRef* ref) {
  auto* wp_instance = get_instance();
  if (wp_instance == nullptr) {
    return false;
  }
  return wp_instance->is_wrapped_api(ref);
}

void optimize_method(const TypeSystem& type_system,
                     const cp::intraprocedural::FixpointIterator& intra_cp,
                     const cp::WholeProgramState& wps,
                     DexMethod* method,
                     cfg::ControlFlowGraph& cfg) {
  auto* wp_instance = get_instance();
  if (wp_instance == nullptr) {
    return;
  }
  wp_instance->optimize_method(type_system, intra_cp, wps, method, cfg);
}
} // namespace wrapped_primitives
