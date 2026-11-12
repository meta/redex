/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IRTypeChecker.h"

#include <optional>
#include <utility>

#include "BigBlocks.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexPosition.h"
#include "MethodUtil.h"
#include "MonitorCount.h"
#include "OptionalIO.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "ShowCFG.h"
#include "Trace.h"

using namespace sparta;
using namespace type_inference;

namespace {

using namespace ir_analyzer;

// We abort the type checking process at the first error encountered.
class TypeCheckingException final : public std::runtime_error {
 public:
  explicit TypeCheckingException(const std::string& what_arg)
      : std::runtime_error(what_arg) {}
};

std::ostringstream& print_register(std::ostringstream& out, reg_t reg) {
  if (reg == RESULT_REGISTER) {
    out << "result";
  } else {
    out << "register v" << reg;
  }
  return out;
}

std::ostream& print_type_hierarchy(std::ostream& out, const DexType* type) {
  size_t indent = 0;
  auto print_indent = [&]() {
    if (indent > 0) {
      for (size_t i = 0; i != indent - 1; ++i) {
        out << "--";
      }
      out << "-> ";
    }
  };

  for (; type != nullptr; ++indent) {
    auto* klass = type_class(type);
    if (klass == nullptr) {
      print_indent();
      out << vshow(type) << " (no class)\n";

      type = nullptr;
      continue;
    }

    print_indent();
    // This does not match vshow(DexClass), so we do it manually.
    out << vshow(klass->get_type());
    if (klass->get_interfaces() != nullptr &&
        !klass->get_interfaces()->empty()) {
      out << " (implements";
      for (const auto& intf : *klass->get_interfaces()) {
        out << " ";
        out << vshow(intf);
      }
      out << ")";
    }
    out << '\n';

    type = klass->get_super_class();
  }

  return out;
}

void check_type_match(reg_t reg, IRType actual, IRType expected) {
  if (actual == IRType::BOTTOM) {
    // There's nothing to do for unreachable code.
    return;
  }
  if (actual == IRType::SCALAR && expected != IRType::REFERENCE) {
    // If the type is SCALAR and we're checking compatibility with an integer
    // or float type, we just bail out.
    return;
  }
  if (!TypeDomain(actual).leq(TypeDomain(expected))) {
    std::ostringstream out;
    print_register(out, reg) << ": expected type " << expected << ", but found "
                             << actual << " instead";
    throw TypeCheckingException(out.str());
  }
}

/*
 * There are cases where we cannot precisely infer the exception type for
 * MOVE_EXCEPTION. In these cases, we use Ljava/lang/Throwable; as a fallback
 * type.
 */
bool is_inference_fallback_type(const DexType* type) {
  return type == type::java_lang_Throwable();
}

/*
 * We might not have the external DexClass to fully determine the hierarchy.
 * Therefore, be more lenient when assigning from or to external DexType.
 */
bool check_cast_helper(const DexType* from, const DexType* to) {
  // We can always cast to Object
  if (to == type::java_lang_Object()) {
    return true;
  }
  // We can never cast from Object to anything besides Object
  if (from == type::java_lang_Object() && from != to) {
    // TODO(T66567547) sanity check that type::check_cast would have agreed
    always_assert(!type::check_cast(from, to));
    return false;
  }
  // If we have any external types (aside from Object and the other well known
  // types), allow them.
  auto* from_cls = type_class(from);
  auto* to_cls = type_class(to);
  if ((from_cls == nullptr) || (to_cls == nullptr)) {
    return true;
  }
  // Assume the type hierarchies of the well known external types are stable
  // across Android versions. When their class definitions present, perform the
  // regular type inheritance check.
  if ((from_cls->is_external() &&
       (g_redex->pointers_cache().m_well_known_types.count(from) == 0u)) ||
      (to_cls->is_external() &&
       (g_redex->pointers_cache().m_well_known_types.count(to) == 0u))) {
    return true;
  }
  return type::check_cast(from, to);
}

// Type assignment check between two reference types. We assume that both `from`
// and `to` are reference types.
// Took reference from:
// http://androidxref.com/6.0.1_r10/xref/art/runtime/verifier/reg_type-inl.h#88
//
// Note: the expectation is that `from` and `to` are reference types, otherwise
//       the check fails.
bool check_is_assignable_from(const DexType* from,
                              const DexType* to,
                              bool strict) {
  always_assert(from && to);
  always_assert_log(!type::is_primitive(from), "%s", SHOW(from));

  if (type::is_primitive(from) || type::is_primitive(to)) {
    return false; // Expect types be a reference type.
  }

  if (from == to) {
    return true; // Fast path if the two are equal.
  }
  if (to == type::java_lang_Object()) {
    return true; // All reference types can be assigned to Object.
  }
  if (type::is_java_lang_object_array(to)) {
    // All reference arrays may be assigned to Object[]
    return type::is_reference_array(from);
  }
  if (type::is_array(from) && type::is_array(to)) {
    if (type::get_array_level(from) != type::get_array_level(to)) {
      return false;
    }
    auto* efrom = type::make_array_element_type(from);
    auto* eto = type::make_array_element_type(to);
    return check_cast_helper(efrom, eto);
  }
  if (!strict) {
    // If `to` is an interface, allow any assignment when non-strict.
    // This behavior is copied from AOSP.
    auto* to_cls = type_class(to);
    if (to_cls != nullptr && is_interface(to_cls)) {
      return true;
    }
  }
  return check_cast_helper(from, to);
}

void check_wide_type_match(reg_t reg,
                           IRType actual1,
                           IRType actual2,
                           IRType expected1,
                           IRType expected2) {
  if (actual1 == IRType::BOTTOM) {
    // There's nothing to do for unreachable code.
    return;
  }

  if (actual1 == IRType::SCALAR1 && actual2 == IRType::SCALAR2) {
    // If type of the pair of registers is (SCALAR1, SCALAR2), we just bail
    // out.
    return;
  }
  if (!(TypeDomain(actual1).leq(TypeDomain(expected1)) &&
        TypeDomain(actual2).leq(TypeDomain(expected2)))) {
    std::ostringstream out;
    print_register(out, reg)
        << ": expected type (" << expected1 << ", " << expected2
        << "), but found (" << actual1 << ", " << actual2 << ") instead";
    throw TypeCheckingException(out.str());
  }
}

void assume_type(TypeEnvironment* state,
                 reg_t reg,
                 IRType expected,
                 bool ignore_top = false) {
  if (state->is_bottom()) {
    // There's nothing to do for unreachable code.
    return;
  }
  IRType actual = state->get_type(reg).element();
  if (ignore_top && actual == IRType::TOP) {
    return;
  }
  check_type_match(reg, actual, /* expected */ expected);
}

void assume_wide_type(TypeEnvironment* state,
                      reg_t reg,
                      IRType expected1,
                      IRType expected2) {
  if (state->is_bottom()) {
    // There's nothing to do for unreachable code.
    return;
  }
  IRType actual1 = state->get_type(reg).element();
  IRType actual2 = state->get_type(reg + 1).element();
  check_wide_type_match(reg,
                        actual1,
                        actual2,
                        /* expected1 */ expected1,
                        /* expected2 */ expected2);
}

// This is used for the operand of a comparison operation with zero. The
// complexity here is that this operation may be performed on either an
// integer or a reference.
void assume_comparable_with_zero(TypeEnvironment* state, reg_t reg) {
  if (state->is_bottom()) {
    // There's nothing to do for unreachable code.
    return;
  }
  IRType t = state->get_type(reg).element();
  if (t == IRType::SCALAR) {
    // We can't say anything conclusive about a register that has SCALAR type,
    // so we just bail out.
    return;
  }
  if (!(TypeDomain(t).leq(TypeDomain(IRType::REFERENCE)) ||
        TypeDomain(t).leq(TypeDomain(IRType::INT)))) {
    std::ostringstream out;
    print_register(out, reg)
        << ": expected integer or reference type, but found " << t
        << " instead";
    throw TypeCheckingException(out.str());
  }
}

// This is used for the operands of a comparison operation between two
// registers. The complexity here is that this operation may be performed on
// either two integers or two references.
void assume_comparable(TypeEnvironment* state, reg_t reg1, reg_t reg2) {
  if (state->is_bottom()) {
    // There's nothing to do for unreachable code.
    return;
  }
  IRType t1 = state->get_type(reg1).element();
  IRType t2 = state->get_type(reg2).element();
  if ((!TypeDomain(t1).leq(TypeDomain(IRType::REFERENCE)) ||
       !TypeDomain(t2).leq(TypeDomain(IRType::REFERENCE))) &&
      (!TypeDomain(t1).leq(TypeDomain(IRType::SCALAR)) ||
       !TypeDomain(t2).leq(TypeDomain(IRType::SCALAR)) ||
       (t1 == IRType::FLOAT) || (t2 == IRType::FLOAT))) {
    // Two values can be used in a comparison operation if they either both
    // have the REFERENCE type or have non-float scalar types. Note that in
    // the case where one or both types have the SCALAR type, we can't
    // definitely rule out the absence of a type error.
    std::ostringstream out;
    print_register(out, reg1) << " and ";
    print_register(out, reg2)
        << ": incompatible types in comparison " << t1 << " and " << t2;
    throw TypeCheckingException(out.str());
  }
}

void assume_integer(TypeEnvironment* state, reg_t reg) {
  assume_type(state, reg, /* expected */ IRType::INT);
}

void assume_float(TypeEnvironment* state, reg_t reg) {
  assume_type(state, reg, /* expected */ IRType::FLOAT);
}

void assume_long(TypeEnvironment* state, reg_t reg) {
  assume_wide_type(
      state, reg, /* expected1 */ IRType::LONG1, /* expected2 */ IRType::LONG2);
}

void assume_double(TypeEnvironment* state, reg_t reg) {
  assume_wide_type(state,
                   reg,
                   /* expected1 */ IRType::DOUBLE1,
                   /* expected2 */ IRType::DOUBLE2);
}

void assume_wide_scalar(TypeEnvironment* state, reg_t reg) {
  assume_wide_type(state,
                   reg,
                   /* expected1 */ IRType::SCALAR1,
                   /* expected2 */ IRType::SCALAR2);
}

class Result final {
 public:
  static Result Ok() { return Result(); }

  static Result make_error(const std::string& s) { return Result(s); }

  const std::string& error_message() const {
    always_assert(!is_ok);
    return m_error_message;
  }

  bool operator==(const Result& that) const {
    return is_ok == that.is_ok && m_error_message == that.m_error_message;
  }

  bool operator!=(const Result& that) const { return !(*this == that); }

 private:
  bool is_ok{true};
  std::string m_error_message;
  explicit Result(std::string s)
      : is_ok(false), m_error_message(std::move(s)) {}
  Result() = default;
};

Result check_load_params(const DexMethod* method) {
  bool is_static_method = is_static(method);
  const auto* signature = method->get_proto()->get_args();
  auto sig_it = signature->begin();
  size_t load_insns_cnt = 0;

  auto handle_instance =
      [&](IRInstruction* insn) -> std::optional<std::string> {
    // Must be a param-object.
    if (insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT) {
      return std::string(
                 "First parameter must be loaded with load-param-object: ") +
             show(insn);
    }
    return std::nullopt;
  };
  auto handle_other = [&](IRInstruction* insn) -> std::optional<std::string> {
    if (sig_it == signature->end()) {
      return std::string("Not enough argument types for ") + show(insn);
    }
    bool ok = false;
    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM_OBJECT:
      ok = type::is_object(*sig_it);
      break;
    case IOPCODE_LOAD_PARAM:
      ok = type::is_primitive(*sig_it) && !type::is_wide_type(*sig_it);
      break;
    case IOPCODE_LOAD_PARAM_WIDE:
      ok = type::is_primitive(*sig_it) && type::is_wide_type(*sig_it);
      break;
    default:
      not_reached();
    }
    if (!ok) {
      return std::string("Incompatible load-param ") + show(insn) + " for " +
             type::type_shorty(*sig_it);
    }
    ++sig_it;
    return std::nullopt;
  };

  bool non_load_param_seen = false;
  using handler_t = std::function<std::optional<std::string>(IRInstruction*)>;
  handler_t handler =
      is_static_method ? handler_t(handle_other) : handler_t(handle_instance);

  for (const auto& mie :
       InstructionIterable(method->get_code()->cfg().entry_block())) {
    IRInstruction* insn = mie.insn;
    if (!opcode::is_a_load_param(insn->opcode())) {
      non_load_param_seen = true;
      continue;
    }
    ++load_insns_cnt;
    if (non_load_param_seen) {
      return Result::make_error("Saw non-load-param instruction before " +
                                show(insn));
    }
    auto res = handler(insn);
    if (res) {
      return Result::make_error(*res);
    }
    // Instance methods have an extra 'load-param' at the beginning for the
    // instance object.
    // Once we've checked that, though, the rest is the same so move on to
    // using 'handle_other' in all cases.
    handler = handler_t(handle_other);
  }

  size_t expected_load_params_cnt =
      method->get_proto()->get_args()->size() +
      static_cast<unsigned long>(!is_static_method);
  if (load_insns_cnt != expected_load_params_cnt) {
    return Result::make_error(
        "Number of existing load-param instructions (" + show(load_insns_cnt) +
        ") is lower than expected (" + show(expected_load_params_cnt) + ")");
  }

  return Result::Ok();
}

// Every variable created by a new-instance call should be initialized by a
// proper invoke-direct <init>. Here, we perform simple check to find some
// missing calls resulting in use of uninitialized variables. We correctly track
// variables in a "big block", the most common form of allocation+init.
Result check_uninitialized(DexMethod* method, bool relaxed_init_check) {
  auto* code = method->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();

  UnorderedSet<cfg::BlockId> block_visited;
  auto ordered_blocks = cfg.order();

  for (cfg::Block* block : ordered_blocks) {
    if (block_visited.count(block->id()) != 0u) {
      continue;
    }
    auto big_block = big_blocks::get_big_block(block);
    if (!big_block) {
      continue;
    }
    // Find a big block starting from current block.
    for (auto* b : big_block->get_blocks()) {
      block_visited.emplace(b->id());
    }
    UnorderedMap<reg_t, IRInstruction*> uninitialized_regs;
    UnorderedMap<IRInstruction*, UnorderedSet<reg_t>> uninitialized_regs_rev;
    auto remove_from_uninitialized_list = [&](reg_t reg) {
      auto it = uninitialized_regs.find(reg);
      if (it != uninitialized_regs.end()) {
        uninitialized_regs_rev[it->second].erase(reg);
        uninitialized_regs.erase(reg);
      }
    };

    auto* current_block = big_block->get_first_block();
    while (current_block != nullptr) {
      auto ii = InstructionIterable(current_block);
      for (auto it = ii.begin(); it != ii.end(); it++) {
        auto* insn = it->insn;
        auto op = insn->opcode();
        if (op == OPCODE_NEW_INSTANCE) {
          auto cfg_it = current_block->to_cfg_instruction_iterator(it);
          auto move_result = cfg.move_result_of(cfg_it);
          if (move_result.is_end()) {
            return Result::make_error(
                "No opcode-move-result after new-instance " + show(*cfg_it) +
                " in \n" + show(cfg));
          }

          auto reg_dest = move_result->insn->dest();
          remove_from_uninitialized_list(reg_dest);

          uninitialized_regs[reg_dest] = insn;
          uninitialized_regs_rev[insn].insert(reg_dest);
          // skip the move_result
          it++;
          if (it == ii.end()) {
            break;
          }
          continue;
        }

        if (opcode::is_a_move(op) && !opcode::is_move_result_any(op)) {
          assert(insn->srcs().size() > 0);
          auto src = insn->srcs()[0];
          auto dest = insn->dest();
          if (src == dest) {
            continue;
          }

          auto it_src = uninitialized_regs.find(src);
          // We no longer care about the old dest
          remove_from_uninitialized_list(dest);
          // But if src was uninitialized, dest is now too
          if (it_src != uninitialized_regs.end()) {
            uninitialized_regs[dest] = it_src->second;
            uninitialized_regs_rev[it_src->second].insert(dest);
          }
          continue;
        }

        auto create_error = [&](const IRInstruction* instruction,
                                const cfg::ControlFlowGraph& cfg) {
          return Result::make_error("Use of uninitialized variable " +
                                    show(instruction) + " detected at " +
                                    show(*it) + " in \n" + show(cfg));
        };

        if (op == OPCODE_INVOKE_DIRECT) {
          auto const& sources = insn->srcs();
          auto object = sources[0];

          auto object_it = uninitialized_regs.find(object);
          if (object_it != uninitialized_regs.end()) {
            auto* object_ir = object_it->second;
            auto* init_method = insn->get_method();
            if (!method::is_init(init_method)) {
              return create_error(object_ir, cfg);
            }
            auto check_type = [&](auto* init_type, auto* object_type) {
              if (relaxed_init_check) {
                return type::is_subclass(init_type, object_type);
              }
              return init_type == object_type;
            };
            if (!check_type(init_method->get_class(), object_ir->get_type())) {
              return Result::make_error("Variable " + show(object_ir) +
                                        " initialized with the wrong type at " +
                                        show(*it) + " in \n" + show(cfg));
            }
            for (auto reg :
                 UnorderedIterable(uninitialized_regs_rev[object_ir])) {
              uninitialized_regs.erase(reg);
            }
            uninitialized_regs_rev.erase(object_ir);
          }

          for (unsigned int i = 1; i < sources.size(); i++) {
            auto u_it = uninitialized_regs.find(sources[i]);
            if (u_it != uninitialized_regs.end()) {
              return create_error(u_it->second, cfg);
            }
          }
          continue;
        }

        auto const& sources = insn->srcs();
        for (auto reg : sources) {
          auto u_it = uninitialized_regs.find(reg);
          if (u_it != uninitialized_regs.end()) {
            return create_error(u_it->second, cfg);
          }
        }

        if (insn->has_dest()) {
          remove_from_uninitialized_list(insn->dest());
        }
      }
      // get the next block.
      if (current_block == big_block->get_last_block()) {
        break;
      }
      current_block = current_block->goes_to();
    }
  }
  return Result::Ok();
}

/*
 * Do a linear pass to sanity-check the structure of the bytecode.
 */
Result check_structure(DexMethod* method,
                       cfg::ControlFlowGraph& cfg,
                       bool check_no_overwrite_this,
                       bool relaxed_init_check) {
  check_no_overwrite_this &= !is_static(method);
  IRInstruction* this_insn = nullptr;
  auto* entry_block = cfg.entry_block();
  for (cfg::Block* block : cfg.blocks()) {
    bool has_seen_non_load_param_opcode{false};
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* insn = it->insn;
      auto op = insn->opcode();
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      if ((block != entry_block || has_seen_non_load_param_opcode) &&
          opcode::is_a_load_param(op)) {
        return Result::make_error("Encountered " + show(*it) +
                                  " not at the start of the method");
      }
      has_seen_non_load_param_opcode = !opcode::is_a_load_param(op);

      if (check_no_overwrite_this) {
        if (op == IOPCODE_LOAD_PARAM_OBJECT && this_insn == nullptr) {
          this_insn = insn;
        } else if (insn->has_dest() && this_insn != nullptr &&
                   insn->dest() == this_insn->dest()) {
          return Result::make_error(
              "Encountered overwrite of `this` register by " + show(insn));
        }
      }

      if (opcode::is_move_result_any(op)) {
        if (block == cfg.entry_block() && it == ii.begin()) {
          return Result::make_error("Encountered " + show(*it) +
                                    " at start of the method");
        }
        auto prev =
            cfg.primary_instruction_of_move_result_for_type_check(cfg_it);
        // The instruction immediately before a move-result instruction must be
        // either an invoke-* or a filled-new-array instruction.
        if (opcode::is_a_move_result(op)) {
          if (prev->type != MFLOW_OPCODE) {
            return Result::make_error("Encountered " + show(*it) +
                                      " at start of the method");
          }
          auto prev_op = prev->insn->opcode();
          if (!(opcode::is_an_invoke(prev_op) ||
                opcode::is_filled_new_array(prev_op))) {
            return Result::make_error(
                "Encountered " + show(*it) +
                " without appropriate prefix "
                "instruction. Expected invoke or filled-new-array, got " +
                show(prev->insn));
          }
          if (!prev->insn->has_move_result()) {
            return Result::make_error("Encountered " + show(*it) +
                                      " without appropriate prefix "
                                      "instruction");
          }
        }

        if (opcode::is_a_move_result_pseudo(insn->opcode()) &&
            (!prev->insn->has_move_result_pseudo())) {
          return Result::make_error("Encountered " + show(*it) +
                                    " without appropriate prefix "
                                    "instruction");
        }
      }
      if (insn->has_move_result_pseudo()) {
        auto move_result = cfg.move_result_of(cfg_it);
        if (move_result.is_end() ||
            !opcode::is_a_move_result_pseudo(move_result->insn->opcode())) {
          return Result::make_error("Did not find move-result-pseudo after " +
                                    show(*it) + " in \n" + show(cfg));
        }
      }
    }
  }
  return check_uninitialized(method, relaxed_init_check);
}

/*
 * Sanity-check the structure of the positions for cfg format.
 */
Result check_positions_cfg(cfg::ControlFlowGraph& cfg) {
  UnorderedSet<DexPosition*> positions;
  auto iterable = cfg::InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->type != MFLOW_POSITION) {
      continue;
    }
    auto* pos = it->pos.get();
    if (!positions.insert(pos).second) {
      return Result::make_error("Duplicate position " + show(pos));
    }
  }

  UnorderedSet<DexPosition*> visited_parents;
  for (auto* pos : UnorderedIterable(positions)) {
    if (pos->parent == nullptr) {
      continue;
    }
    if (positions.count(pos->parent) == 0u) {
      return Result::make_error("Missing parent " + show(pos));
    }
    for (auto* p = pos; p != nullptr; p = p->parent) {
      if (!visited_parents.insert(p).second) {
        return Result::make_error("Cyclic parents around " + show(pos));
      }
    }
    visited_parents.clear();
  }
  return Result::Ok();
}

/*
 * For now, we only check if there are...
 * - mismatches in the monitor stack depth
 * - instructions that may throw in a synchronized region in a try-block without
 *   a catch-all.
 */
Result check_monitors(const DexMethod* method) {
  const auto* code = method->get_code();
  monitor_count::Analyzer monitor_analyzer(code->cfg());
  auto blocks = monitor_analyzer.get_monitor_mismatches();
  if (!blocks.empty()) {
    std::ostringstream out;
    out << "Monitor-stack mismatch (unverifiable code) in "
        << method->get_deobfuscated_name_or_empty() << " at blocks ";
    for (auto* b : blocks) {
      out << "(";
      for (auto* e : b->preds()) {
        auto count = monitor_analyzer.get_exit_state_at(e->src());
        count = monitor_analyzer.analyze_edge(e, count);
        if (!count.is_bottom()) {
          out << "B" << e->src()->id() << ":" << show(count) << " | ";
        }
      }
      auto count = monitor_analyzer.get_entry_state_at(b);
      out << ") ==> B" << b->id() << ":" << show(count) << ", ";
    }
    out << " in\n" + show(code->cfg());
    return Result::make_error(out.str());
  }

  auto sketchy_insns = monitor_analyzer.get_sketchy_instructions();
  UnorderedSet<cfg::Block*> sketchy_blocks;
  for (auto& it : sketchy_insns) {
    sketchy_blocks.insert(it.block());
  }
  unordered_erase_if(sketchy_blocks, [&](auto* b) {
    return !code->cfg().get_succ_edge_of_type(b, cfg::EDGE_THROW);
  });
  if (!sketchy_blocks.empty()) {
    std::ostringstream out;
    out << "Throwing instructions in a synchronized region in a try-block "
           "without a catch-all in "
        << method->get_deobfuscated_name_or_empty();
    bool first = true;
    for (auto& it : sketchy_insns) {
      if (sketchy_blocks.count(it.block()) == 0u) {
        continue;
      }
      if (first) {
        first = false;
      } else {
        out << " and ";
      }
      out << " at instruction B" << it.block()->id() << " '" << SHOW(it->insn)
          << "' @ " << std::hex << static_cast<const void*>(&*it.unwrap());
    }
    out << " in\n" + show(code->cfg());
    return Result::make_error(out.str());
  }
  return Result::Ok();
}

Result validate_no_private_virtual_method(const DexMethodRef* method) {
  if (method == nullptr || !method->is_def()) {
    // Forgive unresolved refs.
    return Result::Ok();
  }

  if (method->as_def()->is_virtual() && is_private(method->as_def())) {
    std::ostringstream out;
    out << "A method cannot be both private and virtual: "
        << show_deobfuscated(method);
    return Result::make_error(out.str());
  }

  return Result::Ok();
}

/**
 * Validate if the caller has the permit to call a method or access a field.
 */
template <typename DexMember>
void validate_access(const DexMethod* accessor, const DexMember* accessee) {
  if (type::can_access(accessor, accessee)) {
    return;
  }

  std::ostringstream out;
  out << "\nillegal access to "
      << (is_private(accessee)
              ? "private "
              : (is_package_private(accessee) ? "package-private "
                                              : "protected "))
      << show_deobfuscated(accessee) << "\n from "
      << show_deobfuscated(accessor);

  // If the accessee is external, we don't report the error, just log it.
  // TODO(fengliu): We should enforce the correctness when visiting external dex
  // members.
  if (accessee->is_external()) {
    TRACE(TYPE, 2, "%s", out.str().c_str());
    return;
  }

  throw TypeCheckingException(out.str());
}

void validate_invoke_polymorphic(const DexMethodRef* callee) {
  // callee must not be null, since this also acts as a precheck before any type
  // check.
  redex_assert(callee != nullptr);

  if (callee->is_def()) {
    // callee is a definition, we can match them exactly with what we want.
    if (callee->as_def() != method::java_lang_invoke_MethodHandle_invoke() &&
        callee->as_def() !=
            method::java_lang_invoke_MethodHandle_invokeExact()) {
      std::ostringstream out;
      out << "invoke-polymorphic: Callee must be either MethodHandle.invoke or "
             "MethodHandle.invokeExact, but found "
          << show_deobfuscated(callee);
      throw TypeCheckingException(out.str());
    }
    return;
  }

  // Fall back to manual check, since we don't know its full definition.
  const auto* arg_types = callee->get_proto()->get_args();

  // invoke-polymorphic works differently in terms of arg counts. The
  // invoked function's arguments are always the object reference followed
  // by an array of Objects (at least for now), but invoke-polymorphic
  // accepts individual elements of the array as its arguments.
  //   (invoke-polymorphic (v0 v1 v2)
  //     "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;")
  if (arg_types->size() != 1) {
    std::ostringstream out;
    out << "invoke-polymorphic: Arg count of " << show_deobfuscated(callee)
        << " is expected to be 1, but found " << arg_types->size();
    throw TypeCheckingException(out.str());
  }
  if (!type::is_array(arg_types->at(0))) {
    std::ostringstream out;
    out << "invoke-polymorphic: Arg type of " << show_deobfuscated(callee)
        << " is expected to be an array, but found " << arg_types->at(0);
    throw TypeCheckingException(out.str());
  }
}

void validate_invoke_super(const DexMethod* caller,
                           const DexMethodRef* callee) {
  if (callee == nullptr) {
    // Forgive unresolved refs.
    return;
  }

  if (callee->is_def() && !callee->as_def()->is_virtual()) {
    std::ostringstream out;
    out << "\nillegal invoke-super to non-virtual method "
        << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
    throw TypeCheckingException(out.str());
  }

  auto* callee_cls = type_class(callee->get_class());
  if ((callee_cls == nullptr) || !is_interface(callee_cls)) {
    return;
  }

  if (callee->is_def()) {
    const DexMethod* callee_method = callee->as_def();
    if (callee_method->is_external() && !is_abstract(callee_method)) {
      // An external interface method might a default one. Invoking the external
      // default method from a subclass using INVOKE_SUPER is permitted. This is
      // independent from Dex format 037 support.
      if (type::can_access(caller, callee_method)) {
        return;
      }
    }
  }

  std::ostringstream out;
  out << "\nillegal invoke-super to interface method defined in class "
      << show_deobfuscated(callee_cls)
      << "(note that this can happen when external framework SDKs are not "
         "passed to D8 as a classpath dependency; in such cases D8 may "
         "silently generate illegal invoke-supers to interface methods)";

  throw TypeCheckingException(out.str());
}

void validate_invoke_class_initializer(const DexMethodRef* callee_ref) {
  if (callee_ref == nullptr) {
    // Forgive unresolved refs.
    return;
  }
  if (method::is_clinit(callee_ref)) {
    std::ostringstream out;
    out << show_deobfuscated(callee_ref)
        << ": invoking a class initializer, which is forbidden";
    throw TypeCheckingException(out.str());
  }
}

void validate_invoke_direct_constructor(const DexMethodRef* callee_ref,
                                        IROpcode opcode) {
  if (callee_ref == nullptr) {
    // Forgive unresolved refs.
    return;
  }
  if (method::is_init(callee_ref) && opcode != OPCODE_INVOKE_DIRECT) {
    std::ostringstream out;
    out << show_deobfuscated(callee_ref)
        << ": invoking a constructor with an unexpected opcode (must be "
           "invoke-direct): "
        << opcode;
    throw TypeCheckingException(out.str());
  }
}

void validate_invoke_virtual(const DexMethod* caller,
                             const DexMethodRef* callee) {
  if (callee == nullptr || !callee->is_def()) {
    // Forgive unresolved refs.
    return;
  }

  if (callee->as_def()->is_virtual()) {
    // Make sure the callee is not known to be an interface.
    auto* callee_type = callee->as_def()->get_class();
    auto* callee_cls = type_class(callee_type);
    if (callee_cls != nullptr && is_interface(callee_cls)) {
      std::ostringstream out;
      out << "\nillegal invoke-virtual to interface type "
          << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
      throw TypeCheckingException(out.str());
    }
    // Otherwise okay.
    return;
  }

  std::ostringstream out;
  out << "\nillegal invoke-virtual to non-virtual method "
      << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
  throw TypeCheckingException(out.str());
}

void validate_invoke_direct(const DexMethod* caller,
                            const DexMethodRef* callee) {
  if (callee == nullptr || !callee->is_def()) {
    // Forgive unresolved refs.
    return;
  }

  if (!callee->as_def()->is_virtual() && !is_static(callee->as_def())) {
    return;
  }

  std::ostringstream out;
  out << "\nillegal invoke-direct to virtual or static method "
      << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
  throw TypeCheckingException(out.str());
}

void validate_invoke_static(const DexMethod* caller,
                            const DexMethodRef* callee) {
  if (callee == nullptr || !callee->is_def()) {
    // Forgive unresolved refs.
    return;
  }

  if (is_static(callee->as_def())) {
    return;
  }

  std::ostringstream out;
  out << "\nillegal invoke-static to non-static method "
      << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
  throw TypeCheckingException(out.str());
}

void validate_invoke_interface(const DexMethod* caller,
                               const DexMethodRef* callee) {
  if (callee == nullptr || !callee->is_def()) {
    // Forgive unresolved refs.
    return;
  }

  auto* callee_cls = type_class(callee->get_class());
  if ((callee_cls == nullptr) ||
      (is_interface(callee_cls) && callee->as_def()->is_virtual())) {
    return;
  }

  std::ostringstream out;
  out << "\nillegal invoke-interface to non-interface method "
      << show_deobfuscated(callee) << " in " << show_deobfuscated(caller);
  throw TypeCheckingException(out.str());
}

} // namespace

IRTypeChecker::~IRTypeChecker() {}

IRTypeChecker::IRTypeChecker(DexMethod* dex_method,
                             bool validate_access,
                             bool validate_invoke_super)
    : m_dex_method(dex_method),
      m_validate_access(validate_access),
      m_validate_invoke_super(validate_invoke_super),
      m_complete(false),
      m_verify_moves(false),
      m_check_no_overwrite_this(false),
      m_relaxed_init_check(false),
      m_good(true),
      m_what("OK") {}

void IRTypeChecker::run() {
  IRCode* code = m_dex_method->get_code();
  if (m_complete) {
    // The type checker can only be run once on any given method.
    return;
  }

  if (code == nullptr) {
    // If the method has no associated code, the type checking trivially
    // succeeds.
    m_complete = true;
    return;
  }

  if (auto result = validate_no_private_virtual_method(m_dex_method);
      result != Result::Ok()) {
    m_complete = true;
    m_good = false;
    m_what = result.error_message();
    return;
  }

  cfg::ScopedCFG cfg(code);

  auto result = check_structure(
      m_dex_method, *cfg, m_check_no_overwrite_this, m_relaxed_init_check);
  if (result != Result::Ok()) {
    m_complete = true;
    m_good = false;
    m_what = result.error_message();
    return;
  }

  // We then infer types for all the registers used in the method.
  // Check that the load-params match the signature.
  auto params_result = check_load_params(m_dex_method);
  if (params_result != Result::Ok()) {
    m_complete = true;
    m_good = false;
    m_what = params_result.error_message();
    return;
  }

  m_type_inference = std::make_unique<TypeInference>(*cfg);
  m_type_inference->run(m_dex_method);

  // Finally, we use the inferred types to type-check each instruction in the
  // method. We stop at the first type error encountered.
  auto& type_envs = m_type_inference->get_type_environments();
  for (const MethodItemEntry& mie : InstructionIterable(*cfg)) {
    IRInstruction* insn = mie.insn;
    try {
      auto it = type_envs.find(insn);
      always_assert_log(
          it != type_envs.end(), "%s in:\n%s", SHOW(mie), SHOW(*cfg));
      check_instruction(insn, &it->second);
    } catch (const TypeCheckingException& e) {
      m_good = false;
      m_error_insn = insn;
      std::ostringstream out;
      out << "Type error in method "
          << m_dex_method->get_deobfuscated_name_or_empty()
          << " at instruction '" << SHOW(insn) << "' @ " << std::hex
          << static_cast<const void*>(&mie) << " for " << e.what();
      m_what = out.str();
      m_complete = true;
      return;
    }
  }

  auto positions_result = check_positions_cfg(*cfg);

  if (positions_result != Result::Ok()) {
    m_complete = true;
    m_good = false;
    m_what = positions_result.error_message();
    return;
  }

  auto monitors_result = check_monitors(m_dex_method);
  if (monitors_result != Result::Ok()) {
    m_complete = true;
    m_good = false;
    m_what = monitors_result.error_message();
    return;
  }

  m_complete = true;

  if (traceEnabled(TYPE, 9)) {
    std::ostringstream out;
    m_type_inference->print(out);
    TRACE(TYPE, 9, "%s", out.str().c_str());
  }
}

void IRTypeChecker::assume_scalar(TypeEnvironment* state,
                                  reg_t reg,
                                  bool in_move) const {
  assume_type(state,
              reg,
              /* expected */ IRType::SCALAR,
              /* ignore_top */ in_move && !m_verify_moves);
}

void IRTypeChecker::assume_reference(TypeEnvironment* state,
                                     reg_t reg,
                                     bool in_move) const {
  assume_type(state,
              reg,
              /* expected */ IRType::REFERENCE,
              /* ignore_top */ in_move && !m_verify_moves);
}

void IRTypeChecker::assume_assignable(std::optional<const DexType*> from,
                                      const DexType* to) const {
  // There are some cases in type inference where we have to give up
  // and claim we don't know anything about a dex type. See
  // IRTypeCheckerTest.joinCommonBaseWithConflictingInterface, for
  // example - the last invoke of 'base.foo()' after the blocks join -
  // we no longer know anything about the type of the reference. It's
  // in such a case as that that we have to bail out here when the from
  // optional is empty.
  if (from && !check_is_assignable_from(*from, to, false)) {
    std::ostringstream out;
    out << ": " << *from << " is not assignable to " << to << "\n";
    print_type_hierarchy(out, *from);
    throw TypeCheckingException(out.str());
  }
}

namespace {

// Discouraged to throw in destructor, but is safe here.
struct Throw {
  std::ostringstream oss;

  explicit Throw() {}

  // NOLINTNEXTLINE(bugprone-exception-escape)
  [[noreturn]] ~Throw() noexcept(false) {
    throw TypeCheckingException(oss.str());
  }

  Throw(const Throw&) = delete;
  Throw(Throw&&) = delete;

  Throw& operator=(const Throw&) = delete;
  Throw& operator=(Throw&&) = delete;
};

template <typename Fn>
void assume_array(const DexType* array_type, const Fn& fn) {
  if (!type::is_array(array_type)) {
    Throw().oss << "Expected  " << *array_type << " to be an array type\n";
  }
  fn(type::make_array_component_type(array_type));
}

template <typename Fn>
void assume_array(TypeEnvironment* state, reg_t reg, const Fn& fn) {
  assume_type(state,
              reg,
              /* expected= */ IRType::REFERENCE,
              /* ignore_top= */ false);

  // TODO: Make sure we have state for every location.
  if (state->is_bottom()) {
    return;
  }

  auto dtype = state->get_dex_type(reg);
  if (!dtype) {
    return;
  }

  assume_array(*dtype, fn);
}

} // namespace

// This method performs type checking only: the type environment is not updated
// and the source registers of the instruction are checked against their
// expected types.
//
// Similarly, the various assume_* functions used throughout the code to check
// that the inferred type of a register matches with its expected type, as
// derived from the context.
void IRTypeChecker::check_instruction(IRInstruction* insn,
                                      TypeEnvironment* current_state) const {
  switch (insn->opcode()) {
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case OPCODE_NOP: {
    // IOPCODE_LOAD_PARAM_* instructions have been processed before the
    // analysis.
    break;
  }
  case OPCODE_MOVE: {
    assume_scalar(current_state, insn->src(0), /* in_move */ true);
    break;
  }
  case OPCODE_MOVE_OBJECT: {
    assume_reference(current_state, insn->src(0), /* in_move */ true);
    break;
  }
  case OPCODE_MOVE_WIDE: {
    assume_wide_scalar(current_state, insn->src(0));
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT: {
    assume_scalar(current_state, RESULT_REGISTER);
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT: {
    assume_reference(current_state, RESULT_REGISTER);
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE: {
    assume_wide_scalar(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN_VOID: {
    // We don't know where to grab the type of the just-caught exception.
    // Simply set to j.l.Throwable here.
    break;
  }
  case OPCODE_RETURN: {
    assume_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_RETURN_WIDE: {
    assume_wide_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_RETURN_OBJECT: {
    assume_reference(current_state, insn->src(0));
    auto dtype = current_state->get_dex_type(insn->src(0));
    auto* rtype = m_dex_method->get_proto()->get_rtype();
    // If the inferred type is a fallback, there's no point performing the
    // accurate type assignment checking.
    if (dtype && !is_inference_fallback_type(*dtype)) {
      // Return type checking is non-strict: it is allowed to return any
      // reference type when `rtype` is an interface.
      if (!check_is_assignable_from(*dtype, rtype, /*strict=*/false)) {
        std::ostringstream out;
        out << "Returning " << dtype << ", but expected from declaration "
            << rtype << "\n";
        print_type_hierarchy(out, *dtype);
        throw TypeCheckingException(out.str());
      }
    }
    break;
  }
  case IOPCODE_R_CONST:
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE: {
    break;
  }
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
  case OPCODE_ARRAY_LENGTH: {
    assume_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_NEW_INSTANCE: {
    break;
  }
  case OPCODE_NEW_ARRAY: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_FILLED_NEW_ARRAY: {
    const DexType* element_type =
        type::make_array_component_type(insn->get_type());
    // We assume that structural constraints on the bytecode are satisfied,
    // i.e., the type is indeed an array type.
    always_assert(element_type != nullptr);
    bool is_array_of_references = type::is_object(element_type);
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      if (is_array_of_references) {
        assume_reference(current_state, insn->src(i));
      } else {
        assume_scalar(current_state, insn->src(i));
      }
    }
    break;
  }
  case OPCODE_FILL_ARRAY_DATA: {
    break;
  }
  case OPCODE_THROW: {
    assume_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_GOTO: {
    break;
  }
  case OPCODE_SWITCH: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT: {
    assume_float(current_state, insn->src(0));
    assume_float(current_state, insn->src(1));
    break;
  }
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE: {
    assume_double(current_state, insn->src(0));
    assume_double(current_state, insn->src(1));
    break;
  }
  case OPCODE_CMP_LONG: {
    assume_long(current_state, insn->src(0));
    assume_long(current_state, insn->src(1));
    break;
  }
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE: {
    assume_comparable(current_state, insn->src(0), insn->src(1));
    break;
  }
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE: {
    assume_integer(current_state, insn->src(0));
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ: {
    assume_comparable_with_zero(current_state, insn->src(0));
    break;
  }
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_AGET: {
    assume_array(current_state, insn->src(0), [](const auto* e_type) {
      if (e_type != type::_int() && e_type != type::_float()) {
        Throw().oss << "Expected int or float array, got component type "
                    << *e_type;
      }
    });
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT: {
    assume_array(current_state, insn->src(0), [&insn](const auto* e_type) {
      const DexType* expected;
      switch (insn->opcode()) {
      case OPCODE_AGET_BOOLEAN:
        expected = type::_boolean();
        break;
      case OPCODE_AGET_BYTE:
        expected = type::_byte();
        break;
      case OPCODE_AGET_CHAR:
        expected = type::_char();
        break;
      case OPCODE_AGET_SHORT:
        expected = type::_short();
        break;
      default:
        not_reached();
      };
      if (e_type != expected) {
        Throw().oss << "Expected from opcode " << *expected
                    << " but got component type " << *e_type;
      }
    });
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_AGET_WIDE: {
    assume_array(current_state, insn->src(0), [](const auto* e_type) {
      if (!type::is_wide_type(e_type)) {
        Throw().oss << "Expected wide array, got component type " << *e_type;
      }
    });
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_AGET_OBJECT: {
    assume_array(current_state, insn->src(0), [](const auto* e_type) {
      if (!type::is_object(e_type)) {
        Throw().oss << "Expected reference array, got component type "
                    << *e_type;
      }
    });
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_APUT: {
    assume_scalar(current_state, insn->src(0));
    assume_array(current_state,
                 insn->src(1),
                 [&insn, &current_state](const auto* e_type) {
                   if (e_type != type::_int() && e_type != type::_float()) {
                     Throw().oss
                         << "Expected int or float array, got component type "
                         << *e_type;
                   }

                   // We cannot use DexType for the value as primitive types are
                   // not tracked in the DexTypeEnvironment.
                   if (e_type == type::_int()) {
                     assume_integer(current_state, insn->src(0));
                   } else {
                     // NOLINTNEXTLINE(bugprone-assert-side-effect)
                     redex_assert(e_type == type::_float());
                     assume_float(current_state, insn->src(0));
                   }
                 });
    assume_integer(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT: {
    assume_integer(current_state, insn->src(0));
    assume_array(current_state, insn->src(1), [&insn](const auto* e_type) {
      const DexType* expected;
      switch (insn->opcode()) {
      case OPCODE_APUT_BOOLEAN:
        expected = type::_boolean();
        break;
      case OPCODE_APUT_BYTE:
        expected = type::_byte();
        break;
      case OPCODE_APUT_CHAR:
        expected = type::_char();
        break;
      case OPCODE_APUT_SHORT:
        expected = type::_short();
        break;
      default:
        not_reached();
      };
      if (e_type != expected) {
        Throw().oss << "Expected from opcode " << *expected
                    << " but got component type " << *e_type;
      }
    });
    assume_integer(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_WIDE: {
    assume_wide_scalar(current_state, insn->src(0));
    assume_array(current_state,
                 insn->src(1),
                 [&insn, &current_state](const auto* e_type) {
                   if (!type::is_wide_type(e_type)) {
                     Throw().oss << "Expected wide array, got component type "
                                 << *e_type;
                   }

                   // We cannot use DexType for the value as primitive types are
                   // not tracked in the DexTypeEnvironment.
                   if (e_type == type::_long()) {
                     assume_long(current_state, insn->src(0));
                   } else {
                     // NOLINTNEXTLINE(bugprone-assert-side-effect)
                     redex_assert(e_type == type::_double());
                     assume_double(current_state, insn->src(0));
                   }
                 });
    assume_integer(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_OBJECT: {
    assume_reference(current_state, insn->src(0));
    assume_array(current_state, insn->src(1), [](const auto* e_type) {
      if (!type::is_object(e_type)) {
        Throw().oss << "Expected reference array, got component type "
                    << *e_type;
      }
      // Array stores are checked at runtime. Nothing else to do.
    });
    assume_integer(current_state, insn->src(2));
    break;
  }
  case OPCODE_IGET: {
    assume_reference(current_state, insn->src(0));
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(0)), f_cls);
    break;
  }
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE: {
    assume_reference(current_state, insn->src(0));
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(0)), f_cls);
    break;
  }
  case OPCODE_IGET_OBJECT: {
    assume_reference(current_state, insn->src(0));
    always_assert(insn->has_field());
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(0)), f_cls);
    break;
  }
  case OPCODE_IPUT: {
    const DexType* type = insn->get_field()->get_type();
    if (type::is_float(type)) {
      assume_float(current_state, insn->src(0));
    } else {
      assume_integer(current_state, insn->src(0));
    }
    assume_reference(current_state, insn->src(1));
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(1)), f_cls);
    break;
  }
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT: {
    assume_integer(current_state, insn->src(0));
    assume_reference(current_state, insn->src(1));
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(1)), f_cls);
    break;
  }
  case OPCODE_IPUT_WIDE: {
    assume_wide_scalar(current_state, insn->src(0));
    assume_reference(current_state, insn->src(1));
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(1)), f_cls);
    break;
  }
  case OPCODE_IPUT_OBJECT: {
    assume_reference(current_state, insn->src(0));
    assume_reference(current_state, insn->src(1));
    always_assert(insn->has_field());
    auto* const f_type = insn->get_field()->get_type();
    assume_assignable(current_state->get_dex_type(insn->src(0)), f_type);
    auto* const f_cls = insn->get_field()->get_class();
    assume_assignable(current_state->get_dex_type(insn->src(1)), f_cls);

    break;
  }
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT: {
    break;
  }
  case OPCODE_SPUT: {
    const DexType* type = insn->get_field()->get_type();
    if (type::is_float(type)) {
      assume_float(current_state, insn->src(0));
    } else {
      assume_integer(current_state, insn->src(0));
    }
    break;
  }
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_WIDE: {
    assume_wide_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_OBJECT: {
    assume_reference(current_state, insn->src(0));
    always_assert(insn->has_field());
    auto* const f_type = insn->get_field()->get_type();
    assume_assignable(current_state->get_dex_type(insn->src(0)), f_type);
    break;
  }
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE: {
    DexMethodRef* dex_method = insn->get_method();
    const auto* arg_types = dex_method->get_proto()->get_args();
    size_t expected_args =
        (insn->opcode() != OPCODE_INVOKE_STATIC ? 1 : 0) + arg_types->size();
    if (insn->opcode() == OPCODE_INVOKE_POLYMORPHIC) {
      validate_invoke_polymorphic(dex_method);
    } else if (insn->srcs_size() != expected_args) {
      std::ostringstream out;
      out << SHOW(insn) << ": argument count mismatch; " << "expected "
          << expected_args << ", " << "but found " << insn->srcs_size()
          << " instead";
      throw TypeCheckingException(out.str());
    }
    size_t src_idx{0};
    if (insn->opcode() != OPCODE_INVOKE_STATIC) {
      // The first argument is a reference to the object instance on which the
      // method is invoked.
      auto src = insn->src(src_idx++);
      assume_reference(current_state, src);
      assume_assignable(current_state->get_dex_type(src),
                        dex_method->get_class());
    }
    if (insn->opcode() == OPCODE_INVOKE_POLYMORPHIC) {
      redex_assert(arg_types->size() == 1);
      redex_assert(src_idx == 1);

      // Starting from the second argument, every argument to invoke-polymorphic
      // is an object. It is unclear whether invoke-polymorphic can be used to a
      // function that accepts an array of other types. Therefore, here we only
      // assume the argument is assignable to the element type of the array
      // argument.
      for (; src_idx < insn->srcs_size(); src_idx++) {
        auto src = insn->src(src_idx);
        assume_reference(current_state, src);
        assume_assignable(current_state->get_dex_type(src),
                          type::make_array_element_type(arg_types->at(0)));
      }
    } else {
      for (const DexType* arg_type : *arg_types) {
        if (type::is_object(arg_type)) {
          auto src = insn->src(src_idx++);
          assume_reference(current_state, src);
          assume_assignable(current_state->get_dex_type(src), arg_type);
          continue;
        }
        if (type::is_integral(arg_type)) {
          assume_integer(current_state, insn->src(src_idx++));
          continue;
        }
        if (type::is_long(arg_type)) {
          assume_long(current_state, insn->src(src_idx++));
          continue;
        }
        if (type::is_float(arg_type)) {
          assume_float(current_state, insn->src(src_idx++));
          continue;
        }
        always_assert(type::is_double(arg_type));
        assume_double(current_state, insn->src(src_idx++));
      }
    }
    if (m_validate_access) {
      auto* resolved = resolve_method_deprecated(
          dex_method, opcode_to_search(insn), m_dex_method);
      ::validate_access(m_dex_method, resolved);
    }
    if (m_validate_invoke_super && insn->opcode() == OPCODE_INVOKE_SUPER) {
      validate_invoke_super(m_dex_method, dex_method);
    } else if (insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      validate_invoke_virtual(m_dex_method, dex_method);
    } else if (insn->opcode() == OPCODE_INVOKE_DIRECT) {
      validate_invoke_direct(m_dex_method, dex_method);
    } else if (insn->opcode() == OPCODE_INVOKE_STATIC) {
      validate_invoke_static(m_dex_method, dex_method);
    } else if (insn->opcode() == OPCODE_INVOKE_INTERFACE) {
      validate_invoke_interface(m_dex_method, dex_method);
    }
    validate_invoke_class_initializer(dex_method);
    validate_invoke_direct_constructor(dex_method, insn->opcode());
    break;
  }
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG: {
    assume_long(current_state, insn->src(0));
    break;
  }
  case OPCODE_NEG_FLOAT: {
    assume_float(current_state, insn->src(0));
    break;
  }
  case OPCODE_NEG_DOUBLE: {
    assume_double(current_state, insn->src(0));
    break;
  }
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_LONG_TO_INT: {
    assume_long(current_state, insn->src(0));
    break;
  }
  case OPCODE_FLOAT_TO_INT: {
    assume_float(current_state, insn->src(0));
    break;
  }
  case OPCODE_DOUBLE_TO_INT: {
    assume_double(current_state, insn->src(0));
    break;
  }
  case OPCODE_INT_TO_LONG: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_FLOAT_TO_LONG: {
    assume_float(current_state, insn->src(0));
    break;
  }
  case OPCODE_DOUBLE_TO_LONG: {
    assume_double(current_state, insn->src(0));
    break;
  }
  case OPCODE_INT_TO_FLOAT: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_LONG_TO_FLOAT: {
    assume_long(current_state, insn->src(0));
    break;
  }
  case OPCODE_DOUBLE_TO_FLOAT: {
    assume_double(current_state, insn->src(0));
    break;
  }
  case OPCODE_INT_TO_DOUBLE: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case OPCODE_LONG_TO_DOUBLE: {
    assume_long(current_state, insn->src(0));
    break;
  }
  case OPCODE_FLOAT_TO_DOUBLE: {
    assume_float(current_state, insn->src(0));
    break;
  }
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT: {
    assume_integer(current_state, insn->src(0));
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG: {
    assume_long(current_state, insn->src(0));
    assume_long(current_state, insn->src(1));
    break;
  }
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG: {
    assume_long(current_state, insn->src(0));
    assume_integer(current_state, insn->src(1));
    break;
  }
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT: {
    assume_float(current_state, insn->src(0));
    assume_float(current_state, insn->src(1));
    break;
  }
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE: {
    assume_double(current_state, insn->src(0));
    assume_double(current_state, insn->src(1));
    break;
  }
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT: {
    assume_integer(current_state, insn->src(0));
    break;
  }
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
  case IOPCODE_WRITE_BARRIER: {
    break;
  }
  }
  if (insn->has_field() && m_validate_access) {
    auto search = opcode::is_an_sfield_op(insn->opcode())
                      ? FieldSearch::Static
                      : FieldSearch::Instance;
    auto* resolved = resolve_field(insn->get_field(), search);
    ::validate_access(m_dex_method, resolved);
    if (resolved != nullptr && opcode::is_an_iput(insn->opcode()) &&
        is_final(resolved)) {
      if (!method::is_init(m_dex_method) ||
          m_dex_method->get_class() != resolved->get_class()) {
        std::ostringstream out;
        out << "final instance field " << show_deobfuscated(resolved)
            << " may only be assigned in an <init> method of "
            << show_deobfuscated(resolved->get_class());
        throw TypeCheckingException(out.str());
      }
    }
  }
}

IRType IRTypeChecker::get_type(IRInstruction* insn, reg_t reg) const {
  check_completion();
  auto& type_envs = m_type_inference->get_type_environments();
  auto it = type_envs.find(insn);
  if (it == type_envs.end()) {
    // The instruction doesn't belong to this method. We treat this as
    // unreachable code and return BOTTOM.
    return IRType::BOTTOM;
  }
  return it->second.get_type(reg).element();
}

std::optional<const DexType*> IRTypeChecker::get_dex_type(IRInstruction* insn,
                                                          reg_t reg) const {
  check_completion();
  auto& type_envs = m_type_inference->get_type_environments();
  auto it = type_envs.find(insn);
  if (it == type_envs.end()) {
    // The instruction doesn't belong to this method. We treat this as
    // unreachable code and return BOTTOM.
    return nullptr;
  }
  return it->second.get_dex_type(reg);
}

std::ostream& operator<<(std::ostream& output, const IRTypeChecker& checker) {
  checker.m_type_inference->print(output);
  return output;
}

void IRTypeChecker::check_completion() const {
  always_assert_log(
      m_complete,
      "The type checker did not run on method %s.\n",
      m_dex_method->get_deobfuscated_name_or_empty_copy().c_str());
}

std::string IRTypeChecker::dump_annotated_cfg(DexMethod* method) const {
  cfg::ScopedCFG cfg{method->get_code()};

  TypeInference inf{method->get_code()->cfg()};
  inf.run(m_dex_method);

  return show_analysis<TypeEnvironment>(method->get_code()->cfg(), inf);
}

std::string IRTypeChecker::dump_annotated_cfg_reduced(DexMethod* method) const {
  return dump_annotated_cfg_reduced_impl(method, /* error_insn */ nullptr);
}

std::string IRTypeChecker::dump_annotated_cfg_on_error(
    DexMethod* method) const {
  return dump_annotated_cfg_reduced_impl(method, error_insn());
}

namespace {

constexpr const char* ERROR_MARKER = ">>>  ";

// `what()` is multi-line, so prefix every line to keep the whole message
// visually attached to the instruction it belongs to.
std::string marked_error_message(const std::string& what) {
  std::istringstream in(what);
  std::ostringstream out;
  std::string line;
  const char* separator = "";
  while (std::getline(in, line)) {
    out << separator << ERROR_MARKER << line;
    separator = "\n";
  }
  return out.str();
}

} // namespace

std::string IRTypeChecker::dump_annotated_cfg_reduced_impl(
    DexMethod* method, const IRInstruction* error_insn) const {
  cfg::ScopedCFG cfg{method->get_code()};

  TypeInference inf{method->get_code()->cfg()};
  inf.run(m_dex_method);

  std::string error_message;
  if (error_insn != nullptr) {
    error_message = marked_error_message("ERROR: " + what());
  }

  struct TypeInferenceReducedSpecial {
    TypeEnvironment cur;
    const TypeInference& iter;
    const IRInstruction* error_insn;
    const std::string& error_message;

    TypeInferenceReducedSpecial(const TypeInference& iter,
                                const IRInstruction* error_insn,
                                const std::string& error_message)
        : iter(iter), error_insn(error_insn), error_message(error_message) {}

    void add_reg(std::ostream& os, reg_t r) const {
      os << " v" << r << "=";
      auto type = cur.get_type(r);
      os << type << "/";
      auto dtype = cur.get_dex_type(r);
      if (dtype) {
        os << show(*dtype);
      } else {
        os << "T";
      }
    }

    // Entry addresses are noise when debugging a type error.
    std::string show_mie(const MethodItemEntry& mie) const {
      return error_insn == nullptr ? show(mie) : show_mie_plain(mie);
    }

    void mie_before(std::ostream& /* os */, const MethodItemEntry& /* mie */) {}
    void mie_after(std::ostream& os, const MethodItemEntry& mie) {
      if (mie.type != MFLOW_OPCODE) {
        return;
      }

      // Find inputs.
      if (mie.insn->srcs_size() != 0) {
        os << "     inputs:";
        for (reg_t r : mie.insn->srcs()) {
          add_reg(os, r);
        }
        os << "\n";
      }

      iter.analyze_instruction(mie.insn, &cur);
      cur.reduce();

      // Find outputs.
      if (mie.insn->has_dest()) {
        os << "     output:";
        add_reg(os, mie.insn->dest());
        os << "\n";
      }

      if (error_insn != nullptr && mie.insn == error_insn) {
        os << error_message << "\n";
      }
    }

    void start_block(std::ostream& os, cfg::Block* b) {
      cur = iter.get_entry_state_at(b);
      os << "entry state: " << cur << "\n";
    }
    void end_block(std::ostream& /* os */, cfg::Block* /* b */) {}
  };

  TypeInferenceReducedSpecial special(inf, error_insn, error_message);
  return show(method->get_code()->cfg(), special);
}
