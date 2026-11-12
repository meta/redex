/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveBuildersHelper.h"

#include <boost/regex.hpp> // NOLINT

#include "ControlFlow.h"
#include "Dataflow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "Show.h"
#include "Trace.h"

namespace {

const IRInstruction* NULL_INSN = nullptr;

void fields_mapping(const cfg::ControlFlowGraph& cfg,
                    const cfg::InstructionIterator& it,
                    FieldsRegs* fregs,
                    DexClass* builder) {
  always_assert(fregs != nullptr);
  always_assert(builder != nullptr);
  always_assert(it->type == MFLOW_OPCODE);

  const IRInstruction* insn = it->insn;

  if (insn->opcode() == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT &&
      cfg.primary_instruction_of_move_result(it)->insn->opcode() ==
          OPCODE_NEW_INSTANCE &&
      cfg.primary_instruction_of_move_result(it)->insn->get_type() ==
          builder->get_type()) {
    // Set fields to UNDEFINED if new builder instance.
    for (auto& pair : UnorderedIterable(fregs->field_to_reg)) {
      fregs->field_to_reg[pair.first] = FieldOrRegStatus::UNDEFINED;
      fregs->field_to_iput_insns[pair.first].clear();
    }
  }

  // Check if the register that used to hold the field's value is overwritten.
  if (insn->has_dest()) {
    const int current_dest = static_cast<int>(insn->dest());

    for (const auto& pair : UnorderedIterable(fregs->field_to_reg)) {
      if (pair.second == current_dest ||
          (insn->dest_is_wide() && pair.second == current_dest + 1)) {
        fregs->field_to_reg[pair.first] = FieldOrRegStatus::OVERWRITTEN;
      }
    }
  }

  if (opcode::is_an_iput(insn->opcode())) {
    auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);

    if (field != nullptr && field->get_class() == builder->get_type()) {
      reg_t current = insn->src(0);
      fregs->field_to_reg[field] = static_cast<int>(current);
      fregs->field_to_iput_insns[field].clear();
      fregs->field_to_iput_insns[field].emplace(insn);
    }
  }
}

/**
 * Returns for every instruction, field value:
 * - a register: representing the register that stores the field's value
 * - UNDEFINED: not defined yet.
 * - DIFFERENT: no unique register.
 * - OVERWRITTEN: register no longer holds the value.
 */
std::unique_ptr<UnorderedMap<IRInstruction*, FieldsRegs>> fields_setters(
    const cfg::ControlFlowGraph& cfg,
    const std::vector<cfg::Block*>& blocks,
    DexClass* builder) {

  std::function<void(cfg::InstructionIterator, FieldsRegs*)> trans =
      [&](const cfg::InstructionIterator& it, FieldsRegs* fregs) {
        fields_mapping(cfg, it, fregs, builder);
      };

  return forwards_dataflow(cfg.entry_block(), blocks, FieldsRegs(builder),
                           trans);
}

IROpcode get_move_opcode(const IRInstruction* insn) {
  always_assert(insn != nullptr);
  always_assert(opcode::is_an_iget(insn->opcode()));

  if (insn->opcode() == OPCODE_IGET_WIDE) {
    return OPCODE_MOVE_WIDE;
  } else if (insn->opcode() == OPCODE_IGET_OBJECT) {
    return OPCODE_MOVE_OBJECT;
  }

  return OPCODE_MOVE;
}

IRInstruction* construct_move_instr(reg_t dest_reg,
                                    reg_t src_reg,
                                    IROpcode move_opcode) {
  IRInstruction* insn = new IRInstruction(move_opcode);
  insn->set_dest(dest_reg);
  insn->set_src(0, src_reg);
  return insn;
}

IRInstruction* construct_null_instr(reg_t reg, IROpcode move_opcode) {
  IRInstruction* insn;
  if (move_opcode == OPCODE_MOVE_WIDE) {
    insn = new IRInstruction(OPCODE_CONST_WIDE);
  } else {
    insn = new IRInstruction(OPCODE_CONST);
  }
  insn->set_dest(reg);
  insn->set_literal(0);
  return insn;
}

/**
 * Adds instructions that initializes registers with null.
 */
void null_initializations(
    cfg::ControlFlowGraph& cfg,
    const std::vector<std::pair<reg_t, IROpcode>>& null_regs) {
  auto* block = cfg.entry_block();
  for (const auto& null_reg_info : null_regs) {
    reg_t null_reg = null_reg_info.first;
    IROpcode move_opcode = null_reg_info.second;
    cfg.insert_before(block->to_cfg_instruction_iterator(
                          block->get_first_non_param_loading_insn()),
                      construct_null_instr(null_reg, move_opcode));
  }
}

void add_instr(cfg::ControlFlowGraph& cfg,
               const IRInstruction* position,
               IRInstruction* new_insn) {
  always_assert(position != nullptr);
  always_assert(new_insn != nullptr);

  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (insn == position) {
      cfg.insert_before(it, new_insn);
      return;
    }
  }
  not_reached_log("insert position not found!");
}

using MoveList = UnorderedMap<const IRInstruction*, IRInstruction*>;

void method_updates(DexMethod* method,
                    const UnorderedBag<IRInstruction*>& deletes,
                    const MoveList& move_list) {
  always_assert(method != nullptr);

  auto* code = method->get_code();
  auto& cfg = code->cfg();

  // This will basically replace an iput / iget instruction
  // with a move (giving the instruction will be removed later).
  //
  // Example:
  //  iput v0, object // field -> move new_reg, v0
  //  iget v0, object // field -> move v0, new_reg
  for (const auto& move_elem : UnorderedIterable(move_list)) {
    const IRInstruction* position = move_elem.first;
    IRInstruction* insn = move_elem.second;
    add_instr(cfg, position, insn);
  }

  for (const auto& insn : UnorderedIterable(deletes)) {
    auto it = cfg.find_insn(insn);
    cfg.remove_insn(it);
  }
}

/**
 * Giving a list of setters and a map with instruction replacements,
 * will return an already allocated new register, in case one of the
 * setters already has a replacement defined. Otherwise, it returns
 * UNDEFINED.
 */
int64_t get_new_reg_if_already_allocated(
    const UnorderedSet<const IRInstruction*>& iput_insns,
    MoveList& move_replacements) {

  int64_t new_reg = FieldOrRegStatus::UNDEFINED;
  for (const auto& iput_insn : UnorderedIterable(iput_insns)) {
    if (iput_insn != NULL_INSN) {
      if (move_replacements.find(iput_insn) != move_replacements.end()) {
        if (new_reg == FieldOrRegStatus::UNDEFINED) {
          new_reg = move_replacements[iput_insn]->dest();
        } else {
          always_assert(new_reg == move_replacements[iput_insn]->dest());
        }
      }
    }
  }

  return new_reg;
}

/**
 * Check builder's constructor does a small amount of work
 *  - instantiates the parent class (Object)
 *  - returns
 */
bool is_trivial_builder_constructor(DexMethod* method) {
  always_assert(method != nullptr);

  auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  auto& cfg = code->cfg();

  if (!method::is_constructor(method)) {
    return false;
  }

  auto ii = InstructionIterable(cfg);
  auto it = ii.begin();
  if (it->insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT) {
    return false;
  }
  ++it;

  if (it->insn->opcode() != OPCODE_INVOKE_DIRECT) {
    return false;
  } else {
    auto* invoked =
        resolve_method_deprecated(it->insn->get_method(), MethodSearch::Direct);
    if (invoked == nullptr || !method::is_constructor(invoked)) {
      return false;
    }
  }

  ++it;
  if (it->insn->opcode() != OPCODE_RETURN_VOID) {
    return false;
  }

  ++it;
  return it == ii.end();
}

UnorderedSet<DexMethod*> get_non_trivial_init_methods(IRCode* code,
                                                      const DexType* type) {
  always_assert(code != nullptr);
  always_assert(type != nullptr);
  auto& cfg = code->cfg();

  UnorderedSet<DexMethod*> methods;
  for (auto const& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      auto* invoked =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
      if (invoked != nullptr && invoked->get_class() == type) {
        if (method::is_constructor(invoked) &&
            !is_trivial_builder_constructor(invoked)) {
          methods.insert(invoked);
        }
      }
    }
  }

  return methods;
}

UnorderedSet<IRInstruction*> get_super_class_initializations(
    DexMethod* method, DexType* parent_type) {
  always_assert(method != nullptr);
  always_assert(parent_type != nullptr);

  UnorderedSet<IRInstruction*> insns;
  auto* code = method->get_code();
  if (code == nullptr) {
    return insns;
  }
  auto& cfg = code->cfg();

  for (auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      auto* invoked =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
      if (invoked != nullptr && invoked->get_class() == parent_type &&
          method::is_init(invoked)) {
        insns.emplace(insn);
      }
    }
  }

  return insns;
}

bool has_super_class_initializations(DexMethod* method, DexType* parent_type) {
  return !get_super_class_initializations(method, parent_type).empty();
}

void remove_super_class_calls(DexMethod* method, DexType* parent_type) {
  UnorderedSet<IRInstruction*> to_delete =
      get_super_class_initializations(method, parent_type);
  auto* code = method->get_code();
  if (code == nullptr) {
    return;
  }
  auto& cfg = code->cfg();

  for (const auto& insn : UnorderedIterable(to_delete)) {
    auto it = cfg.find_insn(insn);
    cfg.remove_insn(it);
  }
}

/**
 * Gathers all `MOVE` instructions that operate on a builder.
 */
UnorderedBag<IRInstruction*> gather_move_builders_insn(
    cfg::ControlFlowGraph& cfg,
    const std::vector<cfg::Block*>& blocks,
    DexType* builder) {
  UnorderedBag<IRInstruction*> insns;

  reg_t regs_size = cfg.get_registers_size();
  auto tainted_map = get_tainted_regs(cfg, regs_size, blocks, builder);

  for (auto it : UnorderedIterable(*tainted_map)) {
    auto* insn = it.first;
    auto tainted = it.second.bits();

    if (opcode::is_a_move(insn->opcode())) {
      if (tainted[insn->src(0)]) {
        insns.insert(insn);
      }
    }
  }

  return insns;
}

/**
 * Keeps tracks of registers that are going to be used for undefined fields
 * depending on the type of field: wide, primitive etc.
 */
class ZeroRegs {
 public:
  bool has(DexType* type) { return get(type) != FieldOrRegStatus::UNDEFINED; }

  reg_t get(DexType* type, reg_t default_value) {
    if (!has(type)) {
      set(type, default_value);
    }
    return get(type);
  }

 private:
  int m_zero_reg_object{FieldOrRegStatus::UNDEFINED};
  int m_zero_reg_int{FieldOrRegStatus::UNDEFINED};
  int m_zero_reg_float{FieldOrRegStatus::UNDEFINED};
  int m_zero_reg_long{FieldOrRegStatus::UNDEFINED};
  int m_zero_reg_double{FieldOrRegStatus::UNDEFINED};

  int get(DexType* type) {
    const auto* name = type->get_name()->c_str();
    switch (name[0]) {
    case 'Z':
    case 'B':
    case 'S':
    case 'C':
    case 'I':
      return m_zero_reg_int;
    case 'J':
      return m_zero_reg_long;
    case 'F':
      return m_zero_reg_float;
    case 'D':
      return m_zero_reg_double;
    case 'L':
    case '[':
      return m_zero_reg_object;
    default:
      not_reached();
    }
  }

  void set(DexType* type, reg_t value) {
    const auto* name = type->get_name()->c_str();
    switch (name[0]) {
    case 'Z':
    case 'B':
    case 'S':
    case 'C':
    case 'I':
      m_zero_reg_int = static_cast<int>(value);
      return;
    case 'J':
      m_zero_reg_long = static_cast<int>(value);
      return;
    case 'F':
      m_zero_reg_float = static_cast<int>(value);
      return;
    case 'D':
      m_zero_reg_double = static_cast<int>(value);
      return;
    case 'L':
    case '[':
      m_zero_reg_object = static_cast<int>(value);
      return;
    default:
      not_reached();
    }
  }
};

bool remove_builder(DexMethod* method, DexClass* builder) {
  always_assert(method != nullptr);
  always_assert(builder != nullptr);

  auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  auto& cfg = code->cfg();

  const auto& blocks = cfg.blocks_reverse_post_deprecated();

  auto fields_in = fields_setters(cfg, blocks, builder);

  static const auto* init = DexString::make_string("<init>");
  reg_t regs_size = cfg.get_registers_size();
  reg_t next_available_reg = regs_size;
  reg_t extra_regs = 0;
  size_t num_builders = 0;
  std::vector<std::pair<reg_t, IROpcode>> extra_null_regs;
  ZeroRegs undef_fields_regs;

  // Instructions where the builder gets moved to a different
  // register need to be also removed (at the end).
  UnorderedBag<IRInstruction*> deletes =
      gather_move_builders_insn(cfg, blocks, builder->get_type());
  MoveList move_replacements;
  UnorderedSet<IRInstruction*> update_list;

  for (const auto& block : blocks) {
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;
      IROpcode opcode = insn->opcode();

      auto& fields_in_insn = fields_in->at(it->insn);

      if (opcode::is_an_iput(opcode)) {
        auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
        if (field != nullptr && field->get_class() == builder->get_type()) {
          deletes.insert(insn);
          continue;
        }

      } else if (opcode::is_an_iget(opcode)) {
        auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
        if (field == nullptr) {
          continue;
        }
        if (field->get_class() == builder->get_type()) {
          IROpcode move_opcode = get_move_opcode(insn);
          bool is_wide = move_opcode == OPCODE_MOVE_WIDE;

          if (fields_in_insn.field_to_reg[field] ==
                  FieldOrRegStatus::DIFFERENT ||
              fields_in_insn.field_to_reg[field] ==
                  FieldOrRegStatus::OVERWRITTEN) {

            const auto& iput_insns = fields_in_insn.field_to_iput_insns[field];
            always_assert(!iput_insns.empty());

            int64_t new_reg =
                get_new_reg_if_already_allocated(iput_insns, move_replacements);
            if (new_reg == FieldOrRegStatus::UNDEFINED) {
              // Allocating a new register since one was not allocated.
              new_reg = next_available_reg + extra_regs;
              extra_regs += is_wide ? 2 : 1;
            }

            for (const auto& iput_insn : UnorderedIterable(iput_insns)) {
              if (iput_insn != NULL_INSN) {
                if (move_replacements.find(iput_insn) !=
                    move_replacements.end()) {
                  always_assert(new_reg ==
                                move_replacements[iput_insn]->dest());
                } else {
                  // Adding a move for each of the setters:
                  //   iput v1, object // field -> move new_reg, v1
                  move_replacements[iput_insn] =
                      construct_move_instr(static_cast<reg_t>(new_reg),
                                           iput_insn->src(0), move_opcode);
                }
              } else {
                // Initializes the register since the field might be
                // uninitialized.
                extra_null_regs.emplace_back(new_reg, move_opcode);
              }
            }

            // Adding a move for the getter:
            //   iget v2, object // field -> move v2, new_reg
            move_replacements[insn] = construct_move_instr(
                cfg.move_result_of(block->to_cfg_instruction_iterator(it))
                    ->insn->dest(),
                static_cast<reg_t>(new_reg), move_opcode);

          } else if (fields_in_insn.field_to_reg[field] ==
                     FieldOrRegStatus::UNDEFINED) {

            // Initializing the field with null.
            bool has_null_reg = undef_fields_regs.has(field->get_type());
            reg_t new_null_reg = undef_fields_regs.get(
                field->get_type(), next_available_reg + extra_regs);

            move_replacements[insn] = construct_move_instr(
                cfg.move_result_of(block->to_cfg_instruction_iterator(it))
                    ->insn->dest(),
                new_null_reg, move_opcode);

            if (!has_null_reg) {
              extra_null_regs.emplace_back(new_null_reg, move_opcode);
              extra_regs += is_wide ? 2 : 1;
            }
          } else {
            // If we got here, the field is held in a register.

            // Get instruction that sets the field.
            const auto& iput_insns = fields_in_insn.field_to_iput_insns[field];
            if (iput_insns.empty()) {
              return false;
            }

            const IRInstruction* iput_insn = only(iput_insns);

            // Check if we already have a value for it.
            if (move_replacements.find(iput_insn) != move_replacements.end()) {
              // Get the actual value.
              IRInstruction* new_insn = move_replacements[iput_insn];
              reg_t new_reg = new_insn->dest();
              move_replacements[insn] = construct_move_instr(
                  cfg.move_result_of(block->to_cfg_instruction_iterator(it))
                      ->insn->dest(),
                  new_reg, move_opcode);

            } else {
              // We can reuse the existing reg, so will have only 1 move.
              //
              // In case this is a parameter reg, it needs to be updated.
              if (iput_insn->src(0) >= next_available_reg) {
                update_list.emplace(insn);
              }
              move_replacements[insn] = construct_move_instr(
                  cfg.move_result_of(block->to_cfg_instruction_iterator(it))
                      ->insn->dest(),
                  iput_insn->src(0), move_opcode);
            }
          }

          deletes.insert(insn);
          continue;
        }

      } else if (opcode == OPCODE_NEW_INSTANCE || opcode == OPCODE_CHECK_CAST) {
        const DexType* cls = insn->get_type();
        if (type_class(cls) == builder) {
          if (opcode == OPCODE_NEW_INSTANCE) {
            num_builders++;
          }

          // Safely avoiding the case where multiple builders are initialized.
          if (num_builders > 1) {
            return false;
          }

          deletes.insert(insn);
          continue;
        }

      } else if (opcode::is_an_invoke(opcode)) {
        auto* invoked = insn->get_method();
        if (invoked->get_class() == builder->get_type() &&
            invoked->get_name() == init) {
          deletes.insert(insn);
          continue;
        }
      }
    }
  }

  cfg.set_registers_size(next_available_reg + extra_regs);

  null_initializations(cfg, extra_null_regs);

  method_updates(method, deletes, move_replacements);
  return true;
}

bool has_only_argument(DexMethod* method, const DexType* type) {
  DexProto* proto = method->get_proto();
  const auto& args = *proto->get_args();
  return args.size() == 1 && args.at(0) == type;
}

/**
 * Checks if the registers which hold the arguments for the given method
 * are used as source for any operation except `iget-*`
 */
bool params_change_regs(DexMethod* method) {
  DexProto* proto = method->get_proto();
  auto* args = proto->get_args();

  auto* code = method->get_code();
  always_assert(code);
  auto& cfg = code->cfg();
  const auto& blocks = cfg.blocks_reverse_post_deprecated();
  reg_t regs_size = cfg.get_registers_size();
  const auto& param_insns = InstructionIterable(cfg.get_param_instructions());
  always_assert(!is_static(method));
  // Skip the `this` param
  auto param_it = std::next(param_insns.begin());

  for (const DexType* arg : *args) {
    std::function<void(cfg::InstructionIterator, TaintedRegs*)> trans =
        [&](const cfg::InstructionIterator& it, TaintedRegs* tregs) {
          if (!opcode::is_a_load_param(it->insn->opcode())) {
            transfer_object_reach(arg, regs_size, it->insn, tregs->m_reg_set);
          }
        };

    auto tainted = TaintedRegs(static_cast<int>(regs_size + 1));
    always_assert(param_it != param_insns.end());
    auto arg_reg = (param_it++)->insn->dest();
    tainted.m_reg_set[arg_reg] = true;

    auto taint_map =
        forwards_dataflow(cfg.entry_block(), blocks, tainted, trans);
    for (auto it : UnorderedIterable(*taint_map)) {
      auto* insn = it.first;
      auto insn_tainted = it.second.bits();
      auto op = insn->opcode();

      if (opcode::is_a_load_param(op)) {
        continue;
      }

      if (opcode::is_an_iget(op)) {
        DexField* field =
            resolve_field(insn->get_field(), FieldSearch::Instance);
        if ((field != nullptr) && field->get_class() == arg) {
          continue;
        }
      }

      if (insn->has_dest() && insn_tainted[insn->dest()]) {
        return true;
      }
      for (size_t index = 0; index < insn->srcs_size(); ++index) {
        if (insn_tainted[insn->src(index)]) {
          return true;
        }
      }
    }
  }

  return false;
}

/**
 *  Creates a DexProto starting from the ifields of the class.
 *  Example: (field1_type, field2_type ...)V;
 */
DexProto* make_proto_for(DexClass* cls) {
  const auto& fields = cls->get_ifields();

  DexTypeList::ContainerType dfields;
  for (const DexField* field : fields) {
    dfields.push_back(field->get_type());
  }

  auto* fields_list = DexTypeList::make_type_list(std::move(dfields));
  return DexProto::make_proto(type::_void(), fields_list);
}

/**
 * Generate load params instructions for a non-static method with
 * the `field` arguments.
 *
 * At the same time, update field to register mapping.
 */
std::vector<IRInstruction*> generate_load_params(
    const std::vector<DexField*>& fields,
    uint32_t& params_reg_start,
    UnorderedMap<DexField*, uint32_t>& field_to_reg) {

  std::vector<IRInstruction*> load_params;

  // Load current instance.
  IRInstruction* insn = new IRInstruction(IOPCODE_LOAD_PARAM_OBJECT);
  insn->set_dest(params_reg_start++);
  load_params.push_back(insn);

  for (DexField* field : fields) {
    IROpcode op;
    if (type::is_wide_type(field->get_type())) {
      op = IOPCODE_LOAD_PARAM_WIDE;
    } else {
      op = type::is_primitive(field->get_type()) ? IOPCODE_LOAD_PARAM
                                                 : IOPCODE_LOAD_PARAM_OBJECT;
    }

    insn = new IRInstruction(op);
    insn->set_dest(params_reg_start);
    field_to_reg[field] = params_reg_start;
    params_reg_start += type::is_wide_type(field->get_type()) ? 2 : 1;
    load_params.push_back(insn);
  }

  return load_params;
}

/**
 * Given a method that takes cls as an argument, creates a new method
 * that takes cls's fields as arguments.
 */
DexMethod* create_fields_constr(DexMethod* method, DexClass* cls) {
  const auto* init = DexString::get_string("<init>");
  auto* void_fields = make_proto_for(cls);
  DexMethod* fields_constr =
      DexMethod::make_method(method->get_class(), init, void_fields)
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);

  auto* code = method->get_code();
  always_assert(code);
  auto& cfg = code->cfg();
  uint32_t regs_size = cfg.get_registers_size();
  const auto& fields = cls->get_ifields();
  UnorderedMap<DexField*, uint32_t> field_to_reg;

  std::unique_ptr<IRCode> new_code = std::make_unique<IRCode>(*code);
  always_assert(new_code->cfg_built());
  auto& new_cfg = new_code->cfg();

  // Non-input registers for the method are all registers except the
  // 'this' register and the arguments (which in this case is just 1)
  uint32_t new_regs_size = regs_size - 2;
  std::vector<IRInstruction*> load_params =
      generate_load_params(fields, new_regs_size, field_to_reg);
  new_cfg.set_registers_size(new_regs_size);

  std::vector<IRList::iterator> to_delete;
  UnorderedMap<IRInstruction*, IRInstruction*> to_replace;
  auto ii = InstructionIterable(new_cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    IRInstruction* insn = it->insn;

    // Delete old parameter loads.
    if (opcode::is_a_load_param(insn->opcode())) {
      to_delete.emplace_back(it.unwrap());
      continue;
    }

    if (opcode::is_an_iget(insn->opcode())) {
      DexField* field = resolve_field(insn->get_field(), FieldSearch::Instance);
      if (field->get_class() == cls->get_type()) {

        // Replace `iget <v_dest>, <v_builder>` with `move <v_dest>, <v_field>`
        uint32_t current_reg = new_cfg.move_result_of(it)->insn->dest();
        IROpcode move_opcode = get_move_opcode(insn);
        auto* move = new IRInstruction(move_opcode);
        move->set_src(0, field_to_reg[field]);
        move->set_dest(current_reg);
        to_replace.emplace(insn, move);
      }
    }
  }

  new_cfg.push_front(new_cfg.entry_block(), load_params);
  for (const auto& it : UnorderedIterable(to_replace)) {
    new_cfg.replace_insn(new_cfg.find_insn(it.first), it.second);
  }
  for (const auto& it : to_delete) {
    auto cfg_it = new_cfg.find_insn(it->insn);
    new_cfg.remove_insn(cfg_it);
  }

  fields_constr->set_code(std::move(new_code));
  type_class(method->get_class())->add_method(fields_constr);
  return fields_constr;
}

DexMethodRef* get_fields_constr_if_exists(DexMethod* method, DexClass* cls) {
  DexType* type = method->get_class();
  auto* void_fields = make_proto_for(cls);
  const auto* init = DexString::get_string("<init>");
  return DexMethod::get_method(type, init, void_fields);
}

DexMethod* get_fields_constr(DexMethod* method, DexClass* cls) {
  DexMethodRef* fields_constr = get_fields_constr_if_exists(method, cls);
  if ((fields_constr == nullptr) || !fields_constr->is_def()) {
    return create_fields_constr(method, cls);
  }

  return fields_constr->as_def();
}

std::vector<cfg::InstructionIterator> get_invokes_for_method(
    cfg::ControlFlowGraph& cfg, DexMethod* method) {
  std::vector<cfg::InstructionIterator> fms;
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      auto* invoked = insn->get_method();
      auto* def = resolve_method_deprecated(invoked, MethodSearch::Any);
      if (def != nullptr) {
        invoked = def;
      }

      if (invoked == method) {
        fms.emplace_back(it);
      }
    }
  }

  return fms;
}

/**
 * For the cases where the buildee accepts the builder as the only argument, we
 * create a new constructor, that will take all the builder's fields as
 * arguments.
 */
bool update_buildee_constructor(DexMethod* method, DexClass* builder) {
  DexType* buildee = get_buildee(builder->get_type());

  DexMethodRef* buildee_constr_ref = DexMethod::get_method(
      buildee,
      DexString::make_string("<init>"),
      DexProto::make_proto(type::_void(),
                           DexTypeList::make_type_list({builder->get_type()})));
  if (buildee_constr_ref == nullptr) {
    // Nothing to search for.
    return true;
  }
  DexMethod* buildee_constr = buildee_constr_ref->as_def();
  if (buildee_constr == nullptr) {
    return true;
  }

  // Extra conservative: We expect the constructor to do minimum work.
  if (params_change_regs(buildee_constr)) {
    return false;
  }

  auto* code = method->get_code();
  always_assert(code);
  auto& cfg = code->cfg();
  std::vector<cfg::InstructionIterator> buildee_constr_calls =
      get_invokes_for_method(cfg, buildee_constr);
  if (!buildee_constr_calls.empty()) {

    DexMethod* fields_constr = get_fields_constr(buildee_constr, builder);
    if (fields_constr == nullptr) {
      return false;
    }

    for (const auto& it : buildee_constr_calls) {
      IRInstruction* insn = it->insn;
      uint32_t builder_reg = insn->src(1);
      uint32_t regs_size = cfg.get_registers_size();
      uint32_t new_regs_size = regs_size;

      auto fields = builder->get_ifields();
      insn->set_method(fields_constr);
      // 'Make room' for the reg arguments.
      insn->set_srcs_size(fields.size() + 1);

      // Loading each of the fields before passing them to the method.
      // `invoke-direct {v_class, v_builder}` ->
      //    `iget v_field_1, v_builder
      //    iget v_field_2, v_builder
      //    ....
      //    invoke_direct {v_class, v_field_1, v_field_2, ...}`
      uint32_t index = 1;
      for (DexField* field : fields) {
        auto* new_insn =
            new IRInstruction(opcode::iget_opcode_for_field(field));
        new_insn->set_src(0, builder_reg);
        new_insn->set_field(field);
        cfg.insert_before(it, new_insn);
        auto* move_result_pseudo =
            new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
        move_result_pseudo->set_dest(new_regs_size);
        cfg.insert_before(it, move_result_pseudo);
        insn->set_src(index++, new_regs_size);
        new_regs_size += type::is_wide_type(field->get_type()) ? 2 : 1;
      }

      cfg.set_registers_size(new_regs_size);
    }
  }

  return true;
}

} // namespace

///////////////////////////////////////////////

void TaintedRegs::meet(const TaintedRegs& that) { m_reg_set |= that.m_reg_set; }

bool TaintedRegs::operator==(const TaintedRegs& that) const {
  return m_reg_set == that.m_reg_set;
}

bool TaintedRegs::operator!=(const TaintedRegs& that) const {
  return !(*this == that);
}

void FieldsRegs::meet(const FieldsRegs& that) {
  for (const auto& pair : UnorderedIterable(field_to_reg)) {
    if (pair.second == FieldOrRegStatus::DEFAULT) {
      field_to_reg[pair.first] = that.field_to_reg.at(pair.first);
      field_to_iput_insns[pair.first] = that.field_to_iput_insns.at(pair.first);
    } else if (that.field_to_reg.at(pair.first) == FieldOrRegStatus::DEFAULT) {
      continue;
    } else {
      if (pair.second == FieldOrRegStatus::UNDEFINED ||
          that.field_to_reg.at(pair.first) == FieldOrRegStatus::UNDEFINED) {
        field_to_iput_insns[pair.first].insert(NULL_INSN);
      }

      field_to_reg[pair.first] = FieldOrRegStatus::DIFFERENT;
      insert_unordered_iterable(field_to_iput_insns[pair.first],
                                that.field_to_iput_insns.at(pair.first));
    }
  }
}

bool FieldsRegs::operator==(const FieldsRegs& that) const {
  return field_to_reg == that.field_to_reg &&
         field_to_iput_insns == that.field_to_iput_insns;
}

bool FieldsRegs::operator!=(const FieldsRegs& that) const {
  return !(*this == that);
}

void transfer_object_reach(const DexType* obj,
                           uint32_t regs_size,
                           const IRInstruction* insn,
                           RegSet& regs) {
  always_assert(obj != nullptr);
  always_assert(insn != nullptr);

  auto op = insn->opcode();
  if (opcode::is_a_move(op)) {
    regs[insn->dest()] = regs[insn->src(0)];
  } else if (opcode::is_a_move_result(op)) {
    regs[insn->dest()] = regs[regs_size];
  } else if (opcode::writes_result_register(op)) {
    if (opcode::is_an_invoke(op)) {
      auto* invoked = insn->get_method();
      auto* def = resolve_method_deprecated(invoked, MethodSearch::Any);
      if (def != nullptr) {
        invoked = def;
      }

      if (invoked->get_proto()->get_rtype() == obj) {
        regs[regs_size] = true;
        return;
      }
    }
    regs[regs_size] = false;
  } else if (static_cast<int>(insn->has_dest()) != 0) {
    regs[insn->dest()] = false;
  }
}

bool tainted_reg_escapes(
    const DexType* ty,
    DexMethod* method,
    const UnorderedMap<IRInstruction*, TaintedRegs>& taint_map,
    bool enable_buildee_constr_change) {
  always_assert(ty != nullptr);

  for (auto it : UnorderedIterable(taint_map)) {
    auto* insn = it.first;
    auto tainted = it.second.bits();
    auto op = insn->opcode();
    if (opcode::is_an_invoke(op)) {
      auto* invoked =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
      size_t args_reg_start{0};
      if (invoked == nullptr) {
        TRACE(BUILDERS, 5, "Unable to resolve %s", SHOW(insn));
        continue;
      }

      if (method::is_init(invoked) ||
          (invoked->get_class() == ty && !opcode::is_invoke_static(op))) {
        // if a builder is passed as the first arg to a virtual function or a
        // ctor, we can treat it as non-escaping, since we also check that
        // those methods don't allow the builder to escape.
        //
        // TODO: we should be able to relax the check above to be simply
        // `!is_static(invoked)`. We don't even need to check that the type
        // matches -- if the builder is being passed as the first arg reg
        // to a non-static function, it must be the `this` arg. And if the
        // non-static function is part of a different class hierarchy, the
        // builder cannot possibly be passed as the `this` arg.
        args_reg_start = 1;
      }
      for (size_t i = args_reg_start; i < insn->srcs_size(); ++i) {
        if (tainted[insn->src(i)]) {

          if (enable_buildee_constr_change) {
            // Don't consider builders that get passed to the buildee's
            // constructor. `update_buildee_constructor` will sort this
            // out later.
            if (method::is_init(invoked) &&
                invoked->get_class() == get_buildee(ty) &&
                has_only_argument(invoked, ty)) {

              // If the 'fields constructor' already exist, don't continue.
              if (get_fields_constr_if_exists(invoked, type_class(ty)) ==
                  nullptr) {
                continue;
              }
            }
          }

          TRACE(BUILDERS, 5, "Escaping instruction: %s", SHOW(insn));
          return true;
        }
      }
    } else if (op == OPCODE_SPUT_OBJECT || op == OPCODE_IPUT_OBJECT ||
               op == OPCODE_APUT_OBJECT || op == OPCODE_RETURN_OBJECT) {
      if (tainted[insn->src(0)]) {
        if (op == OPCODE_RETURN_OBJECT && method->get_class() == ty) {
          continue;
        }
        TRACE(BUILDERS, 5, "Escaping instruction: %s", SHOW(insn));
        return true;
      }
    } else if (opcode::is_a_conditional_branch(op) ||
               opcode::is_a_monitor(op)) {
      if (tainted[insn->src(0)]) {
        // TODO(emmasevastian): Treat this case separate.
        return true;
      }
    } else if (opcode::is_check_cast(op)) {
      if (tainted[insn->src(0)]) {
        TRACE(BUILDERS, 5, "Not supported: %s", SHOW(insn));
        return true;
      }
    }
  }
  return false;
}

/**
 * Keep track, per instruction, what register(s) holds
 * an instance of the `type`.
 */
std::unique_ptr<UnorderedMap<IRInstruction*, TaintedRegs>> get_tainted_regs(
    const cfg::ControlFlowGraph& cfg,
    uint32_t regs_size,
    const std::vector<cfg::Block*>& blocks,
    const DexType* type) {

  std::function<void(cfg::InstructionIterator, TaintedRegs*)> trans =
      [&](const cfg::InstructionIterator& it, TaintedRegs* tregs) {
        auto* insn = it->insn;
        auto& regs = tregs->m_reg_set;
        auto op = insn->opcode();
        if (opcode::is_a_move_result_pseudo(op) &&
            cfg.primary_instruction_of_move_result(it)->insn->opcode() ==
                OPCODE_NEW_INSTANCE) {
          const DexType* cls =
              cfg.primary_instruction_of_move_result(it)->insn->get_type();
          auto dest = it->insn->dest();
          if (cls == type) {
            regs[dest] = true;
          } else {
            regs[dest] = false;
          }
        } else {
          transfer_object_reach(type, regs_size, insn, tregs->m_reg_set);
        }
      };

  // The extra register is used to keep track of the return values.
  return forwards_dataflow(cfg.entry_block(), blocks,
                           TaintedRegs(static_cast<int>(regs_size + 1)), trans);
}

//////////////////////////////////////////////

bool has_builder_name(const DexType* type) {
  always_assert(type != nullptr);

  static boost::regex re{"\\$Builder;$"};

  const auto deobfuscated_name =
      type_class(type)->get_deobfuscated_name_or_empty();
  if (!deobfuscated_name.empty()) {
    return boost::regex_search(str_copy(deobfuscated_name), re);
  }
  return boost::regex_search(type->c_str(), re);
}

DexType* get_buildee(const DexType* builder) {
  always_assert(builder != nullptr);

  const auto deobfuscated_name =
      type_class(builder)->get_deobfuscated_name_or_empty();
  const auto builder_name =
      !deobfuscated_name.empty() ? deobfuscated_name : builder->str();

  auto buildee_name = builder_name.substr(0, builder_name.size() - 9) + ";";
  return DexType::get_type(buildee_name);
}

UnorderedSet<DexMethod*> get_all_methods(cfg::ControlFlowGraph& cfg,
                                         const DexType* type) {
  always_assert(type != nullptr);

  UnorderedSet<DexMethod*> methods;
  for (auto const& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      auto* invoked =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
      if (invoked != nullptr && invoked->get_class() == type) {
        methods.insert(invoked);
      }
    }
  }

  return methods;
}

UnorderedSet<DexMethod*> get_non_init_methods(IRCode* code,
                                              const DexType* type) {
  always_assert(code);
  UnorderedSet<DexMethod*> methods = get_all_methods(code->cfg(), type);
  unordered_erase_if(methods, method::is_init);
  return methods;
}

bool BuilderTransform::inline_methods(
    DexMethod* method,
    const DexType* type,
    const std::function<UnorderedSet<DexMethod*>(IRCode*, const DexType*)>&
        get_methods_to_inline) {
  always_assert(method != nullptr);
  always_assert(type != nullptr);

  auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }

  UnorderedSet<DexMethod*> previous_to_inline;
  UnorderedSet<DexMethod*> to_inline = get_methods_to_inline(code, type);

  while (!to_inline.empty()) {

    for (const auto& inlinable : UnorderedIterable(to_inline)) {
      if (inlinable->get_code() == nullptr) {
        TRACE(BUILDERS,
              2,
              "Trying to inline abstract / native etc method: %s in %s",
              SHOW(inlinable),
              SHOW(method));
        return false;
      }
    }

    always_assert(!to_inline.count(method));
    m_inliner->inline_callees(method, to_inline);

    // Check all possible methods were inlined.
    previous_to_inline = to_inline;
    to_inline = get_methods_to_inline(code, type);

    // Return false if  nothing changed / nothing got inlined though
    // there were methods to inline.
    if (previous_to_inline == to_inline) {
      return false;
    }
  }

  return true;
}

bool remove_builder_from(DexMethod* method,
                         DexClass* builder,
                         BuilderTransform& b_transform,
                         DexType* super_class_holder) {
  DexType* buildee = get_buildee(builder->get_type());
  always_assert(buildee != nullptr);

  DexType* super_class = super_class_holder != nullptr
                             ? super_class_holder
                             : builder->get_super_class();

  // TODO(emmasevastian): extend it.
  static DexType* object_type = type::java_lang_Object();
  if (super_class != object_type) {
    return false;
  }

  bool tried_constructor_inlining = false;
  while (!get_non_trivial_init_methods(method->get_code(), builder->get_type())
              .empty()) {
    tried_constructor_inlining = true;

    // Filter out builders for which the method contains super class invokes.
    if (has_super_class_initializations(method, super_class)) {
      return false;
    }

    if (!b_transform.inline_methods(method, builder->get_type(),
                                    &get_non_trivial_init_methods) ||
        !b_transform.inline_methods(method, builder->get_type(),
                                    &get_non_init_methods)) {
      return false;
    }
  }

  if (!update_buildee_constructor(method, builder)) {
    return false;
  }

  if (!remove_builder(method, builder)) {
    return false;
  }

  // Cleanup after constructor inlining.
  if (tried_constructor_inlining) {
    remove_super_class_calls(method, super_class);
  }
  return true;
}
