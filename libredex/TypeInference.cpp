/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeInference.h"

#include <numeric>
#include <ostream>
#include <sstream>

#include "AnnoUtils.h"
#include "Debug.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"

std::ostream& operator<<(std::ostream& output, const IRType& type) {
  switch (type) {
  case IRType::BOTTOM: {
    output << "BOTTOM";
    break;
  }
  case IRType::ZERO: {
    output << "ZERO";
    break;
  }
  case IRType::CONST: {
    output << "CONST";
    break;
  }
  case IRType::CONST1: {
    output << "CONST1";
    break;
  }
  case IRType::CONST2: {
    output << "CONST2";
    break;
  }
  case IRType::REFERENCE: {
    output << "REF";
    break;
  }
  case IRType::INT: {
    output << "INT";
    break;
  }
  case IRType::FLOAT: {
    output << "FLOAT";
    break;
  }
  case IRType::LONG1: {
    output << "LONG1";
    break;
  }
  case IRType::LONG2: {
    output << "LONG2";
    break;
  }
  case IRType::DOUBLE1: {
    output << "DOUBLE1";
    break;
  }
  case IRType::DOUBLE2: {
    output << "DOUBLE2";
    break;
  }
  case IRType::SCALAR: {
    output << "SCALAR";
    break;
  }
  case IRType::SCALAR1: {
    output << "SCALAR1";
    break;
  }
  case IRType::SCALAR2: {
    output << "SCALAR2";
    break;
  }
  case IRType::TOP: {
    output << "TOP";
    break;
  }
  }
  return output;
}

std::ostream& operator<<(std::ostream& output, const IntType& type) {
  switch (type) {
  case IntType::BOTTOM: {
    output << "BOTTOM";
    break;
  }
  case IntType::INT: {
    output << "INT";
    break;
  }
  case IntType::CHAR: {
    output << "CHAR";
    break;
  }
  case IntType::SHORT: {
    output << "SHORT";
    break;
  }
  case IntType::BOOLEAN: {
    output << "BOOLEAN";
    break;
  }
  case IntType::BYTE: {
    output << "BYTE";
    break;
  }
  case IntType::TOP: {
    output << "TOP";
    break;
  }
  }
  return output;
}

namespace type_inference {

bool is_safely_usable_in_ifs(IRType type) {
  switch (type) {
  case IRType::TOP:
  case IRType::SCALAR:
  case IRType::SCALAR1:
    // This type is the result of joins of very different types.
    // TODO: Actually, our current type-inference implementation introduces
    // scalar values also for AGET, while the actual Android verifier tracks
    // int or float separately. Thus we might be giving up a bit too often
    // here.
    return false;
  case IRType::ZERO:
  case IRType::CONST:
  case IRType::CONST1:
  case IRType::REFERENCE:
  case IRType::INT:
  case IRType::FLOAT:
  case IRType::LONG1:
  case IRType::DOUBLE1:
    // This type is the result of joins producing a consistent type.
    return true;
  default:
    not_reached_log("unexpected type %s", SHOW(type));
  }
}

TypeLattice type_lattice(
    {IRType::BOTTOM, IRType::ZERO, IRType::CONST, IRType::CONST1,
     IRType::CONST2, IRType::REFERENCE, IRType::INT, IRType::FLOAT,
     IRType::LONG1, IRType::LONG2, IRType::DOUBLE1, IRType::DOUBLE2,
     IRType::SCALAR, IRType::SCALAR1, IRType::SCALAR2, IRType::TOP},
    {{IRType::BOTTOM, IRType::ZERO},     {IRType::BOTTOM, IRType::CONST1},
     {IRType::BOTTOM, IRType::CONST2},   {IRType::ZERO, IRType::REFERENCE},
     {IRType::ZERO, IRType::CONST},      {IRType::CONST, IRType::INT},
     {IRType::CONST, IRType::FLOAT},     {IRType::CONST1, IRType::LONG1},
     {IRType::CONST1, IRType::DOUBLE1},  {IRType::CONST2, IRType::LONG2},
     {IRType::CONST2, IRType::DOUBLE2},  {IRType::INT, IRType::SCALAR},
     {IRType::FLOAT, IRType::SCALAR},    {IRType::LONG1, IRType::SCALAR1},
     {IRType::DOUBLE1, IRType::SCALAR1}, {IRType::LONG2, IRType::SCALAR2},
     {IRType::DOUBLE2, IRType::SCALAR2}, {IRType::REFERENCE, IRType::TOP},
     {IRType::SCALAR, IRType::TOP},      {IRType::SCALAR1, IRType::TOP},
     {IRType::SCALAR2, IRType::TOP}});

IntTypeLattice int_type_lattice({IntType::BOTTOM, IntType::INT, IntType::CHAR,
                                 IntType::SHORT, IntType::BOOLEAN,
                                 IntType::BYTE, IntType::TOP},
                                {{IntType::BOTTOM, IntType::BOOLEAN},
                                 {IntType::BOOLEAN, IntType::CHAR},
                                 {IntType::BOOLEAN, IntType::BYTE},
                                 {IntType::BYTE, IntType::SHORT},
                                 {IntType::SHORT, IntType::INT},
                                 {IntType::CHAR, IntType::INT},
                                 {IntType::INT, IntType::TOP}});

void set_type(TypeEnvironment* state, reg_t reg, const TypeDomain& type) {
  state->set_type(reg, type);
}

void set_integral(
    TypeEnvironment* state,
    reg_t reg,
    const std::optional<const DexType*>& annotation = std::nullopt) {
  state->set_type(reg, TypeDomain(IRType::INT));
  const auto anno = DexAnnoType(annotation);
  DexTypeDomain dex_type_domain = DexTypeDomain::create_for_anno(&anno);
  state->set_dex_type(reg, dex_type_domain);
}

void set_float(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, TypeDomain(IRType::FLOAT));
  state->reset_dex_type(reg);
}

void set_scalar(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, TypeDomain(IRType::SCALAR));
  state->reset_dex_type(reg);
}

void set_reference(TypeEnvironment* state,
                   reg_t reg,
                   const std::optional<const DexType*>& dex_type_opt,
                   bool is_not_null = false) {
  state->set_type(reg, TypeDomain(IRType::REFERENCE));
  const auto* dex_type = dex_type_opt ? *dex_type_opt : nullptr;
  always_assert(!is_not_null || dex_type != nullptr);
  const DexTypeDomain dex_type_domain =
      is_not_null ? DexTypeDomain::create_not_null(dex_type)
                  : DexTypeDomain::create_nullable(dex_type);
  state->set_dex_type(reg, dex_type_domain);
}

// The presence of DexAnnoType implies Nullable
void set_reference_with_anno(TypeEnvironment* state,
                             reg_t reg,
                             const std::optional<const DexType*>& dex_type_opt,
                             const std::optional<const DexType*>& annotation) {
  state->set_type(reg, TypeDomain(IRType::REFERENCE));
  const auto* dex_type = dex_type_opt ? *dex_type_opt : nullptr;
  const auto anno = DexAnnoType(annotation);
  const DexTypeDomain dex_type_domain =
      DexTypeDomain::create_nullable(dex_type, &anno);
  state->set_dex_type(reg, dex_type_domain);
}

void set_reference(TypeEnvironment* state,
                   reg_t reg,
                   const DexTypeDomain& dex_type) {
  state->set_type(reg, TypeDomain(IRType::REFERENCE));
  state->set_dex_type(reg, dex_type);
}

void set_long(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, TypeDomain(IRType::LONG1));
  state->set_type(reg + 1, TypeDomain(IRType::LONG2));
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void set_double(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, TypeDomain(IRType::DOUBLE1));
  state->set_type(reg + 1, TypeDomain(IRType::DOUBLE2));
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void set_wide_scalar(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, TypeDomain(IRType::SCALAR1));
  state->set_type(reg + 1, TypeDomain(IRType::SCALAR2));
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void set_type(TypeEnvironment* state, reg_t reg, const IntTypeDomain& type) {
  state->set_type(reg, type);
}

void set_int(TypeEnvironment* state,
             reg_t reg,
             const std::optional<const DexType*>& annotation = std::nullopt) {
  state->set_type(reg, IntTypeDomain(IntType::INT));
  set_integral(state, reg, annotation);
}

void set_char(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, IntTypeDomain(IntType::CHAR));
  set_integral(state, reg);
}

void set_short(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, IntTypeDomain(IntType::SHORT));
  set_integral(state, reg);
}

void set_boolean(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, IntTypeDomain(IntType::BOOLEAN));
  set_integral(state, reg);
}

void set_byte(TypeEnvironment* state, reg_t reg) {
  state->set_type(reg, IntTypeDomain(IntType::BYTE));
  set_integral(state, reg);
}

// This is used for the operand of a comparison operation with zero. The
// complexity here is that this operation may be performed on either an
// integer or a reference.
void refine_comparable_with_zero(TypeEnvironment* state, reg_t reg) {
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
    // The type is incompatible with the operation and hence, the code that
    // follows is unreachable.
    state->set_to_bottom();
    return;
  }
}

// This is used for the operands of a comparison operation between two
// registers. The complexity here is that this operation may be performed on
// either two integers or two references.
void refine_comparable(TypeEnvironment* state, reg_t reg1, reg_t reg2) {
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
    // The types are incompatible and hence, the code that follows is
    // unreachable.
    state->set_to_bottom();
    return;
  }
}

std::optional<const DexType*> get_typedef_annotation(
    const std::vector<std::unique_ptr<DexAnnotation>>& annotations,
    const UnorderedSet<const DexType*>& typedef_annotations) {
  for (auto const& anno : annotations) {
    auto* const anno_class = type_class(anno->type());
    if (anno_class == nullptr) {
      continue;
    }
    bool has_typedef = false;
    for (const auto* annotation : UnorderedIterable(typedef_annotations)) {
      if (get_annotation(anno_class, annotation) != nullptr) {
        if (has_typedef) {
          always_assert_log(
              false,
              "Annotation %s cannot be annotated with more than one TypeDef "
              "annotation",
              SHOW(anno_class));
        }
        has_typedef = true;
      }
    }
    if (has_typedef) {
      return DexType::make_type(anno->type()->get_name());
    }
  }
  return std::nullopt;
}

bool TypeInference::is_pure_virtual_with_annotation(
    DexMethodRef* dex_method) const {
  if (!m_annotations.empty() && dex_method->is_def() &&
      (dex_method->as_def()->get_code() == nullptr)) {
    always_assert(m_method_override_graph != nullptr);
    return method_override_graph::is_true_virtual(*m_method_override_graph,
                                                  dex_method->as_def());
  }
  return false;
}

std::optional<const DexType*> TypeInference::get_return_typedef_anno(
    DexMethodRef* callee) const {
  auto annotation = get_typedef_anno_from_member(callee, m_annotations);
  if (!annotation || !is_pure_virtual_with_annotation(callee)) {
    return annotation;
  }
  bool all_overrides_agree = method_override_graph::all_overriding_methods(
      *m_method_override_graph, callee->as_def(),
      [&](const DexMethod* overrider) {
        return get_typedef_anno_from_member(overrider, m_annotations) ==
               annotation;
      });
  return all_overrides_agree ? annotation : std::nullopt;
}

TypeDomain TypeInference::refine_type(const TypeDomain& type,
                                      IRType expected,
                                      IRType const_type,
                                      IRType scalar_type) const {
  auto refined_type = type.meet(TypeDomain(expected));
  // If constants are not considered polymorphic (the default behavior of the
  // Android verifier), we lift the constant to the type expected in the given
  // context. This only makes sense if the expected type is fully determined
  // by the context, i.e., is not a scalar type (SCALAR/SCALAR1/SCALAR2).
  if (type.leq(TypeDomain(const_type)) && expected != scalar_type) {
    return refined_type.is_bottom() ? refined_type : TypeDomain(expected);
  }

  return refined_type;
}

void TypeInference::set_annotation(TypeEnvironment* state,
                                   reg_t reg,
                                   const DexType* type) const {
  if (!m_annotations.empty()) {
    auto annotation = state->get_annotation(reg);
    const auto anno = DexAnnoType(annotation);
    const DexTypeDomain dex_type_domain =
        DexTypeDomain::create_nullable(type, &anno);
    state->set_dex_type(reg, dex_type_domain);
  }
}

void TypeInference::refine_type(TypeEnvironment* state,
                                reg_t reg,
                                IRType expected) const {
  state->update_type(reg, [this, expected](const TypeDomain& type) {
    return refine_type(type, expected, /* const_type */ IRType::CONST,
                       /* scalar_type */ IRType::SCALAR);
  });
}

void TypeInference::refine_type(TypeEnvironment* state,
                                reg_t reg,
                                IntType expected) const {
  state->update_type(reg, [expected](const IntTypeDomain& type) {
    return type.meet(IntTypeDomain(expected));
  });
}

void TypeInference::refine_wide_type(TypeEnvironment* state,
                                     reg_t reg,
                                     IRType expected1,
                                     IRType expected2) const {
  state->update_type(reg, [this, expected1](const TypeDomain& type) {
    return refine_type(type,
                       expected1,
                       /* const_type */ IRType::CONST1,
                       /* scalar_type */ IRType::SCALAR1);
  });
  state->update_type(reg + 1, [this, expected2](const TypeDomain& type) {
    return refine_type(type,
                       expected2,
                       /* const_type */ IRType::CONST2,
                       /* scalar_type */ IRType::SCALAR2);
  });
}

void TypeInference::refine_reference(TypeEnvironment* state, reg_t reg) const {
  refine_type(state,
              reg,
              /* expected */ IRType::REFERENCE);
}

void TypeInference::refine_scalar(TypeEnvironment* state, reg_t reg) const {
  refine_type(state,
              reg,
              /* expected */ IRType::SCALAR);
  const std::optional<const DexType*> annotation = state->get_annotation(reg);
  const auto anno = DexAnnoType(annotation);
  DexTypeDomain dex_type_domain = DexTypeDomain::create_for_anno(&anno);
  state->set_dex_type(reg, dex_type_domain);
}

void TypeInference::refine_integral(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected */ IRType::INT);
  const std::optional<const DexType*> annotation = state->get_annotation(reg);
  const auto anno = DexAnnoType(annotation);
  DexTypeDomain dex_type_domain = DexTypeDomain::create_for_anno(&anno);
  state->set_dex_type(reg, dex_type_domain);
}

void TypeInference::refine_float(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected */ IRType::FLOAT);
  state->reset_dex_type(reg);
}

void TypeInference::refine_wide_scalar(TypeEnvironment* state,
                                       reg_t reg) const {
  refine_wide_type(state, reg, /* expected1 */ IRType::SCALAR1,
                   /* expected2 */ IRType::SCALAR2);
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void TypeInference::refine_long(TypeEnvironment* state, reg_t reg) const {
  refine_wide_type(state, reg, /* expected1 */ IRType::LONG1,
                   /* expected2 */ IRType::LONG2);
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void TypeInference::refine_double(TypeEnvironment* state, reg_t reg) const {
  refine_wide_type(state, reg, /* expected1 */ IRType::DOUBLE1,
                   /* expected2 */ IRType::DOUBLE2);
  state->reset_dex_type(reg);
  state->reset_dex_type(reg + 1);
}

void TypeInference::refine_int(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected1 */ IntType::INT);
  refine_integral(state, reg);
}

void TypeInference::refine_char(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected1 */ IntType::CHAR);
  refine_integral(state, reg);
}

void TypeInference::refine_boolean(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected1 */ IntType::BOOLEAN);
  refine_integral(state, reg);
}

void TypeInference::refine_short(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected1 */ IntType::SHORT);
  refine_integral(state, reg);
}

void TypeInference::refine_byte(TypeEnvironment* state, reg_t reg) const {
  refine_type(state, reg, /* expected1 */ IntType::BYTE);
  refine_integral(state, reg);
}

void TypeInference::run(const DexMethod* dex_method) {
  run(is_static(dex_method), dex_method->get_class(),
      dex_method->get_proto()->get_args(), dex_method->get_param_anno());
}

void TypeInference::run(bool is_static,
                        const DexType* declaring_type,
                        DexTypeList* args,
                        const ParamAnnotations* param_anno) {
  // We need to compute the initial environment by assigning the parameter
  // registers their correct types derived from the method's signature. The
  // IOPCODE_LOAD_PARAM_* instructions are pseudo-operations that are used to
  // specify the formal parameters of the method. They must be interpreted
  // separately.
  auto init_state = TypeEnvironment::top();
  auto sig_it = args->begin();
  int arg_index = 0;
  bool first_param = true;
  for (const auto& mie : InstructionIterable(m_cfg.get_param_instructions())) {
    IRInstruction* insn = mie.insn;
    std::optional<const DexType*> annotation = std::nullopt;

    if (!first_param || is_static) {
      if (!m_annotations.empty() && (param_anno != nullptr) &&
          param_anno->find(arg_index) != param_anno->end()) {
        annotation = get_typedef_annotation(
            (&param_anno->at(arg_index))->get()->get_annotations(),
            m_annotations);
      }
      arg_index += 1;
    }

    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM_OBJECT: {
      if (first_param && !is_static) {
        // If the method is not static, the first parameter corresponds to
        // `this`.
        first_param = false;
        set_reference_with_anno(&init_state, insn->dest(), declaring_type,
                                annotation);
      } else {
        // This is a regular parameter of the method.
        always_assert(sig_it != args->end());
        const DexType* type = *sig_it;
        set_reference_with_anno(&init_state, insn->dest(), type, annotation);
        ++sig_it;
      }
      break;
    }
    case IOPCODE_LOAD_PARAM: {
      always_assert(sig_it != args->end());
      if (type::is_float(*sig_it)) {
        set_float(&init_state, insn->dest());
      } else {
        if (type::is_char(*sig_it)) {
          set_char(&init_state, insn->dest());
        } else if (type::is_short(*sig_it)) {
          set_short(&init_state, insn->dest());
        } else if (type::is_boolean(*sig_it)) {
          set_boolean(&init_state, insn->dest());
        } else if (type::is_byte(*sig_it)) {
          set_byte(&init_state, insn->dest());
        } else {
          set_int(&init_state, insn->dest(), annotation);
        }
      }
      sig_it++;
      break;
    }
    case IOPCODE_LOAD_PARAM_WIDE: {
      always_assert(sig_it != args->end());
      if (type::is_double(*sig_it++)) {
        set_double(&init_state, insn->dest());
      } else {
        set_long(&init_state, insn->dest());
      }
      break;
    }
    default:
      not_reached();
    }
  }
  MonotonicFixpointIterator::run(init_state);
  populate_type_environments();
}

// This method analyzes an instruction and updates the type environment
// accordingly during the fixpoint iteration.
//
// Similarly, the various refine_* functions are used to refine the
// type of a register depending on the context (e.g., from SCALAR to INT).
void TypeInference::analyze_instruction(const IRInstruction* insn,
                                        TypeEnvironment* current_state,
                                        const cfg::Block* current_block) const {
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
    refine_scalar(current_state, insn->src(0));
    set_type(current_state, insn->dest(),
             current_state->get_type(insn->src(0)));
    set_type(current_state, insn->dest(),
             current_state->get_int_type(insn->src(0)));
    if (!m_annotations.empty()) {
      current_state->set_dex_type(insn->dest(),
                                  current_state->get_type_domain(insn->src(0)));
    }
    break;
  }
  case OPCODE_MOVE_OBJECT: {
    refine_reference(current_state, insn->src(0));
    if (current_state->get_type(insn->src(0)) ==
        TypeDomain(IRType::REFERENCE)) {
      const auto dex_type = current_state->get_type_domain(insn->src(0));
      set_reference(current_state, insn->dest(), dex_type);
    } else {
      set_type(current_state, insn->dest(),
               current_state->get_type(insn->src(0)));
      set_type(current_state, insn->dest(),
               current_state->get_int_type(insn->src(0)));
      current_state->set_dex_type(insn->dest(),
                                  current_state->get_type_domain(insn->src(0)));
    }
    break;
  }
  case OPCODE_MOVE_WIDE: {
    refine_wide_scalar(current_state, insn->src(0));
    TypeDomain td1 = current_state->get_type(insn->src(0));
    TypeDomain td2 = current_state->get_type(insn->src(0) + 1);
    set_type(current_state, insn->dest(), td1);
    set_type(current_state, insn->dest() + 1, td2);
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT: {
    refine_scalar(current_state, RESULT_REGISTER);
    set_type(current_state, insn->dest(),
             current_state->get_type(RESULT_REGISTER));
    set_type(current_state, insn->dest(),
             current_state->get_int_type(RESULT_REGISTER));
    if (!m_annotations.empty()) {
      current_state->set_dex_type(
          insn->dest(), current_state->get_type_domain(RESULT_REGISTER));
    }
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT: {
    refine_reference(current_state, RESULT_REGISTER);
    set_reference(current_state,
                  insn->dest(),
                  current_state->get_type_domain(RESULT_REGISTER));
    break;
  }
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE: {
    refine_wide_scalar(current_state, RESULT_REGISTER);
    set_type(current_state, insn->dest(),
             current_state->get_type(RESULT_REGISTER));
    set_type(current_state,
             insn->dest() + 1,
             current_state->get_type(RESULT_REGISTER + 1));
    break;
  }
  case OPCODE_MOVE_EXCEPTION: {
    if (current_block == nullptr) {
      // We bail just in case the current block is dangling.
      TRACE(TYPE, 2,
            "Warning: Can't infer exception type from unknown catch block.");
      set_reference(current_state, insn->dest(), type::java_lang_Throwable());
      break;
    }

    // The block that contained this instruction must be a catch block.
    const auto& preds = current_block->preds();

    if (preds.empty()) {
      // We bail just in case the current block is dangling.
      TRACE(TYPE, 2,
            "Warning: Catch block doesn't have at least one predecessor.");
      set_reference(current_state, insn->dest(), type::java_lang_Throwable());
      break;
    }

    auto* default_type = type::java_lang_Throwable();
    const DexType* merged_catch_type = std::accumulate(
        preds.begin(), preds.end(), (const DexType*)nullptr,
        [default_type](const auto* acc, auto* edge) {
          if (edge->type() != cfg::EDGE_THROW) {
            return acc;
          }

          auto* catch_type = edge->throw_info()->catch_type;
          const auto* actual_catch_type =
              catch_type != nullptr ? catch_type : default_type;

          if (acc == nullptr) {
            return actual_catch_type;
          }

          DexTypeDomain d1 = DexTypeDomain::create_nullable(acc);
          DexTypeDomain d2 = DexTypeDomain::create_nullable(actual_catch_type);
          d1.join_with(d2);

          auto maybe_dextype = d1.get_dex_type();

          // In case of the join giving up, bail to a default type
          return maybe_dextype ? *maybe_dextype : default_type;
        });
    if (merged_catch_type == nullptr) {
      merged_catch_type = default_type;
    }

    set_reference(current_state, insn->dest(), merged_catch_type);
    break;
  }
  case OPCODE_RETURN_VOID: {
    break;
  }
  case OPCODE_RETURN: {
    refine_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_RETURN_WIDE: {
    refine_wide_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_RETURN_OBJECT: {
    refine_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_CONST:
  case IOPCODE_R_CONST:
  case IOPCODE_INJECTION_ID: {
    if (insn->get_literal() == 0) {
      current_state->set_dex_type(insn->dest(), DexTypeDomain::null());
      set_type(current_state, insn->dest(), TypeDomain(IRType::ZERO));
    } else {
      current_state->set_dex_type(insn->dest(),
                                  DexTypeDomain::create_for_anno(nullptr));
      set_type(current_state, insn->dest(), TypeDomain(IRType::CONST));
    }
    set_type(current_state, insn->dest(), IntTypeDomain(IntType::BOOLEAN));
    break;
  }
  case IOPCODE_UNREACHABLE: {
    current_state->set_dex_type(insn->dest(), DexTypeDomain::null());
    set_type(current_state, insn->dest(), TypeDomain(IRType::ZERO));
    set_type(current_state, insn->dest(), IntTypeDomain(IntType::BOOLEAN));
    break;
  }
  case OPCODE_CONST_WIDE: {
    set_type(current_state, insn->dest(), TypeDomain(IRType::CONST1));
    set_type(current_state, insn->dest() + 1, TypeDomain(IRType::CONST2));
    break;
  }
  case OPCODE_CONST_STRING: {
    // Either we get the interned string or the instruction throws, so the
    // result is never null. java.lang.String is final, so the type is exact.
    set_reference(current_state, RESULT_REGISTER, type::java_lang_String(),
                  /* is_not_null */ true);
    break;
  }
  case OPCODE_CONST_CLASS: {
    // Same as const-string: either we get the class object or the instruction
    // throws, and java.lang.Class is final.
    set_reference(current_state, RESULT_REGISTER, type::java_lang_Class(),
                  /* is_not_null */ true);
    break;
  }
  case OPCODE_CONST_METHOD_HANDLE: {
    always_assert_log(false,
                      "TypeInference::analyze_instruction does not support "
                      "const-method-handle yet");
  }
  case OPCODE_CONST_METHOD_TYPE: {
    always_assert_log(false,
                      "TypeInference::analyze_instruction does not support "
                      "const-method-type yet");
  }
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT: {
    refine_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_CHECK_CAST: {
    refine_reference(current_state, insn->src(0));
    const auto* to_type = insn->get_type();

    if (!m_skip_check_cast_upcasting) {
      set_reference(current_state, RESULT_REGISTER, to_type);
    } else {
      // Avoid using this check-cast type if casting to base class or an
      // interface.
      auto* to_cls = type_class(to_type);
      auto current_type_domain = current_state->get_type_domain(insn->src(0));
      auto current_type = current_type_domain.get_dex_type();
      auto is_intf = (to_cls != nullptr) && is_interface(to_cls);
      auto is_cast_to_base =
          current_type && (to_type != nullptr) &&
          type::check_cast(*current_type, /* base_type */ to_type);
      if (is_intf || is_cast_to_base) {
        set_reference(current_state, RESULT_REGISTER, current_type_domain);
      } else {
        set_reference(current_state, RESULT_REGISTER, to_type);
      }
    }
    break;
  }
  case OPCODE_INSTANCE_OF: {
    refine_reference(current_state, insn->src(0));
    set_boolean(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_ARRAY_LENGTH: {
    refine_reference(current_state, insn->src(0));
    set_int(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_NEW_INSTANCE: {
    set_reference(current_state, RESULT_REGISTER, insn->get_type(),
                  /* is_not_null */ true);
    break;
  }
  case OPCODE_NEW_ARRAY: {
    refine_int(current_state, insn->src(0));
    set_reference(current_state, RESULT_REGISTER, insn->get_type(),
                  /* is_not_null */ true);
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
        refine_reference(current_state, insn->src(i));
      } else {
        refine_scalar(current_state, insn->src(i));
      }
    }
    set_reference(current_state, RESULT_REGISTER, insn->get_type(),
                  /* is_not_null */ true);
    break;
  }
  case OPCODE_FILL_ARRAY_DATA: {
    break;
  }
  case OPCODE_THROW: {
    refine_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_GOTO: {
    break;
  }
  case OPCODE_SWITCH: {
    refine_int(current_state, insn->src(0));
    break;
  }
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT: {
    refine_float(current_state, insn->src(0));
    refine_float(current_state, insn->src(1));
    set_boolean(current_state, insn->dest());
    break;
  }
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE: {
    refine_double(current_state, insn->src(0));
    refine_double(current_state, insn->src(1));
    set_boolean(current_state, insn->dest());
    break;
  }
  case OPCODE_CMP_LONG: {
    refine_long(current_state, insn->src(0));
    refine_long(current_state, insn->src(1));
    set_boolean(current_state, insn->dest());
    break;
  }
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE: {
    refine_comparable(current_state, insn->src(0), insn->src(1));
    break;
  }
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE: {
    refine_int(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    break;
  }
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ: {
    refine_comparable_with_zero(current_state, insn->src(0));
    break;
  }
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ: {
    refine_int(current_state, insn->src(0));
    break;
  }
  case OPCODE_AGET: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_scalar(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_BOOLEAN: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_boolean(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_BYTE: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_byte(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_CHAR: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_char(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_SHORT: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_short(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_WIDE: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_wide_scalar(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_AGET_OBJECT: {
    refine_reference(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    const auto dex_type_opt = current_state->get_dex_type(insn->src(0));
    if (dex_type_opt && (*dex_type_opt != nullptr) &&
        type::is_array(*dex_type_opt)) {
      auto* const etype = type::make_array_component_type(*dex_type_opt);
      set_reference(current_state, RESULT_REGISTER, etype);
    } else {
      set_reference(current_state, RESULT_REGISTER, DexTypeDomain::top());
    }
    break;
  }
  case OPCODE_APUT: {
    refine_scalar(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_BOOLEAN: {
    refine_boolean(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_BYTE: {
    refine_byte(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_CHAR: {
    refine_char(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_SHORT: {
    refine_short(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_WIDE: {
    refine_wide_scalar(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_APUT_OBJECT: {
    refine_reference(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    refine_int(current_state, insn->src(2));
    break;
  }
  case OPCODE_IGET: {
    refine_reference(current_state, insn->src(0));
    DexFieldRef* field = insn->get_field();
    const DexType* type = field->get_type();
    std::optional<const DexType*> annotation =
        get_typedef_anno_from_member(field, m_annotations);
    std::optional<const DexType*> src_anno =
        current_state->get_annotation(insn->src(0));
    DexField* field_def = field->as_def();
    if ((field_def != nullptr) &&
        field_def == type::pseudo::kotlin_jvm_internal_RefIntRef_element()) {
      annotation = src_anno;
    }
    if (type::is_float(type)) {
      set_float(current_state, RESULT_REGISTER);
    } else {
      set_int(current_state, RESULT_REGISTER, annotation);
    }
    break;
  }
  case OPCODE_IGET_BOOLEAN: {
    refine_reference(current_state, insn->src(0));
    set_boolean(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_IGET_BYTE: {
    refine_reference(current_state, insn->src(0));
    set_byte(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_IGET_CHAR: {
    refine_reference(current_state, insn->src(0));
    set_char(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_IGET_SHORT: {
    refine_reference(current_state, insn->src(0));
    set_short(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_IGET_WIDE: {
    refine_reference(current_state, insn->src(0));
    const DexType* type = insn->get_field()->get_type();
    if (type::is_double(type)) {
      set_double(current_state, RESULT_REGISTER);
    } else {
      set_long(current_state, RESULT_REGISTER);
    }
    break;
  }
  case OPCODE_IGET_OBJECT: {
    refine_reference(current_state, insn->src(0));
    std::optional<const DexType*> annotation =
        get_typedef_anno_from_member(insn->get_field(), m_annotations);
    always_assert(insn->has_field());
    auto* const field = insn->get_field();
    std::optional<const DexType*> src_anno =
        current_state->get_annotation(insn->src(0));
    DexField* field_def = field->as_def();
    if ((field_def != nullptr) &&
        field_def == type::pseudo::kotlin_jvm_internal_RefObjectRef_element()) {
      annotation = src_anno;
    }
    set_reference_with_anno(current_state, RESULT_REGISTER, field->get_type(),
                            annotation);
    break;
  }
  case OPCODE_IPUT: {
    const DexType* type = insn->get_field()->get_type();
    if (type::is_float(type)) {
      refine_float(current_state, insn->src(0));
    } else {
      refine_int(current_state, insn->src(0));
    }
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_BOOLEAN: {
    refine_boolean(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_BYTE: {
    refine_byte(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_CHAR: {
    refine_char(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_SHORT: {
    refine_short(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_WIDE: {
    refine_wide_scalar(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_IPUT_OBJECT: {
    refine_reference(current_state, insn->src(0));
    refine_reference(current_state, insn->src(1));
    break;
  }
  case OPCODE_SGET: {
    DexType* type = insn->get_field()->get_type();
    std::optional<const DexType*> annotation =
        get_typedef_anno_from_member(insn->get_field(), m_annotations);
    if (type::is_float(type)) {
      set_float(current_state, RESULT_REGISTER);
    } else {
      set_int(current_state, RESULT_REGISTER, annotation);
    }
    break;
  }
  case OPCODE_SGET_BOOLEAN: {
    set_boolean(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_SGET_BYTE: {
    set_byte(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_SGET_CHAR: {
    set_char(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_SGET_SHORT: {
    set_short(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_SGET_WIDE: {
    DexType* type = insn->get_field()->get_type();
    if (type::is_double(type)) {
      set_double(current_state, RESULT_REGISTER);
    } else {
      set_long(current_state, RESULT_REGISTER);
    }
    break;
  }
  case OPCODE_SGET_OBJECT: {
    always_assert(insn->has_field());
    auto* const field = insn->get_field();
    std::optional<const DexType*> annotation =
        get_typedef_anno_from_member(insn->get_field(), m_annotations);
    set_reference_with_anno(current_state, RESULT_REGISTER, field->get_type(),
                            annotation);
    break;
  }
  case OPCODE_SPUT: {
    const DexType* type = insn->get_field()->get_type();
    set_annotation(current_state, insn->src(0), type);
    if (type::is_float(type)) {
      refine_float(current_state, insn->src(0));
    } else {
      refine_int(current_state, insn->src(0));
    }
    break;
  }
  case OPCODE_SPUT_BOOLEAN: {
    refine_boolean(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_BYTE: {
    refine_byte(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_CHAR: {
    refine_char(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_SHORT: {
    refine_short(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_WIDE: {
    refine_wide_scalar(current_state, insn->src(0));
    break;
  }
  case OPCODE_SPUT_OBJECT: {
    const DexType* type = insn->get_field()->get_type();
    set_annotation(current_state, insn->src(0), type);
    refine_reference(current_state, insn->src(0));
    break;
  }
  case OPCODE_INVOKE_CUSTOM: {
    // TODO(T59277083)
    not_reached_log(
        "TypeInference::analyze_instruction does not support "
        "invoke-custom yet");
  }
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE: {
    DexMethodRef* dex_method = insn->get_method();
    const auto* arg_types = dex_method->get_proto()->get_args();
    if (insn->opcode() == OPCODE_INVOKE_POLYMORPHIC) {
      // invoke-polymorphic can only be used to invoke MethodHandle.invoke and
      // MethodHandle.invokeExact. The first argument is a MethodHandle, and the
      // rest are Objects.
      for (auto src : insn->srcs()) {
        refine_reference(current_state, src);
      }
    } else {
      size_t expected_args =
          (insn->opcode() != OPCODE_INVOKE_STATIC ? 1 : 0) + arg_types->size();
      always_assert_log(insn->srcs_size() == expected_args,
                        "instruction: %s\nexpected: %zu\nactual: %zu",
                        SHOW(insn), expected_args, insn->srcs_size());
      size_t src_idx{0};
      if (insn->opcode() != OPCODE_INVOKE_STATIC) {
        // The first argument is a reference to the object instance on which the
        // method is invoked.
        refine_reference(current_state, insn->src(src_idx++));
      }
      for (const DexType* arg_type : *arg_types) {
        if (type::is_object(arg_type)) {
          refine_reference(current_state, insn->src(src_idx++));
          continue;
        }
        if (type::is_integral(arg_type)) {
          if (type::is_int(arg_type)) {
            refine_int(current_state, insn->src(src_idx++));
            continue;
          }
          if (type::is_char(arg_type)) {
            refine_char(current_state, insn->src(src_idx++));
            continue;
          }
          if (type::is_boolean(arg_type)) {
            refine_boolean(current_state, insn->src(src_idx++));
            continue;
          }
          if (type::is_short(arg_type)) {
            refine_short(current_state, insn->src(src_idx++));
            continue;
          }
          if (type::is_byte(arg_type)) {
            refine_byte(current_state, insn->src(src_idx++));
            continue;
          }
        }
        if (type::is_long(arg_type)) {
          refine_long(current_state, insn->src(src_idx++));
          continue;
        }
        if (type::is_float(arg_type)) {
          refine_float(current_state, insn->src(src_idx++));
          continue;
        }
        always_assert(type::is_double(arg_type));
        refine_double(current_state, insn->src(src_idx++));
      }
    }
    DexType* return_type = dex_method->get_proto()->get_rtype();
    if (type::is_void(return_type)) {
      break;
    }
    if (type::is_object(return_type)) {
      set_reference_with_anno(current_state, RESULT_REGISTER, return_type,
                              get_return_typedef_anno(dex_method));
      break;
    }
    if (type::is_integral(return_type)) {
      if (type::is_int(return_type)) {
        set_int(current_state, RESULT_REGISTER,
                get_return_typedef_anno(dex_method));
        break;
      }
      if (type::is_char(return_type)) {
        set_char(current_state, RESULT_REGISTER);
        break;
      }
      if (type::is_boolean(return_type)) {
        set_boolean(current_state, RESULT_REGISTER);
        break;
      }
      if (type::is_short(return_type)) {
        set_short(current_state, RESULT_REGISTER);
        break;
      }
      if (type::is_byte(return_type)) {
        set_byte(current_state, RESULT_REGISTER);
        break;
      }
    }
    if (type::is_long(return_type)) {
      set_long(current_state, RESULT_REGISTER);
      break;
    }
    if (type::is_float(return_type)) {
      set_float(current_state, RESULT_REGISTER);
      break;
    }
    always_assert(type::is_double(return_type));
    set_double(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT: {
    refine_int(current_state, insn->src(0));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG: {
    refine_long(current_state, insn->src(0));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_NEG_FLOAT: {
    refine_float(current_state, insn->src(0));
    set_float(current_state, insn->dest());
    break;
  }
  case OPCODE_NEG_DOUBLE: {
    refine_double(current_state, insn->src(0));
    set_double(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_BYTE: {
    refine_int(current_state, insn->src(0));
    set_byte(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_CHAR: {
    refine_int(current_state, insn->src(0));
    set_char(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_SHORT: {
    refine_int(current_state, insn->src(0));
    set_short(current_state, insn->dest());
    break;
  }
  case OPCODE_LONG_TO_INT: {
    refine_long(current_state, insn->src(0));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_FLOAT_TO_INT: {
    refine_float(current_state, insn->src(0));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_DOUBLE_TO_INT: {
    refine_double(current_state, insn->src(0));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_LONG: {
    refine_int(current_state, insn->src(0));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_FLOAT_TO_LONG: {
    refine_float(current_state, insn->src(0));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_DOUBLE_TO_LONG: {
    refine_double(current_state, insn->src(0));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_FLOAT: {
    refine_int(current_state, insn->src(0));
    set_float(current_state, insn->dest());
    break;
  }
  case OPCODE_LONG_TO_FLOAT: {
    refine_long(current_state, insn->src(0));
    set_float(current_state, insn->dest());
    break;
  }
  case OPCODE_DOUBLE_TO_FLOAT: {
    refine_double(current_state, insn->src(0));
    set_float(current_state, insn->dest());
    break;
  }
  case OPCODE_INT_TO_DOUBLE: {
    refine_int(current_state, insn->src(0));
    set_double(current_state, insn->dest());
    break;
  }
  case OPCODE_LONG_TO_DOUBLE: {
    refine_long(current_state, insn->src(0));
    set_double(current_state, insn->dest());
    break;
  }
  case OPCODE_FLOAT_TO_DOUBLE: {
    refine_float(current_state, insn->src(0));
    set_double(current_state, insn->dest());
    break;
  }
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT: {
    refine_int(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT: {
    // TODO: The IntType of the destination is set to boolean to make the
    // IntTypePatcher more conservative when finding conversions. The
    // Android 4.4 verifier actually determines the type for the destination
    // based on types of the inputs, so a possible improvement would be to set
    // the IntType based on the inputs.
    refine_int(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_boolean(current_state, insn->dest());
    break;
  }

  case OPCODE_DIV_INT:
  case OPCODE_REM_INT: {
    refine_int(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_int(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG: {
    refine_long(current_state, insn->src(0));
    refine_long(current_state, insn->src(1));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG: {
    refine_long(current_state, insn->src(0));
    refine_long(current_state, insn->src(1));
    set_long(current_state, RESULT_REGISTER);
    break;
  }
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG: {
    refine_long(current_state, insn->src(0));
    refine_int(current_state, insn->src(1));
    set_long(current_state, insn->dest());
    break;
  }
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT: {
    refine_float(current_state, insn->src(0));
    refine_float(current_state, insn->src(1));
    set_float(current_state, insn->dest());
    break;
  }
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE: {
    refine_double(current_state, insn->src(0));
    refine_double(current_state, insn->src(1));
    set_double(current_state, insn->dest());
    break;
  }
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT: {
    refine_int(current_state, insn->src(0));
    set_int(current_state, insn->dest());
    break;
  }
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT: {
    refine_int(current_state, insn->src(0));
    set_boolean(current_state, insn->dest());
    break;
  }
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT: {
    refine_int(current_state, insn->src(0));
    set_int(current_state, RESULT_REGISTER);
    break;
  }
  case IOPCODE_INIT_CLASS:
  case IOPCODE_WRITE_BARRIER: {
    break;
  }
  }

  // If the opcode does not set the RESULT_REGISTER, clear it.
  if (!insn->has_move_result_any()) {
    set_type(current_state, RESULT_REGISTER, TypeDomain::top());
    set_type(current_state, RESULT_REGISTER, IntTypeDomain::top());
    current_state->reset_dex_type(RESULT_REGISTER);
  }
}

void TypeInference::print(std::ostream& output) const {
  for (cfg::Block* block : m_cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      auto it = m_type_envs.find(insn);
      always_assert(it != m_type_envs.end());
      output << SHOW(insn) << " -- " << it->second << '\n';
    }
  }
}

void TypeInference::traceState(TypeEnvironment* state) const {
  if (!traceEnabled(TYPE, 9)) {
    return;
  }
  std::ostringstream out;
  out << *state << '\n';
  TRACE(TYPE, 9, "%s", out.str().c_str());
}

void TypeInference::populate_type_environments() {
  // We reserve enough space for the map in order to avoid repeated rehashing
  // during the computation.
  m_type_envs.reserve(m_cfg.num_blocks() * 16);
  for (cfg::Block* block : m_cfg.blocks()) {
    TypeEnvironment current_state = get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      m_type_envs.emplace(insn, current_state);
      analyze_instruction(insn, &current_state, block);
    }
  }
}

} // namespace type_inference
