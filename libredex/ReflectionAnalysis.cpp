/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReflectionAnalysis.h"

#include <atomic>
#include <functional>
#include <iomanip>
#include <ostream>

#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/ReducedProductAbstractDomain.h>

#include "BaseIRAnalyzer.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "Show.h"
#include "Trace.h"

using namespace sparta;

std::ostream& operator<<(std::ostream& out,
                         const UnorderedSet<const DexType*>& x) {
  if (x.empty()) {
    return out;
  }
  out << "(";
  auto&& ui = UnorderedIterable(x);
  for (auto i = ui.begin(); i != ui.end(); ++i) {
    out << SHOW(*i);
    if (std::next(i) != ui.end()) {
      out << ",";
    }
  }
  out << ")";
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const reflection::AbstractObject& x) {
  switch (x.obj_kind) {
  case reflection::OBJECT: {
    out << "OBJECT{" << SHOW(x.dex_type) << x.potential_dex_types << "}";
    break;
  }
  case reflection::INT: {
    out << "INT{" << (x.dex_int ? std::to_string(*x.dex_int) : "none") << "}";
    break;
  }
  case reflection::STRING: {
    if (x.dex_string != nullptr) {
      auto str = x.dex_string->str();
      if (str.empty()) {
        out << "\"\"";
      } else {
        out << std::quoted(str_copy(str));
      }
    }
    break;
  }
  case reflection::CLASS: {
    out << "CLASS{" << SHOW(x.dex_type) << x.potential_dex_types << "}";
    break;
  }
  case reflection::FIELD: {
    out << "FIELD{" << SHOW(x.dex_type) << x.potential_dex_types << ":"
        << SHOW(x.dex_string) << "}";
    break;
  }
  case reflection::METHOD: {
    out << "METHOD{" << SHOW(x.dex_type) << x.potential_dex_types << ":"
        << SHOW(x.dex_string);

    if (x.dex_type_array) {
      out << "(";
      for (const auto* type : *x.dex_type_array) {
        out << (type != nullptr ? type->str() : "?");
      }
      out << ")";
    }

    out << "}";
    break;
  }
  }
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const reflection::AbstractObjectDomain& x) {
  if (x.is_top()) {
    out << "TOP";
  } else if (x.is_bottom()) {
    out << "BOTTOM";
  } else {
    out << *(x.get_object());
  }
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const reflection::ClassObjectSource& cls_src) {
  switch (cls_src) {
  case reflection::NON_REFLECTION: {
    out << "NON_REFLECTION";
    break;
  }
  case reflection::REFLECTION: {
    out << "REFLECTION";
    break;
  }
  }
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const reflection::ReflectionAbstractObject& aobj) {
  out << aobj.first;
  if (aobj.first.is_class() && aobj.second) {
    out << "(" << *aobj.second << ")";
  }
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const reflection::ReflectionSites& sites) {
  out << "[";
  bool is_first_insn = true;
  for (const auto& insn_to_env : sites) {
    if (is_first_insn) {
      is_first_insn = false;
    } else {
      out << ", ";
    }
    out << show(insn_to_env.first) << " -> {";
    bool is_first_reg = true;
    for (const auto& reg_to_refl_obj : insn_to_env.second) {
      if (is_first_reg) {
        is_first_reg = false;
      } else {
        out << ", ";
      }
      out << "(" << show(reg_to_refl_obj.first) << ", "
          << reg_to_refl_obj.second << ")";
    }
    out << "}";
  }
  out << "]";
  return out;
}

namespace reflection {

AbstractHeapAddress allocate_heap_address() {
  static std::atomic<AbstractHeapAddress> addr{1};
  return addr.fetch_add(1, std::memory_order_relaxed);
}

bool is_not_reflection_output(const AbstractObject& obj) {
  switch (obj.obj_kind) {
  case reflection::OBJECT:
  case reflection::INT:
  case reflection::STRING:
    return true;
  default:
    return false;
  }
}

bool operator==(const AbstractObject& x, const AbstractObject& y) {
  if (x.obj_kind != y.obj_kind) {
    return false;
  }
  switch (x.obj_kind) {
  case INT: {
    return x.dex_int == y.dex_int;
  }
  case OBJECT: {
    return x.dex_type == y.dex_type &&
           x.potential_dex_types == y.potential_dex_types &&
           x.heap_address == y.heap_address &&
           x.dex_type_array == y.dex_type_array;
  }
  case CLASS: {
    return x.dex_type == y.dex_type &&
           x.potential_dex_types == y.potential_dex_types;
  }
  case STRING: {
    return x.dex_string == y.dex_string;
  }
  case FIELD: {
    return x.dex_type == y.dex_type &&
           x.potential_dex_types == y.potential_dex_types &&
           x.dex_string == y.dex_string;
  }
  case METHOD: {
    return x.dex_type == y.dex_type &&
           x.potential_dex_types == y.potential_dex_types &&
           x.dex_string == y.dex_string && x.dex_type_array == y.dex_type_array;
  }
  }
}

bool operator!=(const AbstractObject& x, const AbstractObject& y) {
  return !(x == y);
}

bool AbstractObject::leq(const AbstractObject& other) const {
  // Check if `other` is a general CLASS or OBJECT
  if (obj_kind == other.obj_kind) {
    switch (obj_kind) {
    case AbstractObjectKind::INT: {
      if (other.dex_int == std::nullopt) {
        return true;
      }
      break;
    }
    case AbstractObjectKind::CLASS:
    case AbstractObjectKind::OBJECT:
      if ((dex_type != nullptr) && other.dex_type == nullptr) {
        return true;
      }
      if (dex_type_array && other.dex_type_array == std::nullopt) {
        return true;
      }
      if ((heap_address != 0u) && other.heap_address == 0) {
        return true;
      }
      break;
    case AbstractObjectKind::STRING:
      if (other.dex_string == nullptr) {
        return true;
      }
      break;
    case AbstractObjectKind::FIELD:
      if (other.dex_type == nullptr && other.dex_string == nullptr) {
        return true;
      }
      break;
    case AbstractObjectKind::METHOD:
      if (other.dex_type == nullptr && other.dex_string == nullptr) {
        return true;
      }
      if (dex_type_array && other.dex_type_array == std::nullopt) {
        return true;
      }
      break;
    }
  }
  return equals(other);
}

bool AbstractObject::equals(const AbstractObject& other) const {
  return *this == other;
}

sparta::AbstractValueKind AbstractObject::join_with(
    const AbstractObject& other) {
  if (other.leq(*this)) {
    // We are higher on the lattice
    return sparta::AbstractValueKind::Value;
  }
  if (obj_kind != other.obj_kind) {
    return sparta::AbstractValueKind::Top;
  }

  switch (obj_kind) {
  case AbstractObjectKind::INT:
    // Be conservative and drop the int
    dex_int = std::nullopt;
    break;
  case AbstractObjectKind::OBJECT:
  case AbstractObjectKind::CLASS:
    // Be conservative and drop the type info
    dex_type = nullptr;
    heap_address = 0;
    dex_type_array = std::nullopt;
    potential_dex_types.clear();
    break;
  case AbstractObjectKind::STRING:
    // Be conservative and drop the string info
    dex_string = nullptr;
    break;
  case AbstractObjectKind::FIELD:
  case AbstractObjectKind::METHOD:
    // Be conservative and drop the field and method info
    dex_type = nullptr;
    dex_string = nullptr;
    dex_type_array = std::nullopt;
    potential_dex_types.clear();
    break;
  }
  return sparta::AbstractValueKind::Value;
}

sparta::AbstractValueKind AbstractObject::meet_with(
    const AbstractObject& other) {
  if (leq(other)) {
    // We are lower on the lattice
    return sparta::AbstractValueKind::Value;
  }
  if (other.leq(*this)) {
    *this = other;
    return sparta::AbstractValueKind::Value;
  }
  return sparta::AbstractValueKind::Bottom;
}

namespace impl {

using namespace ir_analyzer;

using ClassObjectSourceDomain =
    sparta::ConstantAbstractDomain<ClassObjectSource>;

using BasicAbstractObjectEnvironment =
    PatriciaTreeMapAbstractEnvironment<reg_t, AbstractObjectDomain>;

using ClassObjectSourceEnvironment =
    PatriciaTreeMapAbstractEnvironment<reg_t, ClassObjectSourceDomain>;

using HeapClassArrayEnvironment = PatriciaTreeMapAbstractEnvironment<
    AbstractHeapAddress,
    ConstantAbstractDomain<std::vector<const DexType*>>>;

using ReturnValueDomain = AbstractObjectDomain;

class AbstractObjectEnvironment final
    : public ReducedProductAbstractDomain<AbstractObjectEnvironment,
                                          BasicAbstractObjectEnvironment,
                                          ClassObjectSourceEnvironment,
                                          HeapClassArrayEnvironment,
                                          ReturnValueDomain,
                                          CallingContextMap> {
 public:
  using ReducedProductAbstractDomain::ReducedProductAbstractDomain;

  static void reduce_product(std::tuple<BasicAbstractObjectEnvironment,
                                        ClassObjectSourceEnvironment,
                                        HeapClassArrayEnvironment,
                                        ReturnValueDomain,
                                        CallingContextMap>& /* product */) {}

  const AbstractObjectDomain& get_abstract_obj(reg_t reg) const {
    return get<0>().get(reg);
  }

  const BasicAbstractObjectEnvironment& get_basic_abstract_obj_env() const {
    return get<0>();
  }

  void set_abstract_obj(reg_t reg, const AbstractObjectDomain& aobj) {
    apply<0>([&](auto env) { env->set(reg, aobj); }, true);
  }

  void update_abstract_obj(
      reg_t reg,
      const std::function<AbstractObjectDomain(const AbstractObjectDomain&)>&
          operation) {
    apply<0>([&](auto env) { env->update(reg, operation); }, true);
  }

  const ClassObjectSourceDomain& get_class_source(reg_t reg) const {
    return get<1>().get(reg);
  }

  void set_class_source(reg_t reg, const ClassObjectSourceDomain& cls_src) {
    apply<1>([&](auto env) { env->set(reg, cls_src); }, true);
  }

  const ConstantAbstractDomain<std::vector<const DexType*>>&
  get_heap_class_array(AbstractHeapAddress addr) const {
    return get<2>().get(addr);
  }

  void set_heap_class_array(
      AbstractHeapAddress addr,
      const ConstantAbstractDomain<std::vector<const DexType*>>& array) {
    apply<2>([&](auto env) { env->set(addr, array); }, true);
  }

  void set_heap_addr_to_top(AbstractHeapAddress addr) {
    auto domain = get_heap_class_array(addr);
    domain.set_to_top();
    set_heap_class_array(addr, domain);
  }

  const ReturnValueDomain& get_return_value() const { return get<3>(); }

  void join_return_value(const ReturnValueDomain& domain) {
    apply<3>([&](auto original) { original->join_with(domain); }, true);
  }

  CallingContextMap get_calling_context_partition() const { return get<4>(); }

  void set_calling_context(const IRInstruction* insn,
                           const CallingContext& context) {
    apply<4>([&](auto partition) { partition->set(insn, context); }, true);
  }
};

class Analyzer final : public BaseIRAnalyzer<AbstractObjectEnvironment> {
 public:
  explicit Analyzer(const DexMethod* dex_method,
                    const cfg::ControlFlowGraph& cfg,
                    SummaryQueryFn* summary_query_fn,
                    const MetadataCache* cache)
      : BaseIRAnalyzer(cfg),
        m_dex_method(dex_method),
        m_cfg(cfg),
        m_summary_query_fn(summary_query_fn),
        m_cache(cache) {}

  static std::optional<std::reference_wrapper<const AbstractObjectDomain>>
  maybe_get_value_type_parameter(CallingContext* context,
                                 param_index_t param_position) {
    if (context == nullptr) {
      return std::nullopt;
    }
    // This is a regular parameter of the method.
    const auto& param_abstract_obj = context->get(param_position);
    if (param_abstract_obj.is_value()) {
      return param_abstract_obj;
    }
    return std::nullopt;
  }

  void run(CallingContext* context) {
    // We need to compute the initial environment by assigning the parameter
    // registers their correct abstract object derived from the method's
    // signature. The IOPCODE_LOAD_PARAM_* instructions are pseudo-operations
    // that are used to specify the formal parameters of the method. They must
    // be interpreted separately.
    //
    // Note that we do not try to infer them as STRINGs.
    // Since we don't have the actual value of the string other than their
    // type being String. Also for CLASSes, the exact Java type they refer to is
    // not available here.
    auto init_state = AbstractObjectEnvironment::top();
    m_return_value.set_to_bottom();
    const auto* signature = m_dex_method->get_proto()->get_args();
    auto sig_it = signature->begin();
    param_index_t param_position = 0;

    for (const auto& mie :
         InstructionIterable(m_cfg.get_param_instructions())) {
      IRInstruction* insn = mie.insn;
      switch (insn->opcode()) {
      case IOPCODE_LOAD_PARAM_OBJECT: {
        if (param_position == 0 && !is_static(m_dex_method)) {
          // If the method is not static, the first parameter corresponds to
          // `this`.
          update_non_string_input(&init_state, insn, m_dex_method->get_class());
        } else {
          const DexType* type = *sig_it;
          always_assert(sig_it++ != signature->end());
          auto maybe_value_param =
              maybe_get_value_type_parameter(context, param_position);
          if (maybe_value_param) {
            // Parameter domain is provided with the calling context.
            init_state.set_abstract_obj(insn->dest(), maybe_value_param->get());
          } else {
            update_non_string_input(&init_state, insn, type);
          }
        }
        param_position++;
        break;
      }
      case IOPCODE_LOAD_PARAM:
      case IOPCODE_LOAD_PARAM_WIDE: {
        default_semantics(insn, &init_state);
        param_position++;
        break;
      }
      default:
        not_reached();
      }
    }

    MonotonicFixpointIterator::run(init_state);
    populate_environments(m_cfg);
  }

  void analyze_instruction(
      const IRInstruction* insn,
      AbstractObjectEnvironment* current_state) const override {
    AbstractObjectDomain callee_return;
    callee_return.set_to_bottom();
    if (opcode::is_an_invoke(insn->opcode())) {
      CallingContext cc;
      auto srcs = insn->srcs();
      for (param_index_t i = 0; i < srcs.size(); i++) {
        reg_t src = insn->src(i);
        const auto& aobj = current_state->get_abstract_obj(src);
        cc.set(i, aobj);
      }
      if (!cc.is_bottom()) {
        current_state->set_calling_context(insn, cc);
      }

      if (m_summary_query_fn != nullptr) {
        callee_return = (*m_summary_query_fn)(insn);
      }
    }

    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM:
    case IOPCODE_LOAD_PARAM_OBJECT:
    case IOPCODE_LOAD_PARAM_WIDE: {
      // IOPCODE_LOAD_PARAM_* instructions have been processed before the
      // analysis.
      break;
    }
    case OPCODE_MOVE:
    case OPCODE_MOVE_OBJECT: {
      const auto& aobj = current_state->get_abstract_obj(insn->src(0));
      current_state->set_abstract_obj(insn->dest(), aobj);
      set_class_source(insn->src(0), insn->dest(), aobj, current_state);
      break;
    }
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case OPCODE_MOVE_RESULT_OBJECT: {
      const auto& aobj = current_state->get_abstract_obj(RESULT_REGISTER);
      current_state->set_abstract_obj(insn->dest(), aobj);
      set_class_source(RESULT_REGISTER, insn->dest(), aobj, current_state);
      break;
    }
    case OPCODE_CONST: {
      current_state->set_abstract_obj(
          insn->dest(),
          AbstractObjectDomain(AbstractObject(insn->get_literal())));
      break;
    }
    case OPCODE_CONST_STRING: {
      set_abstract_obj(RESULT_REGISTER, insn->get_string(), current_state);
      break;
    }
    case OPCODE_CONST_CLASS: {
      set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::CLASS,
                       insn->get_type(), current_state);
      set_reflect_cls_source(RESULT_REGISTER, current_state);
      break;
    }
    case OPCODE_CHECK_CAST: {
      const auto& aobj = current_state->get_abstract_obj(insn->src(0));
      set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::OBJECT,
                       insn->get_type(), current_state);
      set_class_source(insn->src(0), RESULT_REGISTER, aobj, current_state);
      // Note that this is sound. In a concrete execution, if the check-cast
      // operation fails, an exception is thrown and the control point
      // following the check-cast becomes unreachable, which corresponds to
      // _|_ in the abstract domain. Any abstract state is a sound
      // approximation of _|_.
      break;
    }
    case OPCODE_INSTANCE_OF: {
      const auto& aobj = current_state->get_abstract_obj(insn->src(0));
      auto obj = aobj.get_object();
      // Append the referenced type here to the potential dex types list.
      // Doing this increases the type information we have at the reflection
      // site. It's up to the user of the analysis how to interpret this
      // information.
      if (obj && (obj->is_object()) && (obj->dex_type != nullptr)) {
        const auto* dex_type = insn->get_type();
        if (obj->dex_type != dex_type) {
          obj->potential_dex_types.insert(dex_type);
          current_state->set_abstract_obj(
              insn->src(0),
              AbstractObjectDomain(AbstractObject(obj->obj_kind, obj->dex_type,
                                                  obj->potential_dex_types)));
        }
      }

      break;
    }
    case OPCODE_AGET_OBJECT: {
      const auto array_object =
          current_state->get_abstract_obj(insn->src(0)).get_object();
      if (array_object) {
        const auto* type = array_object->dex_type;
        if ((type != nullptr) && type::is_array(type)) {
          auto* const etype = type::make_array_component_type(type);
          update_non_string_input(current_state, insn, etype);
          break;
        }
      }
      default_semantics(insn, current_state);
      break;
    }
    case OPCODE_APUT_OBJECT: {
      // insn format: aput <source> <array> <offset>
      const auto source_object =
          current_state->get_abstract_obj(insn->src(0)).get_object();
      const auto array_object =
          current_state->get_abstract_obj(insn->src(1)).get_object();
      const auto offset_object =
          current_state->get_abstract_obj(insn->src(2)).get_object();

      if (source_object && source_object->is_class() && array_object &&
          array_object->is_known_class_array() && offset_object &&
          offset_object->is_int()) {

        const auto* type = source_object->dex_type;
        std::optional<int64_t> offset = offset_object->dex_int;
        auto class_array =
            current_state->get_heap_class_array(array_object->heap_address)
                .get_constant();

        if (offset && class_array && *offset >= 0 &&
            class_array->size() > (size_t)*offset) {
          (*class_array)[*offset] = const_cast<DexType*>(type);
          current_state->set_heap_class_array(
              array_object->heap_address,
              ConstantAbstractDomain<std::vector<const DexType*>>(
                  *class_array));
        }
      }
      if (source_object && source_object->is_known_class_array()) {
        current_state->set_heap_addr_to_top(source_object->heap_address);
      }
      default_semantics(insn, current_state);
      break;
    }
    case OPCODE_IPUT_OBJECT:
    case OPCODE_SPUT_OBJECT: {
      const auto source_object =
          current_state->get_abstract_obj(insn->src(0)).get_object();
      if (source_object && source_object->is_known_class_array()) {
        current_state->set_heap_addr_to_top(source_object->heap_address);
      }
      break;
    }
    case OPCODE_IGET_OBJECT:
    case OPCODE_SGET_OBJECT: {
      always_assert(insn->has_field());
      auto* const field = insn->get_field();
      const DexType* primitive_type = check_primitive_type_class(field);
      if (primitive_type != nullptr) {
        // The field being accessed is a Class object to a primitive type
        // likely being used for reflection
        set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::CLASS,
                         primitive_type, current_state);
        set_reflect_cls_source(RESULT_REGISTER, current_state);
      } else {
        update_non_string_input(current_state, insn, field->get_type());
      }
      break;
    }
    case OPCODE_NEW_INSTANCE: {
      set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::OBJECT,
                       insn->get_type(), current_state);
      break;
    }
    case OPCODE_NEW_ARRAY: {
      const auto* array_type = insn->get_type();
      always_assert(type::is_array(array_type));
      auto* component_type = type::make_array_component_type(array_type);
      if (component_type == type::java_lang_Class()) {
        const auto aobj =
            current_state->get_abstract_obj(insn->src(0)).get_object();

        if (aobj && aobj->is_int() && aobj->dex_int) {
          AbstractHeapAddress addr = allocate_heap_address();
          int64_t size = *(aobj->dex_int);
          std::vector<const DexType*> array(size);
          ConstantAbstractDomain<std::vector<const DexType*>> heap_array(array);
          current_state->set_heap_class_array(addr, heap_array);
          current_state->set_abstract_obj(
              RESULT_REGISTER,
              AbstractObjectDomain(
                  AbstractObject(AbstractObjectKind::OBJECT, addr)));
          break;
        }
      }
      set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::OBJECT,
                       insn->get_type(), current_state);
      break;
    }
    case OPCODE_FILLED_NEW_ARRAY: {
      const auto* array_type = insn->get_type();
      always_assert(type::is_array(array_type));
      auto* component_type = type::make_array_component_type(array_type);
      AbstractObject aobj(AbstractObjectKind::OBJECT, insn->get_type());
      if (component_type == type::java_lang_Class()) {
        auto arg_count = insn->srcs_size();
        std::vector<const DexType*> known_types;
        known_types.reserve(arg_count);

        // collect known types from the filled new array
        for (auto src_reg : insn->srcs()) {
          auto reg_obj = current_state->get_abstract_obj(src_reg).get_object();
          if (reg_obj && reg_obj->is_class() &&
              (reg_obj->dex_type != nullptr)) {
            known_types.push_back(const_cast<DexType*>(reg_obj->dex_type));
          }
        }

        if (known_types.size() == arg_count) {
          AbstractHeapAddress addr = allocate_heap_address();
          ConstantAbstractDomain<std::vector<const DexType*>> heap_array(
              known_types);
          current_state->set_heap_class_array(addr, heap_array);
          aobj = AbstractObject(AbstractObjectKind::OBJECT, addr);
        }
      }

      current_state->set_abstract_obj(RESULT_REGISTER,
                                      AbstractObjectDomain(aobj));
      break;
    }
    case OPCODE_INVOKE_VIRTUAL: {
      auto receiver =
          current_state->get_abstract_obj(insn->src(0)).get_object();
      if (!receiver) {
        update_return_object_and_invalidate_heap_args(current_state, insn,
                                                      callee_return);
        break;
      }
      process_virtual_call(insn, *receiver, current_state, callee_return);
      break;
    }
    case OPCODE_INVOKE_STATIC: {
      if (insn->get_method() == m_cache->for_name) {
        auto class_name =
            current_state->get_abstract_obj(insn->src(0)).get_object();
        if (class_name && class_name->is_string()) {
          if (class_name->dex_string != nullptr) {
            const auto* internal_name =
                DexString::make_string(java_names::external_to_internal(
                    class_name->dex_string->str()));
            set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::CLASS,
                             DexType::make_type(internal_name), current_state);
          } else {
            set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::CLASS,
                             nullptr, current_state);
          }

          set_reflect_cls_source(RESULT_REGISTER, current_state);
          break;
        }
      }
      update_return_object_and_invalidate_heap_args(current_state, insn,
                                                    callee_return);
      break;
    }
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT: {
      update_return_object_and_invalidate_heap_args(current_state, insn,
                                                    callee_return);
      break;
    }
    case OPCODE_RETURN_OBJECT: {
      this->m_return_value.join_with(
          current_state->get_abstract_obj(insn->src(0)));
      break;
    }
    default: {
      default_semantics(insn, current_state);
    }
    }
  }

  std::optional<AbstractObject> get_abstract_object(size_t reg,
                                                    IRInstruction* insn) const {
    auto it = m_environments.find(insn);
    if (it == m_environments.end()) {
      return std::nullopt;
    }
    return it->second.get_abstract_obj(reg).get_object();
  }

  const AbstractObjectEnvironment& get_abstract_object_env(
      IRInstruction* insn) const {
    auto it = m_environments.find(insn);
    if (it == m_environments.end()) {
      static const AbstractObjectEnvironment empty_environment;
      return empty_environment;
    }
    return it->second;
  }

  std::optional<ClassObjectSource> get_class_source(size_t reg,
                                                    IRInstruction* insn) const {
    auto it = m_environments.find(insn);
    if (it == m_environments.end()) {
      return std::nullopt;
    }
    auto boost_val = it->second.get_class_source(reg).get_constant();
    return boost_val ? std::make_optional(*boost_val) : std::nullopt;
  }

  const AbstractObjectDomain& get_return_value() const {
    return m_return_value;
  }

  const AbstractObjectEnvironment& get_exit_state() const {
    return get_exit_state_at(m_cfg.exit_block());
  }

 private:
  const DexMethod* m_dex_method;
  const cfg::ControlFlowGraph& m_cfg;
  // Mapping from instruction to the AOEnvironment after the instruction.
  // For instance, a const-class produces a CLASS obj. The mapping here includes
  // an entry from the const-class instruction to the AOEnvironment where the
  // created CLASS obj is at RESULT_REGISTER.
  UnorderedMap<IRInstruction*, AbstractObjectEnvironment> m_environments;
  mutable AbstractObjectDomain m_return_value;
  SummaryQueryFn* m_summary_query_fn;

  const MetadataCache* m_cache;

  void update_non_string_input(AbstractObjectEnvironment* current_state,
                               const IRInstruction* insn,
                               const DexType* type) const {
    auto dest_reg =
        insn->has_move_result_any() ? RESULT_REGISTER : insn->dest();
    if (type == type::java_lang_Class()) {
      // We don't have precise type information to which the Class obj refers
      // to.
      set_abstract_obj(dest_reg, AbstractObjectKind::CLASS, nullptr,
                       current_state);
      current_state->set_class_source(
          dest_reg, ClassObjectSourceDomain(ClassObjectSource::NON_REFLECTION));
    } else {
      set_abstract_obj(dest_reg, AbstractObjectKind::OBJECT, type,
                       current_state);
    }
  }

  const DexType* check_primitive_type_class(const DexFieldRef* field) const {

    auto type = m_cache->primitive_field_to_type.find(field);
    if (type != m_cache->primitive_field_to_type.end()) {
      return type->second;
    } else {
      return nullptr;
    }
  }

  void set_abstract_obj(const reg_t dest,
                        const DexString* s,
                        AbstractObjectEnvironment* current_state) const {
    current_state->set_abstract_obj(dest,
                                    AbstractObjectDomain(AbstractObject(s)));
  }

  void set_abstract_obj(const reg_t dest,
                        const AbstractObjectKind kind,
                        const DexType* type,
                        AbstractObjectEnvironment* current_state) const {
    current_state->set_abstract_obj(
        dest, AbstractObjectDomain(AbstractObject(kind, type)));
  }

  void set_class_source(const reg_t src,
                        const reg_t dest,
                        const AbstractObjectDomain& aobj,
                        AbstractObjectEnvironment* current_state) const {
    const auto obj = aobj.get_object();
    if (obj && obj->is_class()) {
      current_state->set_class_source(dest,
                                      current_state->get_class_source(src));
    }
  }

  void set_reflect_cls_source(const reg_t /*dest*/,
                              AbstractObjectEnvironment* current_state) const {
    current_state->set_class_source(
        RESULT_REGISTER,
        ClassObjectSourceDomain(ClassObjectSource::REFLECTION));
  }

  void update_return_object_and_invalidate_heap_args(
      AbstractObjectEnvironment* current_state,
      const IRInstruction* insn,
      const AbstractObjectDomain& callee_return) const {

    invalidate_argument_heap_objects(current_state, insn);
    DexMethodRef* callee = insn->get_method();
    DexType* return_type = callee->get_proto()->get_rtype();
    if (type::is_void(return_type) || !type::is_object(return_type)) {
      return;
    }
    if (callee_return.is_value()) {
      current_state->set_abstract_obj(RESULT_REGISTER, callee_return);
    } else {
      update_non_string_input(current_state, insn, return_type);
    }
  }

  void default_semantics(const IRInstruction* insn,
                         AbstractObjectEnvironment* current_state) const {
    // For instructions that are transparent for this analysis, we just need
    // to clobber the destination registers in the abstract environment. Note
    // that this also covers the MOVE_RESULT_* and MOVE_RESULT_PSEUDO_*
    // instructions following operations that are not considered by this
    // analysis. Hence, the effect of those operations is correctly abstracted
    // away regardless of the size of the destination register.
    if (insn->has_dest()) {
      current_state->set_abstract_obj(insn->dest(),
                                      AbstractObjectDomain::top());
      if (insn->dest_is_wide()) {
        current_state->set_abstract_obj(insn->dest() + 1,
                                        AbstractObjectDomain::top());
      }
    }
    // We need to invalidate RESULT_REGISTER if the instruction writes into
    // this register.
    if (insn->has_move_result_any()) {
      current_state->set_abstract_obj(RESULT_REGISTER,
                                      AbstractObjectDomain::top());
    }
  }

  const DexString* get_dex_string_from_insn(
      AbstractObjectEnvironment* current_state,
      const IRInstruction* insn,
      reg_t reg) const {
    auto element_name =
        current_state->get_abstract_obj(insn->src(reg)).get_object();
    if (element_name && element_name->is_string()) {
      return element_name->dex_string;
    } else {
      return nullptr;
    }
  }

  bool is_method_known_to_preserve_args(DexMethodRef* method) const {
    const std::set<DexMethodRef*, dexmethods_comparator> known_methods{
        m_cache->get_method,
        m_cache->get_declared_method,
    };
    return known_methods.count(method) != 0u;
  }

  void invalidate_argument_heap_objects(
      AbstractObjectEnvironment* current_state,
      const IRInstruction* insn) const {

    if (!insn->has_method() ||
        is_method_known_to_preserve_args(insn->get_method())) {
      return;
    }

    for (const auto reg : insn->srcs()) {
      auto aobj = current_state->get_abstract_obj(reg).get_object();
      if (!aobj) {
        continue;
      }
      auto addr = aobj->heap_address;
      if (addr == 0u) {
        continue;
      }
      current_state->set_heap_addr_to_top(addr);
    }
  }

  void process_virtual_call(const IRInstruction* insn,
                            const AbstractObject& receiver,
                            AbstractObjectEnvironment* current_state,
                            const AbstractObjectDomain& callee_return) const {
    DexMethodRef* callee = insn->get_method();
    switch (receiver.obj_kind) {
    case INT: {
      // calling on int, not valid
      break;
    }
    case OBJECT: {
      if (callee == m_cache->get_class) {
        current_state->set_abstract_obj(
            RESULT_REGISTER,
            AbstractObjectDomain(AbstractObject(AbstractObjectKind::CLASS,
                                                receiver.dex_type,
                                                receiver.potential_dex_types)));
        set_reflect_cls_source(RESULT_REGISTER, current_state);
        return;
      }
      break;
    }
    case STRING: {
      if (callee == m_cache->get_class) {
        set_abstract_obj(RESULT_REGISTER, AbstractObjectKind::CLASS,
                         type::java_lang_String(), current_state);
        set_reflect_cls_source(RESULT_REGISTER, current_state);
        return;
      }
      break;
    }
    case CLASS: {
      AbstractObjectKind element_kind;
      const DexString* element_name = nullptr;
      std::optional<std::vector<const DexType*>> method_param_types =
          std::nullopt;
      if (callee == m_cache->get_method ||
          callee == m_cache->get_declared_method) {
        element_kind = METHOD;
        element_name = get_dex_string_from_insn(current_state, insn, 1);
        auto arr_reg = insn->src(2); // holds java.lang.Class array
        auto arr_obj = current_state->get_abstract_obj(arr_reg).get_object();
        if (arr_obj && arr_obj->is_known_class_array()) {
          auto maybe_array =
              current_state->get_heap_class_array(arr_obj->heap_address)
                  .get_constant();
          if (maybe_array) {
            method_param_types = *maybe_array;
          }
        }
      } else if (callee == m_cache->get_constructor ||
                 callee == m_cache->get_declared_constructor) {
        element_kind = METHOD;
        element_name = DexString::get_string("<init>");
        auto arr_reg = insn->src(1);
        auto arr_obj = current_state->get_abstract_obj(arr_reg).get_object();
        if (arr_obj && arr_obj->is_known_class_array()) {
          auto maybe_array =
              current_state->get_heap_class_array(arr_obj->heap_address)
                  .get_constant();
          if (maybe_array) {
            method_param_types = *maybe_array;
          }
        }
      } else if (callee == m_cache->get_field ||
                 callee == m_cache->get_declared_field) {
        element_kind = FIELD;
        element_name = get_dex_string_from_insn(current_state, insn, 1);
      } else if (callee == m_cache->get_fields ||
                 callee == m_cache->get_declared_fields) {
        element_kind = FIELD;
        element_name = DexString::get_string("");
      } else if (callee == m_cache->get_methods ||
                 callee == m_cache->get_declared_methods) {
        element_kind = METHOD;
        element_name = DexString::get_string("");
      } else if (callee == m_cache->get_constructors ||
                 callee == m_cache->get_declared_constructors) {
        element_kind = METHOD;
        element_name = DexString::get_string("<init>");
      }
      if (element_name == nullptr) {
        break;
      }
      AbstractObject aobj(element_kind,
                          receiver.dex_type,
                          element_name,
                          receiver.potential_dex_types);
      if (method_param_types) {
        aobj.dex_type_array = method_param_types;
      }
      current_state->set_abstract_obj(RESULT_REGISTER,
                                      AbstractObjectDomain(aobj));
      return;
    }
    case FIELD:
    case METHOD: {
      if ((receiver.is_field() && callee == m_cache->get_field_name) ||
          (receiver.is_method() && callee == m_cache->get_method_name)) {
        current_state->set_abstract_obj(
            RESULT_REGISTER,
            AbstractObjectDomain(AbstractObject(receiver.dex_string)));
        return;
      }
      break;
    }
    }
    update_return_object_and_invalidate_heap_args(current_state, insn,
                                                  callee_return);
  }

  // After the fixpoint iteration completes, we replay the analysis on all
  // blocks and we cache the abstract state at each instruction. This cache is
  // used by get_abstract_object() to query the state of a register at a given
  // instruction. Since we use an abstract domain based on Patricia trees, the
  // memory footprint of storing the abstract state at each program point is
  // small.
  void populate_environments(const cfg::ControlFlowGraph& cfg) {
    // We reserve enough space for the map in order to avoid repeated
    // rehashing during the computation.
    m_environments.reserve(cfg.num_blocks() * 16);
    for (cfg::Block* block : cfg.blocks()) {
      AbstractObjectEnvironment current_state = get_entry_state_at(block);
      for (auto& mie : InstructionIterable(block)) {
        IRInstruction* insn = mie.insn;
        analyze_instruction(insn, &current_state);
        m_environments.emplace(insn, current_state);
      }
    }
  }
};

} // namespace impl

ReflectionAnalysis::~ReflectionAnalysis() {
  if (m_fallback_cache != nullptr) {
    delete m_fallback_cache;
    m_fallback_cache = nullptr;
  }
}

ReflectionAnalysis::ReflectionAnalysis(DexMethod* dex_method,
                                       CallingContext* context,
                                       SummaryQueryFn* summary_query_fn,
                                       const MetadataCache* cache)
    : m_dex_method(dex_method) {
  always_assert(dex_method != nullptr);
  IRCode* code = dex_method->get_code();
  if (code == nullptr) {
    return;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  if (cache == nullptr) {
    m_fallback_cache = new MetadataCache;
    cache = m_fallback_cache;
  }
  m_analyzer = std::make_unique<impl::Analyzer>(dex_method, cfg,
                                                summary_query_fn, cache);
  m_analyzer->run(context);
}

void ReflectionAnalysis::gather_reflection_sites(
    IRInstruction* insn,
    std::map<reg_t, ReflectionAbstractObject>* abstract_objects) const {
  const auto& env =
      m_analyzer->get_abstract_object_env(insn).get_basic_abstract_obj_env();
  if (env.kind() != AbstractValueKind::Value) {
    return;
  }
  for (auto&& [reg, domain] : env.bindings()) {
    auto aobj = domain.get_object();
    if (!aobj) {
      continue;
    }
    if (is_not_reflection_output(*aobj)) {
      continue;
    }
    std::optional<ClassObjectSource> cls_src =
        aobj->is_class() ? m_analyzer->get_class_source(reg, insn)
                         : std::nullopt;
    if (aobj->is_class() && cls_src == ClassObjectSource::NON_REFLECTION) {
      continue;
    }
    if (traceEnabled(REFL, 5)) {
      std::ostringstream out;
      out << "reg " << reg << " " << *aobj << " ";
      if (cls_src) {
        out << *cls_src;
      }
      out << '\n';
      TRACE(REFL, 5, " reflection site: %s", out.str().c_str());
    }
    (*abstract_objects)[reg] = ReflectionAbstractObject(*aobj, cls_src);
  }
}

ReflectionSites ReflectionAnalysis::get_reflection_sites() const {
  ReflectionSites reflection_sites;
  auto* code = const_cast<DexMethod*>(m_dex_method)->get_code();
  if (code == nullptr) {
    return reflection_sites;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  for (auto& mie : InstructionIterable(cfg)) {
    IRInstruction* insn = mie.insn;
    std::map<reg_t, ReflectionAbstractObject> abstract_objects;
    gather_reflection_sites(insn, &abstract_objects);

    if (!abstract_objects.empty()) {
      reflection_sites.emplace_back(insn, std::move(abstract_objects));
    }
  }
  return reflection_sites;
}

AbstractObjectDomain ReflectionAnalysis::get_return_value() const {
  if (!m_analyzer) {
    // Method has no code, or is a native method.
    return AbstractObjectDomain::top();
  }
  return m_analyzer->get_return_value();
}

std::optional<std::vector<const DexType*>>
ReflectionAnalysis::get_method_params(IRInstruction* invoke_insn) const {
  auto* code = const_cast<DexMethod*>(m_dex_method)->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  IRInstruction* move_result_insn = nullptr;
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (insn == invoke_insn) {
      auto move_res_it = cfg.move_result_of(it);
      if (!move_res_it.is_end()) {
        move_result_insn = move_res_it->insn;
      }
      break;
    }
  }
  if ((move_result_insn == nullptr) ||
      !opcode::is_a_move_result(move_result_insn->opcode())) {
    return std::nullopt;
  }
  auto arg_param = get_abstract_object(RESULT_REGISTER, move_result_insn);
  if (!arg_param || !arg_param->is_method()) {
    return std::nullopt;
  }
  return arg_param->dex_type_array;
}

bool ReflectionAnalysis::has_found_reflection() const {
  return !get_reflection_sites().empty();
}

std::optional<AbstractObject> ReflectionAnalysis::get_abstract_object(
    size_t reg, IRInstruction* insn) const {
  if (m_analyzer == nullptr) {
    return std::nullopt;
  }
  return m_analyzer->get_abstract_object(reg, insn);
}

std::optional<ClassObjectSource> ReflectionAnalysis::get_class_source(
    size_t reg, IRInstruction* insn) const {
  if (m_analyzer == nullptr) {
    return std::nullopt;
  }
  return m_analyzer->get_class_source(reg, insn);
}

CallingContextMap ReflectionAnalysis::get_calling_context_partition() const {
  if (m_analyzer == nullptr) {
    return CallingContextMap::top();
  }
  return this->m_analyzer->get_exit_state().get_calling_context_partition();
}

} // namespace reflection
