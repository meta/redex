/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PointsToSemantics.h"

#include <algorithm>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <memory>
#include <ostream>
#include <tuple>
#include <utility>

#include <boost/container/flat_set.hpp>
#include <boost/container_hash/hash.hpp>

#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/PatriciaTreeSetAbstractDomain.h>

#include "BaseIRAnalyzer.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "PointsToSemanticsUtils.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace sparta;

s_expr PointsToVariable::to_s_expr() const {
  return s_expr({s_expr("V"), s_expr(m_id)});
}

std::optional<PointsToVariable> PointsToVariable::from_s_expr(const s_expr& e) {
  int32_t id;
  if (!s_patn({s_patn("V"), s_patn(&id)}).match_with(e)) {
    return {};
  }
  return {PointsToVariable(id)};
}

size_t hash_value(const PointsToVariable& v) {
  boost::hash<int32_t> hasher;
  return hasher(v.m_id);
}

bool operator==(const PointsToVariable& v, const PointsToVariable& w) {
  return v.m_id == w.m_id;
}

bool operator<(const PointsToVariable& v, const PointsToVariable& w) {
  return v.m_id < w.m_id;
}

std::ostream& operator<<(std::ostream& o, const PointsToVariable& v) {
  if (v.m_id == PointsToVariable::null_var_id()) {
    o << "NULL";
  } else if (v.m_id == PointsToVariable::this_var_id()) {
    o << "THIS";
  } else {
    o << "V" << v.m_id;
  }
  return o;
}

namespace pts_impl {

/* clang-format off */

#define OP_STRING_TABLE                 \
  {                                     \
    OP_STRING(PTS_CONST_STRING),        \
    OP_STRING(PTS_CONST_CLASS),         \
    OP_STRING(PTS_NEW_OBJECT),          \
    OP_STRING(PTS_GET_CLASS),           \
    OP_STRING(PTS_CHECK_CAST),          \
    OP_STRING(PTS_GET_EXCEPTION),       \
    OP_STRING(PTS_LOAD_PARAM),          \
    OP_STRING(PTS_RETURN),              \
    OP_STRING(PTS_DISJUNCTION),         \
    OP_STRING(PTS_IGET),                \
    OP_STRING(PTS_SGET),                \
    OP_STRING(PTS_IPUT),                \
    OP_STRING(PTS_SPUT),                \
    OP_STRING(PTS_IGET_SPECIAL),        \
    OP_STRING(PTS_IPUT_SPECIAL),        \
    OP_STRING(PTS_INVOKE_VIRTUAL),      \
    OP_STRING(PTS_INVOKE_SUPER),        \
    OP_STRING(PTS_INVOKE_DIRECT),       \
    OP_STRING(PTS_INVOKE_INTERFACE),    \
    OP_STRING(PTS_INVOKE_STATIC),       \
  }                                     \

#define OP_STRING(X) {X, #X}
UnorderedMap<PointsToOperationKind, std::string, std::hash<int>>
    op_to_string_table = OP_STRING_TABLE;
#undef OP_STRING

#define OP_STRING(X) {#X, X}
UnorderedMap<std::string, PointsToOperationKind> string_to_op_table =
    OP_STRING_TABLE;
#undef OP_STRING

/* clang-format on */

s_expr op_kind_to_s_expr(PointsToOperationKind kind) {
  auto it = op_to_string_table.find(kind);
  always_assert(it != op_to_string_table.end());
  return s_expr(it->second);
}

std::optional<PointsToOperationKind> string_to_op_kind(const std::string& str) {
  auto it = string_to_op_table.find(str);
  if (it == string_to_op_table.end()) {
    return {};
  }
  return std::optional<PointsToOperationKind>(it->second);
}

s_expr special_edge_to_s_expr(SpecialPointsToEdge edge) {
  switch (edge) {
  case PTS_ARRAY_ELEMENT: {
    return s_expr("PTS_ARRAY_ELEMENT");
  }
  }
}

std::optional<SpecialPointsToEdge> string_to_special_edge(
    const std::string& str) {
  if (str == "PTS_ARRAY_ELEMENT") {
    return {PTS_ARRAY_ELEMENT};
  }
  return {};
}

s_expr dex_method_to_s_expr(DexMethodRef* dex_method) {
  DexProto* proto = dex_method->get_proto();
  std::vector<s_expr> signature;
  for (const DexType* arg : *proto->get_args()) {
    signature.emplace_back(arg->get_name()->str());
  }
  return s_expr({s_expr(dex_method->get_class()->get_name()->str()),
                 s_expr(dex_method->get_name()->str()),
                 s_expr(proto->get_rtype()->get_name()->str()),
                 s_expr(signature)});
}

std::optional<DexMethodRef*> s_expr_to_dex_method(const s_expr& e) {
  std::string type_str;
  std::string name_str;
  std::string rtype_str;
  s_expr signature;
  if (!s_patn({s_patn(&type_str), s_patn(&name_str), s_patn(&rtype_str),
               s_patn({}, signature)})
           .match_with(e)) {
    return {};
  }
  DexTypeList::ContainerType types;
  for (size_t arg = 0; arg < signature.size(); ++arg) {
    if (!signature[arg].is_string()) {
      return {};
    }
    types.push_back(DexType::make_type(signature[arg].get_string()));
  }
  return {DexMethod::make_method(
      DexType::make_type(type_str),
      DexString::make_string(name_str),
      DexProto::make_proto(DexType::make_type(rtype_str),
                           DexTypeList::make_type_list(std::move(types))))};
}

} // namespace pts_impl

s_expr PointsToOperation::to_s_expr() const {
  using namespace pts_impl;
  switch (kind) {
  case PTS_CONST_STRING: {
    return s_expr({op_kind_to_s_expr(kind), s_expr(dex_string->str())});
  }
  case PTS_CONST_CLASS:
  case PTS_NEW_OBJECT:
  case PTS_CHECK_CAST: {
    return s_expr(
        {op_kind_to_s_expr(kind), s_expr(dex_type->get_name()->str())});
  }
  case PTS_GET_EXCEPTION:
  case PTS_GET_CLASS:
  case PTS_RETURN:
  case PTS_DISJUNCTION: {
    return s_expr({op_kind_to_s_expr(kind)});
  }
  case PTS_LOAD_PARAM: {
    return s_expr(
        {op_kind_to_s_expr(kind), s_expr(static_cast<int32_t>(parameter))});
  }
  case PTS_IGET:
  case PTS_SGET:
  case PTS_IPUT:
  case PTS_SPUT: {
    return s_expr({op_kind_to_s_expr(kind),
                   s_expr(dex_field->get_class()->get_name()->str()),
                   s_expr(dex_field->get_name()->str()),
                   s_expr(dex_field->get_type()->get_name()->str())});
  }
  case PTS_IGET_SPECIAL:
  case PTS_IPUT_SPECIAL: {
    return s_expr(
        {op_kind_to_s_expr(kind), special_edge_to_s_expr(special_edge)});
  }
  case PTS_INVOKE_VIRTUAL:
  case PTS_INVOKE_SUPER:
  case PTS_INVOKE_DIRECT:
  case PTS_INVOKE_INTERFACE:
  case PTS_INVOKE_STATIC: {
    return s_expr({op_kind_to_s_expr(kind), dex_method_to_s_expr(dex_method)});
  }
  }
}

std::optional<PointsToOperation> PointsToOperation::from_s_expr(
    const s_expr& e) {
  using namespace pts_impl;
  std::string op_kind_str;
  s_expr args;
  if (!s_patn({s_patn(&op_kind_str)}, args).match_with(e)) {
    return {};
  }
  auto op_kind_opt = string_to_op_kind(op_kind_str);
  if (!op_kind_opt) {
    return {};
  }
  PointsToOperationKind op_kind = *op_kind_opt;
  switch (op_kind) {
  case PTS_CONST_STRING: {
    std::string dex_string_str;
    if (!s_patn({s_patn(&dex_string_str)}).match_with(args)) {
      return {};
    }
    return {PointsToOperation(op_kind, DexString::make_string(dex_string_str))};
  }
  case PTS_CONST_CLASS:
  case PTS_NEW_OBJECT:
  case PTS_CHECK_CAST: {
    std::string dex_type_str;
    if (!s_patn({s_patn(&dex_type_str)}).match_with(args)) {
      return {};
    }
    return {PointsToOperation(op_kind, DexType::make_type(dex_type_str))};
  }
  case PTS_GET_EXCEPTION:
  case PTS_GET_CLASS:
  case PTS_RETURN:
  case PTS_DISJUNCTION: {
    return {PointsToOperation(op_kind)};
  }
  case PTS_LOAD_PARAM: {
    int32_t parameter;
    if (!s_patn({s_patn(&parameter)}).match_with(args)) {
      return {};
    }
    return {PointsToOperation(op_kind, static_cast<size_t>(parameter))};
  }
  case PTS_IGET:
  case PTS_SGET:
  case PTS_IPUT:
  case PTS_SPUT: {
    std::string container_str;
    std::string name_str;
    std::string type_str;
    if (!s_patn({s_patn(&container_str), s_patn(&name_str), s_patn(&type_str)})
             .match_with(args)) {
      return {};
    }
    return {PointsToOperation(
        op_kind,
        DexField::make_field(DexType::make_type(container_str),
                             DexString::make_string(name_str),
                             DexType::make_type(type_str)))};
  }
  case PTS_IGET_SPECIAL:
  case PTS_IPUT_SPECIAL: {
    std::string edge_str;
    if (!s_patn({s_patn(&edge_str)}).match_with(args)) {
      return {};
    }
    auto edge = string_to_special_edge(edge_str);
    if (!edge) {
      return {};
    }
    return {PointsToOperation(op_kind, *edge)};
  }
  case PTS_INVOKE_VIRTUAL:
  case PTS_INVOKE_SUPER:
  case PTS_INVOKE_DIRECT:
  case PTS_INVOKE_INTERFACE:
  case PTS_INVOKE_STATIC: {
    s_expr dex_method_expr;
    if (!s_patn({s_patn(dex_method_expr)}).match_with(args)) {
      return {};
    }
    auto dex_method_opt = s_expr_to_dex_method(dex_method_expr);
    if (!dex_method_opt) {
      return {};
    }
    return {PointsToOperation(op_kind, *dex_method_opt)};
  }
  }
}

namespace pts_impl {

// A wrapper for a set of variables. We use this structure for the generation of
// disjunctions.
class PointsToVariableSet {
 public:
  struct Hash {
    size_t operator()(const PointsToVariableSet& s) const {
      return boost::hash_range(s.m_set.begin(), s.m_set.end());
    }
  };

  struct EqualTo {
    bool operator()(const PointsToVariableSet& s1,
                    const PointsToVariableSet& s2) const {
      return s1.m_set == s2.m_set;
    }
  };

  using iterator = boost::container::flat_set<PointsToVariable>::const_iterator;

  PointsToVariableSet() = default;

  template <typename InputIterator>
  // NOLINTNEXTLINE(performance-unnecessary-value-param)
  PointsToVariableSet(InputIterator begin, InputIterator end)
      : m_set(begin, end) {}

  void insert(const PointsToVariable& v) { m_set.insert(v); }

  iterator begin() const { return m_set.begin(); }

  iterator end() const { return m_set.end(); }

 private:
  // Sets of variables correspond to sets of anchors and are generally small
  // (most of the time, just a singleton). We use a flat set (i.e., an ordered
  // associative array) in order to optimize memory usage.
  boost::container::flat_set<PointsToVariable> m_set;
};

} // namespace pts_impl

std::vector<std::pair<size_t, PointsToVariable>> PointsToAction::get_arguments()
    const {
  always_assert(m_operation.is_invoke() || m_operation.is_disjunction());
  std::vector<std::pair<size_t, PointsToVariable>> args;
  for (const auto& binding : m_arguments) {
    if (binding.first >= 0) {
      // We filter out special arguments (like the destination variable), which
      // all have a negative index.
      args.emplace_back(binding);
    }
  }
  return args;
}

PointsToAction PointsToAction::load_operation(
    const PointsToOperation& operation, PointsToVariable dest) {
  always_assert(operation.is_load());
  return PointsToAction(operation, {{dest_key(), dest}});
}

PointsToAction PointsToAction::get_class_operation(PointsToVariable dest,
                                                   PointsToVariable src) {
  return PointsToAction(PointsToOperation(PTS_GET_CLASS),
                        {{dest_key(), dest}, {src_key(), src}});
}

PointsToAction PointsToAction::check_cast_operation(const DexType* dex_type,
                                                    PointsToVariable dest,
                                                    PointsToVariable src) {
  return PointsToAction(PointsToOperation(PTS_CHECK_CAST, dex_type),
                        {{dest_key(), dest}, {src_key(), src}});
}

PointsToAction PointsToAction::get_operation(
    const PointsToOperation& operation,
    PointsToVariable dest,
    std::optional<PointsToVariable> instance) {
  always_assert(operation.is_get());
  always_assert(!instance || operation.kind != PTS_SPUT);
  if (instance) {
    return PointsToAction(operation,
                          {{dest_key(), dest}, {instance_key(), *instance}});
  } else {
    return PointsToAction(operation, {{dest_key(), dest}});
  }
}

PointsToAction PointsToAction::put_operation(
    const PointsToOperation& operation,
    PointsToVariable rhs,
    std::optional<PointsToVariable> lhs) {
  always_assert(operation.is_put());
  always_assert(!lhs || operation.kind != PTS_SPUT);
  if (lhs) {
    return PointsToAction(operation, {{lhs_key(), *lhs}, {rhs_key(), rhs}});
  } else {
    return PointsToAction(operation, {{rhs_key(), rhs}});
  }
}

PointsToAction PointsToAction::invoke_operation(
    const PointsToOperation& operation,
    std::optional<PointsToVariable> dest,
    std::optional<PointsToVariable> instance,
    const std::vector<std::pair<int32_t, PointsToVariable>>& args) {
  always_assert(operation.is_invoke());
  always_assert(!instance || operation.kind != PTS_INVOKE_STATIC);
  std::vector<std::pair<int32_t, PointsToVariable>> bindings;
  bindings.reserve(args.size() + 2);
  if (dest) {
    bindings.emplace_back(dest_key(), *dest);
  }
  if (instance) {
    bindings.emplace_back(instance_key(), *instance);
  }
  bindings.insert(bindings.end(), args.begin(), args.end());
  return PointsToAction(operation, bindings);
}

PointsToAction PointsToAction::return_operation(PointsToVariable src) {
  return PointsToAction(PointsToOperation(PTS_RETURN), {{src_key(), src}});
}

template <typename InputIterator>
PointsToAction PointsToAction::disjunction(
    PointsToVariable dest,
    // NOLINTNEXTLINE(performance-unnecessary-value-param)
    InputIterator first,
    // NOLINTNEXTLINE(performance-unnecessary-value-param)
    InputIterator last) {
  pts_impl::PointsToVariableSet vars(first, last);
  std::vector<std::pair<int32_t, PointsToVariable>> args;
  int32_t arg = 0;
  for (const auto& var : vars) {
    args.emplace_back(arg++, var);
  }
  args.emplace_back(dest_key(), dest);
  return PointsToAction(PointsToOperation(PTS_DISJUNCTION), args);
}

PointsToAction::PointsToAction(
    const PointsToOperation& operation,
    const std::vector<std::pair<int32_t, PointsToVariable>>& arguments)
    : m_operation(operation) {
  for (const auto& binding : arguments) {
    auto status = m_arguments.insert(binding);
    // Making sure that there's no duplicate binding in the argument list.
    always_assert(status.second);
  }
  m_arguments.shrink_to_fit();
}

PointsToVariable PointsToAction::get_arg(int32_t key) const {
  auto it = m_arguments.find(key);
  always_assert(it != m_arguments.end());
  return it->second;
}

s_expr PointsToAction::to_s_expr() const {
  std::vector<s_expr> args;
  for (const auto& arg : m_arguments) {
    args.push_back(s_expr({s_expr(arg.first), arg.second.to_s_expr()}));
  }
  return s_expr({m_operation.to_s_expr(), s_expr(args)});
}

std::optional<PointsToAction> PointsToAction::from_s_expr(const s_expr& e) {
  s_expr operation;
  s_expr args;
  if (!s_patn({s_patn(operation), s_patn({}, args)}).match_with(e)) {
    return {};
  }
  auto operation_opt = PointsToOperation::from_s_expr(operation);
  if (!operation_opt) {
    return {};
  }
  std::vector<std::pair<int32_t, PointsToVariable>> arguments;
  for (size_t i = 0; i < args.size(); ++i) {
    int32_t arg;
    s_expr var;
    if (!s_patn({s_patn(&arg), s_patn(var)}).match_with(args[i])) {
      return {};
    }
    auto var_opt = PointsToVariable::from_s_expr(var);
    if (!var_opt) {
      return {};
    }
    arguments.emplace_back(arg, *var_opt);
  }
  return {PointsToAction(*operation_opt, arguments)};
}

namespace pts_impl {

std::string special_edge_to_string(SpecialPointsToEdge e) {
  switch (e) {
  case PTS_ARRAY_ELEMENT: {
    return "ARRAY_ELEM";
  }
  default:
    not_reached();
  }
}

} // namespace pts_impl

std::ostream& operator<<(std::ostream& o, const PointsToAction& a) {
  const PointsToOperation& op = a.operation();
  switch (op.kind) {
  case PTS_CONST_STRING: {
    o << a.dest() << " = " << std::quoted(op.dex_string->str());
    break;
  }
  case PTS_CONST_CLASS: {
    o << a.dest() << " = CLASS<" << op.dex_type->get_name()->str() << ">";
    break;
  }
  case PTS_GET_EXCEPTION: {
    o << a.dest() << " = EXCEPTION";
    break;
  }
  case PTS_NEW_OBJECT: {
    o << a.dest() << " = NEW " << op.dex_type->get_name()->str();
    break;
  }
  case PTS_LOAD_PARAM: {
    o << a.dest() << " = PARAM " << op.parameter;
    break;
  }
  case PTS_GET_CLASS: {
    o << a.dest() << " = GET_CLASS(" << a.src() << ")";
    break;
  }
  case PTS_CHECK_CAST: {
    o << a.dest() << " = CAST<" << op.dex_type->get_name()->str() << ">("
      << a.src() << ")";
    break;
  }
  case PTS_IGET: {
    o << a.dest() << " = " << a.instance() << "."
      << op.dex_field->get_class()->get_name()->str() << "#"
      << op.dex_field->get_name()->str();
    break;
  }
  case PTS_IGET_SPECIAL: {
    o << a.dest() << " = " << pts_impl::special_edge_to_string(op.special_edge)
      << "(" << a.instance() << ")";
    break;
  }
  case PTS_SGET: {
    o << a.dest() << " = " << op.dex_field->get_class()->get_name()->str()
      << "#" << op.dex_field->get_name()->str();
    break;
  }
  case PTS_IPUT: {
    o << a.lhs() << "." << op.dex_field->get_class()->get_name()->str() << "#"
      << op.dex_field->get_name()->str() << " = " << a.rhs();
    break;
  }
  case PTS_IPUT_SPECIAL: {
    o << pts_impl::special_edge_to_string(op.special_edge) << "(" << a.lhs()
      << ") = " << a.rhs();
    break;
  }
  case PTS_SPUT: {
    o << op.dex_field->get_class()->get_name()->str() << "#"
      << op.dex_field->get_name()->str() << " = " << a.rhs();
    break;
  }
  case PTS_INVOKE_VIRTUAL:
  case PTS_INVOKE_SUPER:
  case PTS_INVOKE_DIRECT:
  case PTS_INVOKE_INTERFACE:
  case PTS_INVOKE_STATIC: {
    if (a.has_dest()) {
      o << a.dest() << " = ";
    }
    if (!op.is_static_call()) {
      o << a.instance() << ".{";
      switch (op.kind) {
      case PTS_INVOKE_VIRTUAL: {
        o << "V";
        break;
      }
      case PTS_INVOKE_SUPER: {
        o << "S";
        break;
      }
      case PTS_INVOKE_DIRECT: {
        o << "D";
        break;
      }
      case PTS_INVOKE_INTERFACE: {
        o << "I";
        break;
      }
      default: {
        not_reached();
      }
      }
      o << "}";
    }
    o << op.dex_method->get_class()->get_name()->str() << "#"
      << op.dex_method->get_name()->str() << "(";
    auto args = a.get_arguments();
    for (auto it = args.begin(); it != args.end(); ++it) {
      o << it->first << " => " << it->second;
      if (std::next(it) != args.end()) {
        o << ", ";
      }
    }
    o << ")";
    break;
  }
  case PTS_RETURN: {
    o << "RETURN " << a.src();
    break;
  }
  case PTS_DISJUNCTION: {
    o << a.dest() << " = ";
    auto args = a.get_arguments();
    for (auto it = args.begin(); it != args.end(); ++it) {
      o << it->second;
      if (std::next(it) != args.end()) {
        o << " U ";
      }
    }
    break;
  }
  }
  return o;
}

namespace pts_impl {

/*
 * In Andersen's approach to points-to analysis, a program is translated into a
 * system of set constraints by modeling pointers as sets. This model is
 * flow-insensitive, i.e., control-flow dependencies among statements are
 * abstracted away. While this makes the analysis more tractable, applying this
 * approach naively can lead to major precision problems. For example, consider
 * the following piece of Java code:
 *
 *   x = new A();
 *   x.field1 = new B();
 *   x.field2 = new C();
 *
 * The corresponding Dex code may look like:
 *
 *   new-instance v0, LA;
 *   invoke-direct {v0}, LA;.<init>:()V
 *   new-instance v1, LB;
 *   invoke-direct {v1}, LB;.<init>:()V
 *   iput-object v1, v0, LA;.field1:LB;
 *   new-instance v1, LC;
 *   invoke-direct {v1}, LC;.<init>:()V
 *   iput-object v1, v0, LA;.field2:LC;
 *
 * Applying Andersen's approach directly, we would assign a set variable to each
 * register in the code, thus obtaining the following system of set constraints:
 *
 *   V0 = NEW LA;
 *   V0.{D}LA;#<init>()
 *   V1 = NEW LB;
 *   V1.{D}LB;#<init>()
 *   V1 = NEW LC;
 *   V1.{D}LB;#<init>()
 *   V0.LA;#field1 = V1
 *   V0.LA;#field2 = V1
 *
 * This is obviously very bad, as the points-to sets of field1 and field2 are
 * equated. The problem here is that register v1 is reused in two different
 * contexts and that information is lost by the flow-insensitive abstraction. In
 * order to avoid this pitfall, we use the notion of `anchor` introduced in the
 * following paper:
 *
 *   A. Venet. A Scalable Nonuniform Pointer Analysis for Embedded Programs.
 *   In Proceedings of the International Static Analysis Symposium, 2004.
 *
 * Each operation returning a pointer is associated a unique `anchor`. A
 * preliminary intraprocedural, flow-sensitive analysis assigns a set of anchors
 * to each register. When the points-to equations are generated, we use the
 * anchors and not the registers as the basis for creating set variables. Hence,
 * the points-to equations for the code snippet above would look like:
 *
 *   V0 = NEW LA;
 *   V0.{D}LA;#<init>()
 *   V1 = NEW LB;
 *   V1.{D}LB;#<init>()
 *   V2 = NEW LC;
 *   V2.{D}LB;#<init>()
 *   V0.LA;#field1 = V1
 *   V0.LA;#field2 = V2
 *
 * The points-to sets of field1 and field2 are thus kept separate. We get the
 * same level of precision as if the code were in SSA form, without incurring
 * the cost of managing the SSA representation.
 */

using namespace std::placeholders;

using namespace ir_analyzer;

// We represent an anchor by a pointer to the corresponding instruction. An
// empty anchor set is semantically equivalent to the `null` reference.
using AnchorDomain = PatriciaTreeSetAbstractDomain<const IRInstruction*>;

using AnchorEnvironment =
    PatriciaTreeMapAbstractEnvironment<reg_t, AnchorDomain>;

class AnchorPropagation final : public BaseIRAnalyzer<AnchorEnvironment> {
 public:
  AnchorPropagation(const cfg::ControlFlowGraph& cfg, bool is_static_method)
      : BaseIRAnalyzer(cfg),
        m_is_static_method(is_static_method),
        m_cfg(cfg),
        m_this_anchor(nullptr) {}

  void analyze_instruction(const IRInstruction* insn,
                           AnchorEnvironment* current_state) const override {
    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM_OBJECT: {
      // There's nothing to do, since this instruction has been taken care of
      // during the initialization of the analysis.
      break;
    }
    case OPCODE_MOVE_EXCEPTION: {
      current_state->set(insn->dest(), AnchorDomain(insn));
      break;
    }
    case OPCODE_CONST_STRING:
    case OPCODE_CONST_CLASS:
    case OPCODE_CHECK_CAST:
    case OPCODE_NEW_INSTANCE:
    case OPCODE_NEW_ARRAY:
    case OPCODE_AGET_OBJECT:
    case OPCODE_IGET_OBJECT:
    case OPCODE_SGET_OBJECT:
    case OPCODE_FILLED_NEW_ARRAY: {
      current_state->set(RESULT_REGISTER, AnchorDomain(insn));
      break;
    }
    case OPCODE_MOVE_OBJECT: {
      current_state->set(insn->dest(), current_state->get(insn->src(0)));
      break;
    }
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case OPCODE_MOVE_RESULT_OBJECT: {
      current_state->set(insn->dest(), current_state->get(RESULT_REGISTER));
      break;
    }
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_INTERFACE: {
      DexMethodRef* dex_method = insn->get_method();
      if (type::is_object(dex_method->get_proto()->get_rtype())) {
        // We attach an anchor to a method invocation only if the method returns
        // an object.
        current_state->set(RESULT_REGISTER, AnchorDomain(insn));
      }
      break;
    }
    default: {
      // Since registers can be reused in different contexts, we need to
      // invalidate the corresponding anchor sets. Note that this case also
      // encompasses the initialization to null, like `const v1, 0`.
      if (insn->has_dest()) {
        current_state->set(insn->dest(), AnchorDomain());
        if (insn->dest_is_wide()) {
          current_state->set(insn->dest() + 1, AnchorDomain());
        }
      }
      // There is no need to invalidate RESULT_REGISTER, because all operations
      // that may write a reference into RESULT_REGISTER are handled in the
      // switch statement.
    }
    }
  }

  void run() { MonotonicFixpointIterator::run(initial_environment()); }

  bool is_this_anchor(const IRInstruction* insn) const {
    return insn == m_this_anchor;
  }

 private:
  // We initialize all registers to the empty anchor set, i.e. the semantic
  // equivalent of `null` in our analysis. However, the parameters of the method
  // are initialized to the anchors of the corresponding LOAD_PARAM
  // instructions.
  AnchorEnvironment initial_environment() {
    AnchorEnvironment env;
    // We first initialize all registers to `null`.
    env.set(RESULT_REGISTER, AnchorDomain());
    for (reg_t reg = 0; reg < m_cfg.get_registers_size(); ++reg) {
      env.set(reg, AnchorDomain());
    }
    // We then initialize the parameters of the method.
    bool first_param = true;
    for (const MethodItemEntry& mie :
         InstructionIterable(m_cfg.get_param_instructions())) {
      IRInstruction* insn = mie.insn;
      if (first_param && !m_is_static_method) {
        always_assert_log(insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT,
                          "Unexpected instruction '%s' in virtual method\n",
                          SHOW(insn));
        m_this_anchor = insn;
      }
      switch (insn->opcode()) {
      case IOPCODE_LOAD_PARAM_OBJECT: {
        env.set(insn->dest(), AnchorDomain(insn));
        break;
      }
      case IOPCODE_LOAD_PARAM:
      case IOPCODE_LOAD_PARAM_WIDE: {
        break;
      }
      default: {
        not_reached_log("Unexpected instruction '%s'\n", SHOW(insn));
      }
      }
      first_param = false;
    }
    return env;
  }

  bool m_is_static_method;
  const cfg::ControlFlowGraph& m_cfg;
  IRInstruction* m_this_anchor;
};

// Generates the points-to actions for a single method.
class PointsToActionGenerator final {
 public:
  explicit PointsToActionGenerator(DexMethod* dex_method,
                                   PointsToMethodSemantics* semantics,
                                   const TypeSystem& type_system,
                                   const PointsToSemanticsUtils& utils)
      : m_dex_method(dex_method),
        m_semantics(semantics),
        m_type_system(type_system),
        m_utils(utils) {}

  void run() {
    IRCode* code = m_dex_method->get_code();
    always_assert(code != nullptr);
    always_assert(code->cfg_built());
    cfg::ControlFlowGraph& cfg = code->cfg();
    cfg.calculate_exit_block();

    // We first propagate the anchors across the code.
    m_analysis =
        std::make_unique<AnchorPropagation>(cfg, is_static(m_dex_method));
    m_analysis->run();

    // Then we assign a unique variable to each anchor.
    name_anchors(cfg);

    // The LOAD_PARAM_* instructions sit next to each other at the beginning of
    // the entry block. We need to process them first.
    size_t param_cursor = 0;
    bool first_param = true;
    for (const MethodItemEntry& mie :
         InstructionIterable(cfg.get_param_instructions())) {
      IRInstruction* insn = mie.insn;
      switch (insn->opcode()) {
      case IOPCODE_LOAD_PARAM_OBJECT: {
        if (first_param && !is_static(m_dex_method)) {
          // If the method is not static, the first parameter corresponds to
          // `this`, which is represented using a special points-to variable.
        } else {
          m_semantics->add(PointsToAction::load_operation(
              PointsToOperation(PTS_LOAD_PARAM, param_cursor++),
              get_variable_from_anchor(insn)));
        }
        break;
      }
      case IOPCODE_LOAD_PARAM:
      case IOPCODE_LOAD_PARAM_WIDE: {
        ++param_cursor;
        break;
      }
      default:
        not_reached();
      }
      first_param = false;
    }

    // We go over each IR instruction and generate the corresponding points-to
    // actions.
    for (cfg::Block* block : cfg.blocks()) {
      AnchorEnvironment state = m_analysis->get_entry_state_at(block);
      for (const MethodItemEntry& mie : InstructionIterable(*block)) {
        IRInstruction* insn = mie.insn;
        generate_action(insn, state);
        m_analysis->analyze_instruction(insn, &state);
      }
    }
    m_semantics->shrink();
  }

 private:
  // We associate each anchor with a unique points-to variable.
  void name_anchors(const cfg::ControlFlowGraph& cfg) {
    for (cfg::Block* block : cfg.blocks()) {
      for (const MethodItemEntry& mie : *block) {
        if (mie.type == MFLOW_OPCODE) {
          IRInstruction* insn = mie.insn;
          if (is_anchored_instruction(insn)) {
            m_anchors.insert({insn, m_semantics->get_new_variable()});
          }
        }
      }
    }
  }

  // Each IR instruction that returns a result of reference type is assigned an
  // anchor.
  bool is_anchored_instruction(IRInstruction* insn) const {
    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM_OBJECT:
    case OPCODE_MOVE_EXCEPTION:
    case OPCODE_CONST_STRING:
    case OPCODE_CONST_CLASS:
    case OPCODE_CHECK_CAST:
    case OPCODE_NEW_INSTANCE:
    case OPCODE_NEW_ARRAY:
    case OPCODE_AGET_OBJECT:
    case OPCODE_IGET_OBJECT:
    case OPCODE_SGET_OBJECT:
    case OPCODE_FILLED_NEW_ARRAY: {
      return true;
    }
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_INTERFACE: {
      return type::is_object(insn->get_method()->get_proto()->get_rtype());
    }
    default: {
      return false;
    }
    }
  }

  void generate_action(IRInstruction* insn, const AnchorEnvironment& state) {
    switch (insn->opcode()) {
    case OPCODE_MOVE_EXCEPTION: {
      m_semantics->add(
          PointsToAction::load_operation(PointsToOperation(PTS_GET_EXCEPTION),
                                         get_variable_from_anchor(insn)));
      break;
    }
    case OPCODE_RETURN_OBJECT: {
      m_semantics->add(PointsToAction::return_operation(
          get_variable_from_anchor_set(state.get(insn->src(0)))));
      break;
    }
    case OPCODE_CONST_STRING: {
      m_semantics->add(PointsToAction::load_operation(
          PointsToOperation(PTS_CONST_STRING, insn->get_string()),
          get_variable_from_anchor(insn)));
      break;
    }
    case OPCODE_CONST_CLASS: {
      m_semantics->add(PointsToAction::load_operation(
          PointsToOperation(PTS_CONST_CLASS, insn->get_type()),
          get_variable_from_anchor(insn)));
      break;
    }
    case OPCODE_CHECK_CAST: {
      m_semantics->add(PointsToAction::check_cast_operation(
          insn->get_type(),
          get_variable_from_anchor(insn),
          get_variable_from_anchor_set(state.get(insn->src(0)))));
      break;
    }
    case OPCODE_NEW_INSTANCE: {
      const auto* dex_type = insn->get_type();
      if (m_type_system.is_subtype(type::java_lang_Throwable(), dex_type)) {
        // If the object created is an exception (i.e., its type inherits from
        // java.lang.Throwable), we use PTS_GET_EXCEPTION. In our semantic
        // model, the exact identity of an exception is abstracted away for
        // simplicity. The operation PTS_GET_EXCEPTION can be interpreted as a
        // nondeterministic choice among all abstract object instances that are
        // exceptions.
        m_semantics->add(
            PointsToAction::load_operation(PointsToOperation(PTS_GET_EXCEPTION),
                                           get_variable_from_anchor(insn)));
        break;
      }
      // Otherwise, we fall through to the generic case.
    }
      [[fallthrough]];
    case OPCODE_NEW_ARRAY:
    case OPCODE_FILLED_NEW_ARRAY: {
      m_semantics->add(PointsToAction::load_operation(
          PointsToOperation(PTS_NEW_OBJECT, insn->get_type()),
          get_variable_from_anchor(insn)));
      if (insn->opcode() == OPCODE_FILLED_NEW_ARRAY) {
        const DexType* element_type =
            type::make_array_element_type(insn->get_type());
        if (!type::is_object(element_type)) {
          break;
        }
        auto lhs =
            std::optional<PointsToVariable>(get_variable_from_anchor(insn));
        for (size_t i = 0; i < insn->srcs_size(); ++i) {
          m_semantics->add(PointsToAction::put_operation(
              PointsToOperation(PTS_IPUT_SPECIAL, PTS_ARRAY_ELEMENT),
              get_variable_from_anchor_set(state.get(insn->src(i))),
              lhs));
        }
      }
      break;
    }
    case OPCODE_APUT_OBJECT: {
      PointsToVariable rhs =
          get_variable_from_anchor_set(state.get(insn->src(0)));
      PointsToVariable lhs =
          get_variable_from_anchor_set(state.get(insn->src(1)));
      m_semantics->add(PointsToAction::put_operation(
          PointsToOperation(PTS_IPUT_SPECIAL, PTS_ARRAY_ELEMENT),
          rhs,
          std::optional<PointsToVariable>(lhs)));
      break;
    }
    case OPCODE_IPUT_OBJECT: {
      PointsToVariable rhs =
          get_variable_from_anchor_set(state.get(insn->src(0)));
      PointsToVariable lhs =
          get_variable_from_anchor_set(state.get(insn->src(1)));
      m_semantics->add(PointsToAction::put_operation(
          PointsToOperation(PTS_IPUT, insn->get_field()),
          rhs,
          std::optional<PointsToVariable>(lhs)));
      break;
    }
    case OPCODE_SPUT_OBJECT: {
      m_semantics->add(PointsToAction::put_operation(
          PointsToOperation(PTS_SPUT, insn->get_field()),
          get_variable_from_anchor_set(state.get(insn->src(0)))));
      break;
    }
    case OPCODE_AGET_OBJECT: {
      PointsToVariable instance =
          get_variable_from_anchor_set(state.get(insn->src(0)));
      m_semantics->add(PointsToAction::get_operation(
          PointsToOperation(PTS_IGET_SPECIAL, PTS_ARRAY_ELEMENT),
          get_variable_from_anchor(insn),
          std::optional<PointsToVariable>(instance)));
      break;
    }
    case OPCODE_IGET_OBJECT: {
      PointsToVariable instance =
          get_variable_from_anchor_set(state.get(insn->src(0)));
      m_semantics->add(PointsToAction::get_operation(
          PointsToOperation(PTS_IGET, insn->get_field()),
          get_variable_from_anchor(insn),
          std::optional<PointsToVariable>(instance)));
      break;
    }
    case OPCODE_SGET_OBJECT: {
      // One way to get the java.lang.Class object of a primitive type is by
      // querying the `TYPE` field of the corresponding wrapper class. We
      // translate those kind of sget-object instructions into equivalent
      // PTS_CONST_CLASS operations.
      if (m_utils.is_primitive_type_class_object_retrieval(insn)) {
        m_semantics->add(PointsToAction::load_operation(
            PointsToOperation(PTS_CONST_CLASS, insn->get_field()->get_class()),
            get_variable_from_anchor(insn)));
        break;
      }
      m_semantics->add(PointsToAction::get_operation(
          PointsToOperation(PTS_SGET, insn->get_field()),
          get_variable_from_anchor(insn)));
      break;
    }
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_INTERFACE: {
      translate_invoke(insn, state);
      break;
    }
    default: {
      // All other instructions are either transparent to points-to analysis or
      // have already been taken care of (LOAD_PARAM_*).
    }
    }
  }

  // This is where we can provide the semantics of external API calls that are
  // relevant to points-to analysis and for which the source code is either
  // unavailable or hard to process automatically (e.g., native methods).
  void translate_invoke(IRInstruction* insn, const AnchorEnvironment& state) {
    // Calls to java.lang.Object#getClass() are converted to a points-to
    // operation in order to simplify the analysis.
    if (m_utils.is_get_class_invocation(insn)) {
      m_semantics->add(PointsToAction::get_class_operation(
          get_variable_from_anchor(insn),
          get_variable_from_anchor_set(state.get(insn->src(0)))));
      return;
    }
    // Otherwise, we default to the general translation of method calls.
    default_invoke_translation(insn, state);
  }

  void default_invoke_translation(IRInstruction* insn,
                                  const AnchorEnvironment& state) {
    DexMethodRef* dex_method = insn->get_method();
    DexProto* proto = dex_method->get_proto();
    const auto* signature = proto->get_args();
    std::vector<std::pair<int32_t, PointsToVariable>> args;
    size_t src_idx{0};

    // Allocate a variable for the returned object if any.
    std::optional<PointsToVariable> dest;
    if (type::is_object(insn->get_method()->get_proto()->get_rtype())) {
      dest = {get_variable_from_anchor(insn)};
    }

    // Allocate a variable for the instance object if any.
    std::optional<PointsToVariable> instance;
    if (insn->opcode() != OPCODE_INVOKE_STATIC) {
      // The first argument is a reference to the object instance on which the
      // method is invoked.
      instance = {
          get_variable_from_anchor_set(state.get(insn->src(src_idx++)))};
    }

    // Process the arguments of the method invocation.
    int32_t arg_pos = 0;
    for (const DexType* dex_type : *signature) {
      if (type::is_object(dex_type)) {
        args.emplace_back(
            arg_pos,
            get_variable_from_anchor_set(state.get(insn->src(src_idx++))));
      } else {
        // We skip this argument.
        ++src_idx;
      }
      ++arg_pos;
    }

    // Select the right points-to operation.
    PointsToOperationKind invoke_kind;
    switch (insn->opcode()) {
    case OPCODE_INVOKE_STATIC: {
      invoke_kind = PTS_INVOKE_STATIC;
      break;
    }
    case OPCODE_INVOKE_VIRTUAL: {
      invoke_kind = PTS_INVOKE_VIRTUAL;
      break;
    }
    case OPCODE_INVOKE_SUPER: {
      invoke_kind = PTS_INVOKE_SUPER;
      break;
    }
    case OPCODE_INVOKE_DIRECT: {
      invoke_kind = PTS_INVOKE_DIRECT;
      break;
    }
    case OPCODE_INVOKE_INTERFACE: {
      invoke_kind = PTS_INVOKE_INTERFACE;
      break;
    }
    default: {
      // This function is only called on invoke instructions.
      not_reached();
    }
    }

    m_semantics->add(PointsToAction::invoke_operation(
        PointsToOperation(invoke_kind, insn->get_method()),
        dest,
        instance,
        args));
  }

  PointsToVariable get_variable_from_anchor(const IRInstruction* insn) {
    if (m_analysis->is_this_anchor(insn)) {
      return PointsToVariable::this_variable();
    }
    auto it = m_anchors.find(insn);
    always_assert(it != m_anchors.end());
    return it->second;
  }

  // If the anchor set is not a singleton, we need to introduce a disjunction
  // operation.
  PointsToVariable get_variable_from_anchor_set(const AnchorDomain& s) {
    // By design, the analysis can't generate the Top value.
    always_assert(!s.is_top());
    if (s.is_bottom()) {
      // This means that some code in the method is unreachable.
      TRACE(PTA, 2, "Unreachable code in %s", SHOW(m_dex_method));
      return PointsToVariable();
    }
    auto anchors = s.elements();
    if (anchors.empty()) {
      // The denotation of the anchor set is just the `null` reference. This is
      // represented by a special points-to variable.
      return PointsToVariable::null_variable();
    }
    if (anchors.size() == 1) {
      // When the anchor set is a singleton, there is no need to introduce a
      // disjunction.
      return get_variable_from_anchor(*anchors.begin());
    }
    // Otherwise, we need a disjunction.
    PointsToVariableSet ptv_set;
    for (const IRInstruction* insn : anchors) {
      ptv_set.insert(get_variable_from_anchor(insn));
    }
    auto it = m_anchor_sets.find(ptv_set);
    if (it != m_anchor_sets.end()) {
      // The disjunction has already been generated.
      return it->second;
    }
    // Otherwise, we create a new disjunction.
    PointsToVariable new_v = m_semantics->get_new_variable();
    m_anchor_sets.emplace(ptv_set, new_v);
    // We insert the newly created disjunction before its first use.
    m_semantics->add(
        PointsToAction::disjunction(new_v, ptv_set.begin(), ptv_set.end()));
    return new_v;
  }

  DexMethod* m_dex_method;
  PointsToMethodSemantics* m_semantics;
  const TypeSystem& m_type_system;
  const PointsToSemanticsUtils& m_utils;
  std::unique_ptr<AnchorPropagation> m_analysis;
  // We assign each anchor a points-to variable. This map keeps track of the
  // naming.
  UnorderedMap<const IRInstruction*, PointsToVariable> m_anchors;
  // A table that keeps track of all disjunctions already created, so that we
  // only generate one disjunction per anchor set.
  UnorderedMap<PointsToVariableSet,
               PointsToVariable,
               PointsToVariableSet::Hash,
               PointsToVariableSet::EqualTo>
      m_anchor_sets;
};

// Removes points-to equations that have no effect on the computation of the
// points-to analysis. We compute the dependency graph of the points-to
// equations and we discard all variables that are not involved in any relevant
// computation.
class Shrinker final {
 public:
  explicit Shrinker(std::vector<PointsToAction>* pt_actions)
      : m_pt_actions(pt_actions) {}

  void run() {
    // We first identify all the variables that we surely need to keep in order
    // to perform the points-to analysis.
    find_root_vars();
    // We then compute the dependency graph: there is an edge v -> w between
    // points-to variables v and w iff the value of w is needed to compute the
    // value of v.
    build_dependency_graph();
    // We compute the set of variables that are reachable from any one of the
    // root variables in the dependency graph.
    collect_reachable_vars();
    // We remove any points-to equation assigning a value to a variable that
    // hasn't been marked as reachable in the previous step.
    shrink_points_to_actions();
  }

 private:
  using VariableSet =
      UnorderedSet<PointsToVariable, boost::hash<PointsToVariable>>;

  // We keep all `put`, `invoke` and `return` operations, since they presumably
  // have an effect on the analysis.
  void find_root_vars() {
    for (const PointsToAction& pt_action : *m_pt_actions) {
      const PointsToOperation& op = pt_action.operation();
      if (op.is_put()) {
        if (!op.is_sput()) {
          m_root_vars.insert(pt_action.lhs());
        }
        m_root_vars.insert(pt_action.rhs());
        continue;
      }
      if (op.is_invoke()) {
        if (op.is_virtual_call()) {
          m_root_vars.insert(pt_action.instance());
        }
        for (const auto& arg : pt_action.get_arguments()) {
          m_root_vars.insert(arg.second);
        }
        continue;
      }
      if (op.is_return()) {
        m_root_vars.insert(pt_action.src());
        continue;
      }
    }
  }

  // When building the dependency graph, we are only interested in operations
  // that assign a value to a variable but don't create any points-to relation
  // between objects (unlike a `put` operation, for example). We don't consider
  // `load` operations, because they can't create dependencies among variables.
  // An edge v -> w in the dependency graph means that computing the value of
  // variable v requires the value of variable w.
  void build_dependency_graph() {
    for (const PointsToAction& pt_action : *m_pt_actions) {
      const PointsToOperation& op = pt_action.operation();
      if (op.is_get_class() || op.is_check_cast()) {
        add_dependency(pt_action.dest(), pt_action.src());
        continue;
      }
      if (op.is_get() && !op.is_sget()) {
        add_dependency(pt_action.dest(), pt_action.instance());
        continue;
      }
      if (op.is_disjunction()) {
        for (const auto& arg : pt_action.get_arguments()) {
          add_dependency(pt_action.dest(), arg.second);
        }
        continue;
      }
    }
  }

  void add_dependency(const PointsToVariable& x, const PointsToVariable& y) {
    m_dependency_graph[x].insert(y);
  }

  // If there exists a path from any root variable to a variable v, this means
  // that the value of variable v is required for performing the points-to
  // analysis. All other variables can safely be discarded. We compute the set
  // of reachable variables using a simple breadth-first traversal of the graph.
  void collect_reachable_vars() {
    std::deque<PointsToVariable> queue;
    insert_unordered_iterable(queue, queue.end(), m_root_vars);
    while (!queue.empty()) {
      PointsToVariable v = queue.back();
      queue.pop_back();
      // Note that the variables already visited are exactly the variables that
      // we need to keep.
      if (m_vars_to_keep.count(v) != 0) {
        continue;
      }
      m_vars_to_keep.insert(v);
      const auto& deps = m_dependency_graph[v];
      insert_unordered_iterable(queue, queue.end(), deps);
    }
  }

  void shrink_points_to_actions() {
    // Any `load`, `check_cast`, `get` or `disjunction` operation assigning a
    // value to a variable that hasn't been marked to keep can safely be
    // discarded.
    m_pt_actions->erase(
        std::remove_if(m_pt_actions->begin(),
                       m_pt_actions->end(),
                       [this](const PointsToAction& pt_action) {
                         const PointsToOperation& op = pt_action.operation();
                         return (op.is_load() || op.is_check_cast() ||
                                 op.is_get() || op.is_disjunction()) &&
                                (m_vars_to_keep.count(pt_action.dest()) == 0);
                       }),
        m_pt_actions->end());
    m_pt_actions->shrink_to_fit();

    // We can also safely remove the `dest` variable of a method call if it
    // hasn't been marked to keep. Computing the return value of a virtual call
    // during the analysis may entail performing the join of multiple points-to
    // sets, which is costly. Hence, removing unneeded return values is a
    // valuable optimization.
    for (PointsToAction& pt_action : *m_pt_actions) {
      if (pt_action.operation().is_invoke() && pt_action.has_dest() &&
          (m_vars_to_keep.count(pt_action.dest()) == 0)) {
        pt_action.remove_dest();
      }
    }
  }

  std::vector<PointsToAction>* m_pt_actions;
  UnorderedMap<PointsToVariable, VariableSet, boost::hash<PointsToVariable>>
      m_dependency_graph;
  VariableSet m_root_vars;
  VariableSet m_vars_to_keep;
};

/* clang-format off */

#define KIND_STRING_TABLE         \
  {                               \
    KIND_STRING(PTS_APK),         \
    KIND_STRING(PTS_ABSTRACT),    \
    KIND_STRING(PTS_NATIVE),      \
    KIND_STRING(PTS_STUB),        \
  }                               \

#define KIND_STRING(X) {X, #X}
UnorderedMap<MethodKind, std::string, std::hash<int>>
    method_kind_to_string_table = KIND_STRING_TABLE;
#undef KIND_STRING

#define KIND_STRING(X) {#X, X}
UnorderedMap<std::string, MethodKind> string_to_method_kind_table =
    KIND_STRING_TABLE;
#undef KIND_STRING

/* clang-format on */

s_expr method_kind_to_s_expr(MethodKind kind) {
  auto it = method_kind_to_string_table.find(kind);
  always_assert(it != method_kind_to_string_table.end());
  return s_expr(it->second);
}

std::optional<MethodKind> string_to_method_kind(const std::string& str) {
  auto it = string_to_method_kind_table.find(str);
  if (it == string_to_method_kind_table.end()) {
    return {};
  }
  return std::optional<MethodKind>(it->second);
}

} // namespace pts_impl

PointsToMethodSemantics::PointsToMethodSemantics(DexMethodRef* dex_method,
                                                 MethodKind kind,
                                                 int32_t start_var_id,
                                                 size_t size_hint)
    : m_dex_method(dex_method), m_kind(kind), m_variable_counter(start_var_id) {
  m_points_to_actions.reserve(size_hint);
}

void PointsToMethodSemantics::shrink() {
  pts_impl::Shrinker shrinker(&m_points_to_actions);
  shrinker.run();
}

s_expr PointsToMethodSemantics::to_s_expr() const {
  using namespace pts_impl;
  std::vector<s_expr> actions;
  std::transform(m_points_to_actions.begin(),
                 m_points_to_actions.end(),
                 std::back_inserter(actions),
                 [](const PointsToAction& a) { return a.to_s_expr(); });
  return s_expr({dex_method_to_s_expr(m_dex_method),
                 method_kind_to_s_expr(m_kind), s_expr(m_variable_counter),
                 s_expr(actions)});
}

std::optional<PointsToMethodSemantics> PointsToMethodSemantics::from_s_expr(
    const s_expr& e) {
  using namespace pts_impl;
  s_expr dex_method_expr;
  std::string kind_str;
  int32_t var_counter;
  s_expr actions_expr;
  if (!s_patn({s_patn(dex_method_expr), s_patn(&kind_str), s_patn(&var_counter),
               s_patn({}, actions_expr)})
           .match_with(e)) {
    return {};
  }
  auto dex_method_op = s_expr_to_dex_method(dex_method_expr);
  if (!dex_method_op) {
    return {};
  }
  auto kind_opt = string_to_method_kind(kind_str);
  if (!kind_opt) {
    return {};
  }
  PointsToMethodSemantics semantics(
      *dex_method_op, *kind_opt, var_counter, actions_expr.size());
  for (size_t i = 0; i < actions_expr.size(); ++i) {
    auto action_opt = PointsToAction::from_s_expr(actions_expr[i]);
    if (!action_opt) {
      return {};
    }
    semantics.add(*action_opt);
  }
  return std::optional<PointsToMethodSemantics>(semantics);
}

std::ostream& operator<<(std::ostream& o, const PointsToMethodSemantics& s) {
  o << s.m_dex_method->get_class()->get_name()->str() << "#"
    << s.m_dex_method->get_name()->str() << ": "
    << SHOW(s.m_dex_method->get_proto()) << " ";
  switch (s.kind()) {
  case PTS_ABSTRACT: {
    o << "= ABSTRACT";
    break;
  }
  case PTS_NATIVE: {
    o << "= NATIVE";
    break;
  }
  case PTS_APK:
  case PTS_STUB: {
    o << "{" << '\n';
    for (const auto& a : s.get_points_to_actions()) {
      o << " " << a << '\n';
    }
    o << "}";
    break;
  }
  }
  o << '\n';
  return o;
}

PointsToSemantics::PointsToSemantics(const Scope& scope, bool generate_stubs)
    : m_generate_stubs(generate_stubs), m_type_system(scope) {
  // We size the hash table so as to fit all the methods in scope.
  size_t method_count = 0;
  for (DexClass* dex_class : scope) {
    method_count +=
        dex_class->get_dmethods().size() + dex_class->get_vmethods().size();
  }
  m_method_semantics.reserve(method_count);

  // We initialize all entries in the hash table, which can then be concurrently
  // accessed by the workers using the thread-safe find() operation of
  // UnorderedMap.
  for (DexClass* dex_class : scope) {
    for (DexMethod* dmethod : dex_class->get_dmethods()) {
      initialize_entry(dmethod);
    }
    for (DexMethod* vmethod : dex_class->get_vmethods()) {
      initialize_entry(vmethod);
    }
  }

  // We generate a system of points-to actions for each Dex method in parallel.
  walk::parallel::methods(scope, [this](DexMethod* dex_method) {
    generate_points_to_actions(dex_method);
  });
}

void PointsToSemantics::load_stubs(const std::string& file_name) {
  std::ifstream file_input(file_name);
  s_expr_istream s_expr_input(file_input);
  while (s_expr_input.good()) {
    s_expr expr;
    s_expr_input >> expr;
    if (s_expr_input.eoi()) {
      break;
    }
    always_assert_log(
        !s_expr_input.fail(), "%s\n", s_expr_input.what().c_str());
    auto semantics_opt = PointsToMethodSemantics::from_s_expr(expr);
    always_assert_log(
        semantics_opt, "Couldn't parse S-expression: %s\n", expr.str().c_str());
    DexMethodRef* dex_method = semantics_opt->get_method();
    auto it = m_method_semantics.find(dex_method);
    if (it == m_method_semantics.end()) {
      m_method_semantics.emplace(dex_method, *semantics_opt);
    } else {
      TRACE(PTA, 2, "Collision with stub for method %s", SHOW(dex_method));
    }
  }
}

std::optional<PointsToMethodSemantics*> PointsToSemantics::get_method_semantics(
    DexMethodRef* dex_method) {
  auto entry = m_method_semantics.find(dex_method);
  if (entry == m_method_semantics.end()) {
    return {};
  }
  return std::optional<PointsToMethodSemantics*>(&entry->second);
}

MethodKind PointsToSemantics::default_method_kind() const {
  return m_generate_stubs ? PTS_STUB : PTS_APK;
}

void PointsToSemantics::initialize_entry(DexMethod* dex_method) {
  DexAccessFlags access_flags = dex_method->get_access();
  MethodKind kind;
  if (dex_method->get_code() == nullptr) {
    if ((access_flags & DexAccessFlags::ACC_ABSTRACT) != 0u) {
      kind = PTS_ABSTRACT;
    } else {
      // The definition of a method that is neither abstract nor native should
      // always have an associated IRCode component.
      redex_assert(access_flags & DexAccessFlags::ACC_NATIVE);
      kind = PTS_NATIVE;
    }
  } else {
    kind = default_method_kind();
  }
  m_method_semantics.emplace(std::piecewise_construct,
                             std::forward_as_tuple(dex_method),
                             std::forward_as_tuple(/* dex_method */ dex_method,
                                                   /* kind */ kind,
                                                   /* start_var_id */ 0,
                                                   /* size_hint */ 8));
}

void PointsToSemantics::generate_points_to_actions(DexMethod* dex_method) {
  // According to section [container.requirements.dataraces] of the C++ standard
  // definition document, the find() method of UnorderedMap is
  // thread-safe. Since this function operates on a single Dex method and the
  // hash table m_method_semantics is indexed by Dex methods, the following code
  // is not subject to data races.
  auto entry = m_method_semantics.find(dex_method);
  // All hash table entries have been initialized in the constructor.
  always_assert(entry != m_method_semantics.end());
  PointsToMethodSemantics* semantics = &entry->second;
  if (semantics->kind() == default_method_kind()) {
    pts_impl::PointsToActionGenerator generator(
        dex_method, semantics, m_type_system, m_utils);
    generator.run();
  }
}

std::ostream& operator<<(std::ostream& o, const PointsToSemantics& s) {
  for (const auto& entry : UnorderedIterable(s.m_method_semantics)) {
    o << entry.second;
  }
  return o;
}
