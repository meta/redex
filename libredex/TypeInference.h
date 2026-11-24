/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <ostream>
#include <vector>

#include <sparta/FiniteAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/ReducedProductAbstractDomain.h>

#include "BaseIRAnalyzer.h"
#include "DexAnnotation.h"
#include "DexTypeEnvironment.h"
#include "MethodOverrideGraph.h"

/*
 * This is the implementation of a type checker for the IR that aims at
 * detecting errors such as fetching a reference from a register containing an
 * integer, or incorrectly accessing the pair of registers holding a wide value.
 * Our purpose is not to replicate the Android verifier, which performs
 * fine-grained compatibility checks on scalars of various bitwidths and tracks
 * the precise type of references. This type checker is intended to be used as a
 * sanity check at the end of an optimization pass and it has been designed for
 * high performance. For more information, please see the following link, which
 * points to the code of the Android verifier (there is no requirements
 * specification document):
 *
 *   androidxref.com/7.1.1_r6/xref/art/runtime/verifier/method_verifier.cc
 *
 * We first infer the type of all registers by performing a monotonic fixpoint
 * iteration sequence over the following type lattice:
 *
 *
 *                                   TOP
 *                                    |
 *         +-----------+--------------+---------------+
 *         |           |              |               |
 *         |         SCALAR        SCALAR1         SCALAR2
 *         |         /   \          /    \          /    \
 *         |        /     \        /      \        /      \
 *     REFERENCE  INT    FLOAT  LONG1  DOUBLE1  LONG2  DOUBLE2
 *         |        \     /        \      /        \      /
 *         |         \   /          \    /          \    /
 *         |         CONST          CONST1          CONST2
 *         |           |              |               |
 *         |           |              |               |
 *         +-----+-----+              |               |
 *               |                    |               |
 *             ZERO                   |               |
 *               |                    |               |
 *               +--------------------+---------------+
 *                                    |
 *                                  BOTTOM
 *
 *
 * The const-* operations of the Dalvik bytecode are not typed. Until the
 * context provides additional information, a constant (resp. wide constant) can
 * be either a long or a float (resp. a long or a double), hence the need for
 * the CONST types. The value of the constant doesn't matter unless it's a
 * 32-bit constant equal to 0. Zero needs to be treated specially because it's
 * also used to represent the null reference. Since a type is attached to a
 * 32-bit register, we need two mirror sets of distinct types for a pair of
 * registers holding a wide value.
 *
 * The SCALAR types are required to handle array access operations properly.
 * Although most aget-* operations are typed, this is not the case for aget (the
 * same holds for aput-* operations). This operation can retrieve either an
 * integer or a floating-point number, depending on the type of the array
 * (aget-wide has the same issue). The Android verifier tracks the precise type
 * of references and is able to resolve the type of the element statically. We
 * don't want to do that here for efficiency purposes, hence the need for the
 * SCALAR types, which encode the uncertainty about the actual type of the array
 * element. This means that the checker might not be able to detect type errors
 * in these situations. However, we can refine these types as soon as the
 * context provides enough information.
 *
 * Example:
 *   aget v0, v1, v2     --> v0 has SCALAR type
 *   add-int v3, v0, v4  --> we don't know whether v0 holds an integer value
 *   mul-int v5, v0, v4  --> if we reach this instruction, it means that v0 did
 *   ...                     hold an integer value (otherwise the code would
 *                           have been rejected by the Android verifier). This
 *                           operation is therefore well typed.
 *
 *   We don't know if the first use of a register with SCALAR type in a
 *   typed context is correct. However, after that first use, the register's
 *   type is fully determined. If the first use of the register was erroneous it
 *   would be rejected by the Android verifier and hence, all subsequent uses
 *   would never be executed.
 *
 * As is standard in Abstract Interpretation, the BOTTOM type corresponds to
 * unreachable code. Note that any code that follows a type error is interpreted
 * as unreachable (because it can never be executed). The TOP type corresponds
 * to an undefined behavior, because the register either hasn't been initialized
 * or holds different types along the branches of a merge node in the
 * control-flow graph.
 */

enum class IRType {
  BOTTOM,
  ZERO,
  CONST,
  CONST1,
  CONST2,
  REFERENCE,
  INT,
  FLOAT,
  LONG1,
  LONG2,
  DOUBLE1,
  DOUBLE2,
  SCALAR,
  SCALAR1,
  SCALAR2,
  TOP
};

/*
 * The IRType enum class does not differentiate between the different integral
 * types. This IntType enum class contains all the primitive integral types and
 * their conversions. The type lattice below is from the conversion relationship
 * in the Dalvik verifier
 * http://androidxref.com/4.4_r1/xref/dalvik/vm/analysis/CodeVerify.cpp#271
 *
 *                              TOP
 *                               |
 *                              INT
 *                               |
 *         +--------------------------------------------+
 *         |                                            |
 *        SHORT                                       CHAR
 *         |                                            |
 *        BYTE                                          |
 *         |                                            |
 *         ----------------------+-----------------------
 *                               |
 *                            BOOLEAN
 *                               |
 *                             BOTTOM
 */

enum class IntType { TOP, INT, CHAR, SHORT, BOOLEAN, BYTE, BOTTOM };

std::ostream& operator<<(std::ostream& output, const IRType& type);
std::ostream& operator<<(std::ostream& output, const IntType& type);

namespace type_inference {

// if one of these annotations has the str_typedef_anno or int_typedef_anno
// annotation, return it
std::optional<const DexType*> get_typedef_annotation(
    const std::vector<std::unique_ptr<DexAnnotation>>& annotations,
    const UnorderedSet<const DexType*>& typedef_annotations);

template <typename DexMember>
std::optional<const DexType*> get_typedef_anno_from_member(
    const DexMember* member,
    const UnorderedSet<const DexType*>& typedef_annotations) {
  if (!typedef_annotations.empty() && member->is_def()) {
    auto member_def = member->as_def();
    auto anno_set = member_def->get_anno_set();
    if (anno_set) {
      return get_typedef_annotation(anno_set->get_annotations(),
                                    typedef_annotations);
    }
  }
  return std::nullopt;
}
/*
 * Checks whether a (joined) type can be safely used in the presence of if-
 * instructions. Note that in the case of REFERENCE, joining of array types
 * might still cause problems with array instructions.
 */
bool is_safely_usable_in_ifs(IRType type);
bool is_safely_usable_in_ifs(IntType type);

using std::placeholders::_1;

using TypeLattice = sparta::BitVectorLattice<IRType,
                                             /* kCardinality */ 16>;
using IntTypeLattice = sparta::BitVectorLattice<IntType,
                                                /* kCardinality */ 7>;

extern TypeLattice type_lattice;
extern IntTypeLattice int_type_lattice;

using TypeDomain = sparta::FiniteAbstractDomain<IRType,
                                                TypeLattice,
                                                TypeLattice::Encoding,
                                                &type_lattice>;
using IntTypeDomain = sparta::FiniteAbstractDomain<IntType,
                                                   IntTypeLattice,
                                                   IntTypeLattice::Encoding,
                                                   &int_type_lattice>;

using namespace ir_analyzer;

using BasicTypeEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, TypeDomain>;

using IntTypeEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, IntTypeDomain>;

/*
 * Note that we only track the register DexTypeDomain mapping here. We always
 * take the declared DexType when reading a field. We do not track more precise
 * DexType for fields for individual intraprocedural analysis.
 * The reason is that the analysis can be incomplete. A field can potentially
 * be written by another thread concurrently. That write is visible to the
 * reads of the method we are analyzing currently. We could lose type
 * information if we don't consider write from other methods. Therefore, we stay
 * with the declared field type for local type inference.
 */
class TypeEnvironment final
    : public sparta::ReducedProductAbstractDomain<TypeEnvironment,
                                                  BasicTypeEnvironment,
                                                  RegTypeEnvironment,
                                                  IntTypeEnvironment> {

 public:
  using ReducedProductAbstractDomain::ReducedProductAbstractDomain;

  static void reduce_product(std::tuple<BasicTypeEnvironment,
                                        RegTypeEnvironment,
                                        IntTypeEnvironment>& /* product */) {}

  TypeDomain get_type(reg_t reg) const { return get<0>().get(reg); }
  IntTypeDomain get_int_type(reg_t reg) const { return get<2>().get(reg); }

  void set_type(reg_t reg, const TypeDomain& type) {
    apply<0>([=](auto env) { env->set(reg, type); }, true);
  }

  void set_type(reg_t reg, const IntTypeDomain& type) {
    apply<2>([=](auto env) { env->set(reg, type); }, true);
  }

  void update_type(
      reg_t reg,
      const std::function<TypeDomain(const TypeDomain&)>& operation) {
    apply<0>([=](auto env) { env->update(reg, operation); }, true);
  }
  void update_type(
      reg_t reg,
      const std::function<IntTypeDomain(const IntTypeDomain&)>& operation) {
    apply<2>([=](auto env) { env->update(reg, operation); }, true);
  }

  std::optional<const DexType*> get_dex_type(reg_t reg) const {
    return get<1>().get(reg).get_dex_type();
  }

  std::optional<const DexType*> get_annotation(reg_t reg) const {
    return get<1>().get(reg).get_annotation_type();
  }

  DexTypeDomain get_type_domain(reg_t reg) const { return get<1>().get(reg); }

  void set_dex_type(reg_t reg, const DexTypeDomain& dex_type) {
    apply<1>([=](auto env) { env->set(reg, dex_type); }, true);
  }

  void reset_dex_type(reg_t reg) {
    apply<1>([=](auto env) { env->set(reg, DexTypeDomain::top()); }, true);
  }
};

// The catch type of `throw_edge`, Throwable for a catch-all.
const DexType* get_catch_type(const cfg::Edge* throw_edge);

// The catch types of the throw edges into `catch_block`.
std::vector<const DexType*> get_catch_types(const cfg::Block* catch_block);

/*
 * The type of the exceptions a catch block catches: the join of its catch
 * types. Nothing where the block has no throw edge into it or the join gives
 * up.
 */
std::optional<const DexType*> caught_exception_type(
    const cfg::Block* catch_block);

class TypeInference final
    : public ir_analyzer::BaseIRAnalyzer<TypeEnvironment> {
 public:
  explicit TypeInference(
      const cfg::ControlFlowGraph& cfg,
      bool skip_check_cast_upcasting = false,
      UnorderedSet<const DexType*> annotations = UnorderedSet<const DexType*>(),
      const method_override_graph::Graph* method_override_graph = nullptr)
      : ir_analyzer::BaseIRAnalyzer<TypeEnvironment>(cfg),
        m_cfg(cfg),
        m_skip_check_cast_upcasting(skip_check_cast_upcasting),
        m_annotations(std::move(annotations)),
        m_method_override_graph(method_override_graph) {}

  void run(const DexMethod* dex_method);

  void run(bool is_static,
           const DexType* declaring_type,
           DexTypeList* args,
           const ParamAnnotations* param_anno = nullptr);

  void analyze_node(const cfg::GraphInterface::NodeId& node,
                    TypeEnvironment* current_state) const override {
    for (auto& mie : InstructionIterable(node)) {
      analyze_instruction(mie.insn, current_state, node);
    }
  }

  void analyze_instruction(const IRInstruction* insn,
                           TypeEnvironment* current_state) const override {

    analyze_instruction(insn, current_state, nullptr);
  }

  void analyze_instruction(const IRInstruction* insn,
                           TypeEnvironment* current_state,
                           const cfg::Block* current_block) const;

  void print(std::ostream& output) const;

  void traceState(TypeEnvironment* state) const;

  const UnorderedMap<const IRInstruction*, TypeEnvironment>&
  get_type_environments() const {
    return m_type_envs;
  }

  UnorderedMap<const IRInstruction*, TypeEnvironment>& get_type_environments() {
    return m_type_envs;
  }

  const UnorderedSet<const DexType*>& get_annotations() const {
    return m_annotations;
  }

 private:
  void populate_type_environments();

  const cfg::ControlFlowGraph& m_cfg;
  UnorderedMap<const IRInstruction*, TypeEnvironment> m_type_envs;
  const bool m_skip_check_cast_upcasting;
  const UnorderedSet<const DexType*> m_annotations;
  const method_override_graph::Graph* m_method_override_graph;
  const DexMethod* m;

  TypeDomain refine_type(const TypeDomain& type,
                         IRType expected,
                         IRType const_type,
                         IRType scalar_type) const;
  TypeDomain refine_type(const IntTypeDomain& type,
                         IntType expected,
                         IRType const_type,
                         IRType scalar_type) const;
  IntTypeDomain refine_type(const IntTypeDomain& type, IntType expected) const;
  void refine_type(TypeEnvironment* state, reg_t reg, IRType expected) const;
  void refine_type(TypeEnvironment* state, reg_t reg, IntType expected) const;
  void refine_wide_type(TypeEnvironment* state,
                        reg_t reg,
                        IRType expected1,
                        IRType expected2) const;
  void refine_reference(TypeEnvironment* state, reg_t reg) const;
  void refine_scalar(TypeEnvironment* state, reg_t reg) const;
  void refine_integral(TypeEnvironment* state, reg_t reg) const;
  void refine_float(TypeEnvironment* state, reg_t reg) const;
  void refine_wide_scalar(TypeEnvironment* state, reg_t reg) const;
  void refine_long(TypeEnvironment* state, reg_t reg) const;
  void refine_double(TypeEnvironment* state, reg_t reg) const;
  void refine_int(TypeEnvironment* state, reg_t reg) const;
  void refine_char(TypeEnvironment* state, reg_t reg) const;
  void refine_boolean(TypeEnvironment* state, reg_t reg) const;
  void refine_short(TypeEnvironment* state, reg_t reg) const;
  void refine_byte(TypeEnvironment* state, reg_t reg) const;

  bool is_pure_virtual_with_annotation(DexMethodRef* dex_method) const;
  // The typedef annotation of a value returned by calling `callee`. For a pure
  // virtual callee, every override must carry the same annotation.
  std::optional<const DexType*> get_return_typedef_anno(
      DexMethodRef* callee) const;
  void set_annotation(TypeEnvironment* state,
                      reg_t reg,
                      const DexType* type) const;
};

} // namespace type_inference
