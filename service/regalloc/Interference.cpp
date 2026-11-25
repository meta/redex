/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Interference.h"

#include "Debug.h"
#include "DexOpcode.h"
#include "Show.h"

namespace regalloc {

namespace interference {

namespace impl {

/*
 * We determine a node's colorability using equation E.3 in [Smith00] for
 * registers of varying width in an unaligned architecture.
 *
 * Let w(n) be the width of a node n. E.3 says that n is colorable if the
 * following inequality holds:
 *
 *   ( ∑ ⌈w(j)/w(n)⌉ ) < ⌈register_frame_size / (2 * w(n) + 1)⌉
 *
 * where we take the summation over all nodes j that are adjacent to n. Note
 * that if w(x) = 1 for all nodes x, this reduces to Chaitin's criterion of
 * degree(n) < register_frame_size.
 *
 * To evaluate that inequality in our implementation, we treat ⌈w(j)/w(n)⌉ as
 * an "edge weight" -- but note that even though the edges are undirected,
 * in general edge_weight(u, v) != edge_weight(v, u).
 *
 * The LHS of the inequality is what we call the "node weight" in our
 * implementation -- it is the sum of the weights of its edges.
 *
 * Since this function is very hot, and since division is expensive, we
 * optimize it by observing that w(x) ∊ { 1, 2 } for all nodes x. Thus we can
 * replace it by a cheaper sequence of operations that produce the same output
 * for those inputs.
 */

uint32_t edge_weight_helper(uint8_t u_width, uint8_t v_width) {
  return ((v_width - 1) >> (u_width - 1)) + 1;
}

} // namespace impl

using namespace impl;

uint32_t Graph::edge_weight(const Node& u_node, const Node& v_node) const {
  // We do selection of symregs requiring < 16 bits separately from those
  // without this constraint, since the selection of the latter will never
  // induce a spill. This essentially partitions the graph into two subgraphs.
  // We still need interference edges between nodes in different partitions,
  // but we don't want a node in one partition affecting the selection order of
  // nodes in the other.  As such, nodes in separate partitions don't affect
  // each others' weights.
  auto same_partition = (u_node.max_vreg() < max_unsigned_value(16)) ==
                        (v_node.max_vreg() < max_unsigned_value(16));
  return same_partition ? edge_weight_helper(u_node.width(), v_node.width())
                        : 0;
}

void Graph::add_edge(reg_t u, reg_t v, bool can_coalesce) {
  if (u == v) {
    return;
  }
  if (!is_adjacent(u, v)) {
    auto& u_node = m_nodes.at(u);
    auto& v_node = m_nodes.at(v);
    u_node.m_adjacent.push_back(v);
    v_node.m_adjacent.push_back(u);
    u_node.m_weight += edge_weight(u_node, v_node);
    v_node.m_weight += edge_weight(v_node, u_node);
  }
  // If we have one instruction that creates a coalesceable edge between two
  // nodes s0 and s1, and another that creates a non-coalesceable edge, those
  // edges combined must be non-coalesceable. For example, if we have
  //
  //   move-wide s0, s1 # s0 and s1 may be coalesceable
  //   long-to-double s0, s1 # s0 and s1 definitely not coalesceable
  //
  // then the final state of the edge between s0 and s1 must be
  // non-coalesceable.
  m_adj_matrix[build_edge(u, v)] =
      m_adj_matrix[build_edge(u, v)] || !can_coalesce;
}

uint32_t Node::colorable_limit() const {
  return div_ceil(max_vreg() + 1, 2 * width() - 1);
}

bool Node::definitely_colorable() const { return weight() < colorable_limit(); }

const Node& Graph::get_node(reg_t v) const { return m_nodes.at(v); }

void Graph::combine(reg_t u, reg_t v) {
  auto& u_node = m_nodes.at(u);
  auto& v_node = m_nodes.at(v);
  for (auto t : v_node.adjacent()) {
    auto& t_node = m_nodes.at(t);
    if (!t_node.is_active()) {
      continue;
    }
    t_node.m_weight -= edge_weight(t_node, v_node);
  }
  u_node.m_max_vreg = std::min(u_node.m_max_vreg, v_node.m_max_vreg);
  u_node.m_type_domain.meet_with(v_node.m_type_domain);
  u_node.m_props |= v_node.m_props;
  u_node.m_spill_cost += v_node.m_spill_cost;
  v_node.m_props.reset(Node::ACTIVE);
  for (auto t : v_node.adjacent()) {
    auto& t_node = m_nodes.at(t);
    if (!t_node.is_active()) {
      continue;
    }
    add_edge(u, t, is_coalesceable(v, t));
    if (has_containment_edge(v, t)) {
      add_containment_edge(u, t);
    }
    if (has_containment_edge(t, v)) {
      add_containment_edge(t, u);
    }
  }
}

void Graph::remove_node(reg_t u) {
  auto& u_node = m_nodes.at(u);
  for (auto v : u_node.adjacent()) {
    auto& v_node = m_nodes.at(v);
    if (!v_node.is_active()) {
      continue;
    }
    v_node.m_weight -= edge_weight(v_node, u_node);
  }
  u_node.m_props.reset(Node::ACTIVE);
}

size_t dest_bit_width(const cfg::InstructionIterator& it) {
  auto* insn = it->insn;
  auto op = insn->opcode();
  if (opcode::is_a_move_result_pseudo(op)) {
    auto primary_op =
        it.cfg().primary_instruction_of_move_result(it)->insn->opcode();
    if (primary_op == OPCODE_CHECK_CAST) {
      // check-cast is Dex format 21c: one 8-bit register field acting as both
      // src and dest, so the value can live anywhere in v0-v255. When the IR
      // dest differs from the src, lowering prepends a move-object;
      // select_move_opcode picks move-object/from16, whose dest field is also
      // 8 bits, so the move imposes no tighter bound.
      return 8;
    } else {
      return dex_opcode::dest_bit_width(opcode::to_dex_opcode(primary_op));
    }
  } else if (opcode::is_an_internal(op) || opcode::is_a_move(op)) {
    // move-* opcodes can always be encoded as move-*/16
    return 16;
  } else if (opcode::is_a_literal_const(op)) {
    // const opcodes can always be encoded in a form that addresses 8-bit regs
    return 8;
  } else if (opcode::is_an_int_lit(op)) {
    return (int8_t)insn->get_literal() == insn->get_literal() ? 8 : 4;
  } else {
    return dex_opcode::dest_bit_width(opcode::to_dex_opcode(op));
  }
}

bit_width_t src_bit_width(const IRInstruction* insn, int src_i) {
  auto op = insn->opcode();
  // move-* opcodes can always be encoded as move-*/16
  if (opcode::is_a_move(op)) {
    return 16;
  }
  if (opcode::is_an_int_lit(op)) {
    return (int8_t)insn->get_literal() == insn->get_literal() ? 8 : 4;
  }
  return dex_opcode::src_bit_width(opcode::to_dex_opcode(op), src_i);
}

vreg_t max_value_for_src(const IRInstruction* insn,
                         size_t src_index,
                         bool src_is_wide) {
  auto max_value =
      max_unsigned_value(src_bit_width(insn, static_cast<int>(src_index)));
  auto op = insn->opcode();
  if (opcode::has_range_form(op) && insn->srcs_size() == 1) {
    // An `invoke {v0}` opcode can always be rewritten as `invoke/range {v0}`
    return max_unsigned_value(16);
  } else if (opcode::is_an_invoke(op) && src_is_wide) {
    // invoke instructions need to address both pairs of a wide register in
    // their denormalized form. We are dealing with the normalized form
    // here, so we need to reserve one register for denormalization. I.e.
    // `invoke-static {v14} LFoo.a(J)` will expand into
    // `invoke-static {v14, v15} LFoo.a(J)` after denormalization.
    --max_value;
  }
  return max_value;
}

void GraphBuilder::update_node_constraints(const cfg::InstructionIterator& it,
                                           const RangeSet& range_set,
                                           Graph* graph) {
  auto* insn = it->insn;
  auto op = insn->opcode();
  if (insn->has_dest()) {
    auto dest = insn->dest();
    auto& node = graph->m_nodes[dest];
    if (opcode::is_a_load_param(op)) {
      node.m_props.set(Node::PARAM);
    }
    node.m_type_domain.meet_with(RegisterTypeDomain(dest_reg_type(insn)));
    auto max_vreg = max_unsigned_value(dest_bit_width(it));
    node.m_max_vreg = std::min(node.m_max_vreg, max_vreg);
    node.m_width = insn->dest_is_wide() ? 2 : 1;
    if (max_vreg < max_unsigned_value(16)) {
      ++node.m_spill_cost;
    }
  }

  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    auto src = insn->src(i);
    auto& node = graph->m_nodes[src];
    auto type = src_reg_type(insn, i);
    node.m_type_domain.meet_with(RegisterTypeDomain(type));
    vreg_t max_vreg;
    if (range_set.contains(insn)) {
      max_vreg = max_unsigned_value(16);
      node.m_props.set(Node::RANGE);
    } else {
      max_vreg = max_value_for_src(insn, i, type == RegisterType::WIDE);
    }
    node.m_max_vreg = std::min(node.m_max_vreg, max_vreg);
    if (max_vreg < max_unsigned_value(16)) {
      ++node.m_spill_cost;
    }
  }
}

/*
 * Build the interference graph by adding edges between nodes that are
 * simultaneously live.
 *
 * check-cast instructions have to be handled specially. They are represented
 * with both a dest (via a move-result-pseudo) and a src in our IR. However, in
 * actual Dex bytecode, it only takes a single operand which acts as both src
 * and dest. So when converting IR to Dex bytecode, we need to insert a move
 * instruction if the src and dest operands differ. We must insert the move
 * before, not after, the check-cast. Suppose we did not:
 *
 *        IR                  |           Dex
 *   sget-object v0 LFoo;     |  sget-object v0 LFoo;
 *   check-cast v0 LBar;      |  check-cast v0 LBar;
 *   move-result-pseudo v1    |  move-object v1 v0
 *   invoke-static v0 LFoo.a; |  invoke-static v0 LFoo.a; // v0 is of type Bar!
 *
 * However, inserting before the check-cast is tricky to get right. If the
 * check-cast is in a try region, we must be careful to not clobber other
 * live registers. For example, if we had some IRCode like
 *
 *   B0:
 *     load-param v1 Ljava/lang/Object;
 *     TRY_START
 *     const v0 123
 *     check-cast v1 LFoo;
 *   B1:
 *     move-result-pseudo v0
 *     return v0
 *     TRY_END
 *   B2:
 *     CATCH
 *     // handle failure of check-cast
 *     // Note that v0 has the value of 123 here because the check-cast failed
 *     add-int v0, v0, v0
 *
 * Inserting the move before the check-cast would cause v0 to have an object
 * (instead of integer) type inside the exception handler.
 *
 * The solution is to have the interference graph make check-cast's dest
 * register interfere with the live registers in both B0 and B1, so that when
 * the move gets inserted, it does not clobber any live registers.
 */
Graph GraphBuilder::build(const LivenessFixpointIterator& fixpoint_iter,
                          cfg::ControlFlowGraph& cfg,
                          reg_t initial_regs,
                          const RangeSet& range_set,
                          bool containment_edges) {
  Graph graph;
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    GraphBuilder::update_node_constraints(it, range_set, &graph);
  }

  for (cfg::Block* block : cfg.blocks()) {
    LivenessDomain live_out = fixpoint_iter.get_live_out_vars_at(block);
    for (auto& mie : InstructionIterable(block).reversed()) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (insn->has_dest()) {
        for (auto reg : live_out.elements()) {
          if (opcode::is_a_move(op) && reg == insn->src(0)) {
            continue;
          }
          graph.add_edge(insn->dest(), reg);
        }
        // We add interference edges between the dest and wide src operands of
        // an instruction even if the srcs are not live-out. This avoids
        // allocations like `xor-long v1, v0, v9`, where v1 and v0 overlap --
        // even though this is not a verification error, we have observed bugs
        // in the ART interpreter when handling these sorts of instructions.
        // However, we still want to be able to coalesce these symregs if they
        // don't actually interfere based on liveness information, so that we
        // can remove move-wide opcodes and/or use /2addr encodings.  As such,
        // we insert a specially marked edge that coalescing ignores but
        // coloring respects.
        for (size_t i = 0; i < insn->srcs_size(); ++i) {
          if (insn->src_is_wide(i)) {
            graph.add_coalesceable_edge(insn->dest(), insn->src(i));
          }
        }
      }
      if (op == OPCODE_CHECK_CAST) {
        auto move_result =
            cfg.move_result_of(block->to_cfg_instruction_iterator(mie));
        always_assert(!move_result.is_end());
        IRInstruction* move_result_pseudo = move_result->insn;
        for (auto reg : live_out.elements()) {
          graph.add_edge(move_result_pseudo->dest(), reg);
        }
      }
      // adding containment edge between liverange defined in insn and elements
      // in live-out set of insn
      if (containment_edges && insn->has_dest()) {
        for (auto reg : live_out.elements()) {
          graph.add_containment_edge(insn->dest(), reg);
        }
      }
      fixpoint_iter.analyze_instruction(mie.insn, &live_out);
      // adding containment edge between liverange used in insn and elements
      // in live-in set of insn
      if (containment_edges) {
        for (size_t i = 0; i < insn->srcs_size(); ++i) {
          for (auto reg : live_out.elements()) {
            graph.add_containment_edge(insn->src(i), reg);
          }
        }
      }
    }
  }
  for (auto& pair : UnorderedIterable(graph.nodes())) {
    auto reg = pair.first;
    auto& node = pair.second;
    if (reg >= initial_regs) {
      node.m_props.set(Node::SPILL);
    }
    assert_log(!node.m_type_domain.is_bottom(),
               "Type violation of v%u in code:\n%s\n",
               reg,
               SHOW(cfg));
  }
  return graph;
}

std::ostream& Graph::write_dot_format(std::ostream& o) const {
  o << "graph {\n";
  for (const auto& pair : UnorderedIterable(nodes())) {
    auto reg = pair.first;
    const auto& node = pair.second;
    o << reg << "[label=\"" << reg << " (" << node.weight() << ")\"]" << "\n";
    for (auto adj : node.adjacent()) {
      if (pair.first < adj) {
        o << reg << " -- " << adj << "\n";
      }
    }
  }
  o << "}\n";

  o << "containment graph {\n";
  for (const auto& pair : UnorderedIterable(m_containment_graph)) {
    reg_t reg1 = static_cast<reg_t>((pair & 0xFFFFFFFF00000000) >> 32);
    reg_t reg2 = static_cast<reg_t>(pair & 0x00000000FFFFFFFF);
    o << reg1 << " -- " << reg2 << "\n";
  }
  o << "}\n";
  return o;
}

void GraphBuilder::make_node(Graph* graph,
                             reg_t r,
                             RegisterType type,
                             vreg_t max_vreg) {
  always_assert(graph->m_nodes.find(r) == graph->m_nodes.end());
  graph->m_nodes[r].m_type_domain.meet_with(RegisterTypeDomain(type));
  graph->m_nodes[r].m_width = type == RegisterType::WIDE ? 2 : 1;
  graph->m_nodes[r].m_max_vreg = max_vreg;
}

void GraphBuilder::add_edge(Graph* graph, reg_t u, reg_t v) {
  // Add a non-move(normal) edge.
  graph->add_edge(u, v, false);
}

} // namespace interference

} // namespace regalloc
