/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstring>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <iostream>
#include <memory>
#include <sstream>

#include <sparta/HashedSetAbstractDomain.h>
#include <sparta/MonotonicFixpointIterator.h>

#include "ControlFlow.h"
#include "DexPosition.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "RedexTest.h"
#include "Show.h"

using namespace sparta;

/*
 * The abstract domain for liveness is just the powerset domain of registers,
 * which we represent here as strings for simplicity.
 */
using LivenessDomain = HashedSetAbstractDomain<std::string>;

using namespace std::placeholders;

class IRFixpointIterator final
    : public MonotonicFixpointIterator<
          BackwardsFixpointIterationAdaptor<cfg::GraphInterface>,
          LivenessDomain> {
 public:
  // In the IR a CFG node is a basic block, i.e., a Block structure. A node id
  // is simply a pointer to a Block.
  using NodeId = cfg::Block*;

  explicit IRFixpointIterator(const cfg::ControlFlowGraph& cfg)
      : MonotonicFixpointIterator(cfg, cfg.num_blocks()), m_cfg(cfg) {}

  void analyze_node(const NodeId& block,
                    LivenessDomain* current_state) const override {
    // Since liveness is a backward analysis, we analyze each instruction inside
    // a block in the reverse order of execution.
    for (auto& mie : InstructionIterable(block).reversed()) {
      analyze_instruction(mie.insn, current_state);
    }
  }

  LivenessDomain analyze_edge(
      const EdgeId&,
      const LivenessDomain& exit_state_at_source) const override {
    // Edges have no semantic transformers attached.
    return exit_state_at_source;
  }

  void analyze_instruction(const IRInstruction* insn,
                           LivenessDomain* current_state) const {
    // This is the standard semantic definition of liveness.
    if (insn->has_dest()) {
      // The destination register of an instruction is dead.
      current_state->remove(get_register(insn->dest()));
    }
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      // The source registers of an instruction are live.
      current_state->add(get_register(insn->src(i)));
    }
  }

  LivenessDomain get_live_in_vars_at(const NodeId& block) const {
    // Since we performed a backward analysis by reversing the control-flow
    // graph, the set of live variables upon entering a block is given by
    // the exit state at that block.
    return get_exit_state_at(block);
  }

  LivenessDomain get_live_out_vars_at(const NodeId& block) const {
    // Similarly, the set of live variables upon exiting a block is given by
    // the entry state at that block.
    return get_entry_state_at(block);
  }

 private:
  std::string get_register(size_t i) const {
    std::ostringstream ss;
    ss << "v" << i;
    return ss.str();
  }

  const cfg::ControlFlowGraph& m_cfg;
};

class MonotonicFixpointTest : public RedexIntegrationTest {};

TEST_F(MonotonicFixpointTest, livenessAnalysis) {
  std::cout << "Loaded classes: " << classes->size() << "\n";

  for (const auto& cls : *classes) {
    if (std::strcmp(cls->get_name()->c_str(),
                    "Lcom/facebook/redextest/MonotonicFixpoint;") == 0) {
      for (const auto& method : cls->get_vmethods()) {
        if (std::strcmp(method->get_name()->c_str(), "function_1") == 0) {
          auto* code = method->get_code();
          code->build_cfg();
          cfg::ControlFlowGraph& cfg = code->cfg();
          cfg.calculate_exit_block();
          std::cout << "CFG of function_1:" << "\n" << SHOW(cfg) << "\n";
          ASSERT_EQ(cfg.exit_block()->id(), 2);
          IRFixpointIterator fixpoint_iterator(cfg);
          fixpoint_iterator.run(LivenessDomain());

          for (cfg::Block* block : cfg.blocks()) {
            LivenessDomain live_in =
                fixpoint_iterator.get_live_in_vars_at(block);
            LivenessDomain live_out =
                fixpoint_iterator.get_live_out_vars_at(block);
            // Checking the live in/out variables at block boundaries.
            switch (block->id()) {
            case 0: {
              EXPECT_EQ(0, live_in.size());
              EXPECT_THAT(live_out.elements(),
                          ::testing::UnorderedElementsAre("v0", "v2"));
              break;
            }
            case 1: {
              EXPECT_THAT(live_in.elements(),
                          ::testing::UnorderedElementsAre("v0", "v2"));
              EXPECT_THAT(live_out.elements(),
                          ::testing::UnorderedElementsAre("v0", "v2"));
              break;
            }
            case 2: {
              EXPECT_THAT(live_in.elements(), ::testing::ElementsAre("v2"));
              EXPECT_EQ(0, live_out.size());
              break;
            }
            default: {
              FAIL() << "Unexpected block";
            }
            }

            // Checking the live in/out variables at position instructions.
            for (auto it = block->rbegin(); it != block->rend(); ++it) {
              if (it->type == MFLOW_OPCODE) {
                // We replay the analysis of a block backwards starting from the
                // exit state (the set of live-out variables).
                fixpoint_iterator.analyze_instruction(it->insn, &live_out);
              }
              if (it->type == MFLOW_POSITION) {
                switch (it->pos->line) {
                case 46: {
                  EXPECT_THAT(live_out.elements(),
                              ::testing::UnorderedElementsAre("v0", "v2"));
                  break;
                }
                case 47:
                case 48: {
                  EXPECT_THAT(live_out.elements(),
                              ::testing::UnorderedElementsAre("v1", "v2"));
                  break;
                }
                case 49: {
                  EXPECT_THAT(live_out.elements(),
                              ::testing::UnorderedElementsAre("v0", "v2"));
                  break;
                }
                }
              }
            }
          }
        }
      }
    }
  }
}
