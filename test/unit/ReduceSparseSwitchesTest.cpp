/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <bit>
#include <gtest/gtest.h>
#include <optional>
#include <set>

#include "Show.h"

#include "ClassReorderingPass.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DeterministicContainers.h"
#include "RClass.h"
#include "RedexTest.h"
#include "ReduceSparseSwitchesPass.h"
#include "RegAlloc.h"
#include "SourceBlocks.h"
#include "SourceBlocksViolations.h"
#include "TypeUtil.h"

struct ReduceSparseSwitchesTest : public RedexTest {};

namespace {

int32_t evaluate_switch(cfg::ControlFlowGraph& cfg,
                        const std::vector<int32_t>& inputs,
                        std::vector<cfg::Block*>* visited = nullptr) {
  std::vector<int32_t> regs(cfg.get_registers_size());
  size_t param = 0;
  std::optional<int32_t> call_result;
  auto* block = cfg.entry_block();
  for (size_t steps = 0; steps < 100; ++steps) {
    if (visited != nullptr) {
      visited->push_back(block);
    }
    auto* next = block->goes_to();
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      const auto op = insn->opcode();
      if (op == IOPCODE_LOAD_PARAM) {
        always_assert(param < inputs.size());
        regs[insn->dest()] = inputs[param++];
      } else if (op == OPCODE_INVOKE_STATIC &&
                 insn->get_method()->get_name()->str() == "nextTag") {
        always_assert(param < inputs.size());
        call_result = inputs[param++];
      } else if (op == OPCODE_MOVE_RESULT) {
        always_assert(call_result);
        regs[insn->dest()] = *call_result;
        call_result.reset();
      } else if (op == OPCODE_CONST) {
        regs[insn->dest()] = static_cast<int32_t>(insn->get_literal());
      } else if (op == OPCODE_MOVE) {
        regs[insn->dest()] = regs[insn->src(0)];
      } else if (op == OPCODE_ADD_INT_LIT) {
        regs[insn->dest()] =
            std::bit_cast<int32_t>(static_cast<uint32_t>(regs[insn->src(0)]) +
                                   static_cast<uint32_t>(insn->get_literal()));
      } else if (op == OPCODE_ADD_INT) {
        regs[insn->dest()] =
            std::bit_cast<int32_t>(static_cast<uint32_t>(regs[insn->src(0)]) +
                                   static_cast<uint32_t>(regs[insn->src(1)]));
      } else if (op == OPCODE_SWITCH) {
        for (auto* edge : block->succs()) {
          if (edge->case_key() && *edge->case_key() == regs[insn->src(0)]) {
            next = edge->target();
          }
        }
      } else if (op == OPCODE_IF_LT || op == OPCODE_IF_GT ||
                 op == OPCODE_IF_NE) {
        const auto a = regs[insn->src(0)];
        const auto b = regs[insn->src(1)];
        const bool branch = op == OPCODE_IF_LT   ? a < b
                            : op == OPCODE_IF_GT ? a > b
                                                 : a != b;
        if (branch) {
          next = cfg.get_succ_edge_of_type(block, cfg::EDGE_BRANCH)->target();
        }
      } else if (op == OPCODE_RETURN) {
        return regs[insn->src(0)];
      } else {
        ADD_FAILURE() << "Unexpected opcode in switch fixture";
        return 0;
      }
    }
    if (next == nullptr) {
      ADD_FAILURE() << "Switch fixture did not return";
      return 0;
    }
    block = next;
  }
  ADD_FAILURE() << "Switch fixture looped";
  return 0;
}

int32_t evaluate_switch(cfg::ControlFlowGraph& cfg, int32_t input) {
  return evaluate_switch(cfg, std::vector<int32_t>{input});
}

DexMethod* make_arithmetic_switch(int32_t first,
                                  int32_t delta,
                                  bool aliases_selector,
                                  bool returns,
                                  const std::string& name,
                                  int32_t case_count = 4) {
  std::ostringstream out;
  const auto dest = aliases_selector ? 0 : 1;
  out << "(method (public static) \"LArithmetic;." << name
      << ":(I)I\" ((load-param v0)(switch v0 (";
  for (int32_t i = 0; i < case_count; ++i) {
    out << ":C" << i << ' ';
  }
  out << "))(const v1 -123)(return v1)";
  for (int64_t i = 0; i < case_count; ++i) {
    const auto key = static_cast<int32_t>(static_cast<int64_t>(first) + i);
    const auto value = std::bit_cast<int32_t>(static_cast<uint32_t>(key) +
                                              static_cast<uint32_t>(delta));
    out << "(:C" << i << ' ' << key << ")(const v" << dest << ' ' << value
        << ')';
    out << (returns ? "(return v" + std::to_string(dest) + ")" : "(goto :End)");
  }
  if (!returns) {
    out << "(:End)(return v" << dest << ')';
  }
  out << "))";
  return assembler::method_from_string(out.str());
}

auto run_arithmetic_switch_pass(DexMethod* method, bool enabled) {
  ClassCreator creator(method->get_class());
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC);
  creator.add_method(method);
  DexStoresVector stores;
  stores.emplace_back("classes");
  stores.back().add_classes({creator.create()});
  Json::Value json(Json::objectValue);
  auto& pass_config = json["ReduceSparseSwitchesPass"];
  pass_config["arithmetic_switches"] = enabled;
  // Keep the residual switch visible so this isolates splitting/folding.
  pass_config["expand_remaining"] = false;
  ConfigFiles config(json);
  config.parse_global_config();
  ReduceSparseSwitchesPass pass;
  ClassReorderingPass reorder;
  PassManager manager({&pass, &reorder}, config);
  manager.run_passes(stores, config);
  auto metrics = manager.get_pass_info().at(0).metrics;
  method->get_code()->build_cfg();
  return metrics;
}

} // namespace

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_requires_explicit_enablement) {
  auto* method = make_arithmetic_switch(0, 10, false, true, "configuration");
  ClassCreator creator(method->get_class());
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC);
  creator.add_method(method);
  DexStoresVector stores;
  stores.emplace_back("classes");
  stores.back().add_classes({creator.create()});
  // Linearize once, so that `original` shows the layout that the round trip
  // through the pass manager reproduces.
  method->get_code()->build_cfg();
  method->get_code()->clear_cfg();
  method->get_code()->build_cfg();
  const auto original = show(method->get_code()->cfg());

  for (auto enabled : {std::optional<bool>{}, std::optional<bool>{false},
                       std::optional<bool>{true}}) {
    SCOPED_TRACE(enabled ? (*enabled ? "true" : "false") : "omitted");
    Json::Value json(Json::objectValue);
    auto& pass_config = json["ReduceSparseSwitchesPass"];
    pass_config["expand_remaining"] = false;
    if (enabled) {
      pass_config["arithmetic_switches"] = *enabled;
    }
    ConfigFiles config(json);
    config.parse_global_config();
    ReduceSparseSwitchesPass pass;
    ClassReorderingPass reorder;
    PassManager manager({&pass, &reorder}, config);
    manager.run_passes(stores, config);

    const bool folded = enabled.value_or(false);
    const auto& info = manager.get_pass_info().at(0);
    ASSERT_EQ(&pass, info.pass);
    EXPECT_EQ(folded ? 1 : 0,
              info.metrics.at("num_arithmetic_transformations"));
    EXPECT_EQ(folded ? 4 : 0, info.metrics.at("num_arithmetic_switch_cases"));
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    size_t switches = 0;
    for (auto& mie : cfg::InstructionIterable(cfg)) {
      if (mie.insn->opcode() == OPCODE_SWITCH) {
        ++switches;
      }
    }
    EXPECT_EQ(folded ? 0 : 1, switches);
    if (!folded) {
      EXPECT_EQ(original, show(cfg));
    }
    for (int32_t input : {-1, 0, 1, 2, 3, 4}) {
      EXPECT_EQ(input >= 0 && input <= 3 ? input + 10 : -123,
                evaluate_switch(cfg, input));
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_folds_regions_exposed_by_splitting) {
  size_t index = 0;
  for (bool returns : {false, true}) {
    for (bool profiled : {false, true}) {
      for (bool enabled : {false, true}) {
        SCOPED_TRACE(returns ? "return cases" : "joined cases");
        SCOPED_TRACE(profiled ? "profiled" : "unprofiled");
        SCOPED_TRACE(enabled ? "arithmetic enabled" : "arithmetic disabled");
        const auto name =
            "LPlacement" + std::to_string(index++) + ";.test:(I)I";
        std::ostringstream out;
        out << "(method (public static) \"" << name << "\" ((load-param v0)";
        auto source_block = [&](size_t id, size_t count) {
          if (profiled) {
            out << "(.src_block \"" << name << "\" " << id << " (" << count
                << ".0 1.0))";
          }
        };
        source_block(0, 17);
        out << "(switch v0 (";
        for (int32_t key = 0; key < 10; ++key) {
          out << ":C" << key << ' ';
        }
        out << ":Other))";
        source_block(1, 5);
        out << "(const v1 -123)(return v1)";
        for (int32_t key = 0; key < 10; ++key) {
          out << "(:C" << key << ' ' << key << ')';
          source_block(static_cast<size_t>(key) + 2, 1);
          out << "(const v1 " << key + 10 << ')'
              << (returns ? "(return v1)" : "(goto :End)");
        }
        out << "(:Other 100)";
        source_block(12, 2);
        out << "(add-int/lit v1 v0 233)"
            << (returns ? "(return v1)" : "(goto :End)");
        if (!returns) {
          out << "(:End)(return v1)";
        }
        out << "))";
        auto* method = assembler::method_from_string(out.str());
        method->get_code()->build_cfg();
        std::vector<int32_t> inputs{
            std::numeric_limits<int32_t>::min(), -1, 10, 99, 100, 101,
            std::numeric_limits<int32_t>::max()};
        for (int32_t key = 0; key < 10; ++key) {
          inputs.push_back(key);
        }
        std::vector<int32_t> expected;
        expected.reserve(inputs.size());
        for (auto input : inputs) {
          expected.push_back(evaluate_switch(method->get_code()->cfg(), input));
        }
        const auto metrics = run_arithmetic_switch_pass(method, enabled);
        EXPECT_EQ(1, metrics.at("num_splitting_transformations"));
        EXPECT_EQ(enabled ? 1 : 0,
                  metrics.at("num_arithmetic_transformations"));
        EXPECT_EQ(enabled ? 10 : 0, metrics.at("num_arithmetic_switch_cases"));
        auto& cfg = method->get_code()->cfg();
        size_t switches = 0;
        for (auto& mie : cfg::InstructionIterable(cfg)) {
          if (mie.insn->opcode() == OPCODE_SWITCH) {
            ++switches;
          }
        }
        EXPECT_EQ(enabled ? 1 : 2, switches);
        for (size_t i = 0; i < inputs.size(); ++i) {
          EXPECT_EQ(expected[i], evaluate_switch(cfg, inputs[i]));
        }
        EXPECT_EQ(15, evaluate_switch(cfg, 5));
        EXPECT_EQ(333, evaluate_switch(cfg, 100));
        EXPECT_EQ(-123, evaluate_switch(cfg, 99));
        if (profiled) {
          UnorderedMap<cfg::Block*, size_t> visits;
          auto record = [&](int32_t input) {
            std::vector<cfg::Block*> trace;
            evaluate_switch(cfg, {input}, &trace);
            for (auto* block : trace) {
              ++visits[block];
            }
          };
          for (int32_t key = 0; key < 10; ++key) {
            record(key);
          }
          for (int32_t input :
               {-1, 10, 99, 101, std::numeric_limits<int32_t>::max(), 100,
                100}) {
            record(input);
          }
          size_t values = 0;
          size_t remainders = 0;
          size_t unknown = 0;
          for (auto* block : cfg.blocks()) {
            auto* sb = source_blocks::get_first_source_block(block);
            if (sb == nullptr || sb->id != SourceBlock::kSyntheticId) {
              continue;
            }
            const auto last = block->get_last_insn();
            const bool remaining_switch =
                last != block->end() && last->insn->opcode() == OPCODE_SWITCH;
            sb->foreach_val([&](const auto& value) {
              if (!value) {
                ++unknown;
                return;
              }
              if (visits.count(block) == 0) {
                ADD_FAILURE() << "Profiled block was not visited by the trace";
                return;
              }
              EXPECT_FLOAT_EQ(static_cast<float>(visits.at(block)), value->val);
              if (remaining_switch) {
                EXPECT_FLOAT_EQ(7.0, value->val);
                EXPECT_FLOAT_EQ(1.0, value->appear100);
                ++remainders;
              } else {
                EXPECT_FLOAT_EQ(10.0, value->val);
                EXPECT_FLOAT_EQ(1.0, value->appear100);
                ++values;
              }
            });
          }
          EXPECT_EQ(enabled ? 1 : 0, values);
          EXPECT_EQ(1, remainders);
          EXPECT_EQ(enabled ? 1 : 0, unknown);
        }
      }
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_rejects_split_regions_with_shared_targets) {
  std::ostringstream out;
  out << "(method (public static) \"LPlacementShared;.test:(I)I\""
      << " ((load-param v0)(switch v0 (";
  for (int32_t key = 0; key < 10; ++key) {
    out << ":C" << key << ' ';
  }
  out << ":Other))(const v1 -123)(return v1)";
  for (int32_t key = 0; key < 10; ++key) {
    out << "(:C" << key << ' ' << key << ')';
    if (key == 3) {
      out << "(:Other 100)";
    }
    out << "(const v1 " << key + 10 << ")(return v1)";
  }
  out << "))";
  auto* method = assembler::method_from_string(out.str());
  const auto metrics = run_arithmetic_switch_pass(method, true);
  EXPECT_EQ(1, metrics.at("num_splitting_transformations"));
  EXPECT_EQ(0, metrics.at("num_arithmetic_transformations"));
  auto& cfg = method->get_code()->cfg();
  for (int32_t key = 0; key < 10; ++key) {
    EXPECT_EQ(key + 10, evaluate_switch(cfg, key));
  }
  EXPECT_EQ(13, evaluate_switch(cfg, 100));
  EXPECT_EQ(-123, evaluate_switch(cfg, 99));
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_folds_multiple_split_regions) {
  const std::string name = "LPlacementSegments;.test:(I)I";
  std::ostringstream out;
  out << "(method (public static) \"" << name << "\" ((load-param v0)"
      << "(.src_block \"" << name << "\" 0 (25.0 1.0))(switch v0 (";
  for (int32_t i = 0; i < 20; ++i) {
    out << ":C" << i << ' ';
  }
  out << "))(.src_block \"" << name
      << "\" 1 (5.0 1.0))(const v1 -123)(return v1)";
  for (int32_t group = 0; group < 2; ++group) {
    for (int32_t i = 0; i < 10; ++i) {
      const auto index = group * 10 + i;
      out << "(:C" << index << ' ' << group * 1000 + i << ')'
          << "(.src_block \"" << name << "\" " << index + 2
          << " (1.0 1.0))(const v1 " << i + 10 << ")(return v1)";
    }
  }
  out << "))";
  auto* method = assembler::method_from_string(out.str());
  const auto metrics = run_arithmetic_switch_pass(method, true);
  EXPECT_EQ(1, metrics.at("num_splitting_transformations"));
  EXPECT_EQ(2, metrics.at("num_arithmetic_transformations"));
  EXPECT_EQ(20, metrics.at("num_arithmetic_switch_cases"));
  auto& cfg = method->get_code()->cfg();
  size_t switches = 0;
  for (auto& mie : cfg::InstructionIterable(cfg)) {
    if (mie.insn->opcode() == OPCODE_SWITCH) {
      ++switches;
    }
  }
  EXPECT_EQ(0, switches);
  for (int32_t i = 0; i < 10; ++i) {
    EXPECT_EQ(i + 10, evaluate_switch(cfg, i));
    EXPECT_EQ(i + 10, evaluate_switch(cfg, i + 1000));
  }
  for (int32_t input : {std::numeric_limits<int32_t>::min(), -1, 10, 999, 1010,
                        std::numeric_limits<int32_t>::max()}) {
    EXPECT_EQ(-123, evaluate_switch(cfg, input));
  }
  size_t values = 0;
  size_t remainder_guards = 0;
  size_t unknown = 0;
  for (auto* block : cfg.blocks()) {
    auto* sb = source_blocks::get_first_source_block(block);
    if (sb == nullptr || sb->id != SourceBlock::kSyntheticId) {
      continue;
    }
    sb->foreach_val([&](const auto& value) {
      if (!value) {
        ++unknown;
      } else if (value->val == 15.0) {
        EXPECT_FLOAT_EQ(1.0, value->appear100);
        ++remainder_guards;
      } else {
        EXPECT_FLOAT_EQ(10.0, value->val);
        EXPECT_FLOAT_EQ(1.0, value->appear100);
        ++values;
      }
    });
  }
  EXPECT_EQ(2, values);
  EXPECT_EQ(1, remainder_guards);
  EXPECT_EQ(2, unknown);
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_folds_small_switches) {
  size_t index = 0;
  for (int32_t cases : {1, 2, 3}) {
    for (int32_t first : {0, -2, std::numeric_limits<int32_t>::min()}) {
      for (int32_t delta : {10, 100000}) {
        for (bool aliases : {false, true}) {
          for (bool returns : {false, true}) {
            auto* method = make_arithmetic_switch(
                first, delta, aliases, returns,
                "small" + std::to_string(index++), cases);
            method->get_code()->build_cfg();
            auto& cfg = method->get_code()->cfg();
            std::vector<int32_t> inputs{std::numeric_limits<int32_t>::min(),
                                        std::numeric_limits<int32_t>::max()};
            for (int64_t i = -1; i <= cases; ++i) {
              const auto input = static_cast<int64_t>(first) + i;
              if (input >= std::numeric_limits<int32_t>::min() &&
                  input <= std::numeric_limits<int32_t>::max()) {
                inputs.push_back(static_cast<int32_t>(input));
              }
            }
            std::vector<int32_t> expected;
            expected.reserve(inputs.size());
            for (auto input : inputs) {
              expected.push_back(evaluate_switch(cfg, input));
            }
            const auto stats =
                ReduceSparseSwitchesPass::arithmetic_transformation(cfg,
                                                                    method);
            ASSERT_EQ(1, stats.arithmetic_transformations);
            EXPECT_EQ(cases, stats.arithmetic_switch_cases);
            size_t guards = 0;
            for (auto& mie : cfg::InstructionIterable(cfg)) {
              if (opcode::is_a_conditional_branch(mie.insn->opcode())) {
                ++guards;
              }
            }
            EXPECT_EQ(cases == 1 || first == std::numeric_limits<int32_t>::min()
                          ? 1
                          : 2,
                      guards);
            for (size_t i = 0; i < inputs.size(); ++i) {
              EXPECT_EQ(expected[i], evaluate_switch(cfg, inputs[i]));
            }
          }
        }
      }
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_uses_virtual_register_capacity) {
  DexMethod* allocated = nullptr;
  for (reg_t size : {65535u, 65536u, 70000u}) {
    SCOPED_TRACE(size);
    auto* method = make_arithmetic_switch(0, 10, false, true,
                                          "virtual" + std::to_string(size));
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    cfg.set_registers_size(size);
    const auto stats =
        ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
    ASSERT_EQ(1, stats.arithmetic_transformations);
    EXPECT_EQ(size + 1, cfg.get_registers_size());
    EXPECT_EQ(12, evaluate_switch(cfg, 2));
    EXPECT_EQ(-123, evaluate_switch(cfg, 4));
    allocated = method;
  }
  ClassCreator creator(allocated->get_class());
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC);
  creator.add_method(allocated);
  DexStoresVector stores;
  stores.emplace_back("classes");
  stores.back().add_classes({creator.create()});
  ConfigFiles config{Json::Value{Json::objectValue}};
  config.parse_global_config();
  regalloc::RegAllocPass allocator;
  ClassReorderingPass reorder;
  PassManager manager({&allocator, &reorder}, config);
  manager.run_passes(stores, config);
  allocated->get_code()->build_cfg();
  EXPECT_LT(allocated->get_code()->cfg().get_registers_size(), 65535u);
  EXPECT_EQ(12, evaluate_switch(allocated->get_code()->cfg(), 2));
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_preserves_int_mapping) {
  size_t index = 0;
  for (int32_t first : {0, -10, 1000, std::numeric_limits<int32_t>::min(),
                        std::numeric_limits<int32_t>::max() - 3}) {
    for (int32_t delta :
         {0, -5, 32767, 100000, std::numeric_limits<int32_t>::min()}) {
      for (bool aliases : {false, true}) {
        for (bool returns : {false, true}) {
          auto* method = make_arithmetic_switch(
              first, delta, aliases, returns, "test" + std::to_string(index++));
          method->get_code()->build_cfg();
          auto& cfg = method->get_code()->cfg();
          std::vector<int32_t> inputs{std::numeric_limits<int32_t>::min(),
                                      std::numeric_limits<int32_t>::max(), -1,
                                      0};
          for (int64_t i = -1; i <= 4; ++i) {
            const auto x = static_cast<int64_t>(first) + i;
            if (x >= std::numeric_limits<int32_t>::min() &&
                x <= std::numeric_limits<int32_t>::max()) {
              inputs.push_back(static_cast<int32_t>(x));
            }
          }
          std::vector<int32_t> expected;
          expected.reserve(inputs.size());
          for (auto x : inputs) {
            expected.push_back(evaluate_switch(cfg, x));
          }
          bool resource_values =
              resources::is_potential_resid(first) ||
              resources::is_potential_resid(static_cast<int64_t>(first) + 3) ||
              resources::is_potential_resid(delta);
          for (int64_t i = 0; i < 4; ++i) {
            const auto key =
                static_cast<int32_t>(static_cast<int64_t>(first) + i);
            const auto value = std::bit_cast<int32_t>(
                static_cast<uint32_t>(key) + static_cast<uint32_t>(delta));
            resource_values |= resources::is_potential_resid(value);
          }
          auto stats =
              ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
          ASSERT_EQ(resource_values ? 0 : 1, stats.arithmetic_transformations);
          EXPECT_EQ(resource_values ? 0 : 4, stats.arithmetic_switch_cases);
          for (size_t i = 0; i < inputs.size(); ++i) {
            EXPECT_EQ(expected[i], evaluate_switch(cfg, inputs[i]))
                << "selector=" << inputs[i] << " first=" << first
                << " delta=" << delta << " aliases=" << aliases;
          }
          if (!resource_values) {
            for (auto& mie : cfg::InstructionIterable(cfg)) {
              EXPECT_NE(OPCODE_SWITCH, mie.insn->opcode());
            }
          }
        }
      }
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_preserves_resource_literals) {
  const auto reference_set = [](cfg::ControlFlowGraph& cfg) {
    std::set<int64_t> refs;
    for (auto& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->has_literal() &&
          resources::is_potential_resid(insn->get_literal())) {
        refs.insert(insn->get_literal());
      }
    }
    return refs;
  };
  for (const auto& [first, delta] :
       std::vector<std::pair<int32_t, int32_t>>{{0, 0x7f1f0009},
                                                {0, 0x7efffffd},
                                                {0, 0x7ffffffd},
                                                {0x7f1f0009, -0x7f1f0009},
                                                {-0x7f1f0009, 0x7f1f0009}}) {
    auto* method = make_arithmetic_switch(
        first, delta, false, false,
        "resource" + std::to_string(first) + "_" + std::to_string(delta));
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    const auto before = show(cfg);
    const auto refs = reference_set(cfg);
    const auto registers = cfg.get_registers_size();
    EXPECT_EQ(first == 0, !refs.empty());
    const auto stats =
        ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
    EXPECT_EQ(0, stats.arithmetic_transformations);
    EXPECT_EQ(before, show(cfg));
    EXPECT_EQ(registers, cfg.get_registers_size());
    EXPECT_EQ(refs, reference_set(cfg));
  }
  auto* method = make_arithmetic_switch(-4, 5, false, false, "defaultResource");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  cfg.entry_block()->goes_to()->get_first_insn()->insn->set_literal(0x7f1f0009);
  const auto refs = reference_set(cfg);
  ASSERT_EQ(1, refs.size());
  const auto stats =
      ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  EXPECT_EQ(1, stats.arithmetic_transformations);
  EXPECT_EQ(refs, reference_set(cfg));
  EXPECT_EQ(0x7f1f0009, evaluate_switch(cfg, 0));
  EXPECT_EQ(1, evaluate_switch(cfg, -4));
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_rejects_unsupported_shapes) {
  size_t index = 0;
  for (const auto& body : {
           R"(((load-param v0)(switch v0 (:A :B :C :D))
                (const v1 -1)(return v1)
                (:A 0)(const v1 0)(return v1)
                (:B 1)(const v1 1)(return v1)
                (:C 2)(const v1 3)(return v1)
                (:D 3)(const v1 3)(return v1)))",
           R"(((load-param v0)(switch v0 (:A :B :C :D))
                (const v1 -1)(return v1)
                (:A 0)(const v1 0)(return v1)
                (:B 1)(const v1 1)(return v1)
                (:C 2)(const v1 2)(return v1)
                (:D 4)(const v1 4)(return v1)))",
           R"(((load-param v0)(switch v0 (:A :B :C :D))
                (const v1 -1)(return v1)
                (:A 0)(const v1 0)(return v1)
                (:B 1)(const v2 1)(return v2)
                (:C 2)(const v1 2)(return v1)
                (:D 3)(const v1 3)(return v1)))",
           R"(((load-param v0)(switch v0 (:A :B :C :D))
                (const v1 -1)(return v1)
                (:A 0)(const v1 0)(const v2 42)(return v1)
                (:B 1)(const v1 1)(return v1)
                (:C 2)(const v1 2)(return v1)
                (:D 3)(const v1 3)(return v1)))",
           R"(((load-param v0)(switch v0 (:A :B :C :D))
                (const v1 -1)(goto :External)
                (:A 0)(:External)(const v1 0)(return v1)
                (:B 1)(const v1 1)(return v1)
                (:C 2)(const v1 2)(return v1)
                (:D 3)(const v1 3)(return v1)))"}) {
    auto* method = assembler::method_from_string(
        "(method (public static) \"LArithmetic;.reject" +
        std::to_string(index++) + ":(I)I\" " + body + ")");
    method->get_code()->build_cfg();
    const auto before = show(method->get_code()->cfg());
    const auto regs = method->get_code()->cfg().get_registers_size();
    auto stats = ReduceSparseSwitchesPass::arithmetic_transformation(
        method->get_code()->cfg(), method);
    EXPECT_EQ(0, stats.arithmetic_transformations);
    EXPECT_EQ(regs, method->get_code()->cfg().get_registers_size());
    EXPECT_EQ(before, show(method->get_code()->cfg()));
  }
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_rejects_non_int_returns) {
  for (const std::string rtype : {"F", "Z", "B", "C", "S"}) {
    auto* method = assembler::method_from_string(
        "(method (public static) \"LArithmetic;.return" + rtype + ":(I)" +
        rtype + R"(" ((load-param v0)(switch v0 (:A :B :C :D))
          (const v1 0)(return v1)
          (:A 0)(const v1 0)(return v1)
          (:B 1)(const v1 1)(return v1)
          (:C 2)(const v1 2)(return v1)
          (:D 3)(const v1 3)(return v1))))");
    method->get_code()->build_cfg();
    const auto before = show(method->get_code()->cfg());
    auto stats = ReduceSparseSwitchesPass::arithmetic_transformation(
        method->get_code()->cfg(), method);
    EXPECT_EQ(0, stats.arithmetic_transformations);
    EXPECT_EQ(before, show(method->get_code()->cfg()));
  }
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_keeps_default_registers) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.defaultRegisters:(I)I"
      ((load-param v0)(const v1 99)(switch v0 (:A :B :C :D))
       (return v1)
       (:A -2)(const v1 8)(goto :End)
       (:B -1)(const v1 9)(goto :End)
       (:C 0)(const v1 10)(goto :End)
       (:D 1)(const v1 11)(goto :End)
       (:End)(return v1))))");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  auto stats = ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  ASSERT_EQ(1, stats.arithmetic_transformations);
  EXPECT_EQ(99, evaluate_switch(cfg, -3));
  EXPECT_EQ(99, evaluate_switch(cfg, 2));
  EXPECT_EQ(8, evaluate_switch(cfg, -2));
  EXPECT_EQ(11, evaluate_switch(cfg, 1));
}

TEST_F(ReduceSparseSwitchesTest, arithmetic_switch_conserves_case_counts) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.counts:(I)I"
     ((load-param v0)
      (.src_block "LArithmetic;.counts:(I)I" 0 (100.0 1.0))
      (switch v0 (:A :B :C :D))
      (const v1 -1)(return v1)
      (:A 0)(.src_block "LArithmetic;.counts:(I)I" 1 (2.0 0.2))
      (const v1 0)(return v1)
      (:B 1)(.src_block "LArithmetic;.counts:(I)I" 2 (3.0 0.3))
      (const v1 1)(return v1)
      (:C 2)(.src_block "LArithmetic;.counts:(I)I" 3 (4.0 0.4))
      (const v1 2)(return v1)
      (:D 3)(.src_block "LArithmetic;.counts:(I)I" 4 (5.0 0.5))
      (const v1 3)(return v1))))");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  auto stats = ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  ASSERT_EQ(1, stats.arithmetic_transformations);
  size_t known = 0;
  size_t unknown = 0;
  for (auto* block : cfg.blocks()) {
    auto* sb = source_blocks::get_first_source_block(block);
    if (sb == nullptr || sb->id != SourceBlock::kSyntheticId) {
      continue;
    }
    sb->foreach_val([&](const auto& val) {
      if (val) {
        EXPECT_FLOAT_EQ(14.0, val->val);
        EXPECT_FLOAT_EQ(0.5, val->appear100);
        ++known;
      } else {
        ++unknown;
      }
    });
  }
  EXPECT_EQ(1, known);
  EXPECT_EQ(1, unknown);
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_preserves_implicit_entry_inflow) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.entryInflow:()I"
     ((:E 0)(.src_block "LArithmetic;.entryInflow:()I" 0 (1.0 1.0))
      (const v0 0)(goto :Continue)
      (:Continue)(.src_block "LArithmetic;.entryInflow:()I" 1 (4.0 1.0))
      (add-int/lit v0 v0 1)(switch v0 (:E :A :B :C))
      (.src_block "LArithmetic;.entryInflow:()I" 5 (1.0 1.0))(return v0)
      (:A 1)(.src_block "LArithmetic;.entryInflow:()I" 2 (1.0 1.0))
      (const v0 1)(goto :Continue)
      (:B 2)(.src_block "LArithmetic;.entryInflow:()I" 3 (1.0 1.0))
      (const v0 2)(goto :Continue)
      (:C 3)(.src_block "LArithmetic;.entryInflow:()I" 4 (1.0 1.0))
      (const v0 3)(goto :Continue))))");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  EXPECT_EQ(4, evaluate_switch(cfg, 0));
  const auto stats =
      ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  ASSERT_EQ(1, stats.arithmetic_transformations);
  std::vector<cfg::Block*> visited;
  EXPECT_EQ(4, evaluate_switch(cfg, {0}, &visited));
  size_t value_visits = 0;
  for (auto* block : visited) {
    for (auto& mie : InstructionIterable(block)) {
      if (mie.insn->opcode() == OPCODE_MOVE) {
        ++value_visits;
        auto* sb = source_blocks::get_first_source_block(block);
        ASSERT_NE(nullptr, sb);
        sb->foreach_val([](const auto& value) { EXPECT_FALSE(value); });
      }
    }
  }
  EXPECT_EQ(3, value_visits);
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_preserves_entry_backedge_counts) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.entryBackedge:()I"
     ((:E 0)(.src_block "LArithmetic;.entryBackedge:()I" 0 (2.0 1.0))
      (const v1 10)(goto :Continue)
      (:Continue)(.src_block "LArithmetic;.entryBackedge:()I" 4 (2.0 1.0))
      (invoke-static () "LArithmetic;.nextTag:()I")(move-result v0)
      (switch v0 (:E :A :B :C))
      (.src_block "LArithmetic;.entryBackedge:()I" 5 (1.0 1.0))(return v1)
      (:A 1)(.src_block "LArithmetic;.entryBackedge:()I" 1 (0.0 0.0))
      (const v1 11)(goto :Continue)
      (:B 2)(.src_block "LArithmetic;.entryBackedge:()I" 2 (0.0 0.0))
      (const v1 12)(goto :Continue)
      (:C 3)(.src_block "LArithmetic;.entryBackedge:()I" 3 (0.0 0.0))
      (const v1 13)(goto :Continue))))");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  const std::vector<int32_t> tags{0, 4};
  std::vector<cfg::Block*> visited;
  EXPECT_EQ(10, evaluate_switch(cfg, tags, &visited));
  EXPECT_EQ(2, std::count(visited.begin(), visited.end(), cfg.entry_block()));
  const auto stats =
      ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  ASSERT_EQ(1, stats.arithmetic_transformations);
  visited.clear();
  EXPECT_EQ(10, evaluate_switch(cfg, tags, &visited));
  EXPECT_EQ(1, std::count(visited.begin(), visited.end(), cfg.entry_block()));
  auto* entry_sb = source_blocks::get_first_source_block(cfg.entry_block());
  ASSERT_NE(nullptr, entry_sb);
  entry_sb->foreach_val([](const auto& value) { EXPECT_FALSE(value); });
  size_t calls = 0;
  for (auto* block : visited) {
    for (auto& mie : InstructionIterable(block)) {
      if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
        ++calls;
      }
    }
  }
  EXPECT_EQ(2, calls);
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_preserves_default_case_counts) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.defaultCounts:(I)I"
     ((load-param v0)
      (.src_block "LArithmetic;.defaultCounts:(I)I" 4 (5.0 1.0))
      (switch v0 (:D :A :B :C))
      (:D 0)(.src_block "LArithmetic;.defaultCounts:(I)I" 0 (2.0 1.0))
      (const v1 0)(return v1)
      (:A 1)(.src_block "LArithmetic;.defaultCounts:(I)I" 1 (1.0 1.0))
      (const v1 1)(return v1)
      (:B 2)(.src_block "LArithmetic;.defaultCounts:(I)I" 2 (1.0 1.0))
      (const v1 2)(return v1)
      (:C 3)(.src_block "LArithmetic;.defaultCounts:(I)I" 3 (1.0 1.0))
      (const v1 3)(return v1))))");
  method->get_code()->build_cfg();
  for (bool normalize : {false, true}) {
    SCOPED_TRACE(normalize);
    cfg::ControlFlowGraph cfg;
    method->get_code()->cfg().deep_copy(&cfg);
    if (normalize) {
      const auto stats = ReduceSparseSwitchesPass::trivial_transformation(cfg);
      EXPECT_EQ(1, stats.removed_trivial_switch_cases);
    }
    const auto stats =
        ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
    ASSERT_EQ(1, stats.arithmetic_transformations);
    EXPECT_EQ(normalize ? 3 : 4, stats.arithmetic_switch_cases);
    for (int32_t input : {-1, 0, 1, 2, 3, 4}) {
      EXPECT_EQ(input >= 0 && input <= 3 ? input : 0,
                evaluate_switch(cfg, input));
    }
    size_t value_blocks = 0;
    for (auto* block : cfg.blocks()) {
      for (auto& mie : InstructionIterable(block)) {
        if (mie.insn->opcode() == OPCODE_CONST && mie.insn->dest() == 1 &&
            mie.insn->get_literal() == 0) {
          auto* sb = source_blocks::get_first_source_block(block);
          ASSERT_NE(nullptr, sb);
          sb->foreach_val([normalize](const auto& value) {
            if (normalize) {
              ASSERT_TRUE(value);
              EXPECT_FLOAT_EQ(2.0f, value->val);
            } else {
              EXPECT_FALSE(value);
            }
          });
        }
        if (mie.insn->opcode() == OPCODE_MOVE) {
          ++value_blocks;
          auto* sb = source_blocks::get_first_source_block(block);
          ASSERT_NE(nullptr, sb);
          sb->foreach_val([normalize](const auto& value) {
            if (normalize) {
              ASSERT_TRUE(value);
              EXPECT_FLOAT_EQ(3.0f, value->val);
            } else {
              EXPECT_FALSE(value);
            }
          });
        }
      }
    }
    EXPECT_EQ(1, value_blocks);
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_checks_move_aware_narrow_uses) {
  const std::vector<std::pair<std::string, bool>> uses{
      {R"((move v2 v1)(invoke-static (v2) "LConsumer;.consume:(B)V"))", false},
      {R"((move v2 v1)(sput-byte v2 "LConsumer;.field:B"))", false},
      {R"((move v2 v1)(filled-new-array (v2) "[B")(move-result-object v2))",
       false},
      {R"((move v2 v1)(int-to-byte v2 v2)
          (invoke-static (v2) "LConsumer;.consume:(B)V"))",
       true},
      {R"((move v2 v1)(filled-new-array (v2) "[I")(move-result-object v2))",
       true}};
  size_t index = 0;
  for (const auto& [use, accepted] : uses) {
    const auto body = std::string(R"(
      ((load-param v0)(switch v0 (:A :B :C :D))
       (const v1 0)(return v1)
       (:A 0)(const v1 0)(goto :Use)
       (:B 1)(const v1 1)(goto :Use)
       (:C 2)(const v1 2)(goto :Use)
       (:D 3)(const v1 3)(goto :Use)
       (:Use))") + use +
                      "(const v1 0)(return v1))";
    auto* method = assembler::method_from_string(
        "(method (public static) \"LArithmetic;.uses" +
        std::to_string(index++) + ":(I)I\" " + body + ")");
    method->get_code()->build_cfg();
    const auto before = show(method->get_code()->cfg());
    auto stats = ReduceSparseSwitchesPass::arithmetic_transformation(
        method->get_code()->cfg(), method);
    EXPECT_EQ(accepted ? 1 : 0, stats.arithmetic_transformations);
    if (!accepted) {
      EXPECT_EQ(before, show(method->get_code()->cfg()));
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_preserves_independent_default_parameters) {
  for (size_t result_reg : {1, 2}) {
    auto* method = assembler::method_from_string(
        "(method (public static) \"LArithmetic;.defaultParams" +
        std::to_string(result_reg) + R"(:(III)I"
         ((load-param v0)(load-param v1)(load-param v2)
          (switch v0 (:A :B :C :D))(return v)" +
        std::to_string(result_reg) + R"()
          (:A -2)(const v1 8)(goto :End)
          (:B -1)(const v1 9)(goto :End)
          (:C 0)(const v1 10)(goto :End)
          (:D 1)(const v1 11)(goto :End)
          (:End)(return v1))))");
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    const std::vector<std::vector<int32_t>> inputs{{-3, 17, 91}, {2, 17, 91},
                                                   {-3, -42, 8}, {2, -42, 8},
                                                   {-2, 17, 91}, {1, -42, 8}};
    std::vector<int32_t> expected;
    expected.reserve(inputs.size());
    for (const auto& params : inputs) {
      expected.push_back(evaluate_switch(cfg, params));
    }
    const auto stats =
        ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
    ASSERT_EQ(1, stats.arithmetic_transformations);
    for (size_t i = 0; i < inputs.size(); ++i) {
      EXPECT_EQ(expected[i], evaluate_switch(cfg, inputs[i]));
    }
  }
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_does_not_invent_default_edge_counts) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LArithmetic;.ambiguousCounts:(I)I"
      ((load-param v0)
       (.src_block "LArithmetic;.ambiguousCounts:(I)I" 0 (100.0 1.0))
       (switch v0 (:A :B :C :D))
       (.src_block "LArithmetic;.ambiguousCounts:(I)I" 5 (86.0 1.0))
       (const v1 -1)(return v1)
       (:A 0)(.src_block "LArithmetic;.ambiguousCounts:(I)I" 1 (2.0 0.2))
       (const v1 10)(return v1)
       (:B 1)(.src_block "LArithmetic;.ambiguousCounts:(I)I" 2 (3.0 0.3))
       (const v1 11)(return v1)
       (:C 2)(.src_block "LArithmetic;.ambiguousCounts:(I)I" 3 (4.0 0.4))
       (const v1 12)(return v1)
       (:D 3)(.src_block "LArithmetic;.ambiguousCounts:(I)I" 4 (5.0 0.5))
       (const v1 13)(return v1))))");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();
  const auto stats =
      ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
  ASSERT_EQ(1, stats.arithmetic_transformations);
  cfg::Block* upper = nullptr;
  cfg::Block* value = nullptr;
  for (auto* block : cfg.blocks()) {
    auto* sb = source_blocks::get_first_source_block(block);
    if (sb != nullptr && sb->id == SourceBlock::kSyntheticId) {
      if (sb->get_val(0)) {
        value = block;
      } else {
        upper = block;
      }
    }
  }
  ASSERT_NE(nullptr, upper);
  ASSERT_NE(nullptr, value);
  ASSERT_EQ(14, source_blocks::get_first_source_block(value)->get_val(0));
  for (int32_t default_input : {-1, 4}) {
    size_t upper_visits = 0;
    size_t value_visits = 0;
    for (int32_t selector = 0; selector < 5; ++selector) {
      const size_t count = selector < 4 ? selector + 2 : 86;
      for (size_t n = 0; n < count; ++n) {
        std::vector<cfg::Block*> visited;
        evaluate_switch(
            cfg, std::vector<int32_t>{selector < 4 ? selector : default_input},
            &visited);
        upper_visits += std::count(visited.begin(), visited.end(), upper);
        value_visits += std::count(visited.begin(), visited.end(), value);
      }
    }
    EXPECT_EQ(14, value_visits);
    EXPECT_EQ(default_input < 0 ? 14 : 100, upper_visits);
  }
  using V = source_blocks::ViolationsHelper::Violation;
  EXPECT_EQ(1, source_blocks::compute(V::kHotImmediateDomNotHot, cfg));
  EXPECT_EQ(0, source_blocks::compute(V::kHotImmediateDomNotHot, cfg, true));
}

TEST_F(ReduceSparseSwitchesTest,
       arithmetic_switch_checks_logical_invoke_arguments) {
  const std::vector<std::pair<std::string, bool>> calls{
      {R"((invoke-static (v1) "LConsumer;.intArg:(I)V"))", true},
      {R"((invoke-virtual (v5 v1) "LConsumer;.intArg:(I)V"))", true},
      {R"((invoke-interface (v5 v6 v1) "LConsumer;.mixedArg:(JI)V"))", true},
      {R"((invoke-static (v6 v1 v1 v1 v1 v1 v1 v1 v1 v8)
           "LConsumer;.manyArgs:(JIIIIIIII[I)V"))",
       true},
      {R"((invoke-virtual (v5 v6 v1 v1 v8)
           "LConsumer;.wideAndArray:(JII[I)V"))",
       true},
      {R"((invoke-static (v6 v1) "LConsumer;.narrowAfterWide:(JB)V"))", false},
      {R"((invoke-virtual (v5 v6 v1) "LConsumer;.narrowAfterWide:(JC)V"))",
       false},
      {R"((move v2 v1)(invoke-interface (v5 v6 v2)
           "LConsumer;.narrowMove:(JS)V"))",
       false},
      {R"((move v2 v1)(int-to-byte v2 v2)
           (invoke-virtual (v5 v6 v2) "LConsumer;.converted:(JB)V"))",
       true},
      {R"((filled-new-array (v1) "[I")(move-result-object v2)
           (invoke-static (v2) "LConsumer;.varargs:([I)V"))",
       true}};
  size_t index = 0;
  for (const auto& [call, accepted] : calls) {
    auto* method = assembler::method_from_string(
        "(method (public static) \"LArithmetic;.logicalArgs" +
        std::to_string(index++) + R"(:(ILConsumer;J[I)I"
         ((load-param v0)(load-param-object v5)(load-param-wide v6)
          (load-param-object v8)(switch v0 (:A :B :C :D))
          (const v1 -1)(return v1)
          (:A 0)(const v1 10)(goto :Use)
          (:B 1)(const v1 11)(goto :Use)
          (:C 2)(const v1 12)(goto :Use)
          (:D 3)(const v1 13)(goto :Use)
          (:Use))" +
        call + "(const v1 0)(return v1)))");
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    const auto before = show(cfg);
    const auto regs = cfg.get_registers_size();
    const auto stats =
        ReduceSparseSwitchesPass::arithmetic_transformation(cfg, method);
    EXPECT_EQ(accepted ? 1 : 0, stats.arithmetic_transformations) << call;
    if (!accepted) {
      EXPECT_EQ(before, show(cfg));
      EXPECT_EQ(regs, cfg.get_registers_size());
    }
  }
}

TEST_F(ReduceSparseSwitchesTest, trivial_switch_case) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2))

        (:L1 50)
        (return-void)

        (:L0 0)
        (return-void)

        (:L2 100)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::trivial_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.removed_trivial_switch_cases, 1);
  EXPECT_EQ(stats.removed_trivial_switches, 0);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L0 :L1))
      (return-void)
      (:L0 100)
      (return-void)
      (:L1 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, trivial_switch) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0))

        (:L0 50)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::trivial_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.removed_trivial_switch_cases, 1);
  EXPECT_EQ(stats.removed_trivial_switches, 1);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, splittingEvenSizeSwitch) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3))

        (return-void)

        (:L0 0)
        (return-void)
        (:L1 50)
        (return-void)

        (:L2 100)
        (return-void)
        (:L3 101)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::splitting_transformation(
      4, 2, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.splitting_transformations, 1);
  EXPECT_EQ(stats.splitting_transformations_packed_segments, 1);
  EXPECT_EQ(stats.splitting_transformations_switch_cases_packed, 2);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L2 :L3))

      (switch v0 (:L0 :L1))
      (return-void)

      (:L0 50)
      (return-void)
      (:L1 0)
      (return-void)

      (:L2 101)
      (return-void)
      (:L3 100)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, splittingEvenSizeSwitch2) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3))

        (return-void)

        (:L0 0)
        (return-void)
        (:L1 1)
        (return-void)

        (:L2 100)
        (return-void)
        (:L3 101)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::splitting_transformation(
      4, 2, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.splitting_transformations, 1);
  EXPECT_EQ(stats.splitting_transformations_packed_segments, 2);
  EXPECT_EQ(stats.splitting_transformations_switch_cases_packed, 4);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L2 :L3))

      (switch v0 (:L0 :L1))
      (return-void)

      (:L0 101)
      (return-void)
      (:L1 100)
      (return-void)

      (:L2 1)
      (return-void)
      (:L3 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, splittingOddSizeSwitch) {
  // Note that we considered as for a "packed" switch any switch that is not
  // "sufficiently sparse". Or in other words: It's good enough for a packed
  // switch if at most half of the case keys in its extent are missing.
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3 :L4))

        (return-void)

        (:L0 0)
        (return-void)
        (:L1 50)
        (return-void)

        (:L2 100)
        (return-void)
        (:L3 102)
        (return-void)
        (:L4 104)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::splitting_transformation(
      5, 2, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.splitting_transformations, 1);
  EXPECT_EQ(stats.splitting_transformations_packed_segments, 1);
  EXPECT_EQ(stats.splitting_transformations_switch_cases_packed, 3);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L2 :L3 :L4))

      (switch v0 (:L0 :L1))
      (return-void)

      (:L0 50)
      (return-void)
      (:L1 0)
      (return-void)

      (:L2 104)
      (return-void)
      (:L3 102)
      (return-void)
      (:L4 100)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, splittingPerfectly) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3))

        (return-void)

        (:L0 0)
        (return-void)
        (:L1 1)
        (return-void)

        (:L2 100)
        (return-void)
        (:L3 101)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::splitting_transformation(
      4, 2, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.splitting_transformations, 1);
  EXPECT_EQ(stats.splitting_transformations_packed_segments, 2);
  EXPECT_EQ(stats.splitting_transformations_switch_cases_packed, 4);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L2 :L3))
      (switch v0 (:L0 :L1))
      (return-void)

      (:L0 101)
      (return-void)
      (:L1 100)
      (return-void)

      (:L2 1)
      (return-void)
      (:L3 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, multiplexing) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3 :L4))
        (return-void)

        (:L0 0)
        (return-void)
        (:L1 3)
        (return-void)
        (:L2 6)
        (return-void)
        (:L3 9)
        (return-void)
        (:L4 12)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::multiplexing_transformation(
      5, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.multiplexing.size(), 1);
  EXPECT_EQ(unordered_any(stats.multiplexing)->first, 4);
  auto& mstats = unordered_any(stats.multiplexing)->second;
  EXPECT_EQ(mstats.abandoned, 0);
  EXPECT_EQ(mstats.transformations, 1);
  EXPECT_EQ(mstats.switch_cases, 5);
  EXPECT_EQ(mstats.inefficiency, 0);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (and-int/lit v1 v0 3)
      (switch v1 (:L1 :L2 :L3 :L4))
    (:L0)
      (return-void)
    (:L1 3)
      (const v1 3)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L2 2)
      (const v1 6)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L3 1)
      (const v1 9)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L4 0)
      (switch v0 (:L5 :L6))
      (goto :L0)
    (:L5 12)
      (return-void)
    (:L6 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, multiplexing_shr) {
  // Almost same situation as in multiplexing test, but now all the case keys
  // are doubled, and here our algorithm figures out that we should first shift
  // the selector by 1 to get the best distribution.
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3 :L4))
        (return-void)

        (:L0 0)
        (return-void)
        (:L1 6)
        (return-void)
        (:L2 12)
        (return-void)
        (:L3 18)
        (return-void)
        (:L4 24)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::multiplexing_transformation(
      5, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.multiplexing.size(), 1);
  EXPECT_EQ(unordered_any(stats.multiplexing)->first, 4);
  auto& mstats = unordered_any(stats.multiplexing)->second;
  EXPECT_EQ(mstats.abandoned, 0);
  EXPECT_EQ(mstats.transformations, 1);
  EXPECT_EQ(mstats.switch_cases, 5);
  EXPECT_EQ(mstats.inefficiency, 0);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (shr-int/lit v1 v0 1)
      (and-int/lit v1 v1 3)
      (switch v1 (:L1 :L2 :L3 :L4))
    (:L0)
      (return-void)
    (:L1 3)
      (const v1 6)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L2 2)
      (const v1 12)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L3 1)
      (const v1 18)
      (if-ne v0 v1 :L0)
      (return-void)
    (:L4 0)
      (switch v0 (:L5 :L6))
      (goto :L0)
    (:L5 24)
      (return-void)
    (:L6 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, multiplexing_sums_source_block_counts) {
  // Same shape as the `multiplexing` test, but with per-block SourceBlock
  // counts. Multiplexing splits the switch's traffic into M disjoint buckets,
  // so each bucket's synthetic SourceBlock must carry the SUM of the counts of
  // the case targets it routes to (plus the shared default) -- NOT a verbatim
  // copy of the whole switch's count, which would inflate total mass by ~M.
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (.src_block "LtestClass;.testMethod(:(I)V" 1 (100.0 1.0))
        (switch v0 (:L0 :L1 :L2 :L3 :L4))
        (.src_block "LtestClass;.testMethod(:(I)V" 2 (1.0 1.0))
        (return-void)

        (:L0 0)
        (.src_block "LtestClass;.testMethod(:(I)V" 3 (10.0 1.0))
        (return-void)
        (:L1 3)
        (.src_block "LtestClass;.testMethod(:(I)V" 4 (3.0 1.0))
        (return-void)
        (:L2 6)
        (.src_block "LtestClass;.testMethod(:(I)V" 5 (6.0 1.0))
        (return-void)
        (:L3 9)
        (.src_block "LtestClass;.testMethod(:(I)V" 6 (9.0 1.0))
        (return-void)
        (:L4 12)
        (.src_block "LtestClass;.testMethod(:(I)V" 7 (12.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();

  auto stats = ReduceSparseSwitchesPass::multiplexing_transformation(5, cfg);
  EXPECT_EQ(stats.multiplexing.size(), 1);

  // Buckets by (key & 3): {0,12}, {9}, {6}, {3}; each bucket also routes to the
  // default. The synthetic bucket counts therefore sum to the traffic through
  // the buckets: (10+12) + 9 + 6 + 3 + 4*default(1) = 44 -- not 4*100 = 400,
  // which a verbatim clone of the switch's own count would produce.
  float synthetic_sum = 0;
  for (auto* b : cfg.blocks()) {
    source_blocks::foreach_source_block(b, [&](auto* sb) {
      if (sb->id == SourceBlock::kSyntheticId) {
        if (auto v = sb->get_val(0)) {
          synthetic_sum += *v;
        }
      }
    });
  }
  EXPECT_FLOAT_EQ(synthetic_sum, 44.0f);
}

TEST_F(ReduceSparseSwitchesTest, splittingIntoLog2ManyChunks) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)
        (switch v0 (:L0 :L1 :L2 :L3 :L4 :L5 :L6 :L7 :L8 :L9 :L10 :L11 :L12 :L13 :L14 :L15))

        (return-void)

        (:L0 0)
        (return-void)
        (:L1 1)
        (return-void)
        (:L2 2)
        (return-void)
        (:L3 3)
        (return-void)
        (:L4 4)
        (return-void)
        (:L5 5)
        (return-void)
        (:L6 6)
        (return-void)

        (:L7 50)
        (return-void)

        (:L8 100)
        (return-void)
        (:L9 101)
        (return-void)
        (:L10 102)
        (return-void)
        (:L11 103)
        (return-void)
        (:L12 104)
        (return-void)
        (:L13 105)
        (return-void)
        (:L14 106)
        (return-void)

        (:L15 150)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::splitting_transformation(
      10, 3, method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.splitting_transformations, 1);
  EXPECT_EQ(stats.splitting_transformations_packed_segments, 2);
  EXPECT_EQ(stats.splitting_transformations_switch_cases_packed, 14);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (switch v0 (:L9 :L10 :L11 :L12 :L13 :L14 :L15))
      (switch v0 (:L2 :L3 :L4 :L5 :L6 :L7 :L8))
      (switch v0 (:L0 :L1))
      (return-void)

      (:L0 150)
      (return-void)
      (:L1 50)
      (return-void)

      (:L2 106)
      (return-void)
      (:L3 105)
      (return-void)
      (:L4 104)
      (return-void)
      (:L5 103)
      (return-void)
      (:L6 102)
      (return-void)
      (:L7 101)
      (return-void)
      (:L8 100)
      (return-void)

      (:L9 6)
      (return-void)
      (:L10 5)
      (return-void)
      (:L11 4)
      (return-void)
      (:L12 3)
      (return-void)
      (:L13 2)
      (return-void)
      (:L14 1)
      (return-void)
      (:L15 0)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_sparse) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 0)
        (return-void)
        (:L1 11)
        (return-void)
        (:L2 222)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :L2)
      (const v1 11)
      (if-eq v0 v1 :L1)
      (const v1 222)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (return-void)
      (:L1)
      (return-void)
      (:L2)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_very_small_packed) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 0)
        (return-void)
        (:L1 1)
        (return-void)
        (:L2 2)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (if-eqz v0 :L2)
      (const v1 1)
      (if-eq v0 v1 :L1)
      (const v1 2)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (return-void)
      (:L1)
      (return-void)
      (:L2)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_add) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 10000000)
        (return-void)
        (:L1 10000011)
        (return-void)
        (:L2 10000022)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 10000000)
      (if-eq v0 v1 :L2)
      (add-int/lit v1 v1 11)
      (if-eq v0 v1 :L1)
      (add-int/lit v1 v1 11)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (return-void)
      (:L1)
      (return-void)
      (:L2)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_add_overflowing) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 1073741824)
        (return-void)
        (:L1 -2147483648)
        (return-void)
        (:L2 1073741825)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  const auto& expected_str = R"(
    (
      (load-param v0)
      (const v1 -2147483648)
      (if-eq v0 v1 :L2)
      (const v1 1073741824)
      (if-eq v0 v1 :L1)
      (add-int/lit v1 v1 1)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (return-void)
      (:L1)
      (return-void)
      (:L2)
      (return-void)
    )
  )";
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_not) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (switch v0 (:L0 :L1 :L2 :L3 :L4))
        (return-void)

        (:L0 10000000)
        (return-void)
        (:L1 10000011)
        (return-void)
        (:L2 10000022)
        (return-void)
        (:L3 10000023)
        (return-void)
        (:L4 10000024)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 0);
  EXPECT_EQ(stats.expanded_switch_cases, 0);
}

TEST_F(ReduceSparseSwitchesTest, expand_sparse_hot_source_blocks) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (.src_block "LtestClass;.testMethod(:(I)V" 1 (1.0 1.0))
        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 0)
        (.src_block "LtestClass;.testMethod(:(I)V" 2 (1.0 1.0))
        (return-void)
        (:L1 11)
        (.src_block "LtestClass;.testMethod(:(I)V" 3 (1.0 1.0))
        (return-void)
        (:L2 222)
        (.src_block "LtestClass;.testMethod(:(I)V" 4 (1.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  std::ostringstream oss;
  oss << R"(
    (
      (load-param v0)
      (.src_block "LtestClass;.testMethod(:(I)V" 1 (1.0 1.0))
      (if-eqz v0 :L2)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (2.0 1.0))
      (const v1 11)
      (if-eq v0 v1 :L1)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (1.0 1.0))
      (const v1 222)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (.src_block "LtestClass;.testMethod(:(I)V" 4 (1.0 1.0))
      (return-void)
      (:L1)
      (.src_block "LtestClass;.testMethod(:(I)V" 3 (1.0 1.0))
      (return-void)
      (:L2)
      (.src_block "LtestClass;.testMethod(:(I)V" 2 (1.0 1.0))
      (return-void)
    )
  )";
  const auto& expected_str = oss.str();

  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest, expand_sparse_mixed_source_blocks) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (.src_block "LtestClass;.testMethod(:(I)V" 1 (1.0 1.0))
        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 0)
        (.src_block "LtestClass;.testMethod(:(I)V" 2 (1.0 1.0))
        (return-void)
        (:L1 11)
        (.src_block "LtestClass;.testMethod(:(I)V" 3 (0.0 1.0))
        (return-void)
        (:L2 222)
        (.src_block "LtestClass;.testMethod(:(I)V" 4 (0.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  std::ostringstream oss;
  oss << R"(
    (
      (load-param v0)
      (.src_block "LtestClass;.testMethod(:(I)V" 1 (1.0 1.0))
      (if-eqz v0 :L2)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (0.0 1.0))
      (const v1 11)
      (if-eq v0 v1 :L1)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (0.0 1.0))
      (const v1 222)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (.src_block "LtestClass;.testMethod(:(I)V" 4 (0.0 1.0))
      (return-void)
      (:L1)
      (.src_block "LtestClass;.testMethod(:(I)V" 3 (0.0 1.0))
      (return-void)
      (:L2)
      (.src_block "LtestClass;.testMethod(:(I)V" 2 (1.0 1.0))
      (return-void)
    )
  )";
  const auto& expected_str = oss.str();

  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}

TEST_F(ReduceSparseSwitchesTest,
       expand_sparse_all_cold_except_last_source_block) {
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")LtestClass;.testMethod(:(I)V"
      (
        (load-param v0)

        (.src_block "LtestClass;.testMethod(:(I)V" 1 (0.0 1.0))
        (switch v0 (:L0 :L1 :L2))
        (return-void)

        (:L0 0)
        (.src_block "LtestClass;.testMethod(:(I)V" 2 (0.0 1.0))
        (return-void)
        (:L1 11)
        (.src_block "LtestClass;.testMethod(:(I)V" 3 (0.0 1.0))
        (return-void)
        (:L2 222)
        (.src_block "LtestClass;.testMethod(:(I)V" 4 (1.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();

  auto stats = ReduceSparseSwitchesPass::expand_transformation(
      method->get_code()->cfg());
  method->get_code()->clear_cfg();

  EXPECT_EQ(stats.expanded_transformations, 1);
  EXPECT_EQ(stats.expanded_switch_cases, 3);

  std::ostringstream oss;
  oss << R"(
    (
      (load-param v0)
      (.src_block "LtestClass;.testMethod(:(I)V" 1 (0.0 1.0))
      (if-eqz v0 :L2)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (1.0 1.0))
      (const v1 11)
      (if-eq v0 v1 :L1)
      (.src_block "LtestClass;.testMethod(:(I)V" )"
      << SourceBlock::kSyntheticId << R"( (1.0 1.0))
      (const v1 222)
      (if-eq v0 v1 :L0)
      (return-void)
      (:L0)
      (.src_block "LtestClass;.testMethod(:(I)V" 4 (1.0 1.0))
      (return-void)
      (:L1)
      (.src_block "LtestClass;.testMethod(:(I)V" 3 (0.0 1.0))
      (return-void)
      (:L2)
      (.src_block "LtestClass;.testMethod(:(I)V" 2 (0.0 1.0))
      (return-void)
    )
  )";
  const auto& expected_str = oss.str();

  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), method->get_code());
}
