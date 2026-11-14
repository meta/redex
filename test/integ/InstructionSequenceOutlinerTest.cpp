/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstring>
#include <fstream>
#include <functional>
#include <gtest/gtest.h>
#include <iterator>
#include <json/reader.h>
#include <json/value.h>
#include <optional>
#include <set>
#include <unordered_set>

#include <unistd.h>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "ScopedCFG.h"
#include "TypeUtil.h"

#include "InstructionSequenceOutliner.h"
#include "RedexContext.h"

std::unordered_set<DexMethodRef*> find_invoked_methods(
    const cfg::ControlFlowGraph& cfg, const std::string& name) {
  std::unordered_set<DexMethodRef*> methods;
  for (const auto& mie : InstructionIterable(cfg)) {
    if (mie.insn->has_method()) {
      DexMethodRef* m = mie.insn->get_method();
      if (m->get_name()->str().find(name) != std::string::npos) {
        methods.insert(m);
      }
    }
  }
  return methods;
}

DexMethodRef* find_invoked_method(const cfg::ControlFlowGraph& cfg,
                                  const std::string& name) {
  for (const auto& mie : InstructionIterable(cfg)) {
    if (mie.insn->has_method()) {
      DexMethodRef* m = mie.insn->get_method();
      if (m->get_name()->str().find(name) != std::string::npos) {
        return m;
      }
    }
  }
  return nullptr;
}

size_t count_invokes(const cfg::ControlFlowGraph& cfg, DexMethodRef* m) {
  int count = 0;
  for (const auto& mie : InstructionIterable(cfg)) {
    if (mie.insn->has_method() && mie.insn->get_method() == m) {
      count++;
    }
  }
  return count;
}

size_t count_invokes(const cfg::ControlFlowGraph& cfg,
                     const std::string& name) {
  size_t count = 0;
  for (auto* m : find_invoked_methods(cfg, name)) {
    count += count_invokes(cfg, m);
  }
  return count;
}

void get_positions(std::unordered_set<DexPosition*>& positions,
                   cfg::ControlFlowGraph& cfg) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  for (auto* block : cfg.blocks()) {
    for (auto it = block->begin(); it != block->end(); it++) {
      if (it->type == MFLOW_POSITION) {
        auto* position = it->pos.get();
        if (manager->is_pattern_position(position) ||
            manager->is_switch_position(position)) {
          positions.insert(position);
        }
      }
    }
  }
}

class InstructionSequenceOutlinerTest : public RedexIntegrationTest {
 public:
  std::optional<std::reference_wrapper<DexClasses>> classes;
  InstructionSequenceOutlinerTest() {
    auto* config_file_env = std::getenv("config_file");
    always_assert_log(config_file_env,
                      "Config file must be specified to InterDexTest.\n");

    std::ifstream config_file(config_file_env, std::ifstream::binary);
    config_file >> m_cfg;
    // use a local copy of classes always pointing
    // to the first dex. It keeps the
    // existing test consistent when introduces
    // the secondary dex.
    classes = stores.back().get_dexen().front();
  }

  void run_passes(const std::vector<Pass*>& passes) {
    RedexIntegrationTest::run_passes(passes, nullptr, m_cfg);
  }

  void set_full_dbg_positions(bool value) {
    m_cfg["InstructionSequenceOutlinerPass"]["full_dbg_positions"] = value;
  }

 private:
  Json::Value m_cfg;
};

TEST_F(InstructionSequenceOutlinerTest, basic) {
  // Testing basic outlining, regardless of whether the outlined instruction
  // sequence is surrounded by some distractions
  std::vector<DexMethodRef*> println_methods;
  std::vector<DexMethod*> basic_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("basic") != std::string::npos) {
        IRCode* code = m->get_code();
        cfg::ScopedCFG scoped_cfg(code);
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.push_back(println_method);
        EXPECT_EQ(count_invokes(code->cfg(), println_method), 5);
        basic_methods.push_back(m);
      }
    }
  }
  sort_unique(println_methods);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = println_methods.front();
  EXPECT_EQ(basic_methods.size(), 4);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : basic_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 0);
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    // outlined method should reside in the same class, as the outlined
    // code sequence is not used by any other classs
    EXPECT_EQ(outlined_method->get_class(), m->get_class());
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 5);
  }
}

TEST_F(InstructionSequenceOutlinerTest, twice) {
  // Testing that there can be multiple outlined locations within a method.
  std::vector<DexMethod*> twice_methods;
  DexMethodRef* println_method = nullptr;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("twice") != std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 10);
        twice_methods.push_back(m);
      }
    }
  }
  EXPECT_NE(println_method, nullptr);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  for (auto* m : twice_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 0);
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 2);
  }
}

TEST_F(InstructionSequenceOutlinerTest, in_try) {
  // Testing that we can outlined across a big block (consisting of several
  // individual blocks) surrounded by a try-catch.
  std::vector<DexMethod*> in_try_methods;
  DexMethodRef* println_method = nullptr;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str() == "in_try") {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 5);
        in_try_methods.push_back(m);
      }
    }
  }
  EXPECT_NE(println_method, nullptr);
  EXPECT_EQ(in_try_methods.size(), 1);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  for (auto* m : in_try_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 0);
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, in_try_ineligible_) {
  // Big blocks don't kick in when...
  // - there are different catches
  //   (in_try_ineligible_due_to_different_catches), or
  // - there is a conditional branch
  //   (in_try_ineligible_due_to_conditional_branch)
  std::vector<DexMethod*> in_try_ineligible_methods;
  DexMethodRef* println_method = nullptr;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("in_try_ineligible_") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 5);
        in_try_ineligible_methods.push_back(m);
      }
    }
  }
  EXPECT_NE(println_method, nullptr);
  EXPECT_EQ(in_try_ineligible_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : in_try_ineligible_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 2);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 2);
}

TEST_F(InstructionSequenceOutlinerTest, param) {
  // Testing outlining of code into a method that takes a parameter
  std::vector<DexMethod*> param_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("param") != std::string::npos) {
        param_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(param_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : param_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 2);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 2);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
  }
}

TEST_F(InstructionSequenceOutlinerTest, result) {
  // Testing outlining of code that has a live-out value that needs to be
  // returned by the outlined method
  std::vector<DexMethod*> result_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("result") != std::string::npos) {
        result_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(result_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : result_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_int());
    EXPECT_EQ(proto->get_args()->size(), 0);
  }
}

TEST_F(InstructionSequenceOutlinerTest, normalization) {
  // Testing that outlining happens modulo register naming
  std::vector<DexMethod*> param_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("normalization") != std::string::npos) {
        param_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(param_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : param_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_int());
    EXPECT_EQ(proto->get_args()->size(), 1);
    EXPECT_EQ(proto->get_args()->at(0), type::_int());
  }
}

TEST_F(InstructionSequenceOutlinerTest, defined_reg_escapes_to_catch) {
  // We cannot outline when a defined register escapes to a throw block
  std::vector<DexMethod*> defined_reg_escapes_to_catch_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str() == "defined_reg_escapes_to_catch") {
        defined_reg_escapes_to_catch_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(defined_reg_escapes_to_catch_methods.size(), 1);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  for (auto* m : defined_reg_escapes_to_catch_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_EQ(outlined_method, nullptr);
  }
}

TEST_F(InstructionSequenceOutlinerTest, big_block_can_end_with_no_tries) {
  // Test that a sequence becomes beneficial to outline because a big block
  // can have throwing code followed by non-throwing code.
  std::vector<DexMethod*> big_block_can_end_with_no_tries_methods;
  DexMethodRef* println_method;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("big_block_can_end_with_no_tries") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        println_method = find_invoked_method(*scoped_cfg, "println");
        big_block_can_end_with_no_tries_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(big_block_can_end_with_no_tries_methods.size(), 2);
  EXPECT_NE(println_method, nullptr);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  for (auto* m : big_block_can_end_with_no_tries_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    auto println_method_invokes = count_invokes(*scoped_cfg, println_method);
    EXPECT_EQ(println_method_invokes, 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, two_out_regs) {
  // We cannot outline when there are two defined live-out regs
  std::vector<DexMethod*> two_out_regs_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str() == "defined_reg_escapes_to_catch") {
        two_out_regs_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(two_out_regs_methods.size(), 1);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  for (auto* m : two_out_regs_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_EQ(outlined_method, nullptr);
  }
}

TEST_F(InstructionSequenceOutlinerTest, type_demand) {
  // The arguments of the outlined methods are as weak as allowed by the
  // demands placed on them in the outlined instruction sequence.
  // In particular, here, the argument is of type Object, not String, as the
  // outlined instruction sequence starts with a cast, which only has the
  // weaked type demand of Object.
  std::vector<DexMethod*> param_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("type_demand") != std::string::npos) {
        param_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(param_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : param_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 1);
    EXPECT_EQ(proto->get_args()->at(0), type::java_lang_Object());
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_tree) {
  // We can outline trees of control-flow. We check this by looking for
  // all occurrences of the println method invocations to have moved to
  // the outlined methods
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_tree") != std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, switch) {
  // We can outline entire switches (just a special case of conditional
  // control-flow).
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("switch") != std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 4);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 4);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 4);
  for (auto* m : outlined_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_arg_and_res) {
  // We can outline conditional controlflow with incoming and outgoing
  // registers.
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_arg_and_res") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_const_res) {
  // We can outline conditional controlflow that returns constants,
  // here, ints.
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_const_res") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_float_const_res) {
  // When outlining code that returns costs, we properly distinguish
  // consts. The body of cfg_with_float_const_res* contains the same
  // instructions as cfg_with_const_res*, and yet due to different
  // type usages, we need (and do) generate a different outlined
  // method with a different return type.
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_float_const_res") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_object_res) {
  // When outlining code that returns objects, we can pick the least
  // specific return type (if there is a single such type).
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_object_res") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype()->str(), "V");
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_joinable_object_res) {
  // When outlining code that returns objects, we can pick a joined
  // (common base) type as the return type, even if that type isn't
  // mentioned in the code.
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_joinable_object_res") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 3);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 3);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 3);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype()->str(), "V");
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, cfg_with_object_arg) {
  // When outlining code that receives objects, we can pick the most
  // specific type demand (if there is a single such type).
  std::vector<DexMethod*> cfg_tree_methods;
  std::unordered_set<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str().find("cfg_with_object_arg") !=
          std::string::npos) {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.insert(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 4);
        cfg_tree_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(cfg_tree_methods.size(), 2);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = *println_methods.begin();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* m : cfg_tree_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 4);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 4);
  for (auto* m : outlined_methods) {
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, distributed) {
  // When outlined sequence occur in unrelated classes, the outlined method
  // it put into a generated helper class
  std::vector<DexMethod*> distributed_methods;
  std::vector<DexMethodRef*> println_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_dmethods()) {
      if (m->get_name()->str() == "distributed") {
        cfg::ScopedCFG scoped_cfg(m->get_code());
        auto* println_method = find_invoked_method(*scoped_cfg, "println");
        EXPECT_NE(println_method, nullptr);
        println_methods.push_back(println_method);
        EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 5);
        distributed_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(distributed_methods.size(), 2);
  sort_unique(println_methods);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = println_methods.front();

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (const auto& m : distributed_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
    auto methods = find_invoked_methods(*scoped_cfg, "$outline");
    EXPECT_EQ(methods.size(), 4);
    for (auto* outlined_method : methods) {
      EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
      outlined_methods.push_back(outlined_method->as_def());
    }
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 4);
  for (auto* m : outlined_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 1);
  }
}

TEST_F(InstructionSequenceOutlinerTest, colocate_with_refs) {
  // When an outlinable instruction sequence occurrs in different classes,
  // but the outlinable instrucitons are all members that share a common
  // base class, then that base class will host the outlined method.
  std::vector<DexMethod*> colocate_with_refs_methods;
  for (const auto& cls : classes->get()) {
    for (const auto& m : cls->get_vmethods()) {
      if (m->get_name()->str() == "colocate_with_refs") {
        colocate_with_refs_methods.push_back(m);
      }
    }
  }
  EXPECT_EQ(colocate_with_refs_methods.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };

  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (const auto& m : colocate_with_refs_methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 2);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_EQ(
        m->get_class()->get_name()->str(),
        "Lcom/facebook/redextest/InstructionSequenceOutlinerTest$Nested3;");
  }
}

TEST_F(InstructionSequenceOutlinerTest, reuse_outlined_methods) {
  // It tests the reuse of the outlined methods across dexes.
  // Secondary dex reuses the println methods defined in primary dex.
  // Supposedly, after the ISO the println should be outlined and the
  // outlined method resides in the primary dex.
  std::vector<DexMethodRef*> println_methods;
  std::vector<DexMethod*> basic_methods;
  std::vector<DexMethod*> methods_in_secondary_dex;

  for (auto iter_store = stores.rbegin(); iter_store != stores.rend();
       ++iter_store) {
    const auto& dex = iter_store->get_dexen();
    for (const auto& classes : dex) {
      for (const auto& cls : classes) {
        for (const auto& m : cls->get_vmethods()) {
          if (m->get_name()->str().find("basic") != std::string::npos ||
              m->get_name()->str().find("secondary") != std::string::npos) {

            IRCode* code = m->get_code();
            cfg::ScopedCFG scoped_cfg(code);
            auto* println_method = find_invoked_method(*scoped_cfg, "println");
            EXPECT_NE(println_method, nullptr);
            println_methods.push_back(println_method);
            EXPECT_EQ(count_invokes(code->cfg(), println_method), 5);

            if (m->get_name()->str().find("basic") != std::string::npos) {
              // from primary dex
              basic_methods.push_back(m);
            } else {
              // from secondary dex
              methods_in_secondary_dex.push_back(m);
            }
          }
        }
      }
    }
  }

  // check methods before pass run
  sort_unique(println_methods);
  EXPECT_EQ(println_methods.size(), 1);
  auto* println_method = println_methods.front();
  EXPECT_EQ(methods_in_secondary_dex.size(), 2);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };
  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  // check methods in secondary dex
  for (auto* m : methods_in_secondary_dex) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 0);
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(outlined_method, nullptr);
    // The reused outlined method should reside in the primary class
    EXPECT_EQ(outlined_method->get_class(), basic_methods.front()->get_class());
    EXPECT_EQ(count_invokes(*scoped_cfg, outlined_method), 1);
    outlined_methods.push_back(outlined_method->as_def());
  }

  // check outlined methods
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    EXPECT_TRUE(is_static(m));
    auto* proto = m->get_proto();
    EXPECT_EQ(proto->get_rtype(), type::_void());
    EXPECT_EQ(proto->get_args()->size(), 0);
    cfg::ScopedCFG scoped_cfg(m->get_code());
    EXPECT_EQ(count_invokes(*scoped_cfg, println_method), 5);
  }
}

TEST_F(InstructionSequenceOutlinerTest,
       reduced_positions_mark_collapsed_patterns_without_candidates) {
  set_full_dbg_positions(false);
  std::vector<DexMethod*> methods;
  for (const auto& cls : classes->get()) {
    for (const auto& method : cls->get_vmethods()) {
      if (method->get_name()->str().find("basic") != std::string::npos) {
        methods.push_back(method);
      }
    }
  }
  ASSERT_EQ(methods.size(), 4u);

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };
  run_passes(passes);

  std::vector<DexMethod*> outlined_methods;
  for (auto* method : methods) {
    cfg::ScopedCFG scoped_cfg(method->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    ASSERT_NE(outlined_method, nullptr);
    outlined_methods.push_back(outlined_method->as_def());
  }
  sort_unique(outlined_methods);
  ASSERT_EQ(outlined_methods.size(), 1u);

  bool saw_unreliable = false;
  cfg::ScopedCFG scoped_cfg(outlined_methods.front()->get_code());
  for (auto* block : scoped_cfg->blocks()) {
    for (const auto& mie : *block) {
      if (mie.type != MFLOW_POSITION || mie.pos->file == nullptr) {
        continue;
      }
      if (mie.pos->is_unreliable()) {
        saw_unreliable = true;
        EXPECT_EQ(mie.pos->alt_id(), 0u);
      }
    }
  }
  EXPECT_TRUE(saw_unreliable);
}

TEST_F(InstructionSequenceOutlinerTest, check_positions) {
  // It tests that the positions in the outlined method
  // can be correctly traced back to the callsite positions of the
  // methods (whick invoke the outlined method) when reuse
  // the outlined method across the dex.
  std::vector<DexMethod*> methods;
  std::set<std::string_view> method_names{"basic1", "basic2",     "basic3",
                                          "basic4", "in_try",     "twice1",
                                          "twice2", "secondary1", "secondary2"};
  for (auto iter_store = stores.begin(); iter_store != stores.end();
       ++iter_store) {
    const auto& dex = iter_store->get_dexen();
    for (const auto& classes : dex) {
      for (const auto& cls : classes) {
        for (const auto& m : cls->get_vmethods()) {
          if (method_names.count(m->get_name()->str()) != 0u) {
            methods.push_back(m);
          }
        }
      }
    }
  }

  ASSERT_FALSE(methods.empty());
  {
    // Give every line of one call site a candidate set, so its switch entries
    // have to carry that set through outlining.
    auto* manager = g_redex->get_position_pattern_switch_manager();
    cfg::ScopedCFG scoped_cfg(methods.front()->get_code());
    uint32_t elsewhere_line = 1000;
    for (auto* block : scoped_cfg->blocks()) {
      for (auto& mie : *block) {
        if (mie.type == MFLOW_POSITION && mie.pos->file != nullptr) {
          DexPosition elsewhere(mie.pos->method,
                                DexString::make_string("Elsewhere.java"),
                                elsewhere_line++);
          manager->record_candidates(mie.pos.get(), {&elsewhere});
          ASSERT_NE(mie.pos->alt_id(), 0u);
        }
      }
    }
  }

  std::vector<Pass*> passes = {
      new InstructionSequenceOutliner(),
  };
  run_passes(passes);

  std::unordered_set<DexPosition*> switch_positions;
  std::unordered_set<DexPosition*> pattern_positions;
  std::vector<DexMethod*> outlined_methods;
  // get outlined methods
  for (auto* m : methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    auto* outlined_method = find_invoked_method(*scoped_cfg, "$outline");
    outlined_methods.push_back(outlined_method->as_def());
  }
  // check outlined methods
  sort_unique(outlined_methods);
  EXPECT_EQ(outlined_methods.size(), 1);
  for (auto* m : outlined_methods) {
    auto* code = m->get_code();
    cfg::ScopedCFG scoped_cfg(code);
    // get switch positions from outlined method
    get_positions(switch_positions, *scoped_cfg);
  }

  // pattern id to method map
  std::unordered_map<uint32_t, std::vector<DexMethod*>>
      pattern_id_to_method_map;
  // callsite patterns
  for (auto* m : methods) {
    auto* code = m->get_code();
    cfg::ScopedCFG scoped_cfg(code);
    // get pattern positions
    get_positions(pattern_positions, *scoped_cfg);
    for (auto* pos : pattern_positions) {
      pattern_id_to_method_map[pos->line].push_back(m);
    }
  }

  auto* manager = g_redex->get_position_pattern_switch_manager();
  const auto& alternatives = manager->get_alternatives();
  std::unordered_set<uint32_t> pattern_ids_from_switches;
  bool saw_mixed_reliability = false;

  EXPECT_GT(switch_positions.size(), 0);
  // Get pattern ids from switches and verify that one marked callsite does not
  // mark the other entries sharing its switch.
  for (auto* sp : switch_positions) {
    const auto& group = alternatives.at(sp->line);
    ASSERT_EQ(group.selection, PositionAlternativesSelection::ByPattern);
    bool any_unreliable = false;
    bool all_unreliable = true;
    for (const auto& entry : group.entries) {
      ASSERT_TRUE(entry.pattern_id.has_value());
      pattern_ids_from_switches.insert(*entry.pattern_id);
      any_unreliable = any_unreliable || entry.provenance != nullptr;
      all_unreliable = all_unreliable && entry.provenance != nullptr;
      if (entry.provenance != nullptr) {
        EXPECT_EQ(*entry.provenance, *entry.position);
        EXPECT_NE(entry.provenance->alt_id(), 0u);
      }
    }
    saw_mixed_reliability =
        saw_mixed_reliability || (any_unreliable && !all_unreliable);
  }
  EXPECT_TRUE(saw_mixed_reliability);

  EXPECT_GT(pattern_positions.size(), 0);
  // check callsites pattern ids
  // should be in the switches
  for (auto* pp : pattern_positions) {
    auto pattern_id = pp->line;
    EXPECT_NE(pattern_ids_from_switches.count(pattern_id), 0);
  }

  // Test the pattern ids from switches
  // are from two classes (in two dexes).
  std::unordered_set<std::string> dex_cls_set;
  for (auto pattern_id : pattern_ids_from_switches) {
    for (auto* m : pattern_id_to_method_map.at(pattern_id)) {
      dex_cls_set.insert(m->get_class()->get_name()->c_str());
    }
  }
  EXPECT_EQ(dex_cls_set.size(), 2);
}

namespace {
std::vector<DexMethod*> aba_find_vmethods(std::vector<DexStore>& stores) {
  const std::set<std::string_view> names{"basic1", "basic2",     "basic3",
                                         "basic4", "in_try",     "twice1",
                                         "twice2", "secondary1", "secondary2"};
  std::vector<DexMethod*> methods;
  for (auto& store : stores) {
    for (const auto& classes : store.get_dexen()) {
      for (const auto& cls : classes) {
        for (const auto& m : cls->get_vmethods()) {
          if (names.count(m->get_name()->str()) != 0u) {
            methods.push_back(m);
          }
        }
      }
    }
  }
  std::sort(methods.begin(), methods.end(), compare_dexmethods);
  return methods;
}
} // namespace

// Slots A, B, A: the third run of instructions selects the position of the
// first again, so it must be under A, not left under B.
TEST_F(InstructionSequenceOutlinerTest,
       a_slot_returning_to_an_earlier_position_selects_it_again) {
  auto methods = aba_find_vmethods(stores);
  ASSERT_FALSE(methods.empty());
  // One method string and file for every call site, so all occurrences intern
  // to one pattern and the outlined method has no switch. The k-th println
  // line of each five gets lines[k]; the third returns to the first's line.
  const std::vector<uint32_t> lines{10, 11, 10, 12, 13};
  const auto* same_method = DexString::make_string("LSame;.m:()V");
  const auto* same_file = DexString::make_string("Same.java");
  for (auto* m : methods) {
    cfg::ScopedCFG scoped_cfg(m->get_code());
    size_t sgets = 0;
    DexPosition* pending = nullptr;
    for (auto* block : scoped_cfg->blocks()) {
      for (auto& mie : *block) {
        if (mie.type == MFLOW_POSITION && mie.pos->file != nullptr) {
          pending = mie.pos.get();
          pending->bind(same_method, same_file);
          // A position inside a println line keeps that line.
          pending->line =
              sgets == 0 ? 1 : lines.at(((sgets - 1) / 3) % lines.size());
        } else if (mie.type == MFLOW_OPCODE) {
          if (pending != nullptr && opcode::is_an_sget(mie.insn->opcode()) &&
              sgets % 3 == 0) {
            pending->line = lines.at((sgets / 3) % lines.size());
          }
          pending = nullptr;
          if (opcode::is_an_sget(mie.insn->opcode())) {
            ++sgets;
          }
        }
      }
    }
    ASSERT_EQ(sgets % 15, 0u);
  }
  run_passes({new InstructionSequenceOutliner()});

  cfg::ScopedCFG caller_cfg(methods[0]->get_code());
  auto* ref = find_invoked_method(*caller_cfg, "$outline");
  ASSERT_NE(ref, nullptr);
  auto* code = ref->as_def()->get_code();
  cfg::ScopedCFG scoped_cfg(code);
  std::vector<uint32_t> println_lines;
  const DexPosition* current = nullptr;
  for (auto* block : scoped_cfg->blocks()) {
    for (const auto& mie : *block) {
      if (mie.type == MFLOW_POSITION) {
        current = mie.pos.get();
      } else if (mie.type == MFLOW_OPCODE && mie.insn->has_method() &&
                 mie.insn->get_method()->get_name()->str() == "println") {
        println_lines.push_back(current == nullptr ? 0 : current->line);
      }
    }
  }
  EXPECT_EQ(println_lines, lines);
}

namespace {
std::vector<DexMethod*> find_vmethods(std::vector<DexStore>& stores,
                                      const std::set<std::string_view>& names) {
  std::vector<DexMethod*> methods;
  for (auto& store : stores) {
    for (const auto& classes : store.get_dexen()) {
      for (const auto& cls : classes) {
        for (const auto& m : cls->get_vmethods()) {
          if (names.count(m->get_name()->str()) != 0u) {
            methods.push_back(m);
          }
        }
      }
    }
  }
  std::sort(methods.begin(), methods.end(), compare_dexmethods);
  return methods;
}

const std::set<std::string_view> kCallSiteMethods{
    "basic1", "basic2", "basic3",     "basic4",    "in_try",
    "twice1", "twice2", "secondary1", "secondary2"};

// Gives every line of `method` a candidate set naming a line elsewhere.
void give_every_line_a_candidate(DexMethod* method) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  cfg::ScopedCFG scoped_cfg(method->get_code());
  uint32_t elsewhere_line = 1000;
  for (auto* block : scoped_cfg->blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION && mie.pos->file != nullptr) {
        DexPosition elsewhere(mie.pos->method,
                              DexString::make_string("Elsewhere.java"),
                              elsewhere_line++);
        manager->record_candidates(mie.pos.get(), {&elsewhere});
      }
    }
  }
}

// Calls `fn` on every entry of `code`, read in whatever form it is in: building
// or clearing a CFG here could free positions that were already registered.
template <typename Fn>
void for_each_entry(IRCode* code, Fn fn) {
  if (code->cfg_built()) {
    for (auto* block : code->cfg().blocks()) {
      for (auto& mie : *block) {
        fn(mie);
      }
    }
  } else {
    for (auto& mie : *code) {
      fn(mie);
    }
  }
}

// Calls `fn` on every entry in the code of every method except `skip`.
template <typename Fn>
void for_each_entry_without(std::vector<DexStore>& stores,
                            const DexMethod* skip,
                            Fn fn) {
  for (auto& store : stores) {
    for (const auto& classes : store.get_dexen()) {
      for (const auto& cls : classes) {
        for (auto* m : cls->get_all_methods()) {
          if (m != skip && m->get_code() != nullptr) {
            for_each_entry(m->get_code(), fn);
          }
        }
      }
    }
  }
}

// Registers every position in the code of every method except `skip`, the way
// the dex writer registers what code refers to, and writes the map. Skipping a
// method is what a later pass deleting it looks like to the writer.
void write_map_without(std::vector<DexStore>& stores,
                       const std::string& path,
                       const DexMethod* skip) {
  RealPositionMapper mapper(path);
  for_each_entry_without(stores, skip, [&](MethodItemEntry& mie) {
    if (mie.type != MFLOW_POSITION) {
      return;
    }
    for (auto* p = mie.pos.get(); p != nullptr; p = p->parent) {
      if (p->file == nullptr || p->method == nullptr) {
        return;
      }
    }
    for (auto* p = mie.pos.get(); p != nullptr; p = p->parent) {
      mapper.position_to_line(p);
    }
  });
  mapper.write_map();
}

// The ids of the outlined call sites among the entries `for_each` visits.
template <typename ForEach>
std::set<uint32_t> called_pattern_ids(ForEach for_each) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  std::set<uint32_t> ids;
  for_each([&](MethodItemEntry& mie) {
    if (mie.type == MFLOW_POSITION &&
        manager->is_pattern_position(mie.pos.get())) {
      ids.insert(mie.pos->line);
    }
  });
  return ids;
}

// The pattern ids the switch cases of the line map at `path` select: a case is
// a `redex.$Position.case` record whose line is the selected pattern's id.
// Nothing when the map cannot be read.
std::optional<std::multiset<uint32_t>> case_pattern_ids(
    const std::string& path) {
  std::ifstream ifs(path, std::ios::binary);
  const std::vector<char> bytes((std::istreambuf_iterator<char>(ifs)),
                                std::istreambuf_iterator<char>());
  size_t at = 0;
  auto read_u32 = [&](uint32_t* value) {
    if (bytes.size() - at < sizeof(*value)) {
      return false;
    }
    memcpy(value, bytes.data() + at, sizeof(*value));
    at += sizeof(*value);
    return true;
  };
  uint32_t magic = 0;
  uint32_t version = 0;
  uint32_t string_count = 0;
  if (!read_u32(&magic) || magic != 0xfaceb000u || !read_u32(&version) ||
      version != 2u || !read_u32(&string_count)) {
    return std::nullopt;
  }
  std::vector<std::string> string_pool;
  for (uint32_t i = 0; i < string_count; ++i) {
    uint32_t size = 0;
    if (!read_u32(&size) || bytes.size() - at < size) {
      return std::nullopt;
    }
    string_pool.emplace_back(bytes.data() + at, size);
    at += size;
  }
  uint32_t position_count = 0;
  if (!read_u32(&position_count)) {
    return std::nullopt;
  }
  std::multiset<uint32_t> ids;
  for (uint32_t i = 0; i < position_count; ++i) {
    uint32_t cls = 0;
    uint32_t method = 0;
    uint32_t file = 0;
    uint32_t line = 0;
    uint32_t parent = 0;
    if (!read_u32(&cls) || !read_u32(&method) || !read_u32(&file) ||
        !read_u32(&line) || !read_u32(&parent) || cls >= string_pool.size() ||
        method >= string_pool.size()) {
      return std::nullopt;
    }
    if (string_pool[cls] == "redex.$Position" &&
        string_pool[method] == "case") {
      ids.insert(line);
    }
  }
  return ids;
}

// Puts every top-level position of each method under an inlined caller on
// Caller.java:100, as if each method had been inlined there. The callers of
// the methods selected by `merged` are themselves merged with
// Caller.java:107. A caller has to be a position of the method itself, so it
// is parked before the return, outside any outlined sequence.
void run_under_one_caller(const std::vector<DexMethod*>& methods,
                          const std::vector<bool>& merged) {
  ASSERT_EQ(methods.size(), merged.size());
  auto* manager = g_redex->get_position_pattern_switch_manager();
  DexPosition elsewhere(DexString::make_string("LCaller;.run:()V"),
                        DexString::make_string("Caller.java"), 107);
  for (size_t i = 0; i < methods.size(); ++i) {
    auto caller = std::make_unique<DexPosition>(
        DexString::make_string("LCaller;.run:()V"),
        DexString::make_string("Caller.java"), 100);
    if (merged[i]) {
      manager->record_candidates(caller.get(), {&elsewhere});
      ASSERT_NE(caller->alt_id(), 0u);
    }
    cfg::ScopedCFG scoped_cfg(methods[i]->get_code());
    for (auto* block : scoped_cfg->blocks()) {
      for (auto& mie : *block) {
        if (mie.type == MFLOW_POSITION && mie.pos->file != nullptr &&
            mie.pos->parent == nullptr) {
          mie.pos->parent = caller.get();
        }
      }
    }
    bool parked = false;
    for (auto* block : scoped_cfg->blocks()) {
      auto ii = InstructionIterable(block);
      for (auto it = ii.begin(); it != ii.end() && !parked; ++it) {
        if (opcode::is_a_return(it->insn->opcode())) {
          scoped_cfg->insert_before(block, it.unwrap(), std::move(caller));
          parked = true;
        }
      }
    }
    ASSERT_TRUE(parked);
  }
}

// The collapsed (uncaptured) leaves of the outlined method `caller` calls, and
// how many of them run under a caller presented as exact.
std::pair<size_t, size_t> count_collapsed_leaves(DexMethod* caller) {
  DexMethod* outlined = nullptr;
  {
    cfg::ScopedCFG scoped_cfg(caller->get_code());
    auto* ref = find_invoked_method(*scoped_cfg, "$outline");
    EXPECT_NE(ref, nullptr);
    if (ref == nullptr) {
      return {0, 0};
    }
    outlined = ref->as_def();
  }
  size_t collapsed = 0;
  size_t under_exact_caller = 0;
  cfg::ScopedCFG scoped_cfg(outlined->get_code());
  for (auto* block : scoped_cfg->blocks()) {
    for (const auto& mie : *block) {
      if (mie.type != MFLOW_POSITION || mie.pos->parent == nullptr ||
          !mie.pos->is_unreliable()) {
        continue;
      }
      ++collapsed;
      if (!mie.pos->parent->is_unreliable()) {
        ++under_exact_caller;
      }
    }
  }
  return {collapsed, under_exact_caller};
}

} // namespace

// A call site of an outlined method goes away after outlining while the
// outlined method, and its switch, stay. The writer must not emit the dead
// call site's case, whose provenance it never reached.
TEST_F(InstructionSequenceOutlinerTest,
       the_map_is_written_after_a_call_site_with_candidates_dies) {
  auto methods = find_vmethods(stores, kCallSiteMethods);
  ASSERT_FALSE(methods.empty());
  auto* dead = methods.front();
  give_every_line_a_candidate(dead);
  run_passes({new InstructionSequenceOutliner()});

  DexMethodRef* outlined = nullptr;
  {
    cfg::ScopedCFG scoped_cfg(dead->get_code());
    outlined = find_invoked_method(*scoped_cfg, "$outline");
  }
  ASSERT_NE(outlined, nullptr);
  ASSERT_TRUE(outlined->is_def());
  auto* manager = g_redex->get_position_pattern_switch_manager();
  const auto& alternatives = manager->get_alternatives();
  std::set<uint32_t> case_ids;
  for_each_entry(outlined->as_def()->get_code(), [&](MethodItemEntry& mie) {
    if (mie.type == MFLOW_POSITION &&
        manager->is_switch_position(mie.pos.get())) {
      for (const auto& entry : alternatives.at(mie.pos->line).entries) {
        case_ids.insert(*entry.pattern_id);
      }
    }
  });
  auto dead_ids = called_pattern_ids(
      [&](auto fn) { for_each_entry(dead->get_code(), fn); });
  auto live_ids = called_pattern_ids(
      [&](auto fn) { for_each_entry_without(stores, dead, fn); });
  std::set<uint32_t> dead_case_ids;
  std::set<uint32_t> live_case_ids;
  for (auto id : case_ids) {
    if (live_ids.count(id) != 0u) {
      live_case_ids.insert(id);
    } else if (dead_ids.count(id) != 0u) {
      dead_case_ids.insert(id);
    }
  }
  ASSERT_FALSE(dead_case_ids.empty());
  ASSERT_FALSE(live_case_ids.empty());

  auto path = testing::TempDir() + "outliner-dead-call-site-" +
              std::to_string(getpid()) + ".bin";
  EXPECT_NO_THROW(write_map_without(stores, path, dead));
  auto written = case_pattern_ids(path);
  std::remove(path.c_str());
  ASSERT_TRUE(written.has_value());
  for (auto id : dead_case_ids) {
    EXPECT_EQ(written->count(id), 0u) << "dead pattern " << id;
  }
  for (auto id : live_case_ids) {
    EXPECT_NE(written->count(id), 0u) << "live pattern " << id;
  }
}

// With `full_dbg_positions` off, four call sites share one outlined method and
// name different lines in every slot, so every slot is collapsed. All of them
// run under the same caller line, but only one of those callers is exact: the
// collapsed slots' caller has to keep what the other three knew.
TEST_F(InstructionSequenceOutlinerTest,
       a_collapsed_slot_joins_every_occurrences_caller) {
  set_full_dbg_positions(false);
  auto methods =
      find_vmethods(stores, {"basic1", "basic2", "basic3", "basic4"});
  ASSERT_EQ(methods.size(), 4u);
  run_under_one_caller(methods, {false, true, true, true});
  run_passes({new InstructionSequenceOutliner()});

  auto [collapsed, under_exact_caller] = count_collapsed_leaves(methods[0]);
  EXPECT_GT(collapsed, 0u);
  EXPECT_EQ(under_exact_caller, 0u);
}

// Control: when every occurrence's caller is merged, the kept pattern's own
// caller already carries the set.
TEST_F(InstructionSequenceOutlinerTest,
       a_collapsed_slot_keeps_a_caller_set_every_occurrence_shares) {
  set_full_dbg_positions(false);
  auto methods =
      find_vmethods(stores, {"basic1", "basic2", "basic3", "basic4"});
  ASSERT_EQ(methods.size(), 4u);
  run_under_one_caller(methods, {true, true, true, true});
  run_passes({new InstructionSequenceOutliner()});

  auto [collapsed, under_exact_caller] = count_collapsed_leaves(methods[0]);
  EXPECT_GT(collapsed, 0u);
  EXPECT_EQ(under_exact_caller, 0u);
}
