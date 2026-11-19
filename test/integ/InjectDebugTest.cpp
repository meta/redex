/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <json/value.h>
#include <json/writer.h>

#include <fstream>
#include <functional>
#include <string>

#include "DexInstruction.h"
#include "DexLoader.h"
#include "DexPosition.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexContext.h"
#include "RedexTestUtils.h"
// NOLINTNEXTLINE(facebook-unused-include-check)
#include "SanitizersConfig.h"

#include "tools/bytecode_debugger/InjectDebug.h"

/* Tests that the inject-debug program is able to run to completion and
 * output a new dex file. Tests are run on the output dex file to
 * ensure it is in the state that we want.
 */

class InjectDebugTest : public ::testing::Test {
 protected:
  InjectDebugTest() {
    reset_redex();
    m_test_dex_path = std::getenv("dex");
    m_tmp_dir = prepare_tmp_dir();

    // Always create primary dex file
    m_input_dex_paths.push_back(m_test_dex_path);
    m_output_dex_paths.push_back(m_tmp_dir.path + "/classes.dex");
  }

  void inject() {
    InjectDebug inject_debug(m_tmp_dir.path, m_input_dex_paths);
    inject_debug.run();
  }

  // Secondary dex files are in the form classesN.dex, N >= 2
  void create_secondary_dex(int index) {
    std::string name = "classes" + std::to_string(index);
    std::string input_dex_path = create_dir_with_dex(name);
    m_input_dex_paths.push_back(input_dex_path);
    m_output_dex_paths.push_back(m_tmp_dir.path + "/" + name + ".dex");
  }

  // Application Modules use DexMetadata files (e.g. ApplicationModule.json)
  // that contain a path to an input dex file.
  void create_metadata_dex(const std::string& module_name) {
    std::string module_dir = m_tmp_dir.path + "/" + module_name;
    std::string input_dex_path = create_dir_with_dex(module_name);

    std::string metadata_path = module_dir + "/" + module_name + ".json";
    Json::Value metadata;
    metadata["id"] = module_name;
    metadata["requires"][0] = "dex";
    metadata["files"][0] = input_dex_path;
    std::ofstream metadata_file(metadata_path);
    metadata_file << metadata;
    metadata_file.close();

    m_input_dex_paths.push_back(metadata_path);
    m_output_dex_paths.push_back(m_tmp_dir.path + "/" + module_name + "2.dex");
  }

  DexClasses load_classes(const std::string& path) {
    reset_redex();
    DexStore store("classes");
    store.add_classes(load_classes_from_dex(
        DexLocation::make_location("dex", path),
        /*stats=*/nullptr, /*input_dex_version*/ nullptr, /* balloon */ false));
    return store.get_dexen()[0];
  }

  // Helper to reduce duplicate code - runs a given function to fetch
  // information from classes and then checks equality
  // Compares the primary dex file output with the original input dex file
  void test_dex_equality_helper(
      const std::function<std::vector<std::string>(DexClasses)>& get_info) {
    std::vector<std::string> original_names, modified_names;
    original_names = get_info(load_classes(m_output_dex_paths[0]));
    modified_names = get_info(load_classes(m_test_dex_path));
    EXPECT_EQ(original_names.size(), modified_names.size());

    for (int i = 0; i < original_names.size(); ++i) {
      EXPECT_EQ(original_names[i], modified_names[i]);
    }
  }

  bool file_exists(const std::string& path) {
    std::ifstream file(path.c_str());
    return file.good();
  }

  std::string m_test_dex_path;
  redex::TempDir m_tmp_dir;
  std::vector<std::string> m_input_dex_paths, m_output_dex_paths;

 private:
  void reset_redex() {
    delete g_redex;
    g_redex = new RedexContext(true);
  }

  static redex::TempDir prepare_tmp_dir() {
    auto tmp_dir = redex::make_tmp_dir("redex_inject_debug_test%%%%%%%%");
    boost::filesystem::path meta_dir(tmp_dir.path + "/meta");
    boost::filesystem::create_directories(meta_dir);
    return tmp_dir;
  }

  std::string create_dir_with_dex(const std::string& name) {
    std::string dex_path = m_tmp_dir.path + "/" + name + "/" + name + ".dex";
    boost::filesystem::create_directory(m_tmp_dir.path + "/" + name);
    copy_file(std::getenv("dex"), dex_path);
    return dex_path;
  }

  void copy_file(const std::string& src, const std::string& dest) {
    std::ifstream src_stream(src, std::ios::binary);
    std::ofstream dest_stream(dest, std::ios::binary);
    dest_stream << src_stream.rdbuf();
  }
};

// Check that general class data is unmodified by comparing class names
TEST_F(InjectDebugTest, TestClasses) {
  inject();
  test_dex_equality_helper(
      [](const DexClasses& classes) -> std::vector<std::string> {
        std::vector<std::string> class_names;
        for (DexClass* dex_class : classes) {
          class_names.push_back(dex_class->str_copy());
        }
        return class_names;
      });
}

// Check that general method data is unmodified by comparing method names
TEST_F(InjectDebugTest, TestMethods) {
  inject();
  test_dex_equality_helper(
      [](const DexClasses& classes) -> std::vector<std::string> {
        std::vector<std::string> method_names;
        for (DexClass* dex_class : classes) {
          for (DexMethod* dex_method : dex_class->get_dmethods()) {
            method_names.push_back(dex_method->str_copy());
          }
          for (DexMethod* dex_method : dex_class->get_vmethods()) {
            method_names.push_back(dex_method->str_copy());
          }
        }
        return method_names;
      });
}

// Check that general code data is unmodified by comparing instructions, with
// their branch targets and try regions. Both sides are laid out again through
// the CFG first, without debug information: inject-debug lays out each method
// that way, which may order its blocks differently than the input dex.
TEST_F(InjectDebugTest, TestCodeItems) {
  inject();
  test_dex_equality_helper(
      [](const DexClasses& classes) -> std::vector<std::string> {
        std::vector<std::string> methods;
        for (int i = 0; i < classes.size(); ++i) {
          for (DexMethod* dex_method : classes[i]->get_dmethods()) {
            dex_method->balloon();
            auto* code = dex_method->get_code();
            code->build_cfg();
            code->clear_cfg();
            for (auto it = code->begin(); it != code->end();) {
              if (it->type == MFLOW_POSITION || it->type == MFLOW_DEBUG) {
                it = code->erase_and_dispose(it);
              } else {
                ++it;
              }
            }
            methods.push_back(assembler::to_string(code));
          }
        }
        return methods;
      });
}

// Check that multiple files can be processed at once, including metadata
TEST_F(InjectDebugTest, TestMultipleFiles) {
  create_secondary_dex(2);
  create_secondary_dex(3);
  create_metadata_dex("testmodule");
  inject();

  EXPECT_EQ(m_output_dex_paths.size(), 4);
  for (const std::string& out_path : m_output_dex_paths) {
    EXPECT_TRUE(file_exists(out_path));
  }
}

// Check that there is one debug position emitted for each instruction
TEST_F(InjectDebugTest, TestLineDebugInfoCreated) {
  inject();
  DexClasses classes = load_classes(m_output_dex_paths[0]);

  for (DexClass* dex_class : classes) {
    for (DexMethod* dex_method : dex_class->get_dmethods()) {
      std::vector<DexDebugEntry>& debug_entries =
          dex_method->get_dex_code()->get_debug_item()->get_entries();

      int debug_entry_idx = 0;
      uint32_t line =
          dex_method->get_dex_code()->get_debug_item()->get_line_start();
      uint32_t pc = 0;
      for (DexInstruction* instr :
           dex_method->get_dex_code()->get_instructions()) {
        // Find next position entry
        while (debug_entries[debug_entry_idx].type !=
               DexDebugEntryType::Position) {
          ++debug_entry_idx;
        }

        // Debug information is not emitted for some goto instructions
        if (pc != debug_entries[debug_entry_idx].addr &&
            dex_opcode::is_goto(instr->opcode())) {
          pc += static_cast<uint32_t>(instr->size());
          ++line;
          continue;
        }

        // Check that a debug position entry was emitted at exactly
        // the PC of the current dex instruction
        EXPECT_EQ(pc, debug_entries[debug_entry_idx].addr);

        // Check that debug line numbers increment by exactly 1
        EXPECT_EQ(line, debug_entries[debug_entry_idx].pos->line);
        pc += static_cast<uint32_t>(instr->size());
        ++debug_entry_idx;
        ++line;
      }
    }
  }
}

// Check that local variable debug information is emitted for registers used by
// each instruction
TEST_F(InjectDebugTest, TestLocalVarDebugInfoCreated) {
  inject();
  DexClasses classes = load_classes(m_output_dex_paths[0]);

  for (DexClass* dex_class : classes) {
    for (DexMethod* dex_method : dex_class->get_dmethods()) {
      std::vector<DexDebugEntry>& debug_entries =
          dex_method->get_dex_code()->get_debug_item()->get_entries();

      uint16_t register_size = dex_method->get_dex_code()->get_registers_size();
      uint16_t local_var_count = 0;
      // Check that there is at least one local variable entry for each register
      for (int i = 0; i < debug_entries.size(); ++i) {
        if (debug_entries[i].type == DexDebugEntryType::Instruction &&
            debug_entries[i].insn->opcode() ==
                DexDebugItemOpcodeValues::DBG_START_LOCAL) {
          ++local_var_count;
          // Check that the format of local variable names is like "v1", "v2"...
          auto* start_local = dynamic_cast<DexDebugOpcodeStartLocal*>(
              debug_entries[i].insn.get());
          EXPECT_EQ("v" + std::to_string(debug_entries[i].insn->uvalue()),
                    start_local->name()->str());
        }
      }
      EXPECT_GE(local_var_count, register_size);
    }
  }
}

// Check that the debug information is exactly correct for a specific class
TEST_F(InjectDebugTest, TestSpecificMethod) {
  const std::string CLASS_NAME =
      "Lcom/facebook/pages/browser/fragment/PagesBrowserFragment;";

  inject();
  DexClasses classes = load_classes(m_output_dex_paths[0]);

  DexClass* dex_class = nullptr;
  for (DexClass* class_it : classes) {
    if (class_it->str() == CLASS_NAME) {
      dex_class = class_it;
    }
  }
  EXPECT_NE(dex_class, nullptr);

  for (DexMethod* dex_method : dex_class->get_dmethods()) {
    DexCode* dex_code = dex_method->get_dex_code();
    DexDebugItem* debug_item = dex_code->get_debug_item();

    std::vector<DexDebugEntry>& debug_entries = debug_item->get_entries();
    std::vector<DexInstruction*>& instructions = dex_code->get_instructions();

    auto it = debug_entries.begin();

    // Skip the first position entry (0) - it doesn't map to a dex instruction
    while (it->type != DexDebugEntryType::Position) {
      ++it;
    }

    for (int i = 0; i < instructions.size(); ++i) {
      // Look at the following debug entries up until the next position entry
      // and track which registers were stored as local variables
      std::vector<reg_t> locals;
      for (++it; it != debug_entries.end(); ++it) {
        if (it->type == DexDebugEntryType::Position) {
          break;
        }
        if (it->insn->opcode() == DexDebugItemOpcodeValues::DBG_START_LOCAL) {
          locals.push_back(it->insn->uvalue());
        }
      }
      // Confirm that all registers used by the following instruction were
      // stored as local variables
      if (instructions[i]->has_dest()) {
        EXPECT_TRUE(std::find(locals.begin(),
                              locals.end(),
                              instructions[i]->dest()) != locals.end());
      }
      for (int j = 0; j < instructions[i]->srcs_size(); ++j) {
        EXPECT_TRUE(std::find(locals.begin(),
                              locals.end(),
                              instructions[i]->src(j)) != locals.end());
      }
    }

    // Make sure there are no extra trailing debug entries
    EXPECT_EQ(it, debug_entries.end());
  }
}
