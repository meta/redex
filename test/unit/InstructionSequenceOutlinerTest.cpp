/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InstructionSequenceOutliner.h"

#include <gtest/gtest.h>
#include <utility>

#include "BigBlocks.h"
#include "DeterministicContainers.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "OutliningProfileGuidanceImpl.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "ScopeHelper.h"
#include "SourceBlocks.h"
#include "TypeUtil.h"

namespace {

void run_passes(const std::vector<Pass*>& passes,
                std::vector<DexClass*> classes) {
  std::vector<DexStore> stores;
  DexMetadata dm;
  dm.set_id("classes");
  DexStore store(dm);
  // primary dex
  store.add_classes({});
  // secondary dex
  store.add_classes(std::move(classes));
  stores.emplace_back(std::move(store));
  PassManager manager(passes);

  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);
}

struct InstructionSequenceOutlinerTest : public RedexTest {
  std::vector<DexClass*> m_classes;
  DexMethod* m_init;
  DexMethod* m_other;

  void create() {
    std::vector<DexType*> no_interfaces;

    DexType* c_type = DexType::make_type("LC;");
    DexClass* c_cls = create_class(c_type, type::java_lang_Object(),
                                   no_interfaces, ACC_PUBLIC);
    m_classes.push_back(c_cls);

    auto* args = DexTypeList::make_type_list({});
    auto* proto = DexProto::make_proto(type::_void(), args);

    m_init =
        DexMethod::make_method(c_type, DexString::make_string("<init>"), proto)
            ->make_concrete(ACC_PUBLIC, false);
    m_init->set_code(std::make_unique<IRCode>(m_init, 1));
    c_cls->add_method(m_init);

    m_other =
        DexMethod::make_method(c_type, DexString::make_string("other"), proto)
            ->make_concrete(ACC_PUBLIC, false);
    m_other->set_code(std::make_unique<IRCode>(m_other, 1));
    c_cls->add_method(m_other);

    auto* field = DexField::make_field("LC;.f:Ljava/lang/Object;")
                      ->make_concrete(ACC_PUBLIC);
    c_cls->add_field(field);
  }

  void run() {
    std::vector<Pass*> passes = {new InstructionSequenceOutliner()};
    run_passes(passes, m_classes);
  }

  ~InstructionSequenceOutlinerTest() {}
};

} // namespace

// Tests that we can outline iputs that operate on the new instance in a
// constructor after the base constructor call, but not before. We use IR as we
// cannot write this test in Java or Kotlin directly, due to language
// limitations, even though such iputs are perfectly fine according to the JVM
// and Dalvik spec, and can arise in similar multiples due to other Redex
// optimizations such as ClassMerging.
TEST_F(InstructionSequenceOutlinerTest, iputsBeforeBaseInitInvocation) {
  using namespace dex_asm;
  create();

  const auto* init_str = R"(
    (
      (load-param-object v0)
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (return-void)
    )
  )";

  const auto* other_str = R"(
    (
      (load-param-object v0)
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (return-void)
    )
  )";

  auto init_code = assembler::ircode_from_string(init_str);
  m_init->set_code(std::move(init_code));

  auto other_code = assembler::ircode_from_string(other_str);
  m_other->set_code(std::move(other_code));

  run();

  const auto* expected_init_str = R"(
    (
      (load-param-object v0)
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v0 v0 "LC;.f:Ljava/lang/Object;")
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (invoke-static (v0) "LC;.$outlined$0$45c530c69cb11355:(LC;)V")
      (invoke-static (v0) "LC;.$outlined$0$45c530c69cb11355:(LC;)V")
      (return-void)
    )
  )";

  auto expected_init_code = assembler::ircode_from_string(expected_init_str);
  auto* outlined_init_code = m_init->get_code();
  // remove positions, we are not testing that here
  for (auto it = outlined_init_code->begin();
       it != outlined_init_code->end();) {
    if (it->type == MFLOW_POSITION) {
      it = outlined_init_code->erase(it);
    } else {
      it++;
    }
  }
  EXPECT_CODE_EQ(expected_init_code.get(), outlined_init_code);
}

// Regression for the inverted null-check in throughput detection
// (OutliningProfileGuidanceImpl `if (!val_pair && val_pair->val > ...)`): a
// warm, non-loop big block that carries a throughput-interaction source block
// whose val exceeds `block_profiles_hits` must NOT be freely outlinable. With
// the inverted check the block was never recognized as throughput, so the
// decider wrongly returned CanOutline.
TEST_F(InstructionSequenceOutlinerTest,
       ThroughputSourceBlockSuppressesOutline) {
  using namespace outliner_impl;

  auto code = assembler::ircode_from_string(R"(
    (
      (.src_block "LC;.bar:()V" 0 (1.0 1.0))
      (return-void)
    ))");
  code->build_cfg();
  auto& cfg = code->cfg();
  auto* entry = cfg.entry_block();
  ASSERT_NE(nullptr, source_blocks::get_first_source_block(entry));

  outliner::ProfileGuidanceConfig config;
  // >= 0 so we reach the magnitude comparison rather than the block_profiles<0
  // shortcut; the SB val (1.0) sits above it.
  config.block_profiles_hits = 0.0f;
  UnorderedSet<size_t> throughput_indices;
  throughput_indices.insert(0);

  CanOutlineBlockDecider decider(config, throughput_indices,
                                 /*throughput=*/false,
                                 /*sufficiently_warm=*/true,
                                 /*sufficiently_hot=*/false);
  big_blocks::BigBlock big_block({entry});
  EXPECT_EQ(decider.can_outline_from_big_block(big_block),
            CanOutlineBlockDecider::Result::WarmLoopExceedsThresholds);
}
