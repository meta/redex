/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InstructionSequenceOutliner.h"

#include <gtest/gtest.h>
#include <sstream>
#include <string>
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
#include "ScopedCFG.h"
#include "Show.h"
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

  // `n` static methods that will share one outlinable instruction sequence.
  // Each takes an `LPFSub;` parameter. Two occurrences do not clear the
  // outliner's benefit threshold, so callers need several.
  std::vector<DexMethod*> create_param_flow(size_t n) {
    std::vector<DexType*> no_interfaces;

    DexType* holder = DexType::make_type("LPF;");
    DexClass* holder_cls = create_class(holder, type::java_lang_Object(),
                                        no_interfaces, ACC_PUBLIC);
    m_classes.push_back(holder_cls);

    DexType* sub = DexType::make_type("LPFSub;");
    m_classes.push_back(
        create_class(sub, type::java_lang_Object(), no_interfaces, ACC_PUBLIC));

    // The broad demand comes from an `Object`-typed static field. `sput-object`
    // demands exactly the field's type, so the parameter's uses demand only
    // `java.lang.Object`. Only the result type, which `demand_in_candidate`
    // adds as a demand, can narrow it. The halves on either side of the move
    // store to two distinct fields, so neither half is a repeating sequence
    // that the outliner would rather outline on its own.
    holder_cls->add_field(DexField::make_field("LPF;.sf1:Ljava/lang/Object;")
                              ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    holder_cls->add_field(DexField::make_field("LPF;.sf2:Ljava/lang/Object;")
                              ->make_concrete(ACC_PUBLIC | ACC_STATIC));

    auto make = [&](const char* name) {
      auto* proto = DexProto::make_proto(type::_void(),
                                         DexTypeList::make_type_list({sub}));
      auto* m =
          DexMethod::make_method(holder, DexString::make_string(name), proto)
              ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
      holder_cls->add_method(m);
      return m;
    };
    std::vector<DexMethod*> methods;
    methods.reserve(n);
    for (size_t i = 0; i < n; i++) {
      methods.push_back(make(("m" + std::to_string(i)).c_str()));
    }
    return methods;
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

// Tests that a candidate which starts with instructions that do not touch the
// new instance does not extend into iputs on it before the base constructor
// call. The (const, const, iput...) sequence recurs in the `other` methods,
// where it can be outlined.
TEST_F(InstructionSequenceOutlinerTest,
       candidateDoesNotExtendIntoIputsBeforeBaseInitInvocation) {
  create();

  const auto* body = R"(
      (load-param-object v0)
      (const v1 0)
      (const v2 0)
      (iput-object v1 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v2 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v1 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v2 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v1 v0 "LC;.f:Ljava/lang/Object;")
      (iput-object v2 v0 "LC;.f:Ljava/lang/Object;")
  )";
  const std::string init_str =
      std::string("(") + body +
      R"((invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    ))";
  const std::string other_str = std::string("(") + body + "(return-void))";

  m_init->set_code(assembler::ircode_from_string(init_str));
  m_other->set_code(assembler::ircode_from_string(other_str));
  for (const char* name : {"other2", "other3", "other4", "other5"}) {
    auto* method = DexMethod::make_method(std::string("LC;.") + name + ":()V")
                       ->make_concrete(ACC_PUBLIC, false);
    method->set_code(assembler::ircode_from_string(other_str));
    m_classes.front()->add_method(method);
  }

  run();

  auto has_invoke_static = [](IRCode* code) {
    for (const auto& mie : InstructionIterable(*code)) {
      if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
        return true;
      }
    }
    return false;
  };
  EXPECT_TRUE(has_invoke_static(m_other->get_code()));

  auto expected_init_code = assembler::ircode_from_string(init_str);
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

  auto* method = DexMethod::make_method("LC;.bar:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  UnorderedSet<DexMethod*> throughput_methods;
  UnorderedSet<DexMethod*> warm_methods{method};
  UnorderedSet<DexMethod*> hot_methods;

  const OutlineabilityContext outlineability(config, throughput_indices,
                                             throughput_methods, warm_methods,
                                             hot_methods);
  big_blocks::BigBlock big_block({entry});
  EXPECT_EQ(outlineability.can_outline_from_big_block(method, big_block),
            OutlineabilityContext::Result::WarmLoopExceedsThresholds);
}

// An outlined method's parameter keeps the narrower type of the result it is
// copied into. A wrong parameter type in an outlined method's proto is a
// verifier error, not just a lost narrowing.
//
// The outlined sequence's only out-reg, `v1`, is a `move-object` of the object
// parameter `v0`, so its result type is the parameter's declared type,
// `LPFSub;`. The only other use of `v0` in the sequence accepts any
// `java.lang.Object`, so its uses alone would type the outlined method's
// parameter `Object`. `demand_in_candidate` takes the result register and its
// type, and adds that type as a demand on the register that still holds the
// out-value at the end of the sequence. So `Demand::widest` keeps `LPFSub;`.
//
// The `Object` demand is needed. Without it, no use records a demand, because
// the walk follows a move instead of recording it. `declare_parameter` would
// then fall back to the supplied value and return `LPFSub;` with or without
// the result demand.
//
// Without the result demand, the outliner emits
// `LPF;.$outlined$0$...:(Ljava/lang/Object;)LPFSub;`, whose `RETURN_OBJECT v0`
// returns an `Object` where `LPFSub;` is declared. `IRTypeChecker` rejects that
// method during the pass, so `run()` throws a `RedexError` before the
// assertions below run; the assertions document the expected proto. A wrong
// proto that only an `OPCODE_RETURN` would expose is not caught, because that
// opcode never reads the proto. That case cannot be built with object types,
// so it is not covered here.
TEST_F(InstructionSequenceOutlinerTest, OutlinedParamNarrowedByResultType) {
  auto methods = create_param_flow(4);

  // The two bodies differ only in the trailing call, so the common sequence
  // ends before it and `v1` is live-out of the sequence rather than inside it.
  auto make_body = [](const char* tail) {
    std::ostringstream oss;
    oss << "(\n(load-param-object v0)\n";
    // Shared code on BOTH sides of the move. Without the trailing half, the
    // prefix that stops before the move would be a valid candidate too. That
    // prefix returns nothing, so it would win on `cost_invoke_with_result`.
    for (int i = 0; i < 7; i++) {
      oss << R"((sput-object v0 "LPF;.sf1:Ljava/lang/Object;"))" << "\n";
    }
    oss << "(move-object v1 v0)\n";
    for (int i = 0; i < 7; i++) {
      oss << R"((sput-object v1 "LPF;.sf2:Ljava/lang/Object;"))" << "\n";
    }
    oss << "(invoke-static (v1) \"" << tail << "\")\n"
        << "(return-void)\n)";
    return oss.str();
  };

  // Distinct tails so the shared prefix ends at the last `sput`, leaving `v1`
  // defined inside the sequence and live-out of it.
  for (size_t i = 0; i < methods.size(); i++) {
    auto tail = "LPF;.consume" + std::to_string(i) + ":(LPFSub;)V";
    methods[i]->set_code(
        assembler::ircode_from_string(make_body(tail.c_str())));
  }

  run();

  DexMethod* outlined = nullptr;
  {
    cfg::ScopedCFG cfg(methods[0]->get_code());
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      if (insn->has_method() && insn->get_method()->get_name()->str().find(
                                    "$outlined") != std::string::npos) {
        outlined = insn->get_method()->as_def();
      }
    }
  }
  ASSERT_NE(outlined, nullptr)
      << "nothing was outlined; the fixture no longer presents an outlinable "
         "sequence, so this test is not exercising what it claims";

  // These check preconditions, not the property under test. The outliner
  // chooses among competing candidates by a cost model. If it ever prefers the
  // void prefix that stops before the `move-object`, there is no out-reg and
  // the result demand never applies. A failure here then means the fixture no
  // longer builds the intended case, not that the result demand is broken.
  const auto* proto = outlined->get_proto();
  ASSERT_STRNE(proto->get_rtype()->get_name()->c_str(), "V")
      << "ISO outlined a void candidate, so no out-reg was formed and this "
         "test is no longer exercising the result demand";
  ASSERT_EQ(proto->get_args()->size(), 1u)
      << "expected exactly the one parameter this fixture supplies";

  EXPECT_STREQ(proto->get_args()->at(0)->get_name()->c_str(), "LPFSub;")
      << "the outlined parameter widened to the bare use-demand meet; "
         "the result demand is what narrows it";
  EXPECT_STREQ(proto->get_rtype()->get_name()->c_str(), "LPFSub;");
}

// ART types an `and-int` of two `char`s as `int`. When that value enters the
// outlined code as an argument and leaves it as the result, both are `int`: a
// `(C)C` method would receive an `int` argument, which ART rejects
// (`VerifyRegisterType` in `method_verifier.cc`).
TEST_F(InstructionSequenceOutlinerTest, BitwiseOfCharsPassesThroughAsInt) {
  std::vector<DexType*> no_interfaces;
  DexType* holder = DexType::make_type("LIF;");
  DexClass* holder_cls =
      create_class(holder, type::java_lang_Object(), no_interfaces, ACC_PUBLIC);
  m_classes.push_back(holder_cls);
  // Two fields, so the halves either side of the move are not themselves a
  // repeating sequence.
  holder_cls->add_field(DexField::make_field("LIF;.si1:I")
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  holder_cls->add_field(DexField::make_field("LIF;.si2:I")
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC));

  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < 4; i++) {
    auto* proto = DexProto::make_proto(
        type::_void(),
        DexTypeList::make_type_list({type::_char(), type::_char()}));
    auto* m =
        DexMethod::make_method(
            holder, DexString::make_string("m" + std::to_string(i)), proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    holder_cls->add_method(m);
    // A distinct call after the `and-int` keeps it out of the shared
    // sequence, and a distinct call at the end keeps `v3` live-out of it.
    std::ostringstream oss;
    oss << "(\n(load-param v0)\n(load-param v1)\n(and-int v2 v0 v1)\n"
        << "(invoke-static () \"LIF;.mark" << i << ":()V\")\n";
    for (int j = 0; j < 7; j++) {
      oss << R"((sput v2 "LIF;.si1:I"))" << "\n";
    }
    oss << "(move v3 v2)\n";
    for (int j = 0; j < 7; j++) {
      oss << R"((sput v3 "LIF;.si2:I"))" << "\n";
    }
    oss << "(invoke-static (v3) \"LIF;.consume" << i << ":(I)V\")\n"
        << "(return-void)\n)";
    m->set_code(assembler::ircode_from_string(oss.str()));
    methods.push_back(m);
  }

  run();

  DexMethod* outlined = nullptr;
  {
    cfg::ScopedCFG cfg(methods[0]->get_code());
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      if (insn->has_method() && insn->get_method()->get_name()->str().find(
                                    "$outlined") != std::string::npos) {
        outlined = insn->get_method()->as_def();
      }
    }
  }
  ASSERT_NE(outlined, nullptr) << "nothing was outlined";
  const auto* proto = outlined->get_proto();
  ASSERT_EQ(proto->get_args()->size(), 1u) << SHOW(proto);
  EXPECT_EQ(proto->get_args()->at(0), type::_int()) << SHOW(proto);
  EXPECT_EQ(proto->get_rtype(), type::_int()) << SHOW(proto);
}
