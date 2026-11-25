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

#include "ArtTypeCheck.h"
#include "BigBlocks.h"
#include "DeterministicContainers.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "OutliningProfileGuidanceImpl.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "ScopeHelper.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "TypeUtil.h"

namespace {

void run_passes(const std::vector<Pass*>& passes,
                std::vector<DexClass*> classes,
                bool type_check) {
  std::vector<DexStore> stores;
  DexMetadata dm;
  dm.set_id("classes");
  DexStore store(dm);
  // primary dex
  store.add_classes({});
  // secondary dex
  store.add_classes(std::move(classes));
  stores.emplace_back(std::move(store));
  auto methods = [&stores] {
    std::vector<DexMethod*> all;
    for (auto* cls : build_class_scope(stores)) {
      auto ms = cls->get_all_methods();
      all.insert(all.end(), ms.begin(), ms.end());
    }
    return all;
  };
  const method_splitting_test::ArtTypeCheckOfOutput art_check(methods());
  PassManager manager(passes);
  if (!type_check) {
    manager.disable_checker();
  }

  Json::Value conf_obj = Json::nullValue;
  ConfigFiles dummy_config(conf_obj);
  dummy_config.parse_global_config();
  manager.run_passes(stores, dummy_config);
  EXPECT_EQ(art_check.violations(methods()), "");
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

  // `type_check` runs Redex's type checker on the input and the output.
  void run(bool type_check = true) {
    std::vector<Pass*> passes = {new InstructionSequenceOutliner()};
    run_passes(passes, m_classes, type_check);
  }

  // Gives several methods one body, an outlinable sequence with `middle` in
  // between, runs the outliner and expects every method to still hold its
  // `opcode` instruction. An `invoke-static` in `middle` becomes an
  // `invoke-custom` when `make_invoke_custom` is set.
  void expect_kept_in_place(const std::string& middle,
                            IROpcode opcode,
                            bool make_invoke_custom = false) {
    auto methods = create_param_flow(6);
    // No SDK is loaded, so the reference checks accept `MethodHandle` only as
    // a class in scope.
    m_classes.push_back(create_internal_class(
        DexType::make_type("Ljava/lang/invoke/MethodHandle;"),
        type::java_lang_Object(), {}, ACC_PUBLIC | ACC_ABSTRACT));
    type_class(DexType::make_type("LPF;"))
        ->add_field(
            DexField::make_field("LPF;.h:Ljava/lang/invoke/MethodHandle;")
                ->make_concrete(ACC_PUBLIC | ACC_STATIC));
    std::ostringstream oss;
    oss << "(\n(load-param-object v0)\n";
    for (int i = 0; i < 7; i++) {
      oss << R"((sput-object v0 "LPF;.sf1:Ljava/lang/Object;"))" << "\n";
    }
    oss << middle << "\n";
    for (int i = 0; i < 7; i++) {
      oss << R"((sput-object v0 "LPF;.sf2:Ljava/lang/Object;"))" << "\n";
    }
    oss << "(return-void)\n)";
    for (auto* method : methods) {
      method->set_code(assembler::ircode_from_string(oss.str()));
      if (make_invoke_custom) {
        redex::make_invoke_custom(method->get_code(), "run", "(LPFSub;)V");
      }
    }

    run();

    for (auto* method : methods) {
      cfg::ScopedCFG cfg(method->get_code());
      auto ii = cfg::InstructionIterable(*cfg);
      EXPECT_TRUE(std::any_of(
          ii.begin(), ii.end(),
          [&](const auto& mie) { return mie.insn->opcode() == opcode; }))
          << show(method) << " lost its " << show(opcode) << ":\n"
          << show(*cfg);
    }
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

namespace {

std::string repeat(const std::string& line, size_t n) {
  std::string res;
  for (size_t i = 0; i < n; i++) {
    res += line;
  }
  return res;
}

bool contains_invoke_static(IRCode* code) {
  for (const auto& mie : InstructionIterable(*code)) {
    if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
      return true;
    }
  }
  return false;
}

} // namespace

// A constructor that calls its base constructor through a copy of `this`, as
// a register allocator may do to line up the arguments of an
// `invoke-direct/range`, has initialized `this` in the original register too.
// The iputs on it after that call can be outlined.
TEST_F(InstructionSequenceOutlinerTest,
       iputsAfterBaseInitInvocationThroughACopy) {
  create();

  const auto iputs =
      repeat(R"((iput-object v0 v0 "LC;.f:Ljava/lang/Object;"))", 14);
  m_init->set_code(assembler::ircode_from_string(
      R"((
      (load-param-object v0)
      (move-object v1 v0)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      )" +
      iputs + R"(
      (return-void)
    ))"));
  m_other->set_code(assembler::ircode_from_string("((load-param-object v0)" +
                                                  iputs + "(return-void))"));

  run();

  EXPECT_TRUE(contains_invoke_static(m_init->get_code()));
}

// When the base constructor call throws, `this` is still uninitialized in the
// handler, so the handler's iputs on it must not be outlined: the outlined
// method would receive an uninitialized object, which ART's verifier rejects.
// Hand-written dex can catch the exception of a base constructor call; Java
// and Kotlin cannot.
TEST_F(InstructionSequenceOutlinerTest,
       iputsInTheHandlerOfAThrowingBaseInitInvocation) {
  create();

  const auto iputs =
      repeat(R"((iput-object v2 v0 "LC;.f:Ljava/lang/Object;"))", 14);
  const std::string init_str = R"((
      (load-param-object v0)
      (const v2 0)
      (.try_start t)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (.try_end t)
      (return-void)
      (.catch (t))
      (move-exception v1)
      )" + iputs + R"(
      (throw v1)
    ))";
  m_init->set_code(assembler::ircode_from_string(init_str));
  const std::string other_str =
      "((load-param-object v0)(const v2 0)" + iputs + "(return-void))";
  m_other->set_code(assembler::ircode_from_string(other_str));
  for (const char* name : {"other2", "other3", "other4"}) {
    auto* method = DexMethod::make_method(std::string("LC;.") + name + ":()V")
                       ->make_concrete(ACC_PUBLIC, false);
    method->set_code(assembler::ircode_from_string(other_str));
    m_classes.front()->add_method(method);
  }

  run();

  EXPECT_TRUE(contains_invoke_static(m_other->get_code()));
  EXPECT_FALSE(contains_invoke_static(m_init->get_code()));
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

// `new C()` leaves the object uninitialized until its constructor runs. ART
// lets a comparison read it then, but rejects passing it to a method. The
// sequence that starts at the comparison must not take the object as an
// argument. Redex's own type checker rejects the comparison, so it does not run
// here; the check of the output against ART's rules still does.
TEST_F(InstructionSequenceOutlinerTest, ComparisonOfUninitializedObject) {
  create();
  std::vector<DexType*> no_interfaces;
  DexType* holder = DexType::make_type("LUH;");
  DexClass* holder_cls =
      create_class(holder, type::java_lang_Object(), no_interfaces, ACC_PUBLIC);
  m_classes.push_back(holder_cls);
  for (const auto* field : {"LUH;.f1:I", "LUH;.f2:I"}) {
    holder_cls->add_field(
        DexField::make_field(field)->make_concrete(ACC_PUBLIC | ACC_STATIC));
  }
  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < 4; i++) {
    auto name = "m" + std::to_string(i);
    auto* proto = DexProto::make_proto(
        type::_void(), DexTypeList::make_type_list({type::_int()}));
    auto* m =
        DexMethod::make_method(holder, DexString::make_string(name), proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    holder_cls->add_method(m);
    std::ostringstream oss;
    oss << "(\n(load-param v0)\n(new-instance \"LC;\")\n"
        << "(move-result-pseudo-object v1)\n"
        << "(invoke-static () \"LUH;.mark_" << name << ":()V\")\n"
        << "(if-eqz v1 :skip)\n";
    for (int j = 0; j < 7; j++) {
      oss << "(sput v0 \"LUH;.f1:I\")\n";
    }
    oss << "(:skip)\n";
    for (int j = 0; j < 7; j++) {
      oss << "(sput v0 \"LUH;.f2:I\")\n";
    }
    oss << "(invoke-direct (v1) \"LC;.<init>:()V\")\n"
        << "(invoke-static (v1) \"LUH;.end_" << name << ":(LC;)V\")\n"
        << "(return-void)\n)";
    m->set_code(assembler::ircode_from_string(oss.str()));
    methods.push_back(m);
  }

  run(/* type_check */ false);

  size_t outlined_calls = 0;
  for (auto* m : methods) {
    cfg::ScopedCFG cfg(m->get_code());
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      if (insn->has_method() && insn->get_method()->get_name()->str().find(
                                    "$outlined") != std::string::npos) {
        outlined_calls++;
        // The object is the only reference these methods hold.
        for (const auto* t : *insn->get_method()->get_proto()->get_args()) {
          EXPECT_TRUE(type::is_primitive(t)) << show(insn) << " in " << show(m);
        }
      }
    }
  }
  // The stores are outlined without the object, so the fixture still presents
  // outlinable code.
  EXPECT_GT(outlined_calls, 0u);
}

// The outliner does not represent method handles, method types, the call-site
// prototype of invoke-polymorphic or call sites, so it leaves instructions
// that hold them in place.
TEST_F(InstructionSequenceOutlinerTest, MethodHandleConstantNotOutlined) {
  expect_kept_in_place(R"(
    (const-method-handle invoke-static "LPF;.target:()V")
    (move-result-pseudo-object v1)
    (sput-object v1 "LPF;.sf1:Ljava/lang/Object;")
  )",
                       OPCODE_CONST_METHOD_HANDLE);
}

TEST_F(InstructionSequenceOutlinerTest, MethodTypeConstantNotOutlined) {
  expect_kept_in_place(R"(
    (const-method-type "(LPFSub;)V")
    (move-result-pseudo-object v1)
    (sput-object v1 "LPF;.sf1:Ljava/lang/Object;")
  )",
                       OPCODE_CONST_METHOD_TYPE);
}

TEST_F(InstructionSequenceOutlinerTest, MethodHandleCallNotOutlined) {
  expect_kept_in_place(R"(
    (sget-object "LPF;.h:Ljava/lang/invoke/MethodHandle;")
    (move-result-pseudo-object v1)
    (sget-object "LPF;.sf1:Ljava/lang/Object;")
    (move-result-pseudo-object v2)
    (invoke-polymorphic (v1 v2) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/Object;)V")
  )",
                       OPCODE_INVOKE_POLYMORPHIC);
}

TEST_F(InstructionSequenceOutlinerTest, CallSiteCallNotOutlined) {
  expect_kept_in_place(R"(
    (invoke-static (v0) "LPF;.placeholder:(LPFSub;)V")
  )",
                       OPCODE_INVOKE_CUSTOM,
                       /* make_invoke_custom */ true);
}

namespace {

// Four methods whose handler catches `catch_a` in one try region and `catch_b`
// in the other. The handler's shared code copies the caught exception from
// `v0` to `v1`, which the call after it reads, so an outlined copy of that
// code returns the exception.
std::vector<DexMethod*> make_caught_flow(std::vector<DexClass*>* classes,
                                         const char* catch_a,
                                         const char* catch_b) {
  std::vector<DexType*> no_interfaces;
  DexType* holder = DexType::make_type("LCE;");
  DexClass* holder_cls =
      create_class(holder, type::java_lang_Object(), no_interfaces, ACC_PUBLIC);
  classes->push_back(holder_cls);
  classes->push_back(create_class(DexType::make_type("LCE_E;"),
                                  type::java_lang_Throwable(), no_interfaces,
                                  ACC_PUBLIC));
  for (const auto* field : {"LCE;.f1:I", "LCE;.f2:I"}) {
    holder_cls->add_field(
        DexField::make_field(field)->make_concrete(ACC_PUBLIC | ACC_STATIC));
  }
  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < 4; i++) {
    auto name = "m" + std::to_string(i);
    auto* proto = DexProto::make_proto(
        type::_void(), DexTypeList::make_type_list({type::_int()}));
    auto* m =
        DexMethod::make_method(holder, DexString::make_string(name), proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    holder_cls->add_method(m);
    std::ostringstream oss;
    oss << "(\n(load-param v2)\n"
        << "(if-eqz v2 :second)\n"
        << "(.try_start a)\n"
        << "(invoke-static () \"LCE;.work_" << name << ":()V\")\n"
        << "(.try_end a)\n"
        << "(return-void)\n"
        << "(:second)\n"
        << "(.try_start b)\n"
        << "(invoke-static () \"LCE;.work2_" << name << ":()V\")\n"
        << "(.try_end b)\n"
        << "(return-void)\n"
        << "(.catch (a) \"" << catch_a << "\")\n"
        << "(.catch (b) \"" << catch_b << "\")\n"
        << "(move-exception v0)\n"
        << "(invoke-static () \"LCE;.mark_" << name << ":()V\")\n";
    for (int j = 0; j < 7; j++) {
      oss << "(sput v2 \"LCE;.f1:I\")\n";
    }
    oss << "(move-object v1 v0)\n";
    for (int j = 0; j < 7; j++) {
      oss << "(sput v2 \"LCE;.f2:I\")\n";
    }
    oss << "(invoke-static (v1) \"LCE;.report_" << name << ":(LCE_E;)V\")\n"
        << "(return-void)\n)";
    m->set_code(assembler::ircode_from_string(oss.str()));
    methods.push_back(m);
  }
  return methods;
}

// The outlined calls that return a value. Each value reaches `report_*`, which
// takes a `reported`, so ART rejects the call unless the outlined method
// returns `reported` or a subclass.
size_t check_caught_results(const std::vector<DexMethod*>& methods,
                            const DexType* reported) {
  size_t outlined_with_result = 0;
  for (auto* m : methods) {
    cfg::ScopedCFG cfg(m->get_code());
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      auto* insn = mie.insn;
      if (!insn->has_method() || insn->get_method()->get_name()->str().find(
                                     "$outlined") == std::string::npos) {
        continue;
      }
      auto* rtype = insn->get_method()->get_proto()->get_rtype();
      if (rtype == type::_void()) {
        continue;
      }
      outlined_with_result++;
      EXPECT_TRUE(type::check_cast(rtype, reported))
          << "outlined method returns " << show(rtype)
          << ", which ART does not accept at report_*(" << show(reported)
          << "): " << show(insn) << " in " << show(m);
    }
  }
  return outlined_with_result;
}
} // namespace

// ART types a caught exception by its handler's catch types: here `LCE_E;`,
// which both regions catch. The outlined method returns it as an `LCE_E;`.
TEST_F(InstructionSequenceOutlinerTest, CaughtExceptionResultHasItsCatchType) {
  auto methods = make_caught_flow(&m_classes, "LCE_E;", "LCE_E;");
  run(/* type_check */ false);
  EXPECT_GT(check_caught_results(methods, DexType::make_type("LCE_E;")), 0u);
}

// The two regions catch `LCE_MissingA;` and `LCE_MissingB;`, which Redex does
// not define; on the device both extend `LCE_E;`, so ART types the exception
// as an `LCE_E;`. Redex cannot compute that type, so no outlined method may
// return the exception with a wider one.
TEST_F(InstructionSequenceOutlinerTest,
       CaughtExceptionOfUnjoinableCatchTypesIsNotReturnedWider) {
  auto methods = make_caught_flow(&m_classes, "LCE_MissingA;", "LCE_MissingB;");
  run(/* type_check */ false);
  check_caught_results(methods, DexType::make_type("LCE_E;"));
}

// Four methods like this Java-like source, with one handler per catch type
// and `failure` in the register of `e`:
//
//   try {
//     work();
//   } catch (RuntimeException | TimeoutException | InterruptedException e) {
//     Exception failure = e;
//     if (e instanceof ExecutionException &&
//         e.getCause() instanceof Exception) {
//       failure = (Exception) e.getCause();
//     }
//     report(failure);  // void report(Exception failure)
//   }
//
// The code that computes `failure` is outlined into one method that takes the
// caught exception and returns `failure`. ART types the exception by its
// handler's catch type, so `failure` is an `Exception` in every handler. The
// outlined method must return an `Exception`: with a `Throwable` result, ART
// rejects the call to `report`.
TEST_F(InstructionSequenceOutlinerTest,
       CaughtExceptionsOfDistinctClassesAreReturnedAsTheirJoin) {
  std::vector<DexType*> no_interfaces;
  // No SDK is loaded, so the outliner moves a call to `getCause` only when its
  // class is in scope.
  DexClass* throwable_cls =
      create_class(type::java_lang_Throwable(), type::java_lang_Object(),
                   no_interfaces, ACC_PUBLIC);
  throwable_cls->add_method(
      DexMethod::make_method(
          "Ljava/lang/Throwable;.getCause:()Ljava/lang/Throwable;")
          ->make_concrete(ACC_PUBLIC, /* is_virtual */ true));
  m_classes.push_back(throwable_cls);
  auto* exception = DexType::make_type("Ljava/lang/Exception;");
  m_classes.push_back(create_class(exception, type::java_lang_Throwable(),
                                   no_interfaces, ACC_PUBLIC));
  const std::vector<const char*> catch_types = {
      "Ljava/lang/RuntimeException;", "Ljava/util/concurrent/TimeoutException;",
      "Ljava/lang/InterruptedException;"};
  for (const auto* name : catch_types) {
    m_classes.push_back(create_class(DexType::make_type(name), exception,
                                     no_interfaces, ACC_PUBLIC));
  }
  m_classes.push_back(create_class(
      DexType::make_type("Ljava/util/concurrent/ExecutionException;"),
      exception, no_interfaces, ACC_PUBLIC));
  DexType* holder = DexType::make_type("LCJ;");
  DexClass* holder_cls =
      create_class(holder, type::java_lang_Object(), no_interfaces, ACC_PUBLIC);
  m_classes.push_back(holder_cls);

  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < 4; i++) {
    auto name = "m" + std::to_string(i);
    auto* m = DexMethod::make_method(
                  holder, DexString::make_string(name),
                  DexProto::make_proto(type::_void(),
                                       DexTypeList::make_type_list({})))
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    holder_cls->add_method(m);
    std::ostringstream oss;
    oss << "(\n(.try_start t)\n"
        << "(invoke-static () \"LCJ;.work_" << name << ":()V\")\n"
        << "(.try_end t)\n"
        << "(return-void)\n";
    for (size_t h = 0; h < catch_types.size(); h++) {
      auto next = h + 1 < catch_types.size() ? " h" + std::to_string(h + 1)
                                             : std::string();
      auto here = h == 0 ? std::string("t") : "h" + std::to_string(h);
      oss << "(.catch (" << here << next << ") \"" << catch_types[h] << "\")\n"
          << "(move-exception v0)\n"
          << "(instance-of v0 \"Ljava/util/concurrent/ExecutionException;\")\n"
          << "(move-result-pseudo v2)\n"
          << "(if-eqz v2 :done" << h << ")\n"
          << "(check-cast v0 \"Ljava/util/concurrent/ExecutionException;\")\n"
          << "(move-result-pseudo-object v3)\n"
          << "(invoke-virtual (v3) "
             "\"Ljava/lang/Throwable;.getCause:()Ljava/lang/Throwable;\")\n"
          << "(move-result-object v4)\n"
          << "(instance-of v4 \"Ljava/lang/Exception;\")\n"
          << "(move-result-pseudo v2)\n"
          << "(if-eqz v2 :done" << h << ")\n"
          << "(invoke-virtual (v3) "
             "\"Ljava/lang/Throwable;.getCause:()Ljava/lang/Throwable;\")\n"
          << "(move-result-object v4)\n"
          << "(check-cast v4 \"Ljava/lang/Exception;\")\n"
          << "(move-result-pseudo-object v0)\n"
          << "(:done" << h << ")\n"
          << "(invoke-static (v0) \"LCJ;.report_" << name << "_" << h
          << ":(Ljava/lang/Exception;)V\")\n"
          << "(return-void)\n";
    }
    oss << ")";
    m->set_code(assembler::ircode_from_string(oss.str()));
    methods.push_back(m);
  }

  run(/* type_check */ false);
  EXPECT_GT(check_caught_results(methods, exception), 0u);
}
