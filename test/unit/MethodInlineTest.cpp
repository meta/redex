/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ApiLevelChecker.h"
#include "Creators.h"
#include "Debug.h"
#include "DexAsm.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "Inliner.h"
#include "InlinerConfig.h"
#include "LegacyInliner.h"
#include "MethodInlinePass.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "Walkers.h"

struct MethodInlineTest : public RedexTest {
  MethodInlineTest() {
    DexMethod::make_method("Ljava/lang/Object;.<init>:()V")
        ->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, false);
    DexMethod::make_method("Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z")
        ->make_concrete(ACC_PUBLIC, true);

    DexField::make_field("Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;")
        ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    DexField::make_field("Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
        ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);

    DexMethod::make_method("Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;")
        ->make_concrete(ACC_PUBLIC, true);
    DexMethod::make_method("Ljava/lang/Boolean;.booleanValue:()Z")
        ->make_concrete(ACC_PUBLIC, true);
  }

  ConfigFiles conf = ConfigFiles(Json::nullValue);
};

void test_inliner(const std::string& caller_str,
                  const std::string& callee_str,
                  const std::string& expected_str) {
  auto caller = assembler::ircode_from_string(caller_str);
  auto callee = assembler::ircode_from_string(callee_str);

  const auto& callsite = std::find_if(
      caller->begin(), caller->end(), [](const MethodItemEntry& mie) {
        return mie.type == MFLOW_OPCODE &&
               opcode::is_an_invoke(mie.insn->opcode());
      });
  legacy_inliner::inline_method_unsafe(
      /*caller_method=*/nullptr, caller.get(), callee.get(), callsite);

  auto expected = assembler::ircode_from_string(expected_str);

  EXPECT_CODE_EQ(expected.get(), caller.get());
}

DexClass* create_a_class(const char* description) {
  ClassCreator cc(DexType::make_type(description));
  cc.set_super(type::java_lang_Object());
  return cc.create();
}

void create_runtime_exception_init() {
  auto* init_method =
      static_cast<DexMethod*>(method::java_lang_RuntimeException_init_String());
  init_method->set_external();
}

static void remove_position(IRCode* code) {
  for (auto it = code->begin(); it != code->end();) {
    if (it->type == MFLOW_POSITION) {
      it = code->erase_and_dispose(it);
    } else {
      it++;
    }
  }
}

/**
 * Create a method like
 * void {{name}}() {
 *   const v0 {{val}};
 * }
 */
DexMethod* make_a_method(DexClass* cls, const char* name, int val) {
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string(name), proto);
  MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC, /*anno*/ nullptr,
                   /*with_debug_item*/ false);
  auto* main_block = mc.get_main_block();
  auto loc = mc.make_local(type::_int());
  main_block->load_const(loc, val);
  main_block->ret_void();
  auto* method = mc.create();
  cls->add_method(method);
  return method;
}

/**
 * Create a small method with just one argument like
 * public static void {{name}}(int x) {
 *  return;
 *   }
 * }
 */
DexMethod* make_small_method_with_one_arg(DexClass* cls, const char* name) {
  auto method_name = cls->get_name()->str() + "." + name;
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")" + method_name +
                                               R"(:(Z)V"
      (
        (load-param v0)
        (return-void)
     )
    )
  )");
  cls->add_method(method);
  return method;
}

/**
 * Create a method like
 * void {{name}}() {
 *   while (true) {}
 * }
 */
DexMethod* make_loopy_method(DexClass* cls, const char* name) {
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string(name), proto);
  MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC, /*anno*/ nullptr,
                   /*with_debug_item*/ false);
  auto* method = mc.create();
  method->set_code(assembler::ircode_from_string("((:begin) (goto :begin))"));
  cls->add_method(method);
  return method;
}

/**
 * Create a method like
 * public static void {{name}}(int x) {
 *   if (x != 0) {
 *     throw new RuntimeException("bla");
 *   }
 * }
 */
DexMethod* make_precondition_method(DexClass* cls, const char* name) {
  auto method_name = cls->get_name()->str() + "." + name;
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")" + method_name +
                                               R"(:(I)V"
      (
        (load-param v0)
        (if-eqz v0 :fail)
        (return-void)

        (:fail)
        (new-instance "Ljava/lang/RuntimeException;")
        (move-result-pseudo-object v1)
        (const-string "Bla")
        (move-result-pseudo-object v2)
        (invoke-direct (v1 v2) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
        (throw v1)
     )
    )
  )");
  cls->add_method(method);
  return method;
}

/**
 * Create a method like
 * public static void {{name}}(int x) {
 *   if (x+0+0+0+0 != 0) {
 *     throw new RuntimeException("bla");
 *   }
 * }
 */
DexMethod* make_silly_precondition_method(DexClass* cls, const char* name) {
  auto method_name = cls->get_name()->str() + "." + name;
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")" + method_name +
                                               R"(:(I)V"
      (
        (load-param v0)
        (add-int/lit v0 v0 0)
        (add-int/lit v0 v0 0)
        (add-int/lit v0 v0 0)
        (add-int/lit v0 v0 0)
        (if-eqz v0 :fail)
        (return-void)

        (:fail)
        (new-instance "Ljava/lang/RuntimeException;")
        (move-result-pseudo-object v1)
        (const-string "Bla")
        (move-result-pseudo-object v2)
        (invoke-direct (v1 v2) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
        (throw v1)
     )
    )
  )");
  cls->add_method(method);
  return method;
}

/**
 * Create a method like
 * public static void {{name}}(Boolean x) {
 *   if (Boolean.booleanValue() != 0) {
 *     throw new RuntimeException("bla");
 *   }
 * }
 */
DexMethod* make_unboxing_precondition_method(DexClass* cls, const char* name) {
  auto method_name = cls->get_name()->str() + "." + name;
  auto* method = assembler::method_from_string(std::string("") + R"(
    (method (public static) ")" + method_name +
                                               R"(:(Ljava/lang/Boolean;)V"
      (
        (load-param-object v0)
        (invoke-virtual (v0) "Ljava/lang/Boolean;.booleanValue:()Z")
        (move-result v0)
        (if-eqz v0 :fail)
        (return-void)

        (:fail)
        (new-instance "Ljava/lang/RuntimeException;")
        (move-result-pseudo-object v1)
        (const-string "Bla")
        (move-result-pseudo-object v2)
        (invoke-direct (v1 v2) "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")
        (throw v1)
     )
    )
  )");
  cls->add_method(method);
  return method;
}

/**
 * Create a method calls other methods.
 * void {{name}}() {
 *   other1();
 *   other2();
 *   ...
 * }
 */
DexMethod* make_a_method_calls_others(DexClass* cls,
                                      const char* name,
                                      const std::vector<DexMethod*>& methods) {
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string(name), proto);
  MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC, /*anno*/ nullptr,
                   /*with_debug_item*/ false);
  auto* main_block = mc.get_main_block();
  for (auto* callee : methods) {
    main_block->invoke(callee, {});
  }
  main_block->ret_void();
  auto* method = mc.create();
  cls->add_method(method);
  return method;
}

DexMethod* make_a_method_calls_others_with_arg(
    DexClass* cls,
    const char* name,
    const std::vector<std::pair<DexMethod*, int32_t>>& methods) {
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string(name), proto);
  MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC, /*anno*/ nullptr,
                   /*with_debug_item*/ false);
  auto* main_block = mc.get_main_block();
  auto loc = mc.make_local(type::_int());
  for (const auto& p : methods) {
    main_block->load_const(loc, p.second);
    main_block->invoke(p.first, {loc});
  }
  main_block->ret_void();
  auto* method = mc.create();
  cls->add_method(method);
  return method;
}

DexMethod* make_a_method_calls_others_with_arg(
    DexClass* cls,
    const char* name,
    const std::vector<std::pair<DexMethod*, DexField*>>& methods) {
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* ref = DexMethod::make_method(cls->get_type(),
                                     DexString::make_string(name), proto);
  MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC, /*anno*/ nullptr,
                   /*with_debug_item*/ false);
  auto* main_block = mc.get_main_block();
  auto loc = mc.make_local(type::_int());
  for (const auto& p : methods) {
    main_block->sget(p.second, loc);
    main_block->invoke(p.first, {loc});
  }
  main_block->ret_void();
  auto* method = mc.create();
  cls->add_method(method);
  return method;
}

/*
 * Test that we correctly insert move instructions that map caller args to
 * callee params.
 */
TEST_F(MethodInlineTest, insertMoves) {
  using namespace dex_asm;
  auto* callee = dynamic_cast<DexMethod*>(DexMethod::make_method(
      "Lfoo;", "testCallee", "V", {"I", "Ljava/lang/Object;"}));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  callee->set_code(std::make_unique<IRCode>(callee, 0));

  auto* caller = dynamic_cast<DexMethod*>(
      DexMethod::make_method("Lfoo;", "testCaller", "V", {}));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  caller->set_code(std::make_unique<IRCode>(caller, 0));

  auto* invoke = dasm(OPCODE_INVOKE_STATIC, callee, {});
  invoke->set_srcs_size(2);
  invoke->set_src(0, 1);
  invoke->set_src(1, 2);

  auto* caller_code = caller->get_code();
  caller_code->push_back(dasm(OPCODE_CONST, {1_v, 1_L}));
  caller_code->push_back(dasm(OPCODE_CONST, {2_v, 0_L})); // load null ref
  caller_code->push_back(invoke);
  auto invoke_it = std::prev(caller_code->end());
  caller_code->push_back(dasm(OPCODE_RETURN_VOID));
  caller_code->set_registers_size(3);

  auto* callee_code = callee->get_code();
  callee_code->push_back(dasm(OPCODE_CONST, {1_v, 1_L}));
  callee_code->push_back(dasm(OPCODE_RETURN_VOID));

  legacy_inliner::inline_method_unsafe(
      /*caller_method=*/nullptr,
      caller->get_code(),
      callee->get_code(),
      invoke_it);

  auto it = InstructionIterable(caller_code).begin();
  EXPECT_EQ(*it->insn, *dasm(OPCODE_CONST, {1_v, 1_L}));
  ++it;
  EXPECT_EQ(*it->insn, *dasm(OPCODE_CONST, {2_v, 0_L}));
  ++it;
  EXPECT_EQ(*it->insn, *dasm(OPCODE_MOVE, {3_v, 1_v}));
  ++it;
  EXPECT_EQ(*it->insn, *dasm(OPCODE_MOVE_OBJECT, {4_v, 2_v}));
  ++it;
  EXPECT_EQ(*it->insn, *dasm(OPCODE_CONST, {4_v, 1_L}));
  ++it;
  EXPECT_EQ(*it->insn, *dasm(OPCODE_RETURN_VOID));

  EXPECT_EQ(caller_code->get_registers_size(), 5);
}

TEST_F(MethodInlineTest, debugPositionsAfterReturn) {
  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  DexMethod* callee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.callee:()V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  const auto& caller_str = R"(
    (
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (invoke-static () "LFoo;.bar:()V")
      (return-void)
    )
  )";
  const auto& callee_str = R"(
    (
      (.pos:dbg_0 "LFoo;.callee:()V" "Foo.java" 123)
      (const v0 1)
      (if-eqz v0 :after)

      (:exit)
      (.pos:dbg_1 "LFoo;.callee:()V" "Foo.java" 124)
      (const v1 2)
      (return-void)

      (:after)
      (const v2 3)
      (goto :exit)
    )
  )";
  const auto& expected_str = R"(
    (
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)

      (.pos:dbg_1 "LFoo;.callee:()V" "Foo.java" 123 dbg_0)
      (const v1 1)
      (if-eqz v1 :after)

      (:exit)
      (.pos:dbg_2 "LFoo;.callee:()V" "Foo.java" 124 dbg_0)
      (const v2 2)
      (.pos:dbg_3 "LFoo;.caller:()V" "Foo.java" 10)
      (return-void)

      ; Check that this position was correctly added to the code after the
      ; callee's return
      (.pos:dbg_4 "LFoo;.callee:()V" "Foo.java" 124 dbg_0)
      (:after)
      (const v3 3)
      (goto :exit)
    )
  )";
  test_inliner(caller_str, callee_str, expected_str);
}

TEST_F(MethodInlineTest, test_intra_dex_inlining) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  // Only inline methods within dex.
  bool intra_dex = true;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> canidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");
  {
    // foo is in dex 2, bar is in dex 3.
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    store.add_classes({bar_cls});
    stores.push_back(std::move(store));
  }
  {
    auto* foo_m1 = make_a_method(foo_cls, "foo_m1", 1);
    auto* bar_m1 = make_a_method(bar_cls, "bar_m1", 2001);
    auto* bar_m2 = make_a_method(bar_cls, "bar_m2", 2002);
    canidates.insert(foo_m1);
    canidates.insert(bar_m1);
    canidates.insert(bar_m2);
    // foo_main calls foo_m1 and bar_m2.
    [[maybe_unused]] auto* foo_main =
        make_a_method_calls_others(foo_cls, "foo_main", {foo_m1, bar_m2});
    // bar_main calls bar_m1.
    [[maybe_unused]] auto* bar_main =
        make_a_method_calls_others(bar_cls, "bar_main", {bar_m1});
    // Expect foo_m1 and bar_m1 be inlined if `intra_dex` is true.
    expected_inlined.insert(foo_m1);
    expected_inlined.insert(bar_m1);
    // Expect bar_m2 to be inlined as well if `intra_dex` is true, as it does
    // not bring in any new references.
    expected_inlined.insert(bar_m2);
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);

  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, canidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }
}

TEST_F(MethodInlineTest, test_intra_dex_inlining_new_references) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  // Only inline methods within dex.
  bool intra_dex = true;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> canidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");
  auto* baz_cls = create_a_class("Lbaz;");
  {
    // foo is in dex 2, bar is in dex 3.
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    store.add_classes({bar_cls, baz_cls});
    stores.push_back(std::move(store));
  }
  {
    auto* foo_m1 = make_a_method(foo_cls, "foo_m1", 1);
    auto* baz_m1 = make_a_method(baz_cls, "baz_m1", 3001);

    // bar_m1 calls baz_m1.
    auto* bar_m1 = make_a_method_calls_others(bar_cls, "bar_m1", {baz_m1});

    // foo_main calls foo_m1 and bar_m1.
    [[maybe_unused]] auto* foo_main =
        make_a_method_calls_others(foo_cls, "foo_main", {foo_m1, bar_m1});

    canidates.insert(foo_m1);
    canidates.insert(bar_m1);

    // Expect foo_m1 to be inlined if `intra_dex` is true.
    expected_inlined.insert(foo_m1);

    // Expect bar_m1 not to be inlined, as it does
    // bring a new reference from baz_m1.
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);

  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, canidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }
}

TEST_F(MethodInlineTest, test_intra_dex_inlining_init_class) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  create_object_class();

  // Only inline methods within dex.
  bool intra_dex = true;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> canidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");

  {
    const auto* clinit_name = DexString::make_string("<clinit>");
    auto* void_args = DexTypeList::make_type_list({});
    auto* void_void = DexProto::make_proto(type::_void(), void_args);
    auto* clinit = dynamic_cast<DexMethod*>(
        DexMethod::make_method(bar_cls->get_type(), clinit_name, void_void));
    clinit->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_CONSTRUCTOR, false);
    clinit->set_code(std::make_unique<IRCode>());
    auto* code = clinit->get_code();
    auto* method = DexMethod::make_method("Lunknown;.unknown:()V");
    code->push_back(dex_asm::dasm(OPCODE_INVOKE_STATIC, method, {}));
    code->push_back(dex_asm::dasm(OPCODE_RETURN_VOID));
    bar_cls->add_method(clinit);

    const auto* sfield_name = DexString::make_string("existing_field");
    auto* field = dynamic_cast<DexField*>(
        DexField::make_field(bar_cls->get_type(), sfield_name, type::_int()));
    field->make_concrete(ACC_PUBLIC | ACC_STATIC);
    type_class(bar_cls->get_type())->add_field(field);
  }
  {
    // foo is in dex 2, bar is in dex 3.
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    store.add_classes({bar_cls});
    stores.push_back(std::move(store));
  }
  {
    auto* foo_m1 = make_a_method(foo_cls, "foo_m1", 1);
    auto* bar_m1 = make_a_method(bar_cls, "bar_m1", 10);
    auto init_code = assembler::ircode_from_string(R"(
    (
      (init-class "Lbar;")
      (return-void)
    )
  )");
    bar_m1->set_code(std::move(init_code));

    // foo_main calls foo_m1 and init.
    [[maybe_unused]] auto* foo_main =
        make_a_method_calls_others(foo_cls, "foo_main", {foo_m1, bar_m1});

    canidates.insert(foo_m1);
    canidates.insert(bar_m1);

    // Expect foo_m1 to be inlined if `intra_dex` is true.
    expected_inlined.insert(foo_m1);

    // Expect bar_m1 not to be inlined, as it has an init-class instruction.
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);

  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, canidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }
}

TEST_F(MethodInlineTest, redex_options_architecture_round_trip) {
  for (auto architecture :
       {Architecture::UNKNOWN, Architecture::ARM, Architecture::ARMV7,
        Architecture::ARM64, Architecture::X86, Architecture::X86_64}) {
    RedexOptions input;
    input.arch = architecture;
    Json::Value entry_data;
    input.serialize(entry_data);

    RedexOptions output;
    output.deserialize(entry_data);
    EXPECT_EQ(output.arch, architecture);

    entry_data["redex_options"].removeMember("arch");
    output.arch = Architecture::ARMV7;
    output.deserialize(entry_data);
    EXPECT_EQ(output.arch, Architecture::UNKNOWN);
  }
}

TEST_F(MethodInlineTest, armv7_hard_max_instruction_size_is_arch_specific) {
  constexpr uint64_t kLimit = 15000;

  inliner::InlinerConfig armv7_config;
  armv7_config.armv7_hard_max_instruction_size = kLimit;
  armv7_config.set_architecture(Architecture::ARMV7);
  EXPECT_EQ(armv7_config.get_armv7_hard_max_instruction_size(), kLimit);
  EXPECT_FALSE(armv7_config.is_over_armv7_hard_max_instruction_size(14999, 1));
  EXPECT_FALSE(armv7_config.is_over_armv7_hard_max_instruction_size(0, kLimit));
  EXPECT_TRUE(
      armv7_config.is_over_armv7_hard_max_instruction_size(0, kLimit + 1));
  EXPECT_TRUE(armv7_config.is_over_armv7_hard_max_instruction_size(15000, 1));
  EXPECT_TRUE(
      armv7_config.is_over_armv7_hard_max_instruction_size(10000, 5001));

  for (auto architecture : {Architecture::ARM64, Architecture::ARM,
                            Architecture::UNKNOWN, Architecture::X86}) {
    inliner::InlinerConfig config;
    config.armv7_hard_max_instruction_size = kLimit;
    config.set_architecture(architecture);
    EXPECT_EQ(config.get_armv7_hard_max_instruction_size(), 0);
    EXPECT_FALSE(config.is_over_armv7_hard_max_instruction_size(15000, 1));
  }
}

// Don't inline when it would exceed (configured) size
TEST_F(MethodInlineTest, size_limit) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> canidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");
  {
    // foo is in dex 2, bar is in dex 3.
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    store.add_classes({bar_cls});
    stores.push_back(std::move(store));
  }
  {
    auto* foo_m1 = make_a_method(foo_cls, "foo_m1", 1);
    auto* bar_m1 = make_a_method(bar_cls, "bar_m1", 2001);
    auto* bar_m2 = make_a_method(bar_cls, "bar_m2", 2002);
    canidates.insert(foo_m1);
    canidates.insert(bar_m1);
    canidates.insert(bar_m2);
    // foo_main calls foo_m1 and bar_m2.
    make_a_method_calls_others(foo_cls, "foo_main", {foo_m1, bar_m2});
    // bar_main calls bar_m1.
    make_a_method_calls_others(bar_cls, "bar_main", {bar_m1});
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);

  inliner::InlinerConfig inliner_config;
  inliner_config.soft_max_instruction_size = 0;
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, canidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk, IntraDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), 0);
}

TEST_F(MethodInlineTest, armv7_hard_size_limit_overrides_force_inline) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  auto* cls = create_a_class("LArmv7HardLimit;");
  DexStore store("root");
  store.add_classes({cls});
  stores.push_back(std::move(store));

  auto* callee = make_a_method(cls, "callee", 2001);
  callee->rstate.set_force_inline();
  candidates.insert(callee);
  make_a_method_calls_others(cls, "caller", {callee});

  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);

  inliner::InlinerConfig inliner_config;
  inliner_config.armv7_hard_max_instruction_size = 1;
  inliner_config.set_architecture(Architecture::ARMV7);
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  MultiMethodInliner inliner(scope, init_classes_with_side_effects, stores,
                             conf, candidates,
                             std::ref(concurrent_method_resolver),
                             inliner_config, /* min_sdk */ 0, IntraDex);
  inliner.inline_methods();
  EXPECT_TRUE(inliner.get_inlined().empty());
}

TEST_F(MethodInlineTest, minimal_self_loop_regression) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    auto* foo_m1 = make_loopy_method(foo_cls, "foo_m1");
    candidates.insert(foo_m1);
    // foo_main calls foo_m1.
    make_a_method_calls_others(foo_cls, "foo_main", {foo_m1});
    expected_inlined.insert(foo_m1);
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }
}

TEST_F(MethodInlineTest, non_unique_inlined_registers) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod* foo_main;
  {
    auto* foo_m1 = make_a_method(foo_cls, "foo_m1", 1);
    auto* foo_m2 = make_a_method(foo_cls, "foo_m2", 2);
    candidates.insert(foo_m1);
    candidates.insert(foo_m2);
    // foo_main calls foo_m1 and foo_m2.
    foo_main =
        make_a_method_calls_others(foo_cls, "foo_main", {foo_m1, foo_m2});
    expected_inlined.insert(foo_m1);
    expected_inlined.insert(foo_m2);
  }
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.unique_inlined_registers = false;
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.clear_cfg(); });
  // Note: the position is an artifact and may get cleaned up.
  const auto& expected_str = R"(
    (
      (.pos:dbg_0 "Lfoo;.foo_main:()V" UnknownSource 0)
      (const v0 1)
      (const v0 2)
      (return-void)
    )
  )";
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, inline_beneficial_on_average_after_constant_prop) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    foo_main = make_a_method_calls_others_with_arg(foo_cls,
                                                   "foo_main",
                                                   {
                                                       {check_method, 1},
                                                       {check_method, 1},
                                                       {check_method, 1},
                                                       {check_method, 1},
                                                       {check_method, 1},
                                                       {check_method, 1},
                                                   });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (return-void)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest,
       inline_beneficial_for_particular_instance_after_constant_prop) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    foo_main = make_a_method_calls_others_with_arg(foo_cls,
                                                   "foo_main",
                                                   {
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 1},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                   });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (return-void)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, intradex_legal_after_constant_prop) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = true;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    store.add_classes({bar_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_precondition_method(bar_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    foo_main = make_a_method_calls_others_with_arg(foo_cls,
                                                   "foo_main",
                                                   {
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 1},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                   });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Lbar;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lbar;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lbar;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lbar;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lbar;.check:(I)V")
      (return-void)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(
    MethodInlineTest,
    inline_beneficial_for_particular_instance_after_constant_prop_and_local_dce) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_silly_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    foo_main = make_a_method_calls_others_with_arg(foo_cls,
                                                   "foo_main",
                                                   {
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 1},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                   });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (return-void)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, throw_after_no_return) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_silly_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times. Already the first call is one
    // that will always throw.
    foo_main = make_a_method_calls_others_with_arg(foo_cls,
                                                   "foo_main",
                                                   {
                                                       {check_method, 0},
                                                       {check_method, 0},
                                                       {check_method, 1},
                                                   });
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.throw_after_no_return = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), 0);

  const auto& expected_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "Lfoo;.check:(I)V")
      (unreachable v1)
      (throw v1)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, boxed_boolean) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_unboxing_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    auto* FALSE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;"));
    always_assert(FALSE_field != nullptr);
    auto* TRUE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;"));
    always_assert(TRUE_field != nullptr);
    foo_main =
        make_a_method_calls_others_with_arg(foo_cls,
                                            "foo_main",
                                            {
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                                {check_method, TRUE_field},
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                            });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  UnorderedSet<DexMethodRef*> pure_methods{
      DexMethod::get_method("Ljava/lang/Boolean;.booleanValue:()Z")};
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex,
      /* true_virtual_callers */ {},
      /* inline_for_speed */ nullptr,
      /* analyze_and_prune_inits */ false, pure_methods);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (.pos:dbg_0 "Lfoo;.foo_main:()V" UnknownSource 0)
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (return-void)
    )
  )";
  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, boxed_boolean_without_shrinking) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_unboxing_precondition_method(foo_cls, "check");
    candidates.insert(check_method);
    // foo_main calls check_method a few times.
    auto* FALSE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;"));
    always_assert(FALSE_field != nullptr);
    auto* TRUE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;"));
    always_assert(TRUE_field != nullptr);
    foo_main =
        make_a_method_calls_others_with_arg(foo_cls,
                                            "foo_main",
                                            {
                                                {check_method, TRUE_field},
                                                {check_method, FALSE_field},
                                            });
    expected_inlined.insert(check_method);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  check_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  UnorderedSet<DexMethodRef*> pure_methods{
      DexMethod::get_method("Ljava/lang/Boolean;.booleanValue:()Z")};
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex,
      /* true_virtual_callers */ {},
      /* inline_for_speed */ nullptr,
      /* analyze_and_prune_inits */ false, pure_methods);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), expected_inlined.size());
  for (auto* method : expected_inlined) {
    EXPECT_EQ(inlined.count(method), 1);
  }

  const auto& expected_str = R"(
    (
      (.pos:dbg_0 "Lfoo;.foo_main:()V" UnknownSource 0)
      (sget-object "Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (move-object v1 v0)
      (sget-object "Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lfoo;.check:(Ljava/lang/Boolean;)V")
      (return-void)
    )
  )";

  foo_main->get_code()->clear_cfg();
  auto* actual = foo_main->get_code();
  auto expected = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected.get(), actual);
}

TEST_F(MethodInlineTest, visibility_change_static_invoke) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.callee:()V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  DexMethod* nested_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.nested_callee:()V"));
  nested_callee->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  DexMethod* caller_inside = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.caller_inside:()V"));
  caller_inside->make_concrete(ACC_PRIVATE,
                               /* is_virtual */ false);

  DexMethod* nested_callee_2 = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.nested_callee_2:()V"));
  nested_callee_2->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:()V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);
  foo_cls->add_method(callee);
  foo_cls->add_method(nested_callee);
  foo_cls->add_method(nested_callee_2);
  foo_cls->add_method(caller_inside);

  const auto& caller_str = R"(
    (
      (const v0 0)
      (invoke-static () "LFoo;.callee:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& callee_str = R"(
    (
      (const v0 1)

      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LFoo;.<init>:()V")
      (invoke-direct (v1) "LFoo;.nested_callee:()V")

      (if-eqz v0 :after)

      (:exit)
      (const v1 2)
      (return-void)

      (:after)
      (const v2 3)
      (goto :exit)
    )
  )";

  const auto& caller_inside_str = R"(
    (
      (load-param-object v1)
      (invoke-direct (v1) "LFoo;.nested_callee:()V")
      (const v0 0)
      (return-void)
    )
  )";

  const auto& nested_callee_str = R"(
    (
      (load-param-object v1)
      (invoke-direct (v1) "LFoo;.nested_callee_2:()V")
      (const v0 0)
      (return-void)
    )
  )";

  const auto& nested_callee_2_str = R"(
    (
      (load-param-object v1)
      (const v0 0)
      (return-void)
    )
  )";

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));
  nested_callee->set_code(assembler::ircode_from_string(nested_callee_str));
  caller_inside->set_code(assembler::ircode_from_string(caller_inside_str));
  nested_callee_2->set_code(assembler::ircode_from_string(nested_callee_2_str));
  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(callee);
    candidates.insert(nested_callee);
    expected_inlined.insert(callee);
    expected_inlined.insert(nested_callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.run_local_dce = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();
  nested_callee->get_code()->build_cfg();
  caller_inside->get_code()->build_cfg();
  nested_callee_2->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();
  nested_callee->get_code()->clear_cfg();
  caller_inside->get_code()->clear_cfg();
  nested_callee_2->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  EXPECT_TRUE(is_public(nested_callee_2));

  // visibility does not change, as the call to nested_callee is
  // futher inlined to nested_callee's code
  EXPECT_TRUE(is_private(nested_callee));

  const auto& caller_expected_str = R"(
    (
      (.pos:dbg_0 "LBar;.caller:()V" UnknownSource 0)
      (const v0 0)
      (.pos:dbg_1 "LFoo;.callee:()V" UnknownSource 0 dbg_0)
      (const v1 1)
      (new-instance "LFoo;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "LFoo;.<init>:()V")
      (move-object v5 v2)
      (invoke-static (v5) "LFoo;.nested_callee_2:(LFoo;)V")
      (const v4 0)
      (if-eqz v1 :L1)
      (:L0)
      (const v2 2)
      (.pos:dbg_2 "LBar;.caller:()V" UnknownSource 0)
      (return-void)
      (:L1)
      (const v3 3)
      (goto :L0)
    )
  )";

  auto* caller_actual = caller->get_code();
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());

  const auto& caller_inside_expected_str = R"(
    (
      (load-param-object v1)
      (.pos:dbg_0 "LFoo;.caller_inside:()V" UnknownSource 0)
      (move-object v3 v1)
      (invoke-static (v3) "LFoo;.nested_callee_2:(LFoo;)V")
      (const v2 0)
      (const v0 0)
      (return-void)
    )
  )";

  auto* caller_inside_actual = caller_inside->get_code();
  auto caller_inside_expected =
      assembler::ircode_from_string(caller_inside_expected_str);
  EXPECT_CODE_EQ(caller_inside_actual, caller_inside_expected.get());

  const auto& nested_callee_expected_str = R"(
    (
      (load-param-object v1)
      (invoke-static (v1) "LFoo;.nested_callee_2:(LFoo;)V")
      (const v0 0)
      (return-void)
    )
  )";

  auto* nested_callee_actual = nested_callee->get_code();
  auto nested_callee_expected =
      assembler::ircode_from_string(nested_callee_expected_str);
  EXPECT_CODE_EQ(nested_callee_actual, nested_callee_expected.get());
}

TEST_F(MethodInlineTest, unused_result) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.callee:(I)I"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (const v0 0)
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& callee_str = R"(
    (
      (load-param v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v0)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(callee);
    expected_inlined.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.multiple_callers = true;
  inliner_config.use_call_site_summaries = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (return-void)
    )
  )";

  auto* caller_actual = caller->get_code();
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

// top-down call-site analysis will determine that it's beneficial to inline
// across all nested call-sites
TEST_F(MethodInlineTest, caller_caller_callee_call_site) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* outer_caller = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.outer_caller:()V"));
  outer_caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* inner_caller = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.inner_caller:(I)V"));
  inner_caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.callee:(I)I"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  foo_cls->add_method(outer_caller);
  foo_cls->add_method(inner_caller);
  foo_cls->add_method(callee);

  const auto& outer_caller_str = R"(
    (
      (const v0 1)
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (invoke-static (v0) "LFoo;.inner_caller:(I)V")
      (return-void)
    )
  )";

  outer_caller->set_code(assembler::ircode_from_string(outer_caller_str));

  const auto& inner_caller_str = R"(
    (
      (load-param v0)
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (invoke-static (v0) "LFoo;.callee:(I)I")
      (return-void)
    )
  )";

  inner_caller->set_code(assembler::ircode_from_string(inner_caller_str));

  const auto& callee_str = R"(
    (
      (load-param v0)
      (if-nez v0 :exit)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (:exit)
      (return v0)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(inner_caller);
    candidates.insert(callee);
    expected_inlined.insert(inner_caller);
    expected_inlined.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.multiple_callers = true;
  inliner_config.use_call_site_summaries = true;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.compute_pure_methods = false;

  outer_caller->get_code()->build_cfg();
  inner_caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  outer_caller->get_code()->clear_cfg();
  inner_caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  const auto& outer_caller_expected_str = R"(
    (
      (return-void)
    )
  )";

  auto* outer_caller_actual = outer_caller->get_code();

  // Let's filter out all positions.
  // TODO: Enhance position filtering so that we don't get redundant positions.
  remove_position(outer_caller_actual);

  auto outer_caller_expected =
      assembler::ircode_from_string(outer_caller_expected_str);
  EXPECT_CODE_EQ(outer_caller_actual, outer_caller_expected.get());
}

TEST_F(MethodInlineTest,
       dont_inline_callee_with_tries_and_no_catch_all_at_sketchy_call_site) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.sketchyCaller:()V"));
  caller->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  DexMethod* callee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.callee:()V"));
  callee->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (load-param v0)
      (monitor-enter v0)

      (.try_start a)
      (invoke-static () "LBar;.canThrowInsideTry:()V")
      (.try_end a)
      (invoke-direct (v0) "LFoo;.callee:()V")

      (.catch (a))
      (monitor-exit v0)
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& callee_str = R"(
    (
      (load-param-object v0)

      (.try_start a)
      (invoke-static () "LBar;.canThrowNotImportant:()V")
      (.try_end a)

      (.catch (a) "LSomeSpecificType;")
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  DexStoresVector stores;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  UnorderedSet<DexMethod*> candidates{callee};
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk, IntraDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), 0);
  }
}

TEST_F(MethodInlineTest, dont_inline_sketchy_callee_into_into_try) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.sketchy_callee:()V"));
  callee->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (load-param-object v0)

      (.try_start a)
      (invoke-direct (v0) "LFoo;.sketchy_callee:()V")
      (.try_end a)

      (.catch (a) "LWhatEver;")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& callee_str = R"(
    (
      (load-param v0)
      (monitor-enter v0)

      (.try_start a)
      (invoke-static () "LBar;.canThrowNotImportant:()V")
      (.try_end a)
      (invoke-static () "LBar;.canThrowOutsideTry:()V")

      (.catch (a))
      (monitor-exit v0)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  DexStoresVector stores;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  UnorderedSet<DexMethod*> candidates{callee};
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk, IntraDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), 0);
  }
}

TEST_F(MethodInlineTest, inline_with_string_analyzer) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (const-string "Different String")
      (move-result-pseudo-object v1)
      (if-ne v0 v1 :exit)
      (const v2 0)
      (throw v2)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
    expected_inlined.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.multiple_callers = true;
  inliner_config.use_call_site_summaries = true;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ false, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (return-void)
    )
  )";

  auto* caller_actual = caller->get_code();

  // Let's filter out all positions.
  // TODO: Enhance position filtering so that we don't get redundant positions.
  remove_position(caller_actual);

  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

/// testing parameter max_cost_for_constant_propagation
TEST_F(MethodInlineTest, max_cost_for_constant_propagation) {
  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;
  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  auto* foo_cls = create_a_class("Lfoo;");
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  DexMethod *check_method, *small_method, *foo_main;
  {
    create_runtime_exception_init();
    check_method = make_unboxing_precondition_method(foo_cls, "check");
    small_method = make_small_method_with_one_arg(foo_cls, "small");
    candidates.insert(check_method);
    candidates.insert(small_method);
    // foo_main calls check_method a few times.
    auto* FALSE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;"));
    always_assert(FALSE_field != nullptr);
    auto* TRUE_field = dynamic_cast<DexField*>(
        DexField::get_field("Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;"));
    always_assert(TRUE_field != nullptr);
    foo_main =
        make_a_method_calls_others_with_arg(foo_cls,
                                            "foo_main",
                                            {
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                                {check_method, TRUE_field},
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                                {check_method, FALSE_field},
                                                {small_method, TRUE_field},
                                            });
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  // set the cost threshold so low, the effect is that
  // inliner would think it is too expensive to analyze for inlining
  // thus end up no inlining. this number 8 is carefully chosen as to
  // let check_method fail to inline and small_method go
  inliner_config.max_cost_for_constant_propagation = 8;
  check_method->get_code()->build_cfg();
  small_method->get_code()->build_cfg();
  foo_main->get_code()->build_cfg();
  UnorderedSet<DexMethodRef*> pure_methods{
      DexMethod::get_method("Ljava/lang/Boolean;.booleanValue:()Z")};
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf, candidates,
      std::ref(concurrent_method_resolver), inliner_config, min_sdk,
      intra_dex ? IntraDex : InterDex,
      /* true_virtual_callers */ {},
      /* inline_for_speed */ nullptr,
      /* analyze_and_prune_inits */ false, pure_methods);
  inliner.inline_methods();
  auto inlined = inliner.get_inlined();
  EXPECT_EQ(inlined.size(), 1);
  EXPECT_EQ(inlined.count(check_method), 0);
  EXPECT_EQ(inlined.count(small_method), 1);
}

TEST_F(MethodInlineTest, inline_init_not_relaxed) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:()V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);

  const auto& caller_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LFoo;.<init>:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  const auto& caller_expected_str = caller_str;
  auto* caller_actual = caller->get_code();
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_relaxed) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:()V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);

  const auto& caller_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LFoo;.<init>:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);
  expected_inlined.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )";
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_relaxed_finalize) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:()V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);
  DexMethod* finalize =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.finalize:()V"));
  finalize->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);
  foo_cls->add_method(finalize);

  const auto& caller_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LFoo;.<init>:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  const auto& caller_expected_str = caller_str;
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_relaxed_stores) {
  auto* s = assembler::class_from_string(R"(
    (class (public) "LS;"
      (method (public constructor) "LS;.<init>:()V"
        (
          (load-param-object v0)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
          (return-void)
        )
      )
    )
  )");

  auto* x = assembler::class_from_string(R"(
    (class (public) "LX;" extends "LS;"
      (method (public constructor) "LX;.<init>:()V"
        (
          (load-param-object v0)
          (invoke-direct (v0) "LS;.<init>:()V")
          (return-void)
        )
      )
    )
  )");
  auto* x_init = x->get_ctors().at(0);

  auto* use = assembler::class_from_string(R"(
    (class (public) "LUse;"
      (method (public static) "LUse;.a:()V"
        (
          (new-instance "LX;")
          (move-result-pseudo-object v0)
          (invoke-direct (v0) "LX;.<init>:()V")
          (return-void)
        )
      )
    )
  )");
  auto* caller = use->get_all_methods().at(0);

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined; // intentionally empty.
  {
    DexStore store("classes");
    store.add_classes({});
    store.add_classes({use, s});
    stores.push_back(std::move(store));
  }
  {
    DexStore store("x", {"classes"});
    store.add_classes({x});
    stores.push_back(std::move(store));
  }

  candidates.insert(x_init);

  auto scope = build_class_scope(stores);
  for (auto* cls : scope) {
    for (auto* m : cls->get_all_methods()) {
      auto* code = m->get_code();
      if (code != nullptr) {
        code->build_cfg();
      }
    }
  }

  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();

  // Unchanged from above.
  const auto& caller_expected_str = R"(
    (
      (new-instance "LX;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LX;.<init>:()V")
      (return-void)
    )
  )";
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_unfinalized_relaxed) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexField* field =
      dynamic_cast<DexField*>(DexField::make_field("LFoo;.final_field:Z"));
  field->make_concrete(ACC_PUBLIC);
  foo_cls->add_field(field);
  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:(I)V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);

  const auto& caller_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (const v2 0)
      (invoke-direct (v1 v2) "LFoo;.<init>:(I)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 0)
      (iput-boolean v2 v0 "LFoo;.final_field:Z")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);
  expected_inlined.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;
  inliner_config.unfinalize_perf_mode = inliner::UnfinalizePerfMode::NONE;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    UnorderedSet<const DexMethod*> unfinalized_init_methods{init};
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, /* configured_pure_methods */ {},
        /* min_sdk_api */ nullptr, /* cross_dex_penalty */ false,
        /* configured_finalish_field_names */ {}, /* local_only */ false,
        HotColdInliningBehavior::None, /* baseline_profile */ {},
        DEFAULT_COST_CONFIG, &unfinalized_init_methods);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (const v5 0)
      (iput-boolean v5 v1 "LFoo;.final_field:Z")
      (write-barrier)
      (return-void)
    )
  )";
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_no_unfinalized_relaxed) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */
                        false);

  DexField* field =
      dynamic_cast<DexField*>(DexField::make_field("LFoo;.not_final_field:Z"));
  field->make_concrete(ACC_PUBLIC);
  foo_cls->add_field(field);
  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:(I)V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);

  const auto& caller_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (const v2 0)
      (invoke-direct (v1 v2) "LFoo;.<init>:(I)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 0)
      (iput-boolean v2 v0 "LFoo;.not_final_field:Z")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);
  expected_inlined.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, /* configured_pure_methods */ {},
        /* min_sdk_api */ nullptr, /* cross_dex_penalty */ false,
        /* configured_finalish_field_names */ {}, /* local_only */ false,
        HotColdInliningBehavior::None, /* baseline_profile */ {},
        DEFAULT_COST_CONFIG, /* unfinalized_init_methods */ {});
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/Object;.<init>:()V")
      (const v5 0)
      (iput-boolean v5 v1 "LFoo;.not_final_field:Z")
      (return-void)
    )
  )";
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

TEST_F(MethodInlineTest, inline_init_unfinalized_with_finalize_norelax) {
  auto* foo_cls = create_a_class("LFoo;");
  auto* bar_cls = create_a_class("LBar;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBar;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexField* field =
      dynamic_cast<DexField*>(DexField::make_field("LFoo;.final_field:Z"));
  field->make_concrete(ACC_PUBLIC);
  foo_cls->add_field(field);
  DexMethod* init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.<init>:(I)V"));
  init->make_concrete(ACC_CONSTRUCTOR | ACC_PUBLIC, /* is_virtual */ false);

  DexMethod* finalize =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.finalize:()V"));
  finalize->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  bar_cls->add_method(caller);

  foo_cls->add_method(init);
  foo_cls->add_method(finalize);

  const auto& caller_str = R"(
    (
      (const v2 0)
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1 v2) "LFoo;.<init>:(I)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));

  const auto& init_str = R"(
    (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (const v2 0)
      (iput-boolean v2 v0 "LFoo;.not_final_field:Z")
      (return-void)
    )
  )";

  init->set_code(assembler::ircode_from_string(init_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  candidates.insert(init);

  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.relaxed_init_inline = true;

  caller->get_code()->build_cfg();
  init->get_code()->build_cfg();

  {
    UnorderedSet<const DexMethod*> unfinalized_init_methods{init};
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 21; // the "relaxed init inline" mode only kicks in starting
                      // with min_sdk 21.
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex,
        /* true_virtual_callers */ {},
        /* inline_for_speed */ nullptr,
        /* analyze_and_prune_inits */ true, /* configured_pure_methods */ {},
        /* min_sdk_api */ nullptr, /* cross_dex_penalty */ false,
        /* configured_finalish_field_names */ {}, /* local_only */ false,
        HotColdInliningBehavior::None, /* baseline_profile */ {},
        DEFAULT_COST_CONFIG, &unfinalized_init_methods);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
  }

  caller->get_code()->clear_cfg();
  init->get_code()->clear_cfg();

  // Unchanged from above.
  const auto& caller_expected_str = R"(
    (
      (const v2 0)
      (new-instance "LFoo;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1 v2) "LFoo;.<init>:(I)V")
      (return-void)
    )
  )";
  auto* caller_actual = caller->get_code();
  remove_position(caller_actual);
  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

// Given a hot callsite and a hot callee (= callee with hot entry-point block)
// that has significant cold code portion, test "partial inlining" where the
// inliner peels off the hot (and pure) portion of the callee and inlines it,
// leaving behind a call to the callee as a fallthrough case.
TEST_F(MethodInlineTest, partially_inline) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v0 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
    expected_inlined.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (move-object v1 v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20 callsite)
      (move-object v3 v1)
      (if-eqz v1 :L1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static (v3) "LFoo;.callee:(Ljava/lang/Object;)V")
    (:L1)
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (move-object v4 v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20 callsite)
      (move-object v6 v4)
      (if-eqz v4 :L2)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static (v6) "LFoo;.callee:(Ljava/lang/Object;)V")
    (:L2)
      (return-void)
    )
  )";

  auto* caller_actual = caller->get_code();

  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

// A true-virtual call site poisons only itself: the caller's other, ordinary
// call sites remain eligible for partial inlining. This pins the
// `it2 == cvc.insns.end()` branch of `get_callee`, which those ordinary call
// sites take because their caller has a true-virtual call site elsewhere.
TEST_F(MethodInlineTest,
       partially_inline_with_unrelated_true_virtual_callsite) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* vcallee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.vcallee:()V"));
  vcallee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);
  foo_cls->add_method(vcallee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v2 0)
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-virtual (v2) "LFoo;.vcallee:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v0 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  const auto& vcallee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.vcallee:()V" 1 (1.0 1.0))
      (return-void)
    )
  )";

  vcallee->set_code(assembler::ircode_from_string(vcallee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    // `vcallee` is deliberately not a candidate: it must enter
    // `m_caller_callee` only via `true_virtual_callers`, so that it lands in
    // `exclusive_callees` while `callee` does not.
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();
  vcallee->get_code()->build_cfg();

  // Register only the invoke-virtual, so the two invoke-statics miss in
  // `cvc.insns` while the caller still has an entry in
  // `m_caller_virtual_callees`.
  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      true_virtual_callers[vcallee].caller_insns[caller].insert(mie.insn);
    }
  }
  ASSERT_EQ(true_virtual_callers[vcallee].caller_insns[caller].size(), 1);

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    // Both ordinary call sites get partially inlined.
    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();
  vcallee->get_code()->clear_cfg();
}

// A callee reached only through a true virtual must not be inlined at a call
// site that was NOT registered as one: `get_callee` returns nullopt there. That
// guard is what makes it safe for the test above to stop blocking partial
// inlining across the rest of the method.
TEST_F(MethodInlineTest,
       no_partial_inline_at_an_unregistered_exclusive_callee_site) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* vcallee =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.vcallee:()V"));
  vcallee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);
  foo_cls->add_method(vcallee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v2 0)
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-virtual (v2) "LFoo;.vcallee:()V")
      (invoke-virtual (v2) "LFoo;.vcallee:()V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v0 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  const auto& vcallee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.vcallee:()V" 1 (1.0 1.0))
      (return-void)
    )
  )";

  vcallee->set_code(assembler::ircode_from_string(vcallee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    // `vcallee` is deliberately not a candidate: it must enter
    // `m_caller_callee` only via `true_virtual_callers`, so that it lands in
    // `exclusive_callees` while `callee` does not.
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();
  vcallee->get_code()->build_cfg();

  // Register only the invoke-virtual, so the two invoke-statics miss in
  // `cvc.insns` while the caller still has an entry in
  // `m_caller_virtual_callees`.
  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      true_virtual_callers[vcallee].caller_insns[caller].insert(mie.insn);
      break;
    }
  }
  ASSERT_EQ(true_virtual_callers[vcallee].caller_insns[caller].size(), 1);

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    // The ordinary call sites are unaffected, as in the test above.
    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);

    // The real assertion. `partially_inlined` is 2 either way, so it cannot see
    // this: what distinguishes the two behaviours is which of the two
    // invoke-virtuals survives. The registered one is inlined; the unregistered
    // one resolves to a callee that only ever arrives through a true virtual,
    // so `get_callee` must return nullopt and leave it alone. Drop the
    // exclusivity check and this count goes to 0.
    size_t surviving_virtual_calls = 0;
    for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
      if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
        surviving_virtual_calls++;
      }
    }
    EXPECT_EQ(surviving_virtual_calls, 1u)
        << "the unregistered call site of an exclusive callee must not be "
           "inlined";
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();
  vcallee->get_code()->clear_cfg();
}

// A callsite may name an inherited method via the subtype it is invoked on.
// The fallback invocation names the callee, `LBase;.callee`, where the
// original names `LSub;.callee`; the receiver is a `LSub;` and hence also a
// `LBase;`, so that invocation is a valid stand-in.
TEST_F(MethodInlineTest, partially_inline_inherited_formal_method) {
  auto* base_cls = create_a_class("LBase;");
  ClassCreator sub_cc(DexType::make_type("LSub;"));
  sub_cc.set_super(base_cls->get_type());
  auto* sub_cls = sub_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LSub;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LBase;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  base_cls->add_method(callee);
  sub_cls->add_method(caller);

  // `LSub;` does not define `callee`, so both callsites resolve to
  // `LBase;.callee`.
  const auto& caller_str = R"(
    (
      (.src_block "LSub;.caller:()V" 1 (1.0 1.0))
      (.pos "LSub;.caller:()V" "Sub.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LSub;.callee:(Ljava/lang/Object;)V")
      (invoke-virtual (v0 v1) "LSub;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LBase;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LBase;.callee:(Ljava/lang/Object;)V" "Base.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LBase;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LBase;.callee:(Ljava/lang/Object;)V" "Base.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({base_cls, sub_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  // Each peeled-off prefix falls back to an invocation naming the callee.
  size_t fallback_invokes = 0;
  for (const auto& mie : InstructionIterable(caller->get_code())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL &&
        mie.insn->get_method() == callee) {
      fallback_invokes++;
    }
  }
  EXPECT_EQ(fallback_invokes, 2u);
}

// A callee declared in an interface is invoked with an `invoke-interface`, so
// that is what the fallback invocation uses.
TEST_F(MethodInlineTest, partially_inline_interface_callee) {
  ClassCreator intf_cc(DexType::make_type("LI;"));
  intf_cc.set_super(type::java_lang_Object());
  intf_cc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* intf_cls = intf_cc.create();
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  // A default method: declared in an interface, and carrying code.
  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LI;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  intf_cls->add_method(callee);
  foo_cls->add_method(caller);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-interface (v0 v1) "LI;.callee:(Ljava/lang/Object;)V")
      (invoke-interface (v0 v1) "LI;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LI;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LI;.callee:(Ljava/lang/Object;)V" "I.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LI;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LI;.callee:(Ljava/lang/Object;)V" "I.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({intf_cls, foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  size_t fallback_invokes = 0;
  for (const auto& mie : InstructionIterable(caller->get_code())) {
    if (mie.insn->has_method() && mie.insn->get_method() == callee) {
      EXPECT_EQ(mie.insn->opcode(), OPCODE_INVOKE_INTERFACE);
      fallback_invokes++;
    }
  }
  EXPECT_EQ(fallback_invokes, 2u);
}

// A non-virtual callee is invoked with an `invoke-direct`, so that is what the
// fallback invocation uses.
TEST_F(MethodInlineTest, partially_inline_direct_callee) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PRIVATE, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1) "LFoo;.callee:(Ljava/lang/Object;)V")
      (invoke-direct (v0 v1) "LFoo;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  size_t fallback_invokes = 0;
  for (const auto& mie : InstructionIterable(caller->get_code())) {
    if (mie.insn->has_method() && mie.insn->get_method() == callee) {
      EXPECT_EQ(mie.insn->opcode(), OPCODE_INVOKE_DIRECT);
      fallback_invokes++;
    }
  }
  EXPECT_EQ(fallback_invokes, 2u);
}

// A true-virtual callsite reaches its unique implementation through a receiver
// cast: the callee is a `LFoo;` method while the callsite names `LBase;`. The
// cast must land ahead of the peeled-off prefix, so that the fallback
// invocation of `LFoo;.callee` sees the cast receiver.
TEST_F(MethodInlineTest, partially_inline_true_virtual_with_receiver_cast) {
  auto* base_cls = create_a_class("LBase;");
  base_cls->set_access(base_cls->get_access() | ACC_ABSTRACT);
  ClassCreator foo_cc(DexType::make_type("LFoo;"));
  foo_cc.set_super(base_cls->get_type());
  auto* foo_cls = foo_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* base_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LBase;.callee:(Ljava/lang/Object;)V"));
  base_callee->make_concrete(ACC_ABSTRACT, /* is_virtual */ true);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  base_cls->add_method(base_callee);
  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({base_cls, foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  // Both callsites resolve to `LFoo;.callee` only via a receiver cast, as the
  // true-virtual analysis would record it.
  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      true_virtual_callers[callee].caller_insns[caller].insert(mie.insn);
      true_virtual_callers[callee].inlined_invokes_need_cast.emplace(
          mie.insn, foo_cls->get_type());
    }
  }
  ASSERT_EQ(true_virtual_callers[callee].caller_insns[caller].size(), 2);

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  // Each fallback invocation must take its receiver from the cast, which
  // requires the cast to precede the argument copies that feed it.
  UnorderedMap<reg_t, bool> from_cast;
  bool pending_cast = false;
  size_t fallback_invokes = 0;
  for (const auto& mie : InstructionIterable(caller->get_code())) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (op == OPCODE_CHECK_CAST) {
      pending_cast = insn->get_type() == foo_cls->get_type();
    } else if (op == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
      if (pending_cast) {
        from_cast[insn->dest()] = true;
        pending_cast = false;
      }
    } else if (op == OPCODE_MOVE_OBJECT) {
      from_cast[insn->dest()] = from_cast[insn->src(0)];
    } else if (op == OPCODE_INVOKE_VIRTUAL && insn->get_method() == callee) {
      EXPECT_TRUE(from_cast[insn->src(0)]);
      fallback_invokes++;
    }
  }
  EXPECT_EQ(fallback_invokes, 2u);
}

// A receiver cast to a supertype of the callee's class, as a
// same-implementation cluster records, leaves the receiver something other than
// an instance of that class -- the fallback invocation of `LFoo;.callee` would
// not verify -- so such a callsite is not partially inlined.
TEST_F(MethodInlineTest,
       partially_inline_receiver_cast_to_supertype_regression) {
  auto* base_cls = create_a_class("LBase;");
  base_cls->set_access(base_cls->get_access() | ACC_ABSTRACT);
  ClassCreator foo_cc(DexType::make_type("LFoo;"));
  foo_cc.set_super(base_cls->get_type());
  auto* foo_cls = foo_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* base_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LBase;.callee:(Ljava/lang/Object;)V"));
  base_callee->make_concrete(ACC_ABSTRACT, /* is_virtual */ true);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  base_cls->add_method(base_callee);
  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({base_cls, foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  // Both callsites are registered with a cast to `LBase;`, which is what a
  // same-implementation cluster spanning several `LBase;` subtypes records.
  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      true_virtual_callers[callee].caller_insns[caller].insert(mie.insn);
      true_virtual_callers[callee].inlined_invokes_need_cast.emplace(
          mie.insn, base_cls->get_type());
    }
  }
  ASSERT_EQ(true_virtual_callers[callee].caller_insns[caller].size(), 2);

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 0u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();
}

// An invoke-interface callsite whose unique implementation is a class method:
// the receiver is cast to `LImpl;` and the fallback invocation devirtualizes to
// an `invoke-virtual` of `LImpl;.callee`, which dispatches on the receiver just
// as the original did.
TEST_F(MethodInlineTest, partially_inline_devirtualized_interface_callsite) {
  ClassCreator intf_cc(DexType::make_type("LI;"));
  intf_cc.set_super(type::java_lang_Object());
  intf_cc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* intf_cls = intf_cc.create();

  ClassCreator impl_cc(DexType::make_type("LImpl;"));
  impl_cc.set_super(type::java_lang_Object());
  impl_cc.add_interface(intf_cls->get_type());
  auto* impl_cls = impl_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LImpl;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* intf_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LI;.callee:(Ljava/lang/Object;)V"));
  intf_callee->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LImpl;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  intf_cls->add_method(intf_callee);
  impl_cls->add_method(caller);
  impl_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LImpl;.caller:()V" 1 (1.0 1.0))
      (.pos "LImpl;.caller:()V" "Impl.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-interface (v0 v1) "LI;.callee:(Ljava/lang/Object;)V")
      (invoke-interface (v0 v1) "LI;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LImpl;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LImpl;.callee:(Ljava/lang/Object;)V" "Impl.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LImpl;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LImpl;.callee:(Ljava/lang/Object;)V" "Impl.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({intf_cls, impl_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  // Both interface callsites reach `LImpl;.callee` via a cast to `LImpl;`, as
  // the true-virtual analysis records for a sole implementation.
  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_INTERFACE) {
      true_virtual_callers[callee].caller_insns[caller].insert(mie.insn);
      true_virtual_callers[callee].inlined_invokes_need_cast.emplace(
          mie.insn, impl_cls->get_type());
    }
  }
  ASSERT_EQ(true_virtual_callers[callee].caller_insns[caller].size(), 2);

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    EXPECT_EQ(inliner.get_info().partially_inlined, 2u);
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  size_t fallback_invokes = 0;
  for (const auto& mie : InstructionIterable(caller->get_code())) {
    if (mie.insn->has_method() && mie.insn->get_method() == callee) {
      EXPECT_EQ(mie.insn->opcode(), OPCODE_INVOKE_VIRTUAL);
      fallback_invokes++;
    }
  }
  EXPECT_EQ(fallback_invokes, 2u);
}

// Partially inlining invoke-super is not supported.
TEST_F(MethodInlineTest, partially_inline_invoke_super_regression) {
  auto* base_cls = create_a_class("LBase;");
  ClassCreator foo_cc(DexType::make_type("LFoo;"));
  foo_cc.set_super(base_cls->get_type());
  auto* foo_cls = foo_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* base_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LBase;.callee:(Ljava/lang/Object;)V"));
  base_callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC, /* is_virtual */ true);

  base_cls->add_method(base_callee);
  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-super (v0 v1) "LFoo;.callee:(Ljava/lang/Object;)V")
      (move-result-pseudo-object v0)
      (invoke-super (v0 v1) "LFoo;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  base_callee->set_code(assembler::ircode_from_string(callee_str));
  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({base_cls, foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  base_callee->get_code()->build_cfg();
  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_SUPER) {
      true_virtual_callers[callee].caller_insns[caller].insert(mie.insn);
    }
  }
  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  base_callee->get_code()->clear_cfg();
  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  auto* caller_actual = caller->get_code();
  auto caller_expected = assembler::ircode_from_string(caller_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

// The fallback invocation names the callee, so the receiver must be an
// instance of the callee's class. Here it is only known to be a `Base`, and
// no cast is on record, so partial inlining is off the table.
TEST_F(MethodInlineTest,
       partially_inline_non_matching_formal_method_regression) {
  auto* base_cls = create_a_class("LBase;");
  base_cls->set_access(base_cls->get_access() | ACC_ABSTRACT);
  ClassCreator foo_cc(DexType::make_type("LFoo;"));
  foo_cc.set_super(base_cls->get_type());
  auto* foo_cls = foo_cc.create();

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* base_callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LBase;.callee:(Ljava/lang/Object;)V"));
  base_callee->make_concrete(ACC_ABSTRACT, /* is_virtual */ true);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PRIVATE, /* is_virtual */ true);

  base_cls->add_method(base_callee);
  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const-string "Some string")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0 v1) "LBase;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v1 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (invoke-virtual (v0 v1) "LFoo;.callee:(Ljava/lang/Object;)V")
      (const v1 0)
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({base_cls, foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.virtual_inline = true;
  inliner_config.true_virtual_inline = true;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  CalleeCallerInsns true_virtual_callers;
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      true_virtual_callers[callee].caller_insns[caller].insert(mie.insn);
    }
  }
  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex, true_virtual_callers);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  auto* caller_actual = caller->get_code();
  auto caller_expected = assembler::ircode_from_string(caller_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}

// For debug info attachment a synthetic marker is used. Ensure it is gone
// in the case that the caller has no dex position itself to anchor on.
TEST_F(MethodInlineTest, partially_inline_dex_position_marker_gone) {
  auto* foo_cls = create_a_class("LFoo;");

  DexMethod* caller =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.caller:()V"));
  caller->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  DexMethod* callee = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.callee:(Ljava/lang/Object;)V"));
  callee->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);

  foo_cls->add_method(caller);
  foo_cls->add_method(callee);

  const auto& caller_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (.pos "LFoo;.caller:()V" "Foo.java" 10)
      (move-result-pseudo-object v0)
      (invoke-static (v0) "LFoo;.callee:(Ljava/lang/Object;)V")
      (return-void)
    )
  )";

  caller->set_code(assembler::ircode_from_string(caller_str));
  caller->get_code()->set_debug_item(std::make_unique<DexDebugItem>());

  // We insert a "dummy" instruction into the cold portion of the callee to
  // make the callee large enough to make the transformation worthwhile.
  const auto& callee_str = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20)
      (if-eqz v0 :exit)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 30)
      (const v1 0)
      (invoke-static (v1) "Ldummy;.dummy:(Ljava/lang/Object;)V")
      (throw v1)
      (:exit)
      (return-void)
    )
  )";

  callee->set_code(assembler::ircode_from_string(callee_str));

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;

  bool intra_dex = false;

  DexStoresVector stores;
  UnorderedSet<DexMethod*> candidates;
  std::unordered_set<DexMethod*> expected_inlined;
  {
    DexStore store("root");
    store.add_classes({});
    store.add_classes({foo_cls});
    stores.push_back(std::move(store));
  }
  {
    candidates.insert(caller);
    candidates.insert(callee);
    expected_inlined.insert(callee);
  }
  auto scope = build_class_scope(stores);
  api::LevelChecker::init(0, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);
  inliner_config.partial_hot_hot_inline = true;
  inliner_config.multiple_callers = false;
  inliner_config.use_call_site_summaries = false;
  inliner_config.throws_inline = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.run_const_prop = false;
  inliner_config.shrinker.compute_pure_methods = false;

  caller->get_code()->build_cfg();
  callee->get_code()->build_cfg();

  {
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);
    int min_sdk = 0;
    MultiMethodInliner inliner(
        scope, init_classes_with_side_effects, stores, conf, candidates,
        std::ref(concurrent_method_resolver), inliner_config, min_sdk,
        intra_dex ? IntraDex : InterDex);
    inliner.inline_methods();

    auto inlined = inliner.get_inlined();
    EXPECT_EQ(inlined.size(), expected_inlined.size());
    for (auto* method : expected_inlined) {
      EXPECT_EQ(inlined.count(method), 1);
    }
  }

  caller->get_code()->clear_cfg();
  callee->get_code()->clear_cfg();

  const auto& caller_expected_str = R"(
    (
      (.src_block "LFoo;.caller:()V" 1 (1.0 1.0))
      (const-string "Some string")
      (move-result-pseudo-object v0)
      (move-object v1 v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20 callsite)
      (move-object v3 v1)
      (if-eqz v1 :L1)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (invoke-static (v3) "LFoo;.callee:(Ljava/lang/Object;)V")
    (:L1)
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (move-object v4 v0)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (.pos "LFoo;.callee:(Ljava/lang/Object;)V" "Foo.java" 20 callsite)
      (move-object v6 v4)
      (if-eqz v4 :L2)
      (.src_block "LFoo;.callee:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (.pos:callsite "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static (v6) "LFoo;.callee:(Ljava/lang/Object;)V")
    (:L2)
      (return-void)
    )
  )";

  auto* caller_actual = caller->get_code();

  auto caller_expected = assembler::ircode_from_string(caller_expected_str);
  EXPECT_CODE_EQ(caller_actual, caller_expected.get());
}
namespace {

// Runs MethodInlinePass with true-virtual inlining over prepared stores and
// returns its metrics. The pass leaves method bodies without a CFG.
auto run_method_inline_pass(DexStoresVector& stores, bool normal_primary_dex) {
  Json::Value config;
  config["inliner"]["virtual"] = true;
  config["inliner"]["true_virtual_inline"] = true;
  config["inliner"]["run_const_prop"] = false;
  config["InterDexPass"]["normal_primary_dex"] = normal_primary_dex;
  ConfigFiles conf(config);
  conf.parse_global_config();
  MethodInlinePass pass;
  PassManager manager({&pass}, conf);
  manager.run_passes(stores, conf);
  return manager.get_pass_info().at(0).metrics;
}

// `LHelper;.choose:(I)I` returns 10 for 0 and 20 otherwise.
DexClass* make_choose_helper() {
  return assembler::class_from_string(R"(
    (class (public) "LHelper;"
      (method (public static) "LHelper;.choose:(I)I"
        (
          (load-param v0)
          (if-eqz v0 :zero)
          (const v1 20)
          (return v1)
          (:zero)
          (const v1 10)
          (return v1)
        )
      )
    )
  )");
}

// An implementation of `LI;.get:(I)I` that returns `LHelper;.choose(x)`.
DexClass* make_choosing_impl(const std::string& type,
                             const std::string& super = "") {
  return assembler::class_from_string(
      "(class (public) \"" + type + "\" " + super +
      " implements \"LI;\" (method (public) \"" + type +
      ".get:(I)I\" ((load-param-object v0) (load-param v1) (invoke-static "
      "(v1) \"LHelper;.choose:(I)I\") (move-result v2) (return v2))))");
}

// A static `use:(LI;)I` that returns `get(arg)` on its argument.
DexClass* make_constant_caller(const std::string& type, int arg) {
  return assembler::class_from_string(
      "(class (public) \"" + type + "\" (method (public static) \"" + type +
      ".use:(LI;)I\" ((load-param-object v0) (const v1 " + std::to_string(arg) +
      ") (invoke-interface (v0 v1) \"LI;.get:(I)I\") (move-result v2) "
      "(return v2))))");
}

// The helper may be inlined without specialization, so either form is valid.
bool keeps_choose_result(DexMethod* method, int64_t value) {
  const auto* choose = DexMethod::get_method("LHelper;.choose:(I)I");
  method->get_code()->build_cfg();
  for (auto& mie : InstructionIterable(method->get_code()->cfg())) {
    if ((mie.insn->opcode() == OPCODE_INVOKE_STATIC &&
         mie.insn->get_method() == choose) ||
        (opcode::is_a_const(mie.insn->opcode()) &&
         mie.insn->get_literal() == value)) {
      return true;
    }
  }
  return false;
}

// `LA;` sorts first, so shared calls are recorded against its representative
// method but may run the other implementations despite their super calls
// passing 0. The extra implementation also adds a second shared caller.
void check_identical_implementation_callers(bool keep_shared_calls,
                                            bool extra_implementation) {
  auto* intf_cls = assembler::class_from_string(
      R"((interface (public) "LI;" (method "LI;.get:(I)I")))");
  auto* b_cls = make_choosing_impl("LB;");
  auto* caller_cls = make_constant_caller("LCaller;", 1);
  if (keep_shared_calls) {
    caller_cls->get_dmethods().at(0)->rstate.set_no_optimizations();
  }
  auto make_super_caller = [](const std::string& type,
                              const std::string& base) {
    return assembler::class_from_string(
        "(class (public) \"" + type + "\" extends \"" + base +
        "\" (method (public) \"" + type +
        ".use:()I\" ((load-param-object v0) (const v1 0) "
        "(invoke-super (v0 v1) \"" +
        base + ".get:(I)I\") (move-result v2) (return v2))))");
  };
  auto* sub_cls = make_super_caller("LSub;", "LB;");
  sub_cls->get_vmethods().at(0)->rstate.set_no_optimizations();
  std::vector<DexClass*> classes{
      intf_cls, make_choose_helper(), make_choosing_impl("LA;"),
      b_cls,    caller_cls,           sub_cls};
  DexClass* c_cls = nullptr;
  if (extra_implementation) {
    c_cls = make_choosing_impl("LC;");
    auto* other_caller = make_constant_caller("LOtherCaller;", 1);
    if (keep_shared_calls) {
      other_caller->get_dmethods().at(0)->rstate.set_no_optimizations();
    }
    auto* sub_c = make_super_caller("LSubC;", "LC;");
    sub_c->get_vmethods().at(0)->rstate.set_no_optimizations();
    classes.insert(classes.end(), {c_cls, other_caller, sub_c});
  }

  DexStoresVector stores;
  DexStore store("classes");
  store.add_classes(classes);
  stores.push_back(std::move(store));
  auto scope = build_class_scope(stores);
  walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
  api::LevelChecker::init(0, scope);
  always_assert(DexMethod::get_method("LHelper;.choose:(I)I") != nullptr);
  auto metrics = run_method_inline_pass(stores, /* normal_primary_dex */ false);

  EXPECT_TRUE(keeps_choose_result(b_cls->get_vmethods().at(0), 20));
  if (c_cls != nullptr) {
    EXPECT_TRUE(keeps_choose_result(c_cls->get_vmethods().at(0), 20));
  }
  if (!keep_shared_calls) {
    auto* code = caller_cls->get_dmethods().at(0)->get_code();
    code->build_cfg();
    for (auto& mie : InstructionIterable(code->cfg())) {
      EXPECT_NE(mie.insn->opcode(), OPCODE_INVOKE_INTERFACE);
    }
    EXPECT_GT(metrics.at("calls_inlined"), 0);
  }
}

} // namespace

TEST_F(MethodInlineTest, identical_implementation_keeps_shared_call_sites) {
  check_identical_implementation_callers(/* keep_shared_calls */ true,
                                         /* extra_implementation */ false);
}

TEST_F(MethodInlineTest, identical_implementation_keeps_all_cluster_members) {
  check_identical_implementation_callers(/* keep_shared_calls */ true,
                                         /* extra_implementation */ true);
}

TEST_F(MethodInlineTest, identical_implementation_still_inlines_shared_calls) {
  check_identical_implementation_callers(/* keep_shared_calls */ false,
                                         /* extra_implementation */ false);
}
