/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "MethodUtil.h"
#include "Show.h"
#include "VerifyUtil.h"

namespace {

// Checks only the first callsite in method against num_args_expected
void check_callsite_regs(DexMethod* method,
                         int num_args_expected,
                         uint callsite_index = 0) {
  uint i = 0;
  for (const auto& mie : InstructionIterable(method->get_code())) {
    auto* insn = mie.insn;
    if (opcode::is_a_method_invoke(insn->opcode())) {
      if (i == callsite_index) {
        auto* actual_method = insn->get_method();
        EXPECT_EQ(insn->srcs_size(), num_args_expected) << show(actual_method);
        break;
      }
      i++;
    }
  }
}

// Checks only the first return, whether it returns a value
void check_return(DexMethod* method, bool value) {
  for (const auto& mie : InstructionIterable(method->get_code())) {
    auto* insn = mie.insn;
    if (opcode::is_a_return(insn->opcode())) {
      EXPECT_EQ(opcode::is_a_return_value(insn->opcode()), value);
      break;
    }
  }
}

// Finds vmethod with particular name and proto
DexMethod* find_vmethod(const DexClass& cls,
                        const char* name,
                        const char* proto) {
  auto vmethods = cls.get_vmethods();
  fprintf(stderr, "===\n");
  for (auto* m : vmethods) {
    fprintf(stderr, "%s %s\n", SHOW(m->get_name()), SHOW(m->get_proto()));
  }
  auto it = std::find_if(vmethods.begin(), vmethods.end(),
                         [name, proto](DexMethod* m) {
                           return strcmp(name, m->get_name()->c_str()) == 0 &&
                                  strcmp(proto, SHOW(m->get_proto())) == 0;
                         });
  return it == vmethods.end() ? nullptr : *it;
}

// Sanity check: three foo constructors are defined
TEST_F(PreVerify, CtorsDefined) {
  auto* foo = find_class_named(classes, "Lcom/facebook/redex/test/instr/Foo;");
  ASSERT_NE(nullptr, foo);

  auto ctors = foo->get_ctors();
  EXPECT_EQ(ctors.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    auto* ctor = ctors.at(i);
    ASSERT_NE(nullptr, ctor);
  }
}

// Check unused arguments are successfully removed in constructors
TEST_F(PreVerify, RemoveCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2);
}

TEST_F(PostVerify, RemoveCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1);
}

// Check arguments of constructor aren't removed when they're used
TEST_F(PreVerify, DontRemoveUsedCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo2 = find_vmethod_named(*foo_user, "use_foo2");
  ASSERT_NE(nullptr, use_foo2);
  use_foo2->balloon();

  check_callsite_regs(use_foo2, 3);
}

TEST_F(PostVerify, DontRemoveUsedCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo2 = find_vmethod_named(*foo_user, "use_foo2");
  ASSERT_NE(nullptr, use_foo2);
  use_foo2->balloon();

  check_callsite_regs(use_foo2, 3);
}

// Check arguments of constructor aren't removed when the signature collides
TEST_F(PreVerify, CollidingCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo3 = find_vmethod_named(*foo_user, "use_foo3");
  ASSERT_NE(nullptr, use_foo3);
  use_foo3->balloon();

  check_callsite_regs(use_foo3, 4);
}

TEST_F(PostVerify, CollidingCtorArg) {
  auto* foo_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/FooUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo3 = find_vmethod_named(*foo_user, "use_foo3");
  ASSERT_NE(nullptr, use_foo3);
  use_foo3->balloon();

  check_callsite_regs(use_foo3, 4);
}

// Check no-argument static methods' invokes don't change
TEST_F(PreVerify, StaticsNoArgs) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static1 = find_dmethod_named(*statics, "static1");
  ASSERT_NE(nullptr, static1);

  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static1 = find_vmethod_named(*statics_user, "use_static1");
  ASSERT_NE(nullptr, use_static1);
  use_static1->balloon();

  check_callsite_regs(use_static1, 0);
}

TEST_F(PostVerify, StaticsNoArgs) {
  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static1 = find_vmethod_named(*statics_user, "use_static1");
  ASSERT_NE(nullptr, use_static1);
  use_static1->balloon();

  check_callsite_regs(use_static1, 0);
}

// Check static methods' invokes don't change when args are used
TEST_F(PreVerify, StaticsUsedArgs) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static2 = find_dmethod_named(*statics, "static2");
  ASSERT_NE(nullptr, static2);

  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static2 = find_vmethod_named(*statics_user, "use_static2");
  ASSERT_NE(nullptr, use_static2);
  use_static2->balloon();

  check_callsite_regs(use_static2, 1);
}

TEST_F(PostVerify, StaticsUsedArgs) {
  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static2 = find_vmethod_named(*statics_user, "use_static2");
  ASSERT_NE(nullptr, use_static2);
  use_static2->balloon();

  check_callsite_regs(use_static2, 1);
}

// Check static method arg removal for unused args
TEST_F(PreVerify, StaticsUnusedArgs) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static3 = find_dmethod_named(*statics, "static3");
  ASSERT_NE(nullptr, static3);

  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static3 = find_vmethod_named(*statics_user, "use_static3");
  ASSERT_NE(nullptr, use_static3);
  use_static3->balloon();

  check_callsite_regs(use_static3, 2);
}

TEST_F(PostVerify, StaticsUnusedArgs) {
  auto* statics_user =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/StaticsUser;");
  ASSERT_NE(nullptr, statics_user);

  auto* use_static3 = find_vmethod_named(*statics_user, "use_static3$uva1$0");
  ASSERT_NE(nullptr, use_static3);
  use_static3->balloon();

  check_callsite_regs(use_static3, 1);
}

// Checks that static method result type doesn't change when result is used
TEST_F(PreVerify, StaticsUsedResult) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static4 = find_dmethod_named(*statics, "static4_with_result");
  ASSERT_NE(nullptr, static4);

  ASSERT_FALSE(static4->get_proto()->is_void());
  static4->balloon();
  check_return(static4, true /* value */);
}

TEST_F(PostVerify, StaticsUsedResult) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static4 = find_dmethod_named(*statics, "static4_with_result");
  ASSERT_NE(nullptr, static4);

  ASSERT_FALSE(static4->get_proto()->is_void());
  static4->balloon();
  check_return(static4, true /* value */);
}

// Check static method result removal for unused results
TEST_F(PreVerify, StaticsUnusedResult) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static5 = find_dmethod_named(*statics, "static5_with_result");
  ASSERT_NE(nullptr, static5);

  ASSERT_FALSE(static5->get_proto()->is_void());
  static5->balloon();
  check_return(static5, true /* value */);
}

TEST_F(PostVerify, StaticsUnusedResult) {
  auto* statics =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Statics;");
  ASSERT_NE(nullptr, statics);

  auto* static5 = find_dmethod_named(*statics, "static5_with_result");
  ASSERT_NE(nullptr, static5);

  ASSERT_TRUE(static5->get_proto()->is_void());
  static5->balloon();
  check_return(static5, false /* value */);
}

// Check overloaded name mangling upon collision
TEST_F(PreVerify, PrivatesUsedArgs) {
  auto* privates =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Privates;");
  ASSERT_NE(nullptr, privates);
  Scope scope = {privates};
  balloon_for_test(scope);

  // 1 default constructor + 2 private void private1() methods
  auto dmethods = privates->get_dmethods();
  EXPECT_EQ(dmethods.size(), 3);

  bool two_args_method = false;
  bool three_args_method = false;

  for (auto* dmethod : dmethods) {
    if (!method::is_constructor(dmethod)) {
      auto num_args = dmethod->get_proto()->get_args()->size();
      if (num_args == 2) {
        two_args_method = true;
      } else {
        three_args_method = true;
      }
    }
  }

  EXPECT_TRUE(two_args_method && three_args_method);
  auto* use_private_first = find_vmethod_named(*privates, "use_private_first");
  check_callsite_regs(use_private_first, 3);
  auto* use_private_second =
      find_vmethod_named(*privates, "use_private_second");
  check_callsite_regs(use_private_second, 4);
}

TEST_F(PostVerify, PrivatesUsedArgs) {
  auto* privates =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Privates;");
  ASSERT_NE(nullptr, privates);
  Scope scope = {privates};
  balloon_for_test(scope);

  auto dmethods = privates->get_dmethods();
  EXPECT_EQ(dmethods.size(), 3);

  std::vector<DexMethod*> overloaded_methods;
  for (auto* dmethod : dmethods) {
    if (!method::is_constructor(dmethod)) {
      auto num_args = dmethod->get_proto()->get_args()->size();
      EXPECT_EQ(num_args, 2);
      overloaded_methods.emplace_back(dmethod);
    }
  }

  EXPECT_EQ(overloaded_methods.size(), 2);
  auto name1 = overloaded_methods.at(0)->get_name()->str();
  auto name2 = overloaded_methods.at(1)->get_name()->str();
  ASSERT_NE(name1, name2);

  auto* use_private_first = find_vmethod_named(*privates, "use_private_first");
  check_callsite_regs(use_private_first, 3);
  auto* use_private_second =
      find_vmethod_named(*privates, "use_private_second");
  check_callsite_regs(use_private_second, 3);
}

// Check nonvirtual method arg removal for unused args
TEST_F(PreVerify, PublicNonVirtualsUnusedArgs) {
  auto* non_virtuals =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/NonVirtuals;");
  ASSERT_NE(nullptr, non_virtuals);

  auto* non_virtual1 = find_vmethod_named(*non_virtuals, "non_virtual1");
  ASSERT_NE(nullptr, non_virtual1);
  [[maybe_unused]] auto* code = non_virtual1->get_code();

  auto* non_virtuals_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/NonVirtualsUser;");
  ASSERT_NE(nullptr, non_virtuals_user);

  auto* use_non_virtual1 =
      find_vmethod_named(*non_virtuals_user, "use_non_virtual1");
  ASSERT_NE(nullptr, use_non_virtual1);
  use_non_virtual1->balloon();

  check_callsite_regs(use_non_virtual1, 2);
}

TEST_F(PostVerify, NonVirtualsUnusedArgs) {
  auto* non_virtuals =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/NonVirtuals;");
  ASSERT_NE(nullptr, non_virtuals);

  auto* non_virtual1 = find_vmethod_named(*non_virtuals, "non_virtual1$uva0$0");
  ASSERT_NE(nullptr, non_virtual1);

  auto* non_virtuals_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/NonVirtualsUser;");
  ASSERT_NE(nullptr, non_virtuals_user);

  auto* use_non_virtual1 =
      find_vmethod_named(*non_virtuals_user, "use_non_virtual1");
  ASSERT_NE(nullptr, use_non_virtual1);
  use_non_virtual1->balloon();

  check_callsite_regs(use_non_virtual1, 1);
}

// Check protected method arg removal for unused args
TEST_F(PreVerify, ProtectedNonVirtualsUnusedArgs) {
  auto* non_virtuals =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/NonVirtuals;");
  ASSERT_NE(nullptr, non_virtuals);

  auto* non_virtual2 = find_vmethod_named(*non_virtuals, "non_virtual2");
  ASSERT_NE(nullptr, non_virtual2);

  auto* non_virtuals_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/NonVirtualsUser;");
  ASSERT_NE(nullptr, non_virtuals_user);

  auto* use_non_virtual2 =
      find_vmethod_named(*non_virtuals_user, "use_non_virtual2");
  ASSERT_NE(nullptr, use_non_virtual2);
  use_non_virtual2->balloon();

  check_callsite_regs(use_non_virtual2, 2);
}

TEST_F(PostVerify, ProtectedNonVirtualsUnusedArgs) {
  auto* non_virtuals =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/NonVirtuals;");
  ASSERT_NE(nullptr, non_virtuals);

  auto* non_virtual2 = find_vmethod_named(*non_virtuals, "non_virtual2$uva0$0");
  ASSERT_NE(nullptr, non_virtual2);

  auto* non_virtuals_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/NonVirtualsUser;");
  ASSERT_NE(nullptr, non_virtuals_user);

  auto* use_non_virtual2 =
      find_vmethod_named(*non_virtuals_user, "use_non_virtual2");
  ASSERT_NE(nullptr, use_non_virtual2);
  use_non_virtual2->balloon();

  check_callsite_regs(use_non_virtual2, 1);
}

// Check argument reordering
TEST_F(PreVerify, Reorderables) {
  auto* reorderables =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Reorderables;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 =
      find_vmethod(*reorderables, "reorderable1", "(ILjava/lang/Object;D)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(DILjava/lang/Object;)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;ID)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

TEST_F(PostVerify, Reorderables) {
  auto* reorderables =
      find_class_named(classes, "Lcom/facebook/redex/test/instr/Reorderables;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 = find_vmethod(*reorderables, "reorderable1$rvp0$0",
                                    "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt = find_vmethod(*reorderables, "reorderable2$rvp0$0",
                                       "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt = find_vmethod(*reorderables, "reorderable2$rvp0$1",
                                          "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

TEST_F(PreVerify, ReorderablesInterface) {
  auto* reorderables = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/ReorderablesInterface;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 =
      find_vmethod(*reorderables, "reorderable1", "(ILjava/lang/Object;D)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(DILjava/lang/Object;)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;ID)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

TEST_F(PostVerify, ReorderablesInterface) {
  auto* reorderables = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/ReorderablesInterface;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 = find_vmethod(*reorderables, "reorderable1$rvp0$0",
                                    "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt = find_vmethod(*reorderables, "reorderable2$rvp0$0",
                                       "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt = find_vmethod(*reorderables, "reorderable2$rvp0$1",
                                          "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

TEST_F(PreVerify, SubReorderables) {
  auto* reorderables = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/SubReorderables;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 =
      find_vmethod(*reorderables, "reorderable1", "(ILjava/lang/Object;D)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(DILjava/lang/Object;)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;ID)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

TEST_F(PostVerify, SubReorderables) {
  auto* reorderables = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/SubReorderables;");
  ASSERT_NE(nullptr, reorderables);

  auto* reorderable1 = find_vmethod(*reorderables, "reorderable1$rvp0$0",
                                    "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable1);

  auto* reorderable2 =
      find_vmethod(*reorderables, "reorderable2", "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2);

  auto* reorderable2alt = find_vmethod(*reorderables, "reorderable2$rvp0$0",
                                       "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2alt);

  auto* reorderable2altalt = find_vmethod(*reorderables, "reorderable2$rvp0$1",
                                          "(Ljava/lang/Object;DI)V");
  ASSERT_NE(nullptr, reorderable2altalt);
}

// Check unused arguments are successfully removed in virtual base constructors
TEST_F(PreVerify, RemoveVirtualCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2);
}

TEST_F(PostVerify, RemoveVirtualCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1);
}

// Check unused arguments are successfully removed in virtual derived
// constructors
TEST_F(PreVerify, RemoveDerivedCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2);
}

TEST_F(PostVerify, RemoveDerivedCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo1_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1);
}

// Check used arguments are not removed in virtual base constructors
TEST_F(PreVerify, DontRemoveVirtualCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo2_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 3);
}

TEST_F(PostVerify, DontRemoveVirtualCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo2_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 3);
}

// Check used arguments are not removed in virtual derived constructors
TEST_F(PreVerify, DontRemoveDerivedCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo2_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 3);
}

TEST_F(PostVerify, DontRemoveDerivedCtorArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo2_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 3);
}

// Check used arguments are not removed in virtual base functions that use the
// argument in the base function
TEST_F(PreVerify, DontRemoveVirtualArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_base_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveVirtualArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_base_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual derived functions that use
// the argument in the base function
TEST_F(PreVerify, DontRemoveDerivedArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_base_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveDerivedArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_base_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual base functions that use the
// argument in the derived function
TEST_F(PreVerify, DontRemoveVirtualArgUsedInDerived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveVirtualArgUsedInDerived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual derived functions that use
// the argument in the derived function
TEST_F(PreVerify, DontRemoveDerivedArgUsedInDrived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveDerivedArgUsedInDerived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual base functions that use the
// argument in the both functions
TEST_F(PreVerify, DontRemoveVirtualArgUsedInBoth) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_all_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveVirtualArgUsedInBoth) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_all_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual derived functions that use
// the argument in both functions
TEST_F(PreVerify, DontRemoveDerivedArgUsedInBoth) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_all_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveDerivedArgUsedInBoth) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_all_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are removed in virtual base functions that use the
// argument in the no functions
TEST_F(PreVerify, RemoveVirtualArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_none_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, RemoveVirtualArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_none_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1, 1);
}

// Check used arguments are removed in virtual derived functions that use
// the argument in no functions
TEST_F(PreVerify, RemoveDerivedArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_none_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, RemoveDerivedArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_used_in_none_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1, 1);
}

// Check used arguments are not removed in virtual base functions that use
// the argument in a derived derived function
TEST_F(PreVerify, DontRemoveVirtualArgUsedInDerivedDerived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_derived_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveVirtualArgUsedInDerivedDerived) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_derived_derived_virtual");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual derived derived functions
// that use the argument in a base function
TEST_F(PreVerify, DontRemoveDerivedDerivedArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_base_derived_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveDerivedDerivedArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_base_derived_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual derived functions
// that use the argument in a sibling function
TEST_F(PreVerify, DontRemoveDerivedArgUsedInSibling) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_sibling_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveDerivedArgUsedInSibling) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_sibling_derived");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are removed in virtual interface functions
// that use the argument in a no functions
TEST_F(PreVerify, RemoveInterfaceArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_none_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, RemoveInterfaceArgUsedInNone) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_none_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1, 1);
}

// Check used arguments are not removed in virtual interface functions
// that use the argument in all functions
TEST_F(PreVerify, DontRemoveInterfaceArgUsedInAll) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_all_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveInterfaceArgUsedInAll) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_all_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in virtual interface functions
// that use the argument in base function
TEST_F(PreVerify, DontRemoveInterfaceArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_base_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveInterfaceArgUsedInBase) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo =
      find_vmethod_named(*foo_user, "use_foo_used_in_base_interface");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check used arguments are not removed in abstract class functions
TEST_F(PreVerify, DontRemoveAbstractUsedArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_abstract_used");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, DontRemoveAbstractUsedArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_abstract_used");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

// Check unused arguments are removed in abstract class functions
TEST_F(PreVerify, RemoveAbstractUnusedArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_abstract_unused");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 2, 1);
}

TEST_F(PostVerify, RemoveAbstractUnusedArg) {
  auto* foo_user = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/FooVirtualUser;");
  ASSERT_NE(nullptr, foo_user);

  auto* use_foo = find_vmethod_named(*foo_user, "use_foo_abstract_unused");
  ASSERT_NE(nullptr, use_foo);
  use_foo->balloon();

  check_callsite_regs(use_foo, 1, 1);
}

TEST_F(PostVerify, DontRemoveAnnotatedParameter) {
  auto* annotated_parameter_class = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/AnnotatedParameterInterface;");
  ASSERT_NE(nullptr, annotated_parameter_class);

  auto* annotated_parameter_method = find_vmethod(
      *annotated_parameter_class, "annotated_parameter_method_1", "(I)V");
  ASSERT_NE(nullptr, annotated_parameter_method);
}

TEST_F(PostVerify, RemoveNonAnnotatedParameterSingleParameterMethod) {
  auto* annotated_parameter_class = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/AnnotatedParameterInterface;");
  ASSERT_NE(nullptr, annotated_parameter_class);

  auto* annotated_parameter_method = find_vmethod(
      *annotated_parameter_class, "annotated_parameter_method_2", "(I)V");

  ASSERT_EQ(nullptr, annotated_parameter_method);
}

TEST_F(PostVerify, DontRemoveNonAnnotatedParameterMultiParameterMethod) {
  auto* annotated_parameter_class = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/AnnotatedParameterInterface;");
  ASSERT_NE(nullptr, annotated_parameter_class);

  auto* annotated_parameter_method = find_vmethod(
      *annotated_parameter_class, "annotated_parameter_method_3", "(II)V");

  ASSERT_NE(nullptr, annotated_parameter_method);
}

} // namespace
