/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstructorAccesses.h"

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAccess.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Walkers.h"

namespace ptrs = local_pointers;

class ConstructorAccessesTest : public RedexTest {
 public:
  void SetUp() override {
    ClassCreator base(DexType::make_type("LBase;"));
    base.set_super(type::java_lang_Object());
    base.create();

    ClassCreator creator(DexType::make_type("LFoo;"));
    creator.set_super(DexType::make_type("LBase;"));
    creator.add_field(
        DexField::make_field("LFoo;.a:I")->make_concrete(ACC_PUBLIC));
    creator.add_field(
        DexField::make_field("LFoo;.b:I")->make_concrete(ACC_PUBLIC));
    m_cls = creator.create();
  }

 protected:
  // Builds a constructor of `LFoo;` with parameters `this`, an `int` and
  // another `LFoo;`.
  IRCode* code(const std::string& body) {
    m_code = assembler::ircode_from_string(
        "((load-param-object v0) (load-param v1) (load-param-object v2) " +
        body + ")");
    m_code->build_cfg();
    return m_code.get();
  }

  // The `n`th instruction with opcode `op`.
  const IRInstruction* nth(IROpcode op, size_t n = 0) {
    for (const auto& mie : cfg::InstructionIterable(m_code->cfg())) {
      if (mie.insn->opcode() == op && n-- == 0) {
        return mie.insn;
      }
    }
    not_reached();
  }

  const ptrs::FieldAccess& access(const ptrs::ConstructorAccesses& accesses,
                                  const IRInstruction* insn) {
    auto it = accesses.field_accesses().find(insn);
    always_assert(it != accesses.field_accesses().end());
    return it->second;
  }

  DexClass* m_cls{nullptr};
  std::unique_ptr<IRCode> m_code;
};

TEST_F(ConstructorAccessesTest, CopiesOfThisKeepTheirIdentity) {
  code(R"(
    (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
    (move-object v3 v0)
    (iput v1 v3 "LFoo;.a:I")
    (check-cast v0 "LFoo;")
    (move-result-pseudo-object v4)
    (iget v4 "LFoo;.b:I")
    (move-result-pseudo v5)
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_EQ(access(accesses, nth(OPCODE_IPUT)).receiver, ptrs::Receiver::This);
  EXPECT_EQ(access(accesses, nth(OPCODE_IGET)).receiver, ptrs::Receiver::This);
  EXPECT_FALSE(access(accesses, nth(OPCODE_IPUT)).after_escape);
  EXPECT_FALSE(accesses.is_escape(nth(OPCODE_INVOKE_DIRECT)));
}

TEST_F(ConstructorAccessesTest, ReceiversAreThisMaybeThisOrOther) {
  code(R"(
    (iput v1 v2 "LFoo;.a:I")
    (move-object v3 v2)
    (if-eqz v1 :other)
    (move-object v3 v0)
    (:other)
    (iput v1 v3 "LFoo;.b:I")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_EQ(access(accesses, nth(OPCODE_IPUT, 0)).receiver,
            ptrs::Receiver::Other);
  EXPECT_EQ(access(accesses, nth(OPCODE_IPUT, 1)).receiver,
            ptrs::Receiver::MaybeThis);
}

TEST_F(ConstructorAccessesTest, OnlyTheClassesOwnFieldsAreAccesses) {
  DexField::make_field("LBar;.c:I")->make_concrete(ACC_PUBLIC);
  code(R"(
    (iput v1 v2 "LBar;.c:I")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_TRUE(accesses.field_accesses().empty());
}

TEST_F(ConstructorAccessesTest, CallReceivingThisIsAnEscape) {
  code(R"(
    (iput v1 v0 "LFoo;.a:I")
    (invoke-static (v0) "LHelper;.use:(LFoo;)V")
    (iput v1 v0 "LFoo;.b:I")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_TRUE(accesses.is_escape(nth(OPCODE_INVOKE_STATIC)));
  EXPECT_FALSE(access(accesses, nth(OPCODE_IPUT, 0)).after_escape);
  EXPECT_TRUE(access(accesses, nth(OPCODE_IPUT, 1)).after_escape);
  EXPECT_EQ(access(accesses, nth(OPCODE_IPUT, 1)).receiver,
            ptrs::Receiver::This);
}

TEST_F(ConstructorAccessesTest, CopyOfThisThatEscapesIsAnEscape) {
  // A type test, a null check and a monitor on `this` let nothing escape,
  // but a copy made by a move or a cast escapes like `this` itself.
  for (const auto* copy : {R"((move-object v3 v0))",
                           R"((check-cast v0 "LFoo;")
                              (move-result-pseudo-object v3))"}) {
    code(std::string(R"(
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (instance-of v0 "LFoo;")
      (move-result-pseudo v4)
      (if-eqz v0 :skip)
      (:skip)
      (monitor-enter v0)
      (monitor-exit v0)
      (iput v1 v0 "LFoo;.a:I")
    )") + copy +
         R"(
      (invoke-static (v3) "LHelper;.use:(LFoo;)V")
      (iput v1 v0 "LFoo;.b:I")
      (return-void)
    )");
    ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
    EXPECT_FALSE(access(accesses, nth(OPCODE_IPUT, 0)).after_escape) << copy;
    EXPECT_TRUE(accesses.is_escape(nth(OPCODE_INVOKE_STATIC))) << copy;
    EXPECT_TRUE(access(accesses, nth(OPCODE_IPUT, 1)).after_escape) << copy;
  }
}

TEST_F(ConstructorAccessesTest, CallOfOwnMethodOnThisIsAnEscape) {
  for (const auto* call : {R"((invoke-direct (v0) "LFoo;.helper:()V"))",
                           R"((invoke-virtual (v0) "LFoo;.hook:()V"))"}) {
    code(std::string(call) + R"(
      (iput v1 v0 "LFoo;.a:I")
      (return-void)
    )");
    ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
    EXPECT_TRUE(access(accesses, nth(OPCODE_IPUT)).after_escape) << call;
  }
}

TEST_F(ConstructorAccessesTest, LoopEnteredEscapedStartsWithAnEscape) {
  code(R"(
    (:loop)
    (iput v1 v0 "LFoo;.a:I")
    (invoke-static (v0) "LHelper;.use:(LFoo;)V")
    (if-eqz v1 :loop)
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_TRUE(accesses.is_escape(nth(OPCODE_IPUT)));
  EXPECT_TRUE(access(accesses, nth(OPCODE_IPUT)).after_escape);
}

TEST_F(ConstructorAccessesTest, OnlyOwnConstructorCallsOnThisAreRecorded) {
  code(R"(
    (invoke-direct (v0) "LBase;.<init>:()V")
    (new-instance "LFoo;")
    (move-result-pseudo-object v3)
    (invoke-direct (v3 v1 v2) "LFoo;.<init>:(ILFoo;)V")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  const auto* super_call = nth(OPCODE_INVOKE_DIRECT, 0);
  EXPECT_EQ(accesses.get_delegating_call(super_call), nullptr);
  EXPECT_EQ(accesses.get_delegating_call(nth(OPCODE_INVOKE_DIRECT, 1)),
            nullptr);
  EXPECT_TRUE(accesses.is_escape(super_call));
}

TEST_F(ConstructorAccessesTest, ConstructorKeepingItsReceiverIsNoEscape) {
  code(R"(
    (invoke-direct (v0) "LBase;.<init>:()V")
    (iput v1 v0 "LFoo;.a:I")
    (return-void)
  )");
  const auto* super_call = nth(OPCODE_INVOKE_DIRECT);
  const UnorderedSet<const DexMethod*> keeping{
      DexMethod::make_method("LBase;.<init>:()V")
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false)};
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, keeping);
  EXPECT_FALSE(accesses.is_escape(super_call));
  EXPECT_TRUE(accesses.keeps_this());
  EXPECT_FALSE(access(accesses, nth(OPCODE_IPUT)).after_escape);
}

TEST_F(ConstructorAccessesTest, ConstructorsKeepingThis) {
  // `Base()` keeps `this`. `Foo(int)` calls it and then lets `this` escape,
  // and so does `Foo()`, which calls `Foo(int)`. `Foo(Foo)` calls `Base()` and
  // keeps `this`, and so does `Foo(Foo, int)`, which calls `Foo(Foo)`.
  auto* base_cls = type_class(DexType::make_type("LBase;"));
  auto* base_ctor = assembler::method_from_string(R"(
    (method (public constructor) "LBase;.<init>:()V"
     ((load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)))
  )");
  base_cls->add_method(base_ctor);
  auto* escaping = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(I)V"
     ((load-param-object v0) (load-param v1)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (invoke-static (v0) "LHelper;.use:(LFoo;)V")
      (return-void)))
  )");
  auto* delegating = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:()V"
     ((load-param-object v0)
      (const v1 0)
      (invoke-direct (v0 v1) "LFoo;.<init>:(I)V")
      (return-void)))
  )");
  m_cls->add_field(
      DexField::make_field("LFoo;.other:LFoo;")->make_concrete(ACC_PUBLIC));
  auto* keeping = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LFoo;)V"
     ((load-param-object v0) (load-param-object v1)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (iput-object v1 v0 "LFoo;.other:LFoo;")
      (return-void)))
  )");
  auto* delegating_to_keeping = assembler::method_from_string(R"(
    (method (public constructor) "LFoo;.<init>:(LFoo;I)V"
     ((load-param-object v0) (load-param-object v1) (load-param v2)
      (invoke-direct (v0 v1) "LFoo;.<init>:(LFoo;)V")
      (return-void)))
  )");
  for (auto* method : {escaping, delegating, keeping, delegating_to_keeping}) {
    m_cls->add_method(method);
  }
  for (auto* method :
       {base_ctor, escaping, delegating, keeping, delegating_to_keeping}) {
    method->get_code()->build_cfg();
  }
  const auto result =
      ptrs::get_constructors_keeping_this(Scope{m_cls, base_cls});
  EXPECT_EQ(result.count(base_ctor), 1u);
  EXPECT_EQ(result.count(keeping), 1u);
  EXPECT_EQ(result.count(escaping), 0u);
  EXPECT_EQ(result.count(delegating), 0u);
  EXPECT_EQ(result.count(delegating_to_keeping), 1u);

  // A constructor of a subclass that calls `Base()` directly, as Redex's
  // constructor inlining leaves it, keeps `this` too.
  ClassCreator leaf_creator(DexType::make_type("LLeaf;"));
  leaf_creator.set_super(m_cls->get_type());
  auto* leaf_ctor = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:()V"
     ((load-param-object v0)
      (invoke-direct (v0) "LBase;.<init>:()V")
      (return-void)))
  )");
  leaf_creator.add_method(leaf_ctor);
  auto* leaf_cls = leaf_creator.create();
  leaf_ctor->get_code()->build_cfg();
  EXPECT_EQ(
      ptrs::get_constructors_keeping_this(Scope{m_cls, base_cls, leaf_cls})
          .count(leaf_ctor),
      1u);

  // A constructor excluded from optimization may run other code than it
  // shows.
  base_ctor->rstate.set_no_optimizations();
  const auto excluded =
      ptrs::get_constructors_keeping_this(Scope{m_cls, base_cls});
  EXPECT_EQ(excluded.count(base_ctor), 0u);
  EXPECT_EQ(excluded.count(keeping), 0u);
}

TEST_F(ConstructorAccessesTest, AncestorProofCrossesAClassOutsideTheScope) {
  // `LLeaf;` extends `LMid;`, which extends `LTop;`, and `Leaf()` calls
  // `Top()` directly. `LMid;` is not in the scope, but `Top()` still has to be
  // analyzed before `Leaf()`.
  ClassCreator top(DexType::make_type("LTop;"));
  top.set_super(type::java_lang_Object());
  top.add_method(assembler::method_from_string(R"(
    (method (public constructor) "LTop;.<init>:()V"
     ((load-param-object v0)
      (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
      (return-void)))
  )"));
  auto* top_cls = top.create();
  ClassCreator mid(DexType::make_type("LMid;"));
  mid.set_super(top_cls->get_type());
  mid.create();
  ClassCreator leaf(DexType::make_type("LLeaf;"));
  leaf.set_super(DexType::make_type("LMid;"));
  auto* leaf_ctor = assembler::method_from_string(R"(
    (method (public constructor) "LLeaf;.<init>:()V"
     ((load-param-object v0)
      (invoke-direct (v0) "LTop;.<init>:()V")
      (return-void)))
  )");
  leaf.add_method(leaf_ctor);
  auto* leaf_cls = leaf.create();
  const Scope scope{leaf_cls, top_cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
  EXPECT_EQ(ptrs::get_constructors_keeping_this(scope).count(leaf_ctor), 1u);
  walk::code(scope, [](DexMethod*, IRCode& code) { code.clear_cfg(); });
}

TEST_F(ConstructorAccessesTest, AccessToASubclassFieldDoesNotKeepThis) {
  // A superclass constructor that casts `this` down to `Foo` and writes or
  // reads `Foo.a` does not keep `this`, though `this` never escapes.
  auto* base_cls = type_class(DexType::make_type("LBase;"));
  for (const auto* access : {"(iput v1 v2 \"LFoo;.a:I\")",
                             "(iget v2 \"LFoo;.a:I\") "
                             "(move-result-pseudo v1)"}) {
    m_code = assembler::ircode_from_string(
        std::string("((load-param-object v0) "
                    "(invoke-direct (v0) \"Ljava/lang/Object;.<init>:()V\") "
                    "(const v1 5) (check-cast v0 \"LFoo;\") "
                    "(move-result-pseudo-object v2) ") +
        access + " (return-void))");
    m_code->build_cfg();
    ptrs::ConstructorAccesses accesses(m_code->cfg(), base_cls, {});
    EXPECT_FALSE(accesses.keeps_this()) << access;
  }
}

TEST_F(ConstructorAccessesTest,
       UnresolvedFieldOfTheClassOrAnAncestorKeepsThis) {
  // Nothing declares `Foo.missing` or `Base.missing`. Either reference can
  // only resolve to a field of `Foo` or one of its ancestors, never to a
  // subclass's field.
  code(R"(
    (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
    (iput v1 v0 "LFoo;.missing:I")
    (iget v0 "LBase;.missing:I")
    (move-result-pseudo v3)
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_TRUE(accesses.keeps_this());
}

TEST_F(ConstructorAccessesTest, UnresolvedFieldOfASubclassDoesNotKeepThis) {
  // `Base()` casts `this` down to `Foo` and writes `Foo.missing`, which may
  // resolve to a field of `Foo` at runtime.
  auto* base_cls = type_class(DexType::make_type("LBase;"));
  m_code = assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
     (const v1 5)
     (check-cast v0 "LFoo;")
     (move-result-pseudo-object v2)
     (iput v1 v2 "LFoo;.missing:I")
     (return-void))
  )");
  m_code->build_cfg();
  ptrs::ConstructorAccesses accesses(m_code->cfg(), base_cls, {});
  EXPECT_FALSE(accesses.keeps_this());
}

TEST_F(ConstructorAccessesTest, AccessToAnInheritedFieldKeepsThis) {
  // `Foo` accesses `Base.c`, a field it inherits.
  DexField::make_field("LBase;.c:I")->make_concrete(ACC_PUBLIC);
  code(R"(
    (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
    (iput v1 v0 "LBase;.c:I")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  EXPECT_TRUE(accesses.keeps_this());
}

TEST_F(ConstructorAccessesTest, CallOfOwnConstructorDelegates) {
  code(R"(
    (invoke-direct (v0) "LFoo;.<init>:()V")
    (return-void)
  )");
  ptrs::ConstructorAccesses accesses(m_code->cfg(), m_cls, {});
  const auto* call = nth(OPCODE_INVOKE_DIRECT);
  const auto* delegating = accesses.get_delegating_call(call);
  ASSERT_NE(delegating, nullptr);
  EXPECT_EQ(delegating->callee, call->get_method());
  EXPECT_EQ(delegating->receiver, ptrs::Receiver::This);
  EXPECT_FALSE(delegating->after_escape);
}
