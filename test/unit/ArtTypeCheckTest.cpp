/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <string>

#include "ArtTypeCheck.h"
#include "IRAssembler.h"
#include "RedexTest.h"

namespace mt = method_splitting_test;

namespace {

class ArtTypeCheckTest : public RedexTest {};

std::string violations(const std::string& method_sexpr) {
  auto* m = assembler::method_from_string(method_sexpr);
  m->get_code()->build_cfg();
  return mt::describeArtTypeViolations({m});
}

// The violations in a host and the split it calls, judged together.
std::string violations(const std::string& host_sexpr,
                       const std::string& split_sexpr) {
  auto* split = assembler::method_from_string(split_sexpr);
  auto* host = assembler::method_from_string(host_sexpr);
  split->get_code()->build_cfg();
  host->get_code()->build_cfg();
  return mt::describeArtTypeViolations({host, split});
}

// A boolean merged with the constant 2 is a byte to ART, which a `char`
// parameter rejects. A char merged with 40000 stays a char.
TEST_F(ArtTypeCheckTest, MergedArgumentIsJudgedByItsMerge) {
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(Z)V" (
        (load-param v0)
        (if-eqz v0 :two)
        (move v1 v0)
        (goto :call)
        (:two)
        (const v1 2)
        (:call)
        (invoke-static (v1) "LFoo;.takeChar:(C)V")
        (return-void)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.good:(C)V" (
        (load-param v0)
        (if-eqz v0 :big)
        (move v1 v0)
        (goto :call)
        (:big)
        (const v1 40000)
        (:call)
        (invoke-static (v1) "LFoo;.takeChar:(C)V")
        (return-void)
      )))"),
            "");
}

// A `boolean`, a `char` and the constant 2 reach one register. Merging the
// `char` with 2 first gives `char`, and then with the boolean still `char`, but
// merging the boolean with 2 first gives `byte`, which the `char` takes to
// `int`. ART merges in the order it visits the paths, so the register is
// judged in every order, and a `(C)` call rejects it.
TEST_F(ArtTypeCheckTest, EveryMergeOrderIsJudged) {
  EXPECT_EQ(
      violations(R"(
      (method (public static) "LFoo;.bad:(ZCI)V" (
        (load-param v0)
        (load-param v1)
        (load-param v2)
        (move v3 v0)
        (if-eqz v2 :call)
        (move v3 v1)
        (if-ltz v2 :call)
        (const v3 2)
        (:call)
        (invoke-static (v3) "LFoo;.takeChar:(C)V")
        (return-void)
      )))"),
      "LFoo;.bad:(ZCI)V: INVOKE_STATIC v3, LFoo;.takeChar:(C)V: argument "
      "0 may be boolean | byte | char | int | const 2..127, needs char\n");
}

// ART's `return` accepts what a call argument would, and also an `int` where
// a narrower integral type is declared and a `byte` where a `boolean` is.
TEST_F(ArtTypeCheckTest, ReturnAcceptsWhatArtAccepts) {
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(B)C" (
        (load-param v0)
        (return v0)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(S)Z" (
        (load-param v0)
        (return v0)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(I)C" (
        (load-param v0)
        (return v0)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(B)Z" (
        (load-param v0)
        (return v0)
      )))"),
            "");
}

// ART types the result of a division or a remainder as `int`. In Redex IR the
// result arrives through `move-result-pseudo`, because the instruction may
// throw.
TEST_F(ArtTypeCheckTest, DivisionAndRemainderResultsAreInt) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(II)V" (
        (load-param v0)
        (load-param v1)
        (div-int v0 v1)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.takeInt:(I)V")
        (rem-int v0 v1)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.takeInt:(I)V")
        (div-int/lit v0 3)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.takeInt:(I)V")
        (rem-int/lit v0 3)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.takeInt:(I)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(II)V" (
        (load-param v0)
        (load-param v1)
        (div-int v0 v1)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.takeChar:(C)V")
        (return-void)
      )))"),
            "");
}

// A primitive put accepts any integral value.
TEST_F(ArtTypeCheckTest, PrimitivePutAcceptsAnyIntegralValue) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(I)V" (
        (load-param v0)
        (sput-char v0 "LFoo;.c:C")
        (sput-boolean v0 "LFoo;.z:Z")
        (return-void)
      )))"),
            "");
}

// A constant serves as an `int` or a `float`, but an `int` and a `float` value
// do not stand in for each other.
TEST_F(ArtTypeCheckTest, IntAndFloatAreDistinct) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(IF)V" (
        (load-param v0)
        (load-param v1)
        (const v2 7)
        (invoke-static (v2 v2) "LFoo;.take:(IF)V")
        (invoke-static (v0 v1) "LFoo;.take:(IF)V")
        (return-void)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.bad:(IF)V" (
        (load-param v0)
        (load-param v1)
        (invoke-static (v1 v0) "LFoo;.take:(IF)V")
        (return-void)
      )))"),
            "LFoo;.bad:(IF)V: INVOKE_STATIC v1, v0, LFoo;.take:(IF)V: argument "
            "0 may be float, needs int\nLFoo;.bad:(IF)V: INVOKE_STATIC v1, v0, "
            "LFoo;.take:(IF)V: argument 1 may be int, needs float\n");
}

// A wide constant serves as a `long` or a `double`, but a `long` and a
// `double` value do not stand in for each other.
TEST_F(ArtTypeCheckTest, LongAndDoubleAreDistinct) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(J)V" (
        (load-param-wide v0)
        (const-wide v2 7)
        (invoke-static (v2) "LFoo;.take:(D)V")
        (invoke-static (v0) "LFoo;.take:(J)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(J)V" (
        (load-param-wide v0)
        (invoke-static (v0) "LFoo;.take:(D)V")
        (return-void)
      )))"),
            "");
}

// Zero serves as a reference; no other integral value does, and a reference
// is no integral value.
TEST_F(ArtTypeCheckTest, ReferencesAreDistinctFromIntegralValues) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (const v1 0)
        (invoke-static (v1) "LFoo;.take:(Ljava/lang/Object;)V")
        (invoke-static (v0) "LFoo;.take:(Ljava/lang/Object;)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (const v1 1)
        (invoke-static (v1) "LFoo;.take:(Ljava/lang/Object;)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (invoke-static (v0) "LFoo;.take:(I)V")
        (return-void)
      )))"),
            "");
}

// A register that one path leaves undefined is undefined after the paths
// meet, and an int merged with a reference is a conflict: ART rejects a use of
// either.
TEST_F(ArtTypeCheckTest, UndefinedAndConflictingRegistersAreRejected) {
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(I)V" (
        (load-param v0)
        (if-eqz v0 :call)
        (const v1 3)
        (:call)
        (invoke-static (v1) "LFoo;.take:(I)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(ILjava/lang/Object;)V" (
        (load-param v0)
        (load-param-object v1)
        (move v2 v0)
        (if-eqz v0 :call)
        (move-object v2 v1)
        (:call)
        (invoke-static (v2) "LFoo;.take:(I)V")
        (return-void)
      )))"),
            "");
}

// An `aget` reads the array's element type: a `float[]` gives a `float`.
TEST_F(ArtTypeCheckTest, ArrayElementTypeComesFromTheArray) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:([FI)V" (
        (load-param-object v0)
        (load-param v1)
        (aget v0 v1)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.take:(F)V")
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:([FI)V" (
        (load-param-object v0)
        (load-param v1)
        (aget v0 v1)
        (move-result-pseudo v2)
        (invoke-static (v2) "LFoo;.take:(I)V")
        (return-void)
      )))"),
            "");
}

// A register that may hold a `float[]` or an `int[]` gives an element of
// either type, so a `(I)` call rejects it, as ART does on the path through the
// `float[]`.
TEST_F(ArtTypeCheckTest, EachArrayARegisterMayHoldIsJudged) {
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:([F[II)V" (
        (load-param-object v0)
        (load-param-object v1)
        (load-param v2)
        (move-object v3 v0)
        (if-eqz v2 :get)
        (move-object v3 v1)
        (:get)
        (aget v3 v2)
        (move-result-pseudo v4)
        (invoke-static (v4) "LFoo;.take:(I)V")
        (return-void)
      )))"),
            "");
}

// A field or array access must match the type it accesses, and so must a
// `return`.
TEST_F(ArtTypeCheckTest, AccessesAndReturnsMustMatchTheirType) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:([FI)F" (
        (load-param-object v0)
        (load-param v1)
        (sget "LFoo;.f:F")
        (move-result-pseudo v2)
        (aput v2 v0 v1)
        (return v2)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:()V" (
        (sget-boolean "LFoo;.i:I")
        (move-result-pseudo v0)
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:([II)V" (
        (load-param-object v0)
        (load-param v1)
        (aget-char v0 v1)
        (move-result-pseudo v2)
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(Ljava/lang/Object;)I" (
        (load-param-object v0)
        (return-object v0)
      )))"),
            "");
}

// A `move` copies an int or a float, a `move-object` a reference, and
// `if-eq` compares two integral values or two references.
TEST_F(ArtTypeCheckTest, MovesAndComparisonsCheckCategories) {
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (move v1 v0)
        (return-void)
      )))"),
            "");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:(ILjava/lang/Object;)V" (
        (load-param v0)
        (load-param-object v1)
        (if-eq v0 v1 :end)
        (:end)
        (return-void)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (const v1 0)
        (if-eq v0 v1 :end)
        (:end)
        (return-void)
      )))"),
            "");
}

// Only an integral constant serves as a `float`; a reference does not, and
// neither does a register no path defines.
TEST_F(ArtTypeCheckTest, OnlyAConstantStandsInForAFloat) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.bad:(Ljava/lang/Object;)V" (
        (load-param-object v0)
        (invoke-static (v0) "LFoo;.take:(F)V")
        (return-void)
      )))"),
            "LFoo;.bad:(Ljava/lang/Object;)V: INVOKE_STATIC v0, "
            "LFoo;.take:(F)V: argument 0 may be a reference, needs float\n");
  EXPECT_NE(violations(R"(
      (method (public static) "LFoo;.bad:()V" (
        (invoke-static (v1) "LFoo;.take:(F)V")
        (return-void)
      )))"),
            "");
}

// Method splitting must not move a constructor call out of the method that
// allocated the object. Here the cold arm, with the `<init>`, went to a split,
// which takes the object while it is still uninitialized. ART rejects the
// call: a parameter is declared with an initialized type. Keeping the `<init>`
// before the branch makes the same split valid.
TEST_F(ArtTypeCheckTest, SplitTakingAnUninitializedObjectIsRejected) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.host:(I)V" (
        (load-param v0)
        (new-instance "LBar;")
        (move-result-pseudo-object v1)
        (if-eqz v0 :cold)
        (invoke-direct (v1) "LBar;.<init>:()V")
        (invoke-static (v1) "LFoo;.use:(LBar;)V")
        (return-void)
        (:cold)
        (invoke-static (v1) "LFoo;.host$split:(LBar;)V")
        (return-void)
      )))",
                       R"(
      (method (public static) "LFoo;.host$split:(LBar;)V" (
        (load-param-object v0)
        (invoke-direct (v0) "LBar;.<init>:()V")
        (invoke-static (v0) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "LFoo;.host:(I)V: INVOKE_STATIC v1, LFoo;.host$split:(LBar;)V: "
            "argument 0 may be an uninitialized object, which crosses the "
            "boundary of the split LFoo;.host$split:(LBar;)V\n");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.host2:(I)V" (
        (load-param v0)
        (new-instance "LBar;")
        (move-result-pseudo-object v1)
        (invoke-direct (v1) "LBar;.<init>:()V")
        (if-eqz v0 :cold)
        (invoke-static (v1) "LFoo;.use:(LBar;)V")
        (return-void)
        (:cold)
        (invoke-static (v1) "LFoo;.host2$split:(LBar;)V")
        (return-void)
      )))",
                       R"(
      (method (public static) "LFoo;.host2$split:(LBar;)V" (
        (load-param-object v0)
        (invoke-static (v0) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "");
}

// The constructor runs on one path only, so after the paths meet the register
// holds the object initialized on one and uninitialized on the other, which
// ART merges into a conflict. A constructor on both paths, through either
// copy of the object, initializes it on both.
TEST_F(ArtTypeCheckTest, ObjectUninitializedOnOnePathIsUnusableAfterTheJoin) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.bad:(I)V" (
        (load-param v0)
        (new-instance "LBar;")
        (move-result-pseudo-object v1)
        (if-eqz v0 :join)
        (invoke-direct (v1) "LBar;.<init>:()V")
        (:join)
        (invoke-static (v1) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "LFoo;.bad:(I)V: INVOKE_STATIC v1, LFoo;.use:(LBar;)V: argument 0 "
            "may be a reference | an uninitialized object | conflict, needs a "
            "reference\n");
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(I)V" (
        (load-param v0)
        (new-instance "LBar;")
        (move-result-pseudo-object v1)
        (move-object v2 v1)
        (if-eqz v0 :other)
        (invoke-direct (v1) "LBar;.<init>:()V")
        (goto :join)
        (:other)
        (invoke-direct (v2) "LBar;.<init>:()V")
        (:join)
        (invoke-static (v1) "LFoo;.use:(LBar;)V")
        (invoke-static (v2) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "");
}

// A handler sees the registers as they were before the instruction that
// threw. When the constructor throws, the object is still uninitialized in
// the handler, and passing it to a method there is rejected, while the same
// call after the constructor returned is accepted.
TEST_F(ArtTypeCheckTest, HandlerSeesTheObjectUninitializedWhenItsInitThrows) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.bad:()V" (
        (new-instance "LBar;")
        (move-result-pseudo-object v0)
        (.try_start t)
        (invoke-direct (v0) "LBar;.<init>:()V")
        (.try_end t)
        (invoke-static (v0) "LFoo;.use:(LBar;)V")
        (return-void)
        (.catch (t))
        (move-exception v1)
        (invoke-static (v0) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "LFoo;.bad:()V: INVOKE_STATIC v0, LFoo;.use:(LBar;)V: argument 0 "
            "may be an uninitialized object\n");
}

// In a constructor, `this` is uninitialized until it calls another
// constructor. Before that, it may write its own class's fields, but not be
// the receiver of any other call.
TEST_F(ArtTypeCheckTest, ThisIsUninitializedUntilTheSuperclassInit) {
  EXPECT_EQ(violations(R"(
      (method (public constructor) "LFoo;.<init>:(I)V" (
        (load-param-object v0)
        (load-param v1)
        (iput v1 v0 "LFoo;.f:I")
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (invoke-virtual (v0) "LFoo;.run:()V")
        (return-void)
      )))"),
            "");
  EXPECT_EQ(violations(R"(
      (method (public constructor) "LFoo;.<init>:()V" (
        (load-param-object v0)
        (invoke-virtual (v0) "LFoo;.run:()V")
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
      )))"),
            "LFoo;.<init>:()V: INVOKE_VIRTUAL v0, LFoo;.run:()V: the receiver "
            "may be an uninitialized object\n");
}

// ART lets `move` and `move-object` copy a conflict and rejects it only where
// it is used. An int on one path and a float on the other, or an object
// initialized on one path and not on the other, may still be copied.
TEST_F(ArtTypeCheckTest, MovesMayCopyAConflict) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(IF)V" (
        (load-param v0)
        (load-param v1)
        (new-instance "LBar;")
        (move-result-pseudo-object v3)
        (move v2 v0)
        (if-eqz v0 :join)
        (move v2 v1)
        (invoke-direct (v3) "LBar;.<init>:()V")
        (:join)
        (move v4 v2)
        (move-object v5 v3)
        (return-void)
      )))"),
            "");
}

// An uninitialized object may be copied, compared with another reference and
// tested against zero before its constructor runs.
TEST_F(ArtTypeCheckTest, UninitializedObjectMayBeCopiedAndCompared) {
  EXPECT_EQ(violations(R"(
      (method (public static) "LFoo;.ok:(Ljava/lang/Object;)V" (
        (load-param-object v2)
        (new-instance "LBar;")
        (move-result-pseudo-object v0)
        (move-object v1 v0)
        (if-eq v0 v2 :next)
        (:next)
        (if-eqz v1 :init)
        (:init)
        (invoke-direct (v0) "LBar;.<init>:()V")
        (invoke-static (v1) "LFoo;.use:(LBar;)V")
        (return-void)
      )))"),
            "");
}

} // namespace
