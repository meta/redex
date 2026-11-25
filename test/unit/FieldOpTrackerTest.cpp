/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DexClass.h"
#include "FieldOpTracker.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Walkers.h"

class FieldOpTrackerTest : public RedexTest {};

// With no TypeLifetimes, object types count as having a lifetime and primitive
// types do not; the int argument that `caller` passes to `set` is primitive.
//
//   class Foo {
//     static int sField;
//     static Object sObject;
//     static void set(int x) { sField = x; }
//     static void setObject(Object o) { sObject = o; }
//     static void caller() { set(1); }
//   }
TEST_F(FieldOpTrackerTest, analyzeWritesWithoutTypeLifetimes) {
  auto* cls = assembler::class_from_string(R"(
    (class (public) "LFoo;"
      (field (public static) "LFoo;.sField:I")
      (field (public static) "LFoo;.sObject:Ljava/lang/Object;")
      (method (public static) "LFoo;.set:(I)V"
        (
          (load-param v0)
          (sput v0 "LFoo;.sField:I")
          (return-void)
        )
      )
      (method (public static) "LFoo;.setObject:(Ljava/lang/Object;)V"
        (
          (load-param-object v0)
          (sput-object v0 "LFoo;.sObject:Ljava/lang/Object;")
          (return-void)
        )
      )
      (method (public static) "LFoo;.caller:()V"
        (
          (const v0 1)
          (invoke-static (v0) "LFoo;.set:(I)V")
          (return-void)
        )
      )
    )
  )");
  Scope scope{cls};
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto field_stats = field_op_tracker::analyze(scope);
  field_op_tracker::FieldWrites field_writes;
  field_op_tracker::analyze_writes(scope, field_stats,
                                   /* type_lifetimes */ nullptr, &field_writes);

  auto* int_field = DexField::get_field("LFoo;.sField:I")->as_def();
  EXPECT_EQ(field_writes.non_zero_written_fields.count(int_field), 1u);
  EXPECT_EQ(field_writes.non_vestigial_objects_written_fields.count(int_field),
            0u);

  auto* object_field =
      DexField::get_field("LFoo;.sObject:Ljava/lang/Object;")->as_def();
  EXPECT_EQ(field_writes.non_zero_written_fields.count(object_field), 1u);
  EXPECT_EQ(
      field_writes.non_vestigial_objects_written_fields.count(object_field),
      1u);
}
