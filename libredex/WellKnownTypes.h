/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

// (name, java_name)
#define WELL_KNOWN_TYPES                                                 \
  FOR_EACH(_void, "V")                                                   \
  FOR_EACH(_byte, "B")                                                   \
  FOR_EACH(_char, "C")                                                   \
  FOR_EACH(_short, "S")                                                  \
  FOR_EACH(_int, "I")                                                    \
  FOR_EACH(_long, "J")                                                   \
  FOR_EACH(_boolean, "Z")                                                \
  FOR_EACH(_float, "F")                                                  \
  FOR_EACH(_double, "D")                                                 \
  FOR_EACH(java_lang_String, "Ljava/lang/String;")                       \
  FOR_EACH(java_lang_Class, "Ljava/lang/Class;")                         \
  FOR_EACH(java_lang_Enum, "Ljava/lang/Enum;")                           \
  FOR_EACH(java_lang_Object, "Ljava/lang/Object;")                       \
  FOR_EACH(java_lang_Void, "Ljava/lang/Void;")                           \
  FOR_EACH(java_lang_Throwable, "Ljava/lang/Throwable;")                 \
  FOR_EACH(java_lang_Boolean, "Ljava/lang/Boolean;")                     \
  FOR_EACH(java_lang_Byte, "Ljava/lang/Byte;")                           \
  FOR_EACH(java_lang_Short, "Ljava/lang/Short;")                         \
  FOR_EACH(java_lang_Character, "Ljava/lang/Character;")                 \
  FOR_EACH(java_lang_Integer, "Ljava/lang/Integer;")                     \
  FOR_EACH(java_lang_Long, "Ljava/lang/Long;")                           \
  FOR_EACH(java_lang_Float, "Ljava/lang/Float;")                         \
  FOR_EACH(java_lang_Double, "Ljava/lang/Double;")                       \
  FOR_EACH(java_lang_RuntimeException, "Ljava/lang/RuntimeException;")   \
  FOR_EACH(dalvik_annotation_Signature, "Ldalvik/annotation/Signature;") \
  FOR_EACH(dalvik_annotation_EnclosingClass,                             \
           "Ldalvik/annotation/EnclosingClass;")                         \
  FOR_EACH(dalvik_annotation_EnclosingMethod,                            \
           "Ldalvik/annotation/EnclosingMethod;")                        \
  FOR_EACH(dalvik_annotation_InnerClass,                                 \
           "Ldalvik/annotation/"                                         \
           "InnerClass;")                                                \
  FOR_EACH(dalvik_annotation_MemberClasses,                              \
           "Ldalvik/annotation/"                                         \
           "MemberClasses;")                                             \
  FOR_EACH(dalvik_annotation_optimization_NeverCompile,                  \
           "Ldalvik/annotation/optimization/NeverCompile;")              \
  FOR_EACH(dalvik_annotation_optimization_NeverInline,                   \
           "Ldalvik/annotation/optimization/NeverInline;")

#define PRIMITIVE_PSEUDO_TYPE_FIELDS                                       \
  FOR_EACH(Void_TYPE, "Ljava/lang/Void;.TYPE:Ljava/lang/Class;")           \
  FOR_EACH(Byte_TYPE, "Ljava/lang/Byte;.TYPE:Ljava/lang/Class;")           \
  FOR_EACH(Character_TYPE, "Ljava/lang/Character;.TYPE:Ljava/lang/Class;") \
  FOR_EACH(Short_TYPE, "Ljava/lang/Short;.TYPE:Ljava/lang/Class;")         \
  FOR_EACH(Integer_TYPE, "Ljava/lang/Integer;.TYPE:Ljava/lang/Class;")     \
  FOR_EACH(Long_TYPE, "Ljava/lang/Long;.TYPE:Ljava/lang/Class;")           \
  FOR_EACH(Boolean_TYPE, "Ljava/lang/Boolean;.TYPE:Ljava/lang/Class;")     \
  FOR_EACH(Float_TYPE, "Ljava/lang/Float;.TYPE:Ljava/lang/Class;")         \
  FOR_EACH(Double_TYPE, "Ljava/lang/Double;.TYPE:Ljava/lang/Class;")

#define WELL_KNOWN_METHODS                                                    \
  FOR_EACH(java_lang_Object_ctor, "Ljava/lang/Object;.<init>:()V")            \
  FOR_EACH(java_lang_Object_finalize, "Ljava/lang/Object;.finalize:()V")      \
  FOR_EACH(java_lang_Object_equals,                                           \
           "Ljava/lang/Object;.equals:(Ljava/lang/Object;)Z")                 \
  FOR_EACH(java_lang_Enum_ctor,                                               \
           "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")                  \
  FOR_EACH(java_lang_Enum_ordinal, "Ljava/lang/Enum;.ordinal:()I")            \
  FOR_EACH(java_lang_Enum_name, "Ljava/lang/Enum;.name:()Ljava/lang/String;") \
  FOR_EACH(java_lang_Enum_equals,                                             \
           "Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z")                   \
  FOR_EACH(java_lang_Integer_valueOf,                                         \
           "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")              \
  FOR_EACH(java_lang_Integer_intValue, "Ljava/lang/Integer;.intValue:()I")    \
  FOR_EACH(java_lang_Throwable_fillInStackTrace,                              \
           "Ljava/lang/Throwable;.fillInStackTrace:()Ljava/lang/"             \
           "Throwable;")                                                      \
  FOR_EACH(java_lang_RuntimeException_init_String,                            \
           "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V")       \
  FOR_EACH(java_lang_String_equals,                                           \
           "Ljava/lang/String;.equals:(Ljava/lang/Object;)Z")                 \
  FOR_EACH(java_lang_String_hashCode, "Ljava/lang/String;.hashCode:()I")      \
  FOR_EACH(java_lang_String_length, "Ljava/lang/String;.length:()I")          \
  FOR_EACH(java_lang_String_isEmpty, "Ljava/lang/String;.isEmpty:()Z")        \
  FOR_EACH(java_lang_String_charAt, "Ljava/lang/String;.charAt:(I)C")         \
  FOR_EACH(java_lang_StringBuilder_append_String,                             \
           "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/" \
           "StringBuilder;")                                                  \
  FOR_EACH(java_lang_StringBuilder_toString,                                  \
           "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")         \
  FOR_EACH(java_lang_Objects_clone,                                           \
           "[Ljava/lang/Object;.clone:()Ljava/lang/Object;")                  \
  FOR_EACH(java_lang_Class_cast,                                              \
           "Ljava/lang/Class;.cast:(Ljava/lang/Object;)Ljava/lang/Object;")   \
  FOR_EACH(java_lang_Class_forName,                                           \
           "Ljava/lang/Class;.forName:(Ljava/lang/String;)Ljava/"             \
           "lang/Class;")                                                     \
  FOR_EACH(java_lang_Class_isInstance,                                        \
           "Ljava/lang/Class;.isInstance:(Ljava/lang/Object;)Z")

#define KOTLIN_JVM_INTERNAL_TYPES                                              \
  FOR_EACH(kotlin_jvm_internal_Lambda, "Lkotlin/jvm/internal/Lambda;")         \
  FOR_EACH(kotlin_jvm_internal_Ref_IntRef, "Lkotlin/jvm/internal/Ref$IntRef;") \
  FOR_EACH(kotlin_jvm_internal_Ref_ObjectRef,                                  \
           "Lkotlin/jvm/internal/Ref$ObjectRef;")                              \
  FOR_EACH(kotlin_coroutines_jvm_internal_ContinuationImpl,                    \
           "Lkotlin/coroutines/jvm/internal/ContinuationImpl;")                \
  FOR_EACH(kotlin_coroutines_jvm_internal_RestrictedSuspendLambda,             \
           "Lkotlin/coroutines/jvm/internal/RestrictedSuspendLambda;")         \
  FOR_EACH(kotlin_coroutines_jvm_internal_SuspendLambda,                       \
           "Lkotlin/coroutines/jvm/internal/SuspendLambda;")

#define KOTLIN_JVM_INTERNAL_FIELDS                       \
  FOR_EACH(kotlin_jvm_internal_RefIntRef_element,        \
           "Lkotlin/jvm/internal/Ref$IntRef;.element:I") \
  FOR_EACH(kotlin_jvm_internal_RefObjectRef_element,     \
           "Lkotlin/jvm/internal/Ref$ObjectRef;.element:Ljava/lang/Object;")
