/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

class DexMethodRef;
class DexProto;
struct RedexContext;

/*
 * The two references of an `invoke-polymorphic` instruction: the
 * signature-polymorphic method it names, and the prototype of the call site.
 *
 * The method's declared prototype says nothing about the call. For
 *
 *   long start = (long) NOW.invokeExact(42);
 *
 * javac names
 * `MethodHandle.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;` and
 * records the call-site prototype `(I)J`, which gives the types of the
 * arguments after the receiver and of the result.
 *
 * Instances are interned: equal pairs are the same object.
 */
class DexSignaturePolymorphicRef {
  friend struct RedexContext;

  DexMethodRef* m_method;
  DexProto* m_callsite_proto;

  DexSignaturePolymorphicRef(DexMethodRef* method, DexProto* callsite_proto)
      : m_method(method), m_callsite_proto(callsite_proto) {}

 public:
  DexSignaturePolymorphicRef(const DexSignaturePolymorphicRef&) = delete;
  DexSignaturePolymorphicRef(DexSignaturePolymorphicRef&&) = delete;
  DexSignaturePolymorphicRef& operator=(const DexSignaturePolymorphicRef&) =
      delete;
  DexSignaturePolymorphicRef& operator=(DexSignaturePolymorphicRef&&) = delete;
  ~DexSignaturePolymorphicRef() = default;

  static DexSignaturePolymorphicRef* make(DexMethodRef* method,
                                          DexProto* callsite_proto);

  DexMethodRef* method() const { return m_method; }
  DexProto* callsite_proto() const { return m_callsite_proto; }
};
