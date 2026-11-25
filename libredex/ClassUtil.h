/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexClass.h"

namespace klass {

struct Serdes {
  std::vector<const DexType*> serdes;

  Serdes(const DexType* deser,
         const DexType* flatbuf_deser,
         const DexType* ser,
         const DexType* flatbuf_ser)
      : serdes{deser, flatbuf_deser, ser, flatbuf_ser} {}

  std::vector<const DexType*> get_all_serdes() { return serdes; }

  const DexType* get_deser() { return serdes[0]; }
  const DexType* get_flatbuf_deser() { return serdes[1]; }
  const DexType* get_ser() { return serdes[2]; }
  const DexType* get_flatbuf_ser() { return serdes[3]; }
};

/**
 * Return possible deserializer and serializer classes of the given class
 * 'class$Deserializer;', 'class_Deserializer;', 'class$Serializer;',
 * 'class_Serializer;'
 */
Serdes get_serdes(const DexClass* cls);

/**
 * Looks for a <clinit> method for the given class, creates a new one if it
 * does not exist
 */
DexMethod* get_or_create_clinit(DexClass* cls, bool need_cfg = false);

/**
 * Return true if the parent chain leads to known classes.
 * False if one of the parent is in a scope unknown to redex.
 */
bool has_hierarchy_in_scope(DexClass* cls);

/**
 * Return true if the name matches "$$Lambda$", "$$ExternalSyntheticLambda"
 */
bool maybe_d8_desugared_anonymous_class(const DexClass* cls);

/*
 * Return true if the name matches "$[0-9]".
 */
bool maybe_non_d8_desugared_anonymous_class(const DexClass* cls);

/**
 * Return true if it is either a d8-desugared or non-d8-desugared anonymous
 * class.
 */
bool maybe_anonymous_class(const DexClass* cls);

/**
 * Whether the runtime may create instances of the interface without a class
 * in the input implementing it: a java.lang.reflect.Proxy class for it, or the
 * implementation of an annotation. Keep rules mark the interfaces a proxy may
 * be created for: they keep the interface or one of its methods, or do not
 * allow renaming them.
 */
bool may_be_instantiated_at_runtime(const DexClass* intf);

}; // namespace klass
