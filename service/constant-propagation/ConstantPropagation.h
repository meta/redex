/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationState.h"
#include "ConstantPropagationTransform.h"
#include "IRCode.h"

namespace constant_propagation {

struct Config {
  Transform::Config transform;
  // In constructors, track the class's own fields from their zero initial
  // values until `this` may escape.
  bool track_constructor_fields{false};
};

class ConstantPropagation final {
 public:
  explicit ConstantPropagation(const Config& config) : m_config(config) {}

  // With `track_constructor_fields`, the constructors of each class are
  // analyzed together, before any of its methods change.
  Transform::Stats run(const Scope& scope,
                       const XStoreRefs* xstores,
                       const NullCheckMethods& state);

 private:
  // `constructor_fields`, when set, analyzes the constructors of `method`'s
  // class.
  Transform::Stats run_method(DexMethod* method,
                              const XStoreRefs* xstores,
                              const NullCheckMethods& state,
                              const ClassConstructorFields* constructor_fields);

  const Config& m_config;
};
} // namespace constant_propagation
