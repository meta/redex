/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagation.h"

#include <algorithm>

#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
#include "IPConstantPropagationAnalysis.h"

#include "MethodUtil.h"
#include "ScopedCFG.h"
#include "Trace.h"
#include "Walkers.h"

namespace constant_propagation {

Transform::Stats ConstantPropagation::run_method(
    DexMethod* method,
    const XStoreRefs* xstores,
    const NullCheckMethods& state,
    const ClassConstructorFields* constructor_fields) {
  if (!method::is_optimizable(method)) {
    return Transform::Stats();
  }
  TRACE(CONSTP, 2, "Method: %s", SHOW(method));
  auto* code = method->get_code();
  cfg::ScopedCFG cfg(code);

  TRACE(CONSTP, 5, "CFG: %s", SHOW(*cfg));
  // Seed the parameters: an instance method's receiver is non-null.
  auto env = interprocedural::env_with_params(
      is_static(method), code, interprocedural::ArgumentDomain::top());
  Transform::Config transform_config(m_config.transform);
  InstructionAnalyzer<ConstantEnvironment> analyzer =
      ConstantPrimitiveAnalyzer();
  if (constructor_fields != nullptr && method::is_init(method)) {
    const auto* fields = &constructor_fields->constructors.at(method);
    constructor_fields->initialize_fields(method, fields->tracked_fields(),
                                          &env);
    analyzer = InstructionAnalyzerCombiner<ConstructorFieldAnalyzer,
                                           PrimitiveAnalyzer>(fields, nullptr);
    transform_config.constructor_fields = fields;
  }
  Transform::Stats local_stats;
  {
    intraprocedural::FixpointIterator fp_iter(
        *cfg, analyzer,
        intraprocedural::make_default_no_throw_analyzer(&state));
    fp_iter.run(env);
    constant_propagation::Transform tf(transform_config, state);
    tf.apply(fp_iter, WholeProgramState(), code->cfg(), xstores,
             is_static(method), method->get_class(), method->get_proto());
    local_stats = tf.get_stats();
  }
  return local_stats;
}

Transform::Stats ConstantPropagation::run(const Scope& scope,
                                          const XStoreRefs* xstores,
                                          const NullCheckMethods& state) {
  if (!m_config.track_constructor_fields) {
    return walk::parallel::methods<Transform::Stats>(
        scope, [&](DexMethod* method) {
          return run_method(method, xstores, state, nullptr);
        });
  }
  // Whether a constructor starts with its fields zero depends on the class's
  // other constructors, so each class is analyzed as a unit, before any of its
  // methods change.
  return walk::parallel::classes<Transform::Stats>(scope, [&](DexClass* cls) {
    const auto& ctors = cls->get_ctors();
    std::optional<ClassConstructorFields> constructor_fields;
    if (std::any_of(ctors.begin(), ctors.end(), method::is_optimizable)) {
      constructor_fields = ClassConstructorFields::create(cls, {});
    }
    Transform::Stats stats;
    for (auto* method : cls->get_all_methods()) {
      stats += run_method(method, xstores, state,
                          constructor_fields ? &*constructor_fields : nullptr);
    }
    return stats;
  });
}
} // namespace constant_propagation
