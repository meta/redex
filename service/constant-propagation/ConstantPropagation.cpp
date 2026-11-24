/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagation.h"

#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
#include "IPConstantPropagationAnalysis.h"

#include "MethodUtil.h"
#include "ScopedCFG.h"
#include "Trace.h"
#include "Walkers.h"

namespace constant_propagation {

Transform::Stats ConstantPropagation::run(DexMethod* method,
                                          const XStoreRefs* xstores,
                                          const NullCheckMethods& state) {
  if (!method::is_optimizable(method)) {
    return Transform::Stats();
  }
  TRACE(CONSTP, 2, "Method: %s", SHOW(method));
  auto* code = method->get_code();
  cfg::ScopedCFG cfg(code);

  TRACE(CONSTP, 5, "CFG: %s", SHOW(*cfg));
  Transform::Stats local_stats;
  {
    intraprocedural::FixpointIterator fp_iter(
        *cfg, ConstantPrimitiveAnalyzer(),
        intraprocedural::make_default_no_throw_analyzer(&state));
    // Seed the parameters: an instance method's receiver is non-null.
    fp_iter.run(interprocedural::env_with_params(
        is_static(method), code, interprocedural::ArgumentDomain::top()));
    constant_propagation::Transform tf(m_config.transform, state);
    tf.apply(fp_iter, WholeProgramState(), code->cfg(), xstores,
             is_static(method), method->get_class(), method->get_proto());
    local_stats = tf.get_stats();
  }
  return local_stats;
}

Transform::Stats ConstantPropagation::run(const Scope& scope,
                                          const XStoreRefs* xstores,
                                          const NullCheckMethods& state) {
  return walk::parallel::methods<Transform::Stats>(
      scope, [&](DexMethod* method) { return run(method, xstores, state); });
}
} // namespace constant_propagation
