/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "RedexOptions.h"
#include "ShrinkerConfig.h"

// When to consider running constant-propagation to better estimate inlined
// cost. It just takes too much time to run the analysis for large methods.
const size_t MAX_COST_FOR_CONSTANT_PROPAGATION = 5000;

// Maximum size of reduced code to keep for specific call-site. It just takes
// too much memory to retain individual larger reduced code.
const size_t MAX_REDUCED_SIZE = 100;

// Maximum estimated code units of the hot prefix retained when partially
// inlining a callee.
const uint32_t MAX_PARTIALLY_INLINED_CODE_UNITS = 10;

namespace inliner {

enum UnfinalizePerfMode {
  NONE = 0,
  NOT_COLD = 1,
  MAYBE_HOT = 2,
  HOT = 3,
};

/**
 * The global inliner config.
 */
struct InlinerConfig {
  bool delete_non_virtuals{true};
  // inline virtual methods
  bool virtual_inline{true};
  bool true_virtual_inline{false};
  bool relaxed_init_inline{false};
  bool unfinalize_relaxed_init_inline{false};
  bool relaxed_init_inline_maybe_anonymous{false};
  bool strict_throwable_init_inline{false};
  bool throws_inline{false};
  bool throw_after_no_return{false};
  bool enforce_method_size_limit{true};
  // A zero value disables the architecture-specific cap.
  uint64_t armv7_hard_max_instruction_size{0};
  bool multiple_callers{false};
  bool use_call_site_summaries{true};
  bool intermediate_shrinking{false};
  shrinker::ShrinkerConfig shrinker;
  bool shrink_other_methods{true};
  bool unique_inlined_registers{true};
  bool respect_sketchy_methods{true};
  bool debug{false};
  bool check_min_sdk_refs{true};
  bool rewrite_invoke_super{false};
  bool partial_hot_hot_inline{false};

  /*
   * Some versions of ART (5.0.0 - 5.0.2) will fail to verify a method if it
   * is too large. See https://code.google.com/p/android/issues/detail?id=66655.
   *
   * The verifier rounds up to the next power of two, and doesn't support any
   * size greater than 16. See
   * http://androidxref.com/5.0.0_r2/xref/art/compiler/dex/verified_method.cc#107
   */
  uint64_t soft_max_instruction_size{1 << 15};
  // INSTRUCTION_BUFFER is added because the final method size is often larger
  // than our estimate -- during the sync phase, we may have to pick larger
  // branch opcodes to encode large jumps.
  uint64_t instruction_size_buffer{1 << 12};

  // max_cost_for_constant_propagation is maximum size of code
  // we can tolerate when making decision to inline
  size_t max_cost_for_constant_propagation{MAX_COST_FOR_CONSTANT_PROPAGATION};

  // max_reduced_size is maximum size of reduced code to keep for particular
  // callsite.
  size_t max_reduced_size{MAX_REDUCED_SIZE};

  uint32_t max_partially_inlined_code_units{MAX_PARTIALLY_INLINED_CODE_UNITS};

  std::string unfinalize_perf_mode_str{"not-cold"};
  UnfinalizePerfMode unfinalize_perf_mode{UnfinalizePerfMode::NOT_COLD};

  // We will populate the information to rstate of classes and methods.
  UnorderedSet<const DexType*> no_inline_annos;
  UnorderedSet<const DexType*> force_inline_annos;
  // Prefixes of classes not to inline from / into
  std::vector<std::string> blocklist;
  std::vector<std::string> caller_blocklist;
  std::vector<std::string> intradex_allowlist;
  std::vector<std::string> no_inline_blocklist;
  // Prefixes of methods to force inline.
  std::vector<std::string> force_inline_prefixes;

  // Limit on number of relevant invokes to speed up local-only pass.
  uint64_t max_relevant_invokes_when_local_only{10};

  /**
   * 1. Derive blocklist/caller_blocklist/intradex_allowlist/no_inline_blocklist
   *    from patterns.
   * 2. Set rstate of classes and methods if they are annotated by any
   *    no_inline_annos, force_inline_annos, or match no_inline_blocklist.
   */
  void set_architecture(Architecture architecture) {
    if (m_populated) {
      always_assert_log(m_architecture == architecture,
                        "Cannot change architecture after populating inliner "
                        "config");
      return;
    }
    m_architecture = architecture;
  }

  uint64_t get_armv7_hard_max_instruction_size() const {
    return m_architecture == Architecture::ARMV7
               ? armv7_hard_max_instruction_size
               : 0;
  }

  bool is_over_armv7_hard_max_instruction_size(
      uint64_t estimated_caller_size, uint64_t estimated_callee_size) const {
    auto max = get_armv7_hard_max_instruction_size();
    return max > 0 && (estimated_caller_size > max ||
                       estimated_callee_size > max - estimated_caller_size);
  }

  void populate(const Scope& scope);

  const UnorderedSet<const DexType*>& get_blocklist() const {
    always_assert_log(m_populated, "Should populate blocklist\n");
    return m_blocklist;
  }

  void clear_blocklist() {
    blocklist.clear();
    m_blocklist.clear();
  }

  const UnorderedSet<const DexType*>& get_caller_blocklist() const {
    always_assert_log(m_populated, "Should populate blocklist\n");
    return m_caller_blocklist;
  }

  void clear_caller_blocklist() {
    caller_blocklist.clear();
    m_caller_blocklist.clear();
  }

  void apply_intradex_allowlist() {
    always_assert_log(m_populated, "Should populate allowlist\n");
    for (const DexType* type : UnorderedIterable(m_intradex_allowlist)) {
      m_blocklist.erase(type);
      m_caller_blocklist.erase(type);
    }
  }

 private:
  bool m_populated{false};
  Architecture m_architecture{Architecture::UNKNOWN};
  // The populated black lists.
  UnorderedSet<const DexType*> m_blocklist;
  UnorderedSet<const DexType*> m_caller_blocklist;
  UnorderedSet<const DexType*> m_intradex_allowlist;
};
} // namespace inliner
