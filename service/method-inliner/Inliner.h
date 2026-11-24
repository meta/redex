/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <limits>
#include <vector>

#include "BaselineProfile.h"
#include "CallSiteSummaries.h"
#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "PriorityThreadPoolDAGScheduler.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "Shrinker.h"

class InlineForSpeed;

namespace inliner {

struct InlinerConfig;

/*
 * Use the CFG instead of IRCode to do the inlining. Return true on
 * success. Registers starting with next_caller_reg must be available
 */
bool inline_with_cfg(DexMethod* caller_method,
                     DexMethod* callee_method,
                     IRInstruction* callsite,
                     const DexType* needs_receiver_cast,
                     const DexType* needs_init_class,
                     size_t next_caller_reg,
                     const cfg::ControlFlowGraph* reduced_cfg = nullptr,
                     DexMethod* rewrite_invoke_super_callee = nullptr,
                     bool needs_constructor_fence = false);

} // namespace inliner

/**
 * What kind of caller-callee relationships the inliner should consider.
 */
enum MultiMethodInlinerMode {
  None,
  InterDex,
  IntraDex,
};

struct InlinerCostConfig {
  // The following costs are in terms of code-units (2 bytes).
  // Typical overhead of calling a method, without move-result overhead.
  float cost_invoke;

  // Typical overhead of having move-result instruction.
  float cost_move_result;

  // Overhead of having a method and its metadata.
  size_t cost_method;

  // Typical savings in caller when callee doesn't use any argument.
  float unused_args_discount;

  size_t reg_threshold_1;

  size_t reg_threshold_2;

  size_t op_init_class_cost;

  size_t op_injection_id_cost;

  size_t op_unreachable_cost;

  size_t op_move_exception_cost;

  size_t insn_cost_1;

  size_t insn_has_data_cost;

  size_t insn_has_lit_cost_1;

  size_t insn_has_lit_cost_2;

  size_t insn_has_lit_cost_3;

  // Those configs are used to calculate the penalty for worse cross-dex-ref
  // minimization results due to inlining.
  float cross_dex_penalty_coe1;
  float cross_dex_penalty_coe2;
  float cross_dex_penalty_const;
  float cross_dex_bonus_const;

  float unused_arg_zero_multiplier;
  float unused_arg_non_zero_constant_multiplier;
  float unused_arg_nez_multiplier;
  float unused_arg_interval_multiplier;
  float unused_arg_singleton_object_multiplier;
  float unused_arg_object_with_immutable_attr_multiplier;
  float unused_arg_string_multiplier;
  float unused_arg_class_object_multiplier;
  float unused_arg_new_object_multiplier;
  float unused_arg_other_object_multiplier;
  float unused_arg_not_top_multiplier;

  // These are used to bias the inliner when presented with a method found in a
  // baseline profile
  float profile_guided_heat_threshold;
  float profile_guided_heat_discount;
  float profile_guided_shrink_bias;
  float profile_guided_block_appear_threshold;

  // [experimental] Callsite-count-percentile inlining lever. Rank percentiles,
  // high = hot: p95 is the hottest 5% of profiled (positive-count) callsites.
  //
  //   d(p) = d_start * (d_top/d_start) ^ clamp((p-p_start)/(p_top-p_start),0,1)
  //
  // A callsite at or above p_start has its local inline cost scaled by d(p), so
  // hot callsites inline callees the flat cost model would reject. Geometric,
  // so equal percentile steps are equal cost ratios -- the right spacing for a
  // factor that composes multiplicatively with the baseline-profile discounts
  // above.
  //
  // With p_top unset the ramp degenerates to a flat step at d_start for every
  // callsite above p_start. p_start <= 0 disables the lever entirely (NFC).
  int inline_hot_callsite_count_percentile; // p_start
  float inline_hot_callsite_count_discount; // d_start, at p_start
  int inline_hot_callsite_count_top_percentile; // p_top
  float inline_hot_callsite_count_top_discount; // d_top, the cap
};

inline const struct InlinerCostConfig DEFAULT_COST_CONFIG = {
    3.7f, // cost_invoke
    3.0f, // cost_move_result
    16, // cost_method
    1.0f, // unused_args_discount
    3, // reg_threshold_1
    2, // reg_threshold_2
    2, // op_init_class_cost
    3, // op_injection_id_cost
    1, // op_unreachable_cost
    8, // op_move_exception_cost
    1, // insn_cost_1
    4, // insn_has_data_cost
    4, // insn_has_lit_cost_1
    2, // insn_has_lit_cost_2
    1, // insn_has_lit_cost_3
    1.0f, // cross_dex_penalty_coe1
    0.0f, // cross_dex_penalty_coe2
    1.0f, // cross_dex_penalty_const
    0.0f, // cross_dex_bonus_const
    1.0f, // unused_arg_zero_multiplier
    1.0f, // unused_arg_non_zero_constant_multiplier
    1.0f, // unused_arg_nez_multiplier
    1.0f, // unused_arg_interval_multiplier
    1.0f, // unused_arg_singleton_object_multiplier
    1.0f, // unused_arg_object_with_immutable_attr_multiplier
    1.0f, // unused_arg_string_multiplier
    1.0f, // unused_arg_class_object_multiplier
    1.0f, // unused_arg_new_object_multiplier
    1.0f, // unused_arg_other_object_multiplier
    1.0f, // unused_arg_not_top_multiplier
    0.5f, // profile_guided_heat_threshold
    1.0f, // profile_guided_heat_discount
    0.0f, // profile_guided_shrink_bias
    0.0f, // profile_guided_block_appear_threshold
    -1, // inline_hot_callsite_count_percentile
    1.0f, // inline_hot_callsite_count_discount
    -1, // inline_hot_callsite_count_top_percentile
    -1.0f, // inline_hot_callsite_count_top_discount
};

// All call-sites of a callee.
struct CallerInsns {
  // Invoke instructions per caller
  UnorderedMap<const DexMethod*, UnorderedSet<IRInstruction*>> caller_insns;
  // Invoke instructions that need a cast
  UnorderedMap<IRInstruction*, const DexType*> inlined_invokes_need_cast;
  // Whether there may be any other unknown call-sites.
  bool other_call_sites{false};
  bool other_call_sites_overriding_methods_added{false};
  bool empty() const { return caller_insns.empty() && !other_call_sites; }
};

using CalleeCallerInsns = UnorderedMap<DexMethod*, CallerInsns>;

class ReducedCode {
 public:
  ReducedCode() : m_code(std::make_unique<cfg::ControlFlowGraph>()) {}
  IRCode& code() { return m_code; }
  cfg::ControlFlowGraph& cfg() { return m_code.cfg(); }

 private:
  IRCode m_code;
};

struct PartialCode {
  std::shared_ptr<ReducedCode> reduced_code{nullptr};
  size_t insn_size{0};
  bool is_valid() const { return reduced_code != nullptr; }
  bool operator==(const PartialCode& other) const {
    // TODO: Also check that reduced_cfg's are equivalent
    return insn_size == other.insn_size;
  }
};

struct Inlinable {
  DexMethod* callee;
  // Invoke instruction to callee
  IRInstruction* insn;
  // Whether the invocation at a particular call-site is guaranteed to not
  // return normally, and instead of inlining, a throw statement should be
  // inserted afterwards.
  bool no_return{false};
  // Whether the reduced-code represent a partial inlining transformation.
  bool partial{false};
  // Whether the inline is done for speed, even at the cost of code size.
  bool for_speed{false};
  // For a specific call-site, reduced cfg template after applying call-site
  // summary
  std::shared_ptr<ReducedCode> reduced_code;
  // Estimated size of callee, possibly reduced by call-site specific knowledge
  size_t insn_size;
  // Whether the callee is a virtual method different from the one referenced in
  // the invoke instruction.
  const DexType* needs_receiver_cast;
};

struct CalleeCallerRefs {
  bool same_class;
  size_t classes;
};

// The average or call-site specific inlined costs, depending on how it is
// retrieved
struct InlinedCost {
  // Full code costs of the original callee
  size_t full_code;
  // Average or call-site specific code costs of the callee after pruning
  float code;
  // Average or call-site specific method-refs count of the callee after pruning
  float method_refs;
  // Average or call-site specific others-refs count of the callee after pruning
  float other_refs;
  // Whether all or a specific call-site is guaranteed to not return normally
  bool no_return;
  // Average or call-site specific value indicating whether result is used
  float result_used;
  // Average or call-site specific value indicating how many callee arguments
  // are unused
  float unused_args;
  // For a specific call-site, reduced cfg template after applying call-site
  // summary
  std::shared_ptr<ReducedCode> reduced_code;
  // Maximum or call-site specific estimated callee size after pruning
  size_t insn_size;
  // For a specific call-site, partially inlined code.
  PartialCode partial_code{};

  bool operator==(const InlinedCost& other) const {
    // TODO: Also check that reduced_cfg's are equivalent
    return full_code == other.full_code && code == other.code &&
           method_refs == other.method_refs && other_refs == other.other_refs &&
           no_return == other.no_return && result_used == other.result_used &&
           insn_size == other.insn_size && partial_code == other.partial_code;
  }
};

enum class HotColdInliningBehavior {
  None,
  RespectNotCold,
  RespectMaybeHot,
};

/**
 * Helper class to inline a set of candidates.
 * Take a set of candidates and a scope and walk all instructions in scope
 * to find and inline all calls to candidate.
 * A resolver is used to map a method reference to a method definition, and must
 * be thread-safe. Not all methods may be inlined both for restriction on the
 * caller or the callee. Perform inlining bottom up.
 */
class MultiMethodInliner {
 public:
  /**
   * We can do global inlining before InterDexPass, but after InterDexPass, we
   * can only inline methods within each dex. Set intra_dex to true if
   * inlining is needed after InterDex.
   */
  MultiMethodInliner(
      const std::vector<DexClass*>& scope,
      const init_classes::InitClassesWithSideEffects&
          init_classes_with_side_effects,
      DexStoresVector& stores,
      const ConfigFiles& conf,
      const UnorderedSet<DexMethod*>& candidates,
      std::function<DexMethod*(DexMethodRef*, MethodSearch, const DexMethod*)>
          concurrent_resolve_fn,
      const inliner::InlinerConfig& config,
      int min_sdk,
      MultiMethodInlinerMode mode = InterDex,
      const CalleeCallerInsns& true_virtual_callers = {},
      InlineForSpeed* inline_for_speed = nullptr,
      bool analyze_and_prune_inits = false,
      const UnorderedSet<DexMethodRef*>& configured_pure_methods = {},
      const api::AndroidSDK* min_sdk_api = nullptr,
      bool cross_dex_penalty = false,
      const UnorderedSet<const DexString*>& configured_finalish_field_names =
          {},
      bool local_only = false,
      HotColdInliningBehavior hot_cold_inlining_behavior =
          HotColdInliningBehavior::None,
      std::optional<baseline_profiles::BaselineProfile> baseline_profile = {},
      InlinerCostConfig inliner_cost_config = DEFAULT_COST_CONFIG,
      const UnorderedSet<const DexMethod*>* unfinalized_init_methods = nullptr,
      InsertOnlyConcurrentSet<DexMethod*>* methods_with_write_barrier = nullptr,
      const method_override_graph::Graph* method_override_graph = nullptr);

  /*
   * Applies certain delayed scope-wide changes, including in particular
   * visibility and staticizing changes.
   */
  void flush() {
    delayed_visibility_changes_apply();
    delayed_invoke_direct_to_static();
  }

  /**
   * Attempt inlining for all candidates, and flushes scope-wide changes.
   */
  void inline_methods();

  /**
   * Return the set of unique inlined methods.
   */
  UnorderedSet<DexMethod*> get_inlined() const {
    UnorderedSet<DexMethod*> res;
    res.reserve(m_inlined.size());
    insert_unordered_iterable(res, m_inlined);
    return res;
  }

  UnorderedSet<const DexMethod*> get_inlined_with_fence() const {
    UnorderedSet<const DexMethod*> res;
    res.reserve(m_inlined_with_fence.size());
    insert_unordered_iterable(res, m_inlined_with_fence);
    return res;
  }

  size_t get_not_cold_methods() const { return m_not_cold_methods.size(); }

  size_t get_maybe_hot_methods() const { return m_maybe_hot_methods.size(); }

  bool for_speed() const { return m_inline_for_speed != nullptr; }

  /**
   * Inline callees in the caller if is_inlinable below returns true.
   */
  void inline_callees(DexMethod* caller,
                      const UnorderedSet<DexMethod*>& callees,
                      bool filter_via_should_inline = false);

  /**
   * Inline callees in the given instructions in the caller, if is_inlinable
   * below returns true.
   */
  size_t inline_callees(DexMethod* caller,
                        const UnorderedSet<IRInstruction*>& insns);

  /**
   * Inline callees in the given instructions in the caller, if is_inlinable
   * below returns true.
   */
  size_t inline_callees(DexMethod* caller,
                        const UnorderedMap<IRInstruction*, DexMethod*>& insns);

  struct InlinableDecision {
    enum class Decision : uint8_t {
      kInlinable,
      kCallerNoOpt,
      kCrossStore,
      kCrossDexRef,
      kHotCold,
      kBlocklisted,
      kExternalCatch,
      kUninlinableOpcodes,
      kApiMismatch,
      kCalleeDontInline,
      kCallerTooLarge,
      kProblematicRefs,
    };
    Decision decision{Decision::kInlinable};

    explicit InlinableDecision(Decision decision) : decision(decision) {}

    // NOLINTNEXTLINE(google-explicit-constructor)
    operator bool() const { return decision == Decision::kInlinable; }

    std::string to_str() const;
  };

  /**
   * Return true if the callee is inlinable into the caller.
   * The predicates below define the constraints for inlining.
   * Providing an instrucion is optional, and only used for logging.
   */
  InlinableDecision is_inlinable(const DexMethod* caller,
                                 const DexMethod* callee,
                                 const cfg::ControlFlowGraph* reduced_cfg,
                                 const IRInstruction* insn,
                                 uint64_t estimated_caller_size,
                                 uint64_t estimated_callee_size,
                                 bool* caller_too_large_ = nullptr);

  void visibility_changes_apply_and_record_make_static(
      const VisibilityChanges& visibility_changes);

  shrinker::Shrinker& get_shrinker() { return m_shrinker; }

 private:
  void make_partial(const DexMethod* method, InlinedCost* inlined_Cost);

  const DexType* get_needs_init_class(DexMethod* callee) const;

  bool get_needs_constructor_fence(const DexMethod* caller,
                                   const DexMethod* callee) const;

  /**
   * The method that `insn` invokes, or std::nullopt if we must not inline at
   * `insn` at all. For a callsite that the true-virtual analysis registered,
   * that is the unique implementation it found. Otherwise it is the resolved
   * method, which is inlinable only if it is also in `caller`'s callee set,
   * where plain resolution puts overrideless candidates alone. Either way the
   * result is the implementation that actually runs, which is what makes it
   * sound to inline (part of) its body.
   */
  std::optional<DexMethod*> get_callee(DexMethod* caller, IRInstruction* insn);

  /**
   * The type the true-virtual analysis recorded for `insn`'s receiver to be
   * cast to on the way into the inlined code, or nullptr if it recorded none.
   */
  const DexType* get_recorded_receiver_cast(IRInstruction* insn) const;

  /**
   * Whether a plain invocation of `callee`, as the partially inlined code's
   * fallback performs it, can stand in for `insn`. It must dispatch the same
   * way, and, as it names `callee` where `insn` names its own method ref, the
   * receiver must be an instance of the callee's class by the time it reaches
   * the fallback.
   */
  bool can_invoke_callee_directly(IRInstruction* insn,
                                  const DexMethod* callee) const;

  size_t inline_inlinables(DexMethod* caller,
                           const std::vector<Inlinable>& inlinables);

  /**
   * Return true if the method is related to enum (java.lang.Enum and derived).
   * Cannot inline enum methods because they can be called by code we do
   * not own.
   */
  bool is_blocklisted(const DexMethod* callee);

  bool caller_is_blocklisted(const DexMethod* caller);

  /**
   * Return true if the callee contains external catch exception types
   * which are not public.
   */
  bool has_external_catch(const DexMethod* callee,
                          const cfg::ControlFlowGraph* reduced_cfg);

  /**
   * Return true if the callee contains certain opcodes that are difficult
   * or impossible to inline.
   * Some of the opcodes are defined by the methods below.
   */
  bool cannot_inline_opcodes(const DexMethod* caller,
                             const DexMethod* callee,
                             const cfg::ControlFlowGraph* reduced_cfg,
                             const IRInstruction* invk_insn);

  /**
   * Return true if inlining would require a method called from the callee
   * (candidate) to turn into a virtual method (e.g. private to public).
   */
  bool create_vmethod(IRInstruction* insn,
                      const DexMethod* callee,
                      const DexMethod* caller);

  /**
   * Return true if we would create an invocation within an outlined method to
   * another outlined method.
   */
  bool outlined_invoke_outlined(IRInstruction* insn, const DexMethod* caller);

  /**
   * Return true if a callee contains an instruction whose behavior depends on
   * the class that holds it (`depends_on_holder_class`): an invoke super to a
   * different method in the hierarchy, which `CFGInliner` cannot rewrite, a
   * method handle that calls like one, or an invoke-custom.
   * invoke-super can only exist within the class the call lives in.
   */
  bool nonrelocatable_invoke_super(IRInstruction* insn,
                                   const DexMethod* callee);

  /**
   * Return true if the callee contains a call to an unknown virtual method,
   * by an instruction or a method handle.
   * We cannot determine the visibility of the method invoked and thus
   * we cannot inline as we could cause a verification error if the method
   * was package/protected and we move the call out of context.
   */
  bool unknown_virtual(IRInstruction* insn, const DexMethod* caller);

  /**
   * Return true if the callee contains an access to an unknown field, by an
   * instruction or a method handle.
   * We cannot determine the visibility of the field accessed and thus
   * we cannot inline as we could cause a verification error if the field
   * was package/protected and we move the access out of context.
   */
  bool unknown_field(IRInstruction* insn);

  /**
   * return true if `insn` is
   *   sget android.os.Build.VERSION.SDK_INT
   */
  bool check_android_os_version(IRInstruction* insn);

  /**
   * Return true if a caller is in a DEX in a store and any opcode in callee
   * refers to a DexMember in a different store .
   */
  bool cross_store_reference(const DexMethod* caller,
                             const DexMethod* callee,
                             const cfg::ControlFlowGraph* reduced_cfg);

  bool cross_dex_reference(const DexMethod* caller,
                           const DexMethod* callee,
                           const cfg::ControlFlowGraph* reduced_cfg);

  bool cross_hot_cold(const DexMethod* caller,
                      const DexMethod* callee,
                      uint64_t estimated_callee_size = 0);

  /**
   * Return true if a caller is in a DEX in a store and any opcode in callee
   * refers to a problematic ref, i.e. one that directly or indirectly refers to
   * another store, or a non-min-sdk API.
   */
  bool problematic_refs(const DexMethod* caller,
                        const DexMethod* callee,
                        const cfg::ControlFlowGraph* reduced_cfg);

  bool is_estimate_over_max(uint64_t estimated_caller_size,
                            uint64_t estimated_callee_size,
                            uint64_t max);

  /**
   * Some versions of ART (5.0.0 - 5.0.2) will fail to verify a method if it
   * is too large. See https://code.google.com/p/android/issues/detail?id=66655.
   *
   * Right now we only check for the number of instructions, but there are
   * other constraints that might be worth looking into, e.g. the number of
   * registers.
   */
  bool caller_too_large(DexType* caller_type,
                        uint64_t estimated_caller_size,
                        uint64_t estimated_callee_size);

  /**
   * Return whether the callee should be inlined into the caller. This differs
   * from is_inlinable in that the former is concerned with whether inlining is
   * possible to do correctly at all, whereas this is concerned with whether the
   * inlining is beneficial for size / performance.
   *
   * This method does *not* need to return a subset of is_inlinable. We will
   * only inline callsites that pass both should_inline and is_inlinable.
   *
   * Note that this filter will only be applied when inlining is initiated via
   * a call to `inline_methods()`, but not if `inline_callees()` is invoked
   * directly.
   */
  bool should_inline_always(const DexMethod* callee);

  /**
   * Whether it's beneficial to inline the callee at a particular callsite.
   * no_return may be set to true when the return value is false.
   */
  bool should_inline_at_call_site(DexMethod* caller,
                                  cfg::Block* caller_block,
                                  const IRInstruction* invoke_insn,
                                  DexMethod* callee,
                                  bool* no_return = nullptr,
                                  bool* for_speed = nullptr,
                                  PartialCode* partial_code = nullptr);

  /**
   * Whether we should, and legally can, partially inline a particular callee
   * at a particular callsite.
   */
  bool should_partially_inline(cfg::Block* block,
                               IRInstruction* insn,
                               DexMethod* callee,
                               PartialCode* partial_code);

  /**
   * should_inline_fast will return true for a subset of methods compared to
   * should_inline. should_inline_fast can be evaluated much more quickly, as it
   * doesn't need to peek into the callee code.
   */
  bool should_inline_fast(const DexMethod* callee);

  /**
   * Gets the partially inlined callee, if any.
   */
  PartialCode get_callee_partial_code(const DexMethod* callee);

  /**
   * Gets the number of instructions in a callee.
   */
  size_t get_callee_insn_size(const DexMethod* callee);

  /**
   * Gets the set of referenced types in a callee.
   */
  std::shared_ptr<UnorderedBag<const DexType*>> get_callee_type_refs(
      const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg);

  /**
   * Gets the set of references in a callee's code.
   */
  std::shared_ptr<CodeRefs> get_callee_code_refs(
      const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg);

  /**
   * Gets the set of x-dex references in a callee's code.
   */
  std::shared_ptr<XDexMethodRefs::Refs> get_callee_x_dex_refs(
      const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg);

  /**
   * Computes information about callers of a method.
   */
  CalleeCallerRefs get_callee_caller_refs(const DexMethod* callee);

  /**
   * We want to avoid inlining a large method with many callers as that would
   * bloat the bytecode.
   */
  bool too_many_callers(const DexMethod* callee);

  // Reduce a cfg with a call-site summary, if given.
  std::shared_ptr<ReducedCode> apply_call_site_summary(
      bool is_static,
      DexType* declaring_type,
      DexProto* proto,
      const cfg::ControlFlowGraph& original_cfg,
      const CallSiteSummary* call_site_summary);

  /*
   * Try to estimate number of code units (2 bytes each) of code. Also take
   * into account costs arising from control-flow overhead and constant
   * arguments, if any
   */
  InlinedCost get_inlined_cost(
      bool is_static,
      DexType* declaring_type,
      DexProto* proto,
      const IRCode* code,
      const CallSiteSummary* call_site_summary = nullptr);

  float get_unused_arg_multiplier(const ConstantValue&) const;

  /**
   * Estimate inlined cost for fully inlining a callee without using any
   * summaries for pruning.
   */
  const InlinedCost* get_fully_inlined_cost(const DexMethod* callee);

  /**
   * Estimate average inlined cost when inlining a callee, considering all
   * call-site summaries for pruning.
   */
  const InlinedCost* get_average_inlined_cost(const DexMethod* callee);

  /**
   * Estimate inlined cost for a particular call-site, if available.
   */
  const InlinedCost* get_call_site_inlined_cost(
      const IRInstruction* invoke_insn, const DexMethod* callee);

  /**
   * Estimate inlined cost for a particular call-site summary, if available.
   */
  const InlinedCost* get_call_site_inlined_cost(
      const CallSiteSummary* call_site_summary, const DexMethod* callee);

  /**
   * Change visibilities of methods, assuming that`m_visibility_changes` is
   * non-null.
   */
  void delayed_visibility_changes_apply();

  /**
   * Staticize required methods (stored in `m_delayed_make_static`) and update
   * opcodes accordingly.
   */
  void delayed_invoke_direct_to_static();

  /**
   * Initiate computation of various callee costs asynchronously.
   */
  void compute_callee_costs(DexMethod* method);

  /**
   * Post-processing a method synchronously.
   */
  void postprocess_method(DexMethod* method);

  /**
   * Shrink a method (run constant-prop, cse, copy-prop, local-dce,
   * dedup-blocks) synchronously.
   */
  void shrink_method(DexMethod* method);

  // Checks that...
  // - there are no assignments to (non-inherited) instance fields before
  //   a constructor call, and
  // - the constructor refers to a method of the same class, and
  // - there are no assignments to any final fields.
  // Under these conditions, a constructor is universally inlinable.
  bool can_inline_init(const DexMethod* init_method);

  float compute_profile_guided_discount(DexMethod* caller,
                                        DexMethod* callee,
                                        float inline_cost,
                                        cfg::Block* caller_block,
                                        ReducedCode* reduced_callee);

  // Builds the count -> discount ramp (entry cutoff, quantile table, and the
  // discount at each quantile). Called once at construction.
  void build_hot_callsite_count_ramp();

  // Discount for a callsite whose block execution count is `count`; 1.0 when
  // the lever is off or the callsite is below p_start.
  float hot_callsite_count_discount(float count) const;

  const api::AndroidSDK* m_min_sdk_api;

  std::unique_ptr<InsertOnlyConcurrentMap<size_t, RefChecker>> m_ref_checkers;

  /**
   * Resolver function to map a method reference to a method definition. Must be
   * thread-safe.
   */
  std::function<DexMethod*(DexMethodRef*, MethodSearch, const DexMethod*)>
      m_concurrent_resolver;

  /**
   * Inlined methods.
   */
  ConcurrentSet<DexMethod*> m_inlined;

  InsertOnlyConcurrentSet<const DexMethod*> m_not_cold_methods;

  InsertOnlyConcurrentSet<const DexMethod*> m_maybe_hot_methods;

  const InsertOnlyConcurrentSet<const DexMethod*>* get_preferred_methods()
      const {
    if (m_hot_cold_inlining_behavior ==
        HotColdInliningBehavior::RespectNotCold) {
      return &m_not_cold_methods;
    }
    if (m_hot_cold_inlining_behavior ==
        HotColdInliningBehavior::RespectMaybeHot) {
      return &m_maybe_hot_methods;
    }
    return nullptr;
  }

  InsertOnlyConcurrentSet<const DexMethod*> m_hot_methods;

  ConcurrentSet<const DexMethod*> m_inlined_with_fence;

  //
  // Maps from callee to callers and reverse map from caller to callees.
  // Those are used to perform bottom up inlining.
  //
  ConcurrentMethodToMethodOccurrences m_callee_caller;

  ConcurrentMethodToMethodOccurrences m_caller_callee;

  // Auxiliary data for a caller that contains true virtual callees
  struct CallerVirtualCallees {
    // Mapping of instructions to representative
    UnorderedMap<IRInstruction*, DexMethod*> insns;
    // Set of callees which must only be inlined via above insns
    UnorderedSet<DexMethod*> exclusive_callees;
  };
  // Mapping from callers to auxiliary data for contained true virtual callees
  UnorderedMap<const DexMethod*, CallerVirtualCallees> m_caller_virtual_callees;

  // Casts that a partially-inlined fallback invocation needs, keyed by invoke
  // instruction. Flattened from the per-callee CallerInsns, so each callee
  // contributes its whole map once, not once per caller.
  UnorderedMap<IRInstruction*, const DexType*> m_inlined_invokes_need_cast;

  UnorderedSet<const DexMethod*> m_true_virtual_callees_with_other_call_sites;

  UnorderedSet<const DexMethod*> m_recursive_callees;
  UnorderedSet<const DexMethod*> m_speed_excluded_callees;

  // If mode == IntraDex, then we maintaing information about x-dex method
  // references.
  std::unique_ptr<XDexMethodRefs> m_x_dex;

  // Cache of the inlined costs of fully inlining a calle without using any
  // summaries for pruning.
  mutable InsertOnlyConcurrentMap<const DexMethod*, InlinedCost>
      m_fully_inlined_costs;

  // Cache of the average inlined costs of each method.
  mutable InsertOnlyConcurrentMap<const DexMethod*, InlinedCost>
      m_average_inlined_costs;

  // Cache of the inlined costs of each call-site summary after pruning.
  mutable InsertOnlyConcurrentMap<CalleeCallSiteSummary,
                                  InlinedCost,
                                  boost::hash<CalleeCallSiteSummary>>
      m_call_site_inlined_costs;

  // Cache of the inlined costs of each call-site after pruning.
  mutable InsertOnlyConcurrentMap<const IRInstruction*, const InlinedCost*>
      m_invoke_call_site_inlined_costs;

  // Priority thread pool to handle parallel processing of methods, either
  // shrinking initially / after inlining into them, or even to inline in
  // parallel. By default, parallelism is disabled num_threads = 0).
  PriorityThreadPoolDAGScheduler<DexMethod*> m_scheduler;

  // Set of methods that need to be made static eventually. The destructor
  // of this class will do the necessary delayed work.
  ConcurrentSet<DexMethod*> m_delayed_make_static;

  // Accumulated visibility changes that must be applied eventually.
  // This happens locally within inline_methods.
  std::unique_ptr<VisibilityChanges> m_delayed_visibility_changes;

  // When mutating m_delayed_visibility_changes or applying visibility changes
  // eagerly
  std::mutex m_visibility_changes_mutex;

  // Cache for should_inline function
  InsertOnlyConcurrentMap<const DexMethod*, bool> m_should_inline;

  // Optional cache for get_callee_insn_size function
  std::unique_ptr<InsertOnlyConcurrentMap<const DexMethod*, size_t>>
      m_callee_insn_sizes;

  // Optional cache for get_partial_callee function
  std::unique_ptr<InsertOnlyConcurrentMap<const DexMethod*, PartialCode>>
      m_callee_partial_code;

  // Optional cache for get_callee_type_refs function
  std::unique_ptr<
      InsertOnlyConcurrentMap<const DexMethod*,
                              std::shared_ptr<UnorderedBag<const DexType*>>>>
      m_callee_type_refs;

  // Optional cache for get_callee_code_refs function
  std::unique_ptr<
      InsertOnlyConcurrentMap<const DexMethod*, std::shared_ptr<CodeRefs>>>
      m_callee_code_refs;

  // Optional cache for get_callee_caller_res function
  std::unique_ptr<InsertOnlyConcurrentMap<const DexMethod*, CalleeCallerRefs>>
      m_callee_caller_refs;

  // Optional cache for get_callee_x_dex_refs function
  std::unique_ptr<
      InsertOnlyConcurrentMap<const DexMethod*,
                              std::shared_ptr<XDexMethodRefs::Refs>>>
      m_callee_x_dex_refs;

  // Cache of whether a constructor can be unconditionally inlined.
  mutable InsertOnlyConcurrentMap<const DexMethod*, bool> m_can_inline_init;

  std::unique_ptr<inliner::CallSiteSummarizer> m_call_site_summarizer;

  /**
   * Info about inlining.
   */
  struct InliningInfo {
    // statistics that must be incremented sequentially
    size_t recursive{0};
    size_t max_call_stack_depth{0};
    size_t waited_seconds{0};
    uint32_t critical_path_length{0};

    // statistics that may be incremented concurrently
    std::atomic<size_t> kotlin_lambda_inlined{0};
    std::atomic<size_t> partially_inlined{0};
    std::atomic<size_t> calls_inlined{0};
    std::atomic<size_t> init_classes{0};
    std::atomic<size_t> constructor_fences{0};
    std::atomic<size_t> calls_not_inlinable{0};
    std::atomic<size_t> calls_not_inlined{0};
    std::atomic<size_t> calls_not_inlined_with_perf_sensitive_constructors{0};
    std::atomic<size_t> no_returns{0};
    std::atomic<size_t> unreachable_insns{0};
    std::atomic<size_t> intermediate_shrinkings{0};
    std::atomic<size_t> intermediate_remove_unreachable_blocks{0};
    std::atomic<size_t> not_found{0};
    std::atomic<size_t> blocklisted{0};
    std::atomic<size_t> throws{0};
    std::atomic<size_t> multi_ret{0};
    std::atomic<size_t> need_vmethod{0};
    std::atomic<size_t> invoke_super{0};
    std::atomic<size_t> escaped_virtual{0};
    std::atomic<size_t> known_public_methods{0};
    std::atomic<size_t> unresolved_methods{0};
    std::atomic<size_t> non_pub_virtual{0};
    std::atomic<size_t> escaped_field{0};
    std::atomic<size_t> non_pub_field{0};
    std::atomic<size_t> non_pub_ctor{0};
    std::atomic<size_t> cross_dex{0};
    std::atomic<size_t> cross_store{0};
    std::atomic<size_t> api_level_mismatch{0};
    std::atomic<size_t> problematic_refs{0};
    std::atomic<size_t> caller_too_large{0};
    std::atomic<size_t> constant_invoke_callees_analyzed{0};
    std::atomic<size_t> constant_invoke_callees_unused_results{0};
    std::atomic<size_t> constant_invoke_callees_no_return{0};
    inliner::CallSiteSummaryStats call_site_summary_stats;
    AtomicMap<const DexMethod*, size_t> partially_inlined_callees;
  };
  InliningInfo info;

  const std::vector<DexClass*>& m_scope;

  // The methods that method handles name or can run, which are never made
  // static (see `create_vmethod`).
  const InsertOnlyConcurrentSet<const DexMethod*> m_method_handle_methods;

  const inliner::InlinerConfig& m_config;

  const MultiMethodInlinerMode m_mode;

  // Non-const to allow for caching behavior.
  InlineForSpeed* m_inline_for_speed;

  // Whether to do some deep analysis to determine if constructor candidates
  // can be safely inlined, and don't inline them otherwise.
  bool m_analyze_and_prune_inits;

  bool m_cross_dex_penalty;

  shrinker::Shrinker m_shrinker;

  AccumulatingTimer m_inline_callees_timer;
  AccumulatingTimer m_inline_callees_should_inline_timer;
  AccumulatingTimer m_inline_callees_init_timer;
  AccumulatingTimer m_inline_inlinables_timer;
  AccumulatingTimer m_inline_with_cfg_timer;
  AccumulatingTimer m_call_site_inlined_cost_timer;
  AccumulatingTimer m_cannot_inline_sketchy_code_timer;

  const DexFieldRef* m_sdk_int_field =
      DexField::get_field("Landroid/os/Build$VERSION;.SDK_INT:I");

  bool m_local_only;
  HotColdInliningBehavior m_hot_cold_inlining_behavior;

  std::optional<baseline_profiles::BaselineProfile> m_baseline_profile;

  InlinerCostConfig m_inliner_cost_config;

  // Entry cutoff for the callsite-count lever: the count at p_start, computed
  // once at construction when the lever is enabled; +inf otherwise (nothing
  // qualifies).
  float m_hot_callsite_count_cutoff{std::numeric_limits<float>::infinity()};
  // Ascending quantile table of profiled callsite block counts: entry i is the
  // count at rank percentile 100*i/(N-1). Empty when the lever is off or no
  // ramp is configured. Fixed size, so the per-callsite rank lookup is a binary
  // search over a few thousand floats, not over the whole scope.
  std::vector<float> m_hot_callsite_count_quantiles;
  // Discount per quantile bucket, precomputed so the hot path does no
  // transcendentals. Parallel to m_hot_callsite_count_quantiles.
  std::vector<float> m_hot_callsite_count_discounts;

  const UnorderedSet<const DexMethod*>* m_unfinalized_init_methods;
  InsertOnlyConcurrentMap<const DexMethod*, const DexMethod*>
      m_unfinalized_overloads;

  InsertOnlyConcurrentSet<DexMethod*>* m_methods_with_write_barrier;

 public:
  const InliningInfo& get_info() { return info; }

  size_t get_callers() { return m_caller_callee.size(); }

  double get_call_site_inlined_cost_seconds() const {
    return m_call_site_inlined_cost_timer.get_seconds();
  }
  double get_inline_callees_seconds() const {
    return m_inline_callees_timer.get_seconds() -
           m_inline_callees_should_inline_timer.get_seconds() -
           m_inline_callees_init_timer.get_seconds();
  }
  double get_inline_callees_should_inline_seconds() const {
    return m_inline_callees_should_inline_timer.get_seconds();
  }
  double get_inline_callees_init_seconds() const {
    return m_inline_callees_init_timer.get_seconds();
  }
  double get_inline_inlinables_seconds() const {
    return m_inline_inlinables_timer.get_seconds() -
           m_inline_with_cfg_timer.get_seconds();
  }
  double get_inline_with_cfg_seconds() const {
    return m_inline_with_cfg_timer.get_seconds();
  }
  double get_cannot_inline_sketchy_code_timer_seconds() const {
    return m_cannot_inline_sketchy_code_timer.get_seconds();
  }
};
