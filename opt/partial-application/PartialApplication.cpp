/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This pass identifies commonly used constant arguments that methods are
 * invoked with, and then introduces helper functions that bind those arguments
 * if it seems beneficial to reduce the overall code size by rewriting the
 * call-sites. The new helper methods are placed in the same class as the
 * callee. Their name is stable, including a hash derived from the bound
 * constant arguments.
 *
 * The most interesting part of this optimization, with likely further tuning
 * potential, is the priority-queue based approach to find beneficial subsets of
 * common constant arguments.
 *
 * While this is similar in spirit to what the InstructionSequenceOutliner does,
 * a major difference is that this pass specifically targets individual method
 * invocations, and it picks up incoming constant arguments based on our
 * existing constant-propagation analysis, not caring where earlier in the code,
 * or in which order, the constant are defined. And ultimately, it picks a
 * beneficial subset of constant arguments regardless of what order they were
 * defined in. In contrast, the InstructionSequenceOutliner requires precise
 * matches of frequently occurring instruction opcodes sequences (but module
 * register names) in order outline any particular call-site.
 *
 * Here's an example of what the optimization does. Let's say there's a method
 * like this:
 *
 *   void foo(int a, int b, Integer c);
 *
 * And it is invoked 10 times as
 *
 *   foo(10, 20, Integer.valueOf(23));
 *
 * And another 10 times as
 *
 *   foo(13, 20, Integer.valueOf(23));
 *
 * Let's say in neither case would a new helper function be beneficial to reduce
 * size. However, when we trim off the first argument, we are left with 20 times
 *
 *   foo(*, 20, Integer.valueOf(23));
 *
 * And this might be beneficial to transform. Then we introduce a helper
 * function like the following.
 *
 *   foo$pa$xxxx(int a) { foo(a, 20, Integer.valueOf(23)); }
 *
 * And rewrite the call-sites to
 *
 *   foo$pa$xxxx(10);
 *
 * and
 *
 *   foo$pa$xxxx(13);
 *
 * respectively.
 *
 * Various safe-guards are in place:
 * - We won't introduce helper methods that would contain cross-store or
 *   non-min-sdk level references.
 * - We only transform code with the largest root store id (so not in the
 *   primary dex, unless there only is one, and not in other auxiliary stores)
 * - We won't rewrite code that sits in hot blocks in hot methods, or loops in
 *   warm methods (reuses logic from InstructionSequenceOutliner)
 *
 * We don't do anything special for symbolication. Thus, the new helper methods
 * will appear in stack traces, but probably won't be confusing, as they have
 * names derived from the final callee, appearing as some trampoline method. The
 * code in the helper methods will never fail (except maybe under the most
 * obscure circumstances such as a stack-overflow), and thus will never be on
 * top of a stack trace, and only the top frame is used for symbolication.
 */

#include "PartialApplication.h"

#include <cinttypes>

#include <boost/format.hpp> // NOLINT

#include "CFGMutation.h"
#include "CallSiteSummaries.h"
#include "CallSiteSummaryReductions.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "LiveRange.h"
#include "MethodProfiles.h"
#include "MutablePriorityQueue.h"
#include "OutliningProfileGuidanceImpl.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "RefChecker.h"
#include "Show.h"
#include "Shrinker.h"
#include "SourceBlocks.h"
#include "SourceBlocksUtils.h"
#include "Trace.h"
#include "Walkers.h"

using namespace inliner;
using namespace outliner;
using namespace outliner_impl;
using namespace live_range;
using namespace shrinker;

namespace {
// Retrieve list of classes in primary dex, if there is more than one store and
// dexes.
UnorderedSet<const DexType*> get_excluded_classes(DexStoresVector& stores) {
  UnorderedSet<const DexType*> excluded_classes;
  bool has_other_stores{false};
  bool has_other_dexes{false};
  for (auto& store : stores) {
    if (store.is_root_store()) {
      auto& dexen = store.get_dexen();
      always_assert(!dexen.empty());
      for (auto* cls : dexen.front()) {
        excluded_classes.insert(cls->get_type());
      }
      if (dexen.size() > 1) {
        has_other_dexes = true;
      }
    } else {
      has_other_stores = true;
    }
  }
  if (!has_other_stores && !has_other_dexes) {
    excluded_classes.clear();
  }
  return excluded_classes;
}

const api::AndroidSDK* get_min_sdk_api(ConfigFiles& conf, PassManager& mgr) {
  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  mgr.incr_metric("min_sdk", min_sdk);
  TRACE(PA, 2, "min_sdk: %d", min_sdk);
  auto min_sdk_api_file = conf.get_android_sdk_api_file(min_sdk);
  if (!min_sdk_api_file) {
    mgr.incr_metric("min_sdk_no_file", 1);
    TRACE(PA, 2, "Android SDK API %d file cannot be found.", min_sdk);
    return nullptr;
  } else {
    return &conf.get_android_sdk_api(min_sdk);
  }
}

using EnumUtilsCache = InsertOnlyConcurrentMap<int32_t, DexField*>;

// Check if we have a boxed value for which there is a $EnumUtils field.
DexField* try_get_enum_utils_f_field(EnumUtilsCache& cache,
                                     const ObjectWithImmutAttr& object) {
  // This matches EnumUtilsFieldAnalyzer::analyze_sget.
  always_assert(object.jvm_cached_singleton);
  const auto& attribute = only(object.attributes);
  if (object.type != type::java_lang_Integer()) {
    return nullptr;
  }
  const auto& signed_value = attribute.value.get<SignedConstantDomain>();
  auto c = signed_value.get_constant();
  always_assert(c);
  return *cache
              .get_or_create_and_assert_equal(
                  static_cast<int32_t>(*c),
                  [&](int32_t key) -> DexField* {
                    auto* cls =
                        type_class(DexType::make_type("Lredex/$EnumUtils;"));
                    if (cls == nullptr) {
                      return nullptr;
                    }
                    std::string field_name = "f" + std::to_string(key);
                    auto* field = cls->find_sfield(field_name.c_str(),
                                                   type::java_lang_Integer());
                    always_assert(!field || is_static(field));
                    return field;
                  })
              .first;
}

// Identify how many argument slots an invocation needs after expansion of wide
// types, and thus whether a range instruction will be needed.
std::pair<param_index_t, bool> analyze_args(const DexMethod* callee) {
  const auto* args = callee->get_proto()->get_args();
  param_index_t src_regs = args->size();
  if (!is_static(callee)) {
    src_regs++;
  }
  param_index_t expanded_src_regs{
      static_cast<param_index_t>(!is_static(callee))};
  for (const auto* t : *args) {
    expanded_src_regs += type::is_wide_type(t) ? 2 : 1;
  }
  auto needs_range = expanded_src_regs > 5;
  return {src_regs, needs_range};
}

struct ArgExclusivity {
  // between 0 and 1
  float ownership{0};
  bool needs_move{false};
};

struct AggregatedArgExclusivity {
  double ownership{0};
  uint32_t needs_move{0};
};

using ArgExclusivityVector =
    std::vector<std::pair<src_index_t, ArgExclusivity>>;
// Determine whether, or to what extent, the instructions to compute arguments
// to an invocation are exclusive to that invocation. (If not, then eliminating
// the argument in the invocation likely won't give us expected cost savings.)
ArgExclusivityVector get_arg_exclusivity(const UseDefChains& use_def_chains,
                                         const DefUseChains& def_use_chains,
                                         bool needs_range,
                                         IRInstruction* insn) {
  ArgExclusivityVector aev;
  for (param_index_t src_idx = 0; src_idx < insn->srcs_size(); src_idx++) {
    const auto& defs = use_def_chains.at((Use){insn, src_idx});
    if (defs.size() != 1) {
      continue;
    }
    auto* const def = *defs.begin();
    bool other_use = false;
    param_index_t count = 0;
    for (const auto& use : UnorderedIterable(def_use_chains.at(def))) {
      if (!opcode::is_a_move(use.insn->opcode()) &&
          (use.insn->opcode() != insn->opcode() ||
           use.insn->get_method() != insn->get_method())) {
        other_use = true;
        break;
      }
      count++;
    }
    float ownership = other_use ? 0.0f : (1.0f / static_cast<float>(count));
    // TODO: We also likely need a move if there are more than 16 args
    // (including extra wides) live at this point.
    bool needs_move = needs_range && (other_use || count > 1);
    if (ownership > 0 || needs_move) {
      aev.emplace_back(src_idx, (ArgExclusivity){ownership, needs_move});
    }
  }
  return aev;
}

using InsnsArgExclusivity =
    InsertOnlyConcurrentMap<const IRInstruction*, ArgExclusivityVector>;
using CalleeCallerClasses =
    ConcurrentMap<const DexMethod*, UnorderedSet<const DexType*>>;
// Gather all (caller, callee) pairs. Also compute arg exclusivity, which invoke
// instructions we should exclude, and how many classes calls are distributed
// over.
void gather_caller_callees(
    const OutlineabilityContext& outlineability,
    const Scope& scope,
    const GetCalleeFunction& get_callee_fn,
    ConcurrentMethodToMethodOccurrences* callee_caller,
    ConcurrentMethodToMethodOccurrences* caller_callee,
    InsnsArgExclusivity* arg_exclusivity,
    ConcurrentSet<const IRInstruction*>* excluded_invoke_insns,
    CalleeCallerClasses* callee_caller_classes) {
  Timer timer("gather_caller_callees");
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    if (caller->rstate.no_optimizations() ||
        caller->rstate.should_not_outline()) {
      return;
    }
    always_assert(code.cfg_built());
    MoveAwareChains move_aware_chains(code.cfg());
    const auto use_def_chains = move_aware_chains.get_use_def_chains();
    const auto def_use_chains = move_aware_chains.get_def_use_chains();
    for (auto& big_block : big_blocks::get_big_blocks(code.cfg())) {
      auto can_outline =
          outlineability.can_outline_from_big_block(caller, big_block) ==
          OutlineabilityContext::Result::CanOutline;
      for (auto& mie : big_blocks::InstructionIterable(big_block)) {
        auto* insn = mie.insn;
        auto* callee = get_callee_fn(caller, insn);
        if (callee == nullptr) {
          continue;
        }
        if (!can_outline) {
          excluded_invoke_insns->insert(insn);
          continue;
        }
        auto needs_range = analyze_args(callee).second;
        auto ae = get_arg_exclusivity(use_def_chains, def_use_chains,
                                      needs_range, insn);
        if (ae.empty()) {
          excluded_invoke_insns->insert(insn);
          continue;
        }
        callee_caller->update(callee,
                              [caller](const DexMethod*,
                                       UnorderedMap<DexMethod*, size_t>& v,
                                       bool) { ++v[caller]; });
        caller_callee->update(caller,
                              [callee](const DexMethod*,
                                       UnorderedMap<DexMethod*, size_t>& v,
                                       bool) { ++v[callee]; });
        arg_exclusivity->emplace(insn, std::move(ae));
        callee_caller_classes->update(
            callee,
            [caller](const DexMethod*,
                     UnorderedSet<const DexType*>& value,
                     bool) { value.insert(caller->get_class()); });
      }
    }
  });
}

using InvokeCallSiteSummaries =
    UnorderedMap<const IRInstruction*, const CallSiteSummary*>;

// Whether to include a particular constant argument value. We only include
// actual constant (not just abstract value like NEZ), and only if they don't
// violate anything the ref-checker would complain about. We can also handle
// singletons and immutable objects if they represent jvm cached singletons.
bool filter(const RefChecker& ref_checker,
            EnumUtilsCache& enum_utils_cache,
            const ConstantValue& value) {
  if (const auto& signed_value = value.maybe_get<SignedConstantDomain>()) {
    return !!signed_value->get_constant();
  } else if (const auto& singleton_value =
                 value.maybe_get<SingletonObjectDomain>()) {
    const auto* field = *singleton_value->get_constant();
    return ref_checker.check_field(field);
  } else if (const auto& obj_or_none =
                 value.maybe_get<ObjectWithImmutAttrDomain>()) {
    auto object = obj_or_none->get_constant();
    if (!object->jvm_cached_singleton) {
      return false;
    }
    if (DexField* field =
            try_get_enum_utils_f_field(enum_utils_cache, *object)) {
      return ref_checker.check_field(field);
    } else {
      const auto& signed_value2 =
          only(object->attributes).value.maybe_get<SignedConstantDomain>();
      always_assert(signed_value2);
      return filter(ref_checker, enum_utils_cache, *signed_value2);
    }
    // NOLINTNEXTLINE(bugprone-branch-clone)
  } else if (const auto& string_value = value.maybe_get<StringDomain>()) {
    // TODO: Support strings.
    return false;
    // NOLINTNEXTLINE(bugprone-branch-clone)
  } else if (const auto& class_or_none =
                 value.maybe_get<ConstantClassObjectDomain>()) {
    // TODO: Support class objects.
    return false;
    // NOLINTNEXTLINE(bugprone-branch-clone)
  } else if (const auto& new_obj_or_none = value.maybe_get<NewObjectDomain>()) {
    return false;
  } else {
    not_reached_log("unexpected value: %s", SHOW(value));
  }
}

using CallSiteSummarySet = UnorderedSet<const CallSiteSummary*>;
using CallSiteSummaryVector = std::vector<const CallSiteSummary*>;
CallSiteSummaryVector order_csses(const CallSiteSummarySet& csses) {
  return unordered_to_ordered(
      csses, [](const CallSiteSummary* a, const CallSiteSummary* b) {
        return a->get_key() < b->get_key();
      });
}

// Priority-queue based algorithm to select which invocations and which constant
// arguments are beneficial to transform.
class CalleeInvocationSelector {
 private:
  EnumUtilsCache& m_enum_utils_cache;
  CallSiteSummarizer& m_call_site_summarizer;
  const DexMethod* m_callee;
  const InsnsArgExclusivity& m_arg_exclusivity;
  size_t m_callee_caller_classes;

  param_index_t m_src_regs;
  bool m_needs_range;

  // When we merge different call-site summaries after simplifying, we need to
  // track which weaker summary each one got folded into, so that we can later
  // serve each invoke with a helper method that binds constants the invoke
  // actually passes.
  partial_application::CallSiteSummaryReductions m_reductions;

  CallSiteSummarySet m_call_site_summaries;
  using ArgumentCosts = UnorderedMap<src_index_t, int32_t>;
  UnorderedMap<const CallSiteSummary*, ArgumentCosts>
      m_call_site_summary_argument_costs;
  using KeyedCosts = UnorderedMap<std::string, int32_t>;
  std::vector<KeyedCosts> m_total_argument_costs;
  using KeyedCsses = UnorderedMap<std::string, CallSiteSummarySet>;
  std::vector<KeyedCsses> m_dependencies;
  std::vector<std::pair<const IRInstruction*, const CallSiteSummary*>>
      m_call_site_invoke_summaries;

  UnorderedMap<const CallSiteSummary*,
               UnorderedMap<src_index_t, AggregatedArgExclusivity>>
      m_aggregated_arg_exclusivity;

  const PartialApplicationConfig& m_cost_config;

  static std::string get_key(const ConstantValue& value) {
    std::ostringstream oss;
    CallSiteSummary::append_key_value(oss, value);
    return oss.str();
  }

  static int32_t sum_call_sites_savings(const ArgumentCosts& ac) {
    int32_t savings = 0;
    for (const auto& p : UnorderedIterable(ac)) {
      savings += p.second;
    }
    return savings;
  }

  int16_t const_value_cost(const ConstantValue& value) const {
    if (const auto& signed_value = value.maybe_get<SignedConstantDomain>()) {
      auto c = signed_value->get_constant();
      always_assert(c);
      auto lit = *c;
      if (lit < -2147483648 || lit > 2147483647) {
        return static_cast<int16_t>(m_cost_config.const_signed_cost_base +
                                    m_cost_config.const_signed_cost_addon_1 +
                                    m_cost_config.const_signed_cost_addon_2 +
                                    m_cost_config.const_signed_cost_addon_3);
      } else if (lit < -32768 || lit > 32767) {
        return static_cast<int16_t>(m_cost_config.const_signed_cost_base +
                                    m_cost_config.const_signed_cost_addon_1 +
                                    m_cost_config.const_signed_cost_addon_2);
      } else if (lit < -8 || lit > 7) {
        return static_cast<int16_t>(m_cost_config.const_signed_cost_base +
                                    m_cost_config.const_signed_cost_addon_1);
      } else {
        return static_cast<int16_t>(m_cost_config.const_signed_cost_base);
      }
    } else if (const auto& singleton_value =
                   value.maybe_get<SingletonObjectDomain>()) {
      return static_cast<int16_t>(m_cost_config.const_singleton_cost);
    } else if (const auto& obj_or_none =
                   value.maybe_get<ObjectWithImmutAttrDomain>()) {
      auto object = obj_or_none->get_constant();
      always_assert(object);
      if (try_get_enum_utils_f_field(m_enum_utils_cache, *object) != nullptr) {
        return static_cast<int16_t>(m_cost_config.const_obj_or_none_cost_1);
      } else {
        always_assert(object->jvm_cached_singleton);
        const auto& signed_value2 =
            only(object->attributes).value.maybe_get<SignedConstantDomain>();
        always_assert(signed_value2);
        return static_cast<int16_t>(m_cost_config.const_obj_or_none_cost_2 +
                                    const_value_cost(*signed_value2));
      }
    } else {
      not_reached_log("unexpected value: %s", SHOW(value));
    }
  }

  std::pair<param_index_t, uint32_t> find_argument_with_least_cost(
      const CallSiteSummary* css) const {
    const auto& bindings = css->arguments.bindings();
    std::optional<int32_t> least_cost;
    param_index_t least_cost_src_idx = 0;
    for (const auto& p : bindings) {
      const auto& arguments_cost = m_total_argument_costs.at(p.first);
      auto it = arguments_cost.find(get_key(p.second));
      auto cost = it == arguments_cost.end() ? 0 : it->second;
      if (!least_cost || *least_cost > cost ||
          (*least_cost == cost && p.first < least_cost_src_idx)) {
        least_cost = cost;
        least_cost_src_idx = p.first;
      }
    }
    always_assert(least_cost);
    return {least_cost_src_idx, *least_cost};
  }

  int32_t get_net_savings(const CallSiteSummary* css) const {
    // The cost for an additional partial-application helper method consists
    // of...
    // - the basic overhead of having a method
    // - an estimated cross-dex penalty, as the PartialApplication pass has to
    //   run before the InterDex pass, and adding extra method-refs has global
    //   negative effects on the number of needed cross-dex references.
    // - an extra move-result instruction
    // - the cost of const instructions
    // - some extra potetnail move overhead if we need the range form
    int32_t pa_cross_dex_penalty =
        static_cast<int32_t>(2 * std::ceil(std::sqrt(m_callee_caller_classes)));
    int32_t pa_method_cost = static_cast<int32_t>(m_cost_config.cost_method) +
                             pa_cross_dex_penalty +
                             static_cast<int32_t>(css->result_used);
    const auto& bindings = css->arguments.bindings();
    for (const auto& r : bindings) {
      pa_method_cost += const_value_cost(r.second);
    }
    if (m_needs_range) {
      pa_method_cost += static_cast<int32_t>(m_src_regs);
    }

    auto call_sites_savings =
        sum_call_sites_savings(m_call_site_summary_argument_costs.at(css));
    return call_sites_savings - pa_method_cost;
  }

  using Priority = uint64_t;
  uint64_t m_running_index = 0;
  Priority make_priority(const CallSiteSummary* css) {
    // We order by...
    // - (1 bit) whether net savings are positive
    // - (31 bits) if not, (clipped) least argument costs (smaller is better)
    // - (32 bits) running index to make the priority unique
    auto net_savings = get_net_savings(css);
    uint64_t positive = static_cast<uint64_t>(net_savings > 0);
    uint64_t a = 0;
    if (positive == 0u) {
      auto least_cost = find_argument_with_least_cost(css).second;
      a = std::min<uint32_t>(least_cost, (1U << 31) - 1);
    }
    uint64_t b = m_running_index++;
    always_assert(positive < 2);
    always_assert(a < (1UL << 31));
    always_assert(b < (static_cast<uint64_t>(1u) << 32));
    return (positive << 63) | (a << 32) | b;
  }

  MutablePriorityQueue<const CallSiteSummary*, Priority> m_pq;

 public:
  CalleeInvocationSelector(EnumUtilsCache& enum_utils_cache,
                           CallSiteSummarizer& call_site_summarizer,
                           const DexMethod* callee,
                           const InsnsArgExclusivity& arg_exclusivity,
                           size_t callee_caller_classes,
                           const PartialApplicationConfig& cost_config)
      : m_enum_utils_cache(enum_utils_cache),
        m_call_site_summarizer(call_site_summarizer),
        m_callee(callee),
        m_arg_exclusivity(arg_exclusivity),
        m_callee_caller_classes(callee_caller_classes),
        m_cost_config(cost_config) {
    const auto* callee_call_site_invokes =
        call_site_summarizer.get_callee_call_site_invokes(callee);
    if (callee_call_site_invokes == nullptr) {
      return;
    }

    std::tie(m_src_regs, m_needs_range) = analyze_args(callee);
    TRACE(
        PA, 2,
        "[PartialApplication] Processing %s, %zu caller classes, %u src regs%s",
        SHOW(m_callee), callee_caller_classes, m_src_regs,
        m_needs_range ? ", needs_range" : "");

    m_total_argument_costs = std::vector<KeyedCosts>(m_src_regs, KeyedCosts());
    m_dependencies = std::vector<KeyedCsses>(m_src_regs, KeyedCsses());

    // Aggregate arg exclusivity across call-sites with the same summary.
    for (const auto* invoke_insn : *callee_call_site_invokes) {
      const auto* css =
          call_site_summarizer.get_instruction_call_site_summary(invoke_insn);
      if (css->arguments.is_top()) {
        continue;
      }
      if (!is_static(callee) && !css->arguments.get(0).is_top()) {
        // We don't want to deal with cases where an instance method is called
        // with nullptr.
        TRACE(PA, 2,
              "[PartialApplication] Ignoring invocation of instance method %s "
              "with %s",
              SHOW(callee), css->get_key().c_str());
        continue;
      }
      m_call_site_invoke_summaries.emplace_back(invoke_insn, css);
      const auto& aev = arg_exclusivity.at_unsafe(invoke_insn);
      auto& aaem = m_aggregated_arg_exclusivity[css];
      for (const auto& p : aev) {
        auto& aae = aaem[p.first];
        aae.ownership += p.second.ownership;
        aae.needs_move += static_cast<unsigned int>(p.second.needs_move);
      }
    }

    // For each call-site summary,
    // - compute current constant argument costs that could potentially be saved
    //   when introducing partial-application helper method, and
    // - keep track of which constant value for which parameter is involved in
    // that call-site summary, which we'll need later when re-prioritizing
    // call-site summaries in the priority queue.
    for (auto& p : UnorderedIterable(m_aggregated_arg_exclusivity)) {
      const auto* css = p.first;
      auto& aaem = p.second;
      m_call_site_summaries.insert(css);
      auto& ac = m_call_site_summary_argument_costs[css];
      const auto& bindings = css->arguments.bindings();
      for (const auto& q : bindings) {
        const auto src_idx = q.first;
        const auto& value = q.second;
        auto& aae = aaem[src_idx];
        int32_t cost = static_cast<int32_t>(
            const_value_cost(value) * aae.ownership + 2 * aae.needs_move);
        ac.emplace(src_idx, cost);
        auto key = get_key(value);
        m_total_argument_costs.at(src_idx)[key] += cost;
        m_dependencies.at(src_idx)[key].insert(css);
      }
    }
  }

  // Fill priority queue with raw data.
  void fill_pq() {
    // Populate priority queue
    for (const auto* css : order_csses(m_call_site_summaries)) {
      auto priority = make_priority(css);
      TRACE(PA, 4,
            "[PartialApplication] Considering %s(%s): net savings %d, priority "
            "%016" PRIx64,
            SHOW(m_callee), css->get_key().c_str(), get_net_savings(css),
            priority);
      m_pq.insert(css, priority);
    }
  }

  // For all items in the queue which have non-positive net savings, chop
  // off the argument with least cost, and lump it together with any
  // possibly already existing item.
  void reduce_pq() {
    while (!m_pq.empty() && get_net_savings(m_pq.back()) <= 0) {
      const auto* css = m_pq.back();
      m_pq.erase(css);
      auto ac_it = m_call_site_summary_argument_costs.find(css);
      auto ac = std::move(ac_it->second);
      m_call_site_summary_argument_costs.erase(ac_it);
      for (const auto& p : css->arguments.bindings()) {
        bool erased =
            m_dependencies.at(p.first).at(get_key(p.second)).erase(css) != 0u;
        always_assert(erased);
      }
      auto [src_idx, least_cost] = find_argument_with_least_cost(css);
      always_assert(!css->arguments.get(src_idx).is_top());
      auto key = get_key(css->arguments.get(src_idx));
      m_total_argument_costs.at(src_idx).at(key) -= ac.at(src_idx);

      CallSiteSummary reduced_css_val{css->arguments, css->result_used};
      reduced_css_val.arguments.set(src_idx, ConstantValue::top());
      if (reduced_css_val.arguments.is_top()) {
        TRACE(PA, 4,
              "[PartialApplication] Removing %s(%s) with least cost %u@%u",
              SHOW(m_callee), css->get_key().c_str(), least_cost, src_idx);
      } else {
        const auto* reduced_css =
            m_call_site_summarizer.internalize_call_site_summary(
                reduced_css_val);
        ac_it = m_call_site_summary_argument_costs.find(reduced_css);
        if (ac_it == m_call_site_summary_argument_costs.end()) {
          ac_it = m_call_site_summary_argument_costs
                      .emplace(reduced_css, ArgumentCosts())
                      .first;
          for (const auto& p : reduced_css->arguments.bindings()) {
            bool inserted = m_dependencies.at(p.first)
                                .at(get_key(p.second))
                                .insert(reduced_css)
                                .second;
            always_assert(inserted);
          }
        } else {
          m_pq.erase(reduced_css);
        }
        for (auto& p : UnorderedIterable(ac)) {
          ac_it->second[p.first] += p.second;
        }
        ac_it->second.erase(src_idx);
        m_pq.insert(reduced_css, make_priority(reduced_css));
        m_call_site_summaries.insert(reduced_css);
        m_reductions.add(css, reduced_css);
        TRACE(PA, 4,
              "[PartialApplication] Merging %s(%s ===> %s) with least cost "
              "%u@%u: net savings %d",
              SHOW(m_callee), css->get_key().c_str(),
              reduced_css->get_key().c_str(), least_cost, src_idx,
              get_net_savings(reduced_css));
      }
      const auto& csses = m_dependencies.at(src_idx).at(key);
      for (const auto* dependent_css : order_csses(csses)) {
        TRACE(PA, 4, "[PartialApplication] Reprioritizing %s(%s)",
              SHOW(m_callee), dependent_css->get_key().c_str());
        m_pq.update_priority(dependent_css, make_priority(dependent_css));
      }
    }
  }

  // Identify all invocations which contributed to groups with combined positive
  // expected savings.
  void select_invokes(std::atomic<size_t>* total_estimated_savings,
                      InvokeCallSiteSummaries* selected_invokes) {
    UnorderedMap<const CallSiteSummary*, int32_t> selected_net_savings;
    while (!m_pq.empty()) {
      const auto* css = m_pq.front();
      auto net_savings = get_net_savings(css);
      m_pq.erase(css);
      always_assert(net_savings > 0);
      selected_net_savings.emplace(css, net_savings);
      TRACE(PA, 3, "[PartialApplication] Selected %s(%s) with net savings %d",
            SHOW(m_callee), css->get_key().c_str(), net_savings);
    }
    auto is_selected = [&selected_net_savings](const CallSiteSummary* css) {
      return selected_net_savings.count(css) != 0u;
    };

    UnorderedSet<const CallSiteSummary*> used_csses;

    for (auto& p : m_call_site_invoke_summaries) {
      const auto* invoke_insn = p.first;
      const auto* css = p.second;
      // Follow the chain of reductions to the strongest selected summary that
      // this invoke's own constant arguments still satisfy.
      const auto* reduced_css = m_reductions.find_selected(css, is_selected);
      if (reduced_css == nullptr) {
        continue;
      }
      always_assert_log(partial_application::is_reduction_of(reduced_css, css),
                        "%s(%s) is not a reduction of %s", SHOW(m_callee),
                        reduced_css->get_key().c_str(), css->get_key().c_str());
      // This invoke got selected because including it together with all
      // other invokes with the same css was beneficial on average. Check
      // (and filter out) if it's not actually beneficial for this particular
      // invoke.
      const auto& aev = m_arg_exclusivity.at_unsafe(invoke_insn);
      const auto& bindings = reduced_css->arguments.bindings();
      if (std::find_if(aev.begin(), aev.end(), [&bindings](auto& q) {
            return !bindings.at(q.first).is_top();
          }) == aev.end()) {
        continue;
      }
      used_csses.insert(reduced_css);
      selected_invokes->emplace(invoke_insn, reduced_css);
    }

    // Only summaries that actually ended up serving an invoke will cause a
    // helper method to be created, so only those contribute savings.
    uint32_t callee_estimated_savings = 0;
    for (const auto* css : UnorderedIterable(used_csses)) {
      callee_estimated_savings += selected_net_savings.at(css);
    }
    if (callee_estimated_savings > 0) {
      TRACE(PA, 2,
            "[PartialApplication] Selected %s(...) for %zu constant argument "
            "combinations across %zu invokes with net savings %u",
            SHOW(m_callee), used_csses.size(), selected_invokes->size(),
            callee_estimated_savings);
      *total_estimated_savings += callee_estimated_savings;
    }
  }
};

// From a call-site summary that include constant-arguments, derive the
// signature of the new helper methods that will bind them.
DexTypeList* get_partial_application_args(bool callee_is_static,
                                          const DexProto* callee_proto,
                                          const CallSiteSummary* css) {
  const auto* args = callee_proto->get_args();
  DexTypeList::ContainerType new_args;
  param_index_t offset = 0;
  if (!callee_is_static) {
    always_assert(css->arguments.get(0).is_top());
    offset++;
  }
  for (param_index_t i = 0; i < args->size(); i++) {
    if (css->arguments.get(offset + i).is_top()) {
      new_args.push_back(args->at(i));
    }
  }
  return DexTypeList::make_type_list(std::move(new_args));
}

uint64_t get_stable_hash(uint64_t a, uint64_t b) { return a ^ b; }

uint64_t get_stable_hash(const std::string& s) {
  uint64_t stable_hash{s.size()};
  for (auto c : s) {
    stable_hash = stable_hash * 7 + c;
  }
  return stable_hash;
}

using PaMethodRefs =
    InsertOnlyConcurrentMap<CalleeCallSiteSummary,
                            DexMethodRef*,
                            boost::hash<CalleeCallSiteSummary>>;
// Run the analysis over all callees.
void select_invokes_and_callers(
    EnumUtilsCache& enum_utils_cache,
    CallSiteSummarizer& call_site_summarizer,
    const ConcurrentMethodToMethodOccurrences& callee_caller,
    const InsnsArgExclusivity& arg_exclusivity,
    const CalleeCallerClasses& callee_caller_classes,
    size_t iteration,
    std::atomic<size_t>* total_estimated_savings,
    PaMethodRefs* pa_method_refs,
    InvokeCallSiteSummaries* selected_invokes,
    UnorderedSet<DexMethod*>* selected_callers,
    const PartialApplicationConfig& config) {
  Timer t("select_invokes_and_callers");
  std::vector<const DexMethod*> callees;
  UnorderedMap<const DexType*, std::vector<const DexMethod*>>
      callees_by_classes;
  UnorderedMap<const DexMethod*, InvokeCallSiteSummaries>
      selected_invokes_by_callees;
  for (const auto& p : UnorderedIterable(callee_caller)) {
    const auto* callee = p.first;
    callees.push_back(callee);
    callees_by_classes[callee->get_class()].push_back(callee);
    selected_invokes_by_callees[callee];
  }

  workqueue_run<const DexMethod*>(
      [&](const DexMethod* callee) {
        CalleeInvocationSelector cis(
            enum_utils_cache, call_site_summarizer, callee, arg_exclusivity,
            callee_caller_classes.at_unsafe(callee).size(), config);
        cis.fill_pq();
        cis.reduce_pq();
        cis.select_invokes(total_estimated_savings,
                           &selected_invokes_by_callees.at(callee));
      },
      callees);

  std::vector<const DexType*> callee_classes;
  callee_classes.reserve(callees_by_classes.size());
  for (auto& p : UnorderedIterable(callees_by_classes)) {
    callee_classes.push_back(p.first);
  }
  std::mutex mutex;
  workqueue_run<const DexType*>(
      [&](const DexType* callee_class) {
        auto& class_callees = callees_by_classes.at(callee_class);
        std::sort(class_callees.begin(), class_callees.end(),
                  compare_dexmethods);
        UnorderedMap<uint64_t, uint32_t> stable_hash_indices;
        for (const auto* callee : class_callees) {
          auto& callee_selected_invokes =
              selected_invokes_by_callees.at(callee);
          if (callee_selected_invokes.empty()) {
            continue;
          }
          auto callee_stable_hash = get_stable_hash(show(callee));
          std::map<const DexTypeList*, UnorderedSet<const CallSiteSummary*>,
                   dextypelists_comparator>
              ordered_pa_args_csses;
          auto callee_is_static = is_static(callee);
          auto* callee_proto = callee->get_proto();
          for (auto& p : UnorderedIterable(callee_selected_invokes)) {
            const auto* css = p.second;
            auto* pa_args = get_partial_application_args(callee_is_static,
                                                         callee_proto, css);
            [[maybe_unused]] auto inserted =
                ordered_pa_args_csses[pa_args].insert(css).second;
            always_assert(true);
          }
          for (auto& p : ordered_pa_args_csses) {
            const auto* pa_args = p.first;
            auto& csses = p.second;
            for (const auto* css : order_csses(csses)) {
              auto css_stable_hash = get_stable_hash(css->get_key());
              auto stable_hash =
                  get_stable_hash(callee_stable_hash, css_stable_hash);
              auto stable_hash_index = stable_hash_indices[stable_hash]++;
              std::ostringstream oss;
              oss << callee->get_name()->str()
                  << (is_static(callee) ? "$spa$" : "$ipa$") << iteration << "$"
                  << ((boost::format("%08x") % stable_hash).str()) << "$"
                  << stable_hash_index;
              const auto* pa_name = DexString::make_string(oss.str());
              auto* pa_rtype =
                  css->result_used ? callee_proto->get_rtype() : type::_void();
              auto* pa_proto = DexProto::make_proto(pa_rtype, pa_args);
              auto* pa_type = callee->get_class();
              auto* pa_method_ref =
                  DexMethod::make_method(pa_type, pa_name, pa_proto);
              CalleeCallSiteSummary ccss{callee, css};
              pa_method_refs->emplace(ccss, pa_method_ref);
            }
          }
          std::lock_guard<std::mutex> lock_guard(mutex);
          insert_unordered_iterable(*selected_invokes, callee_selected_invokes);
          for (const auto& p :
               UnorderedIterable(callee_caller.at_unsafe(callee))) {
            selected_callers->insert(p.first);
          }
        }
      },
      callee_classes);
}

IROpcode get_invoke_opcode(const DexMethod* callee) {
  return callee->is_virtual() ? OPCODE_INVOKE_VIRTUAL
         : is_static(callee)  ? OPCODE_INVOKE_STATIC
                              : OPCODE_INVOKE_DIRECT;
}

using PaCallers = ConcurrentMap<DexMethodRef*, std::vector<DexMethod*>>;
// Per helper method, a copy of the source block covering each call-site it will
// serve. These are copies rather than pointers because `shrink_method` below
// may free the blocks they live in.
using PaCallSiteSourceBlocks =
    ConcurrentMap<DexMethodRef*, std::vector<SourceBlock>>;

// Given the analysis results, rewrite all callers to invoke the new helper
// methods with bound arguments.
void rewrite_callers(
    const Scope& scope,
    Shrinker& shrinker,
    const GetCalleeFunction& get_callee_fn,
    const UnorderedMap<const IRInstruction*, const CallSiteSummary*>&
        selected_invokes,
    const UnorderedSet<DexMethod*>& selected_callers,
    PaMethodRefs& pa_method_refs,
    std::atomic<size_t>* removed_args,
    PaCallers* pa_callers,
    PaCallSiteSourceBlocks* pa_call_site_source_blocks) {
  Timer t("rewrite_callers");

  auto make_partial_application_invoke_insn =
      [&](DexMethod* caller, IRInstruction* insn) -> IRInstruction* {
    if (!opcode::is_an_invoke(insn->opcode())) {
      return nullptr;
    }
    auto it = selected_invokes.find(insn);
    if (it == selected_invokes.end()) {
      return nullptr;
    }
    auto* callee = get_callee_fn(caller, insn);
    always_assert(callee != nullptr);
    const auto* css = it->second;
    CalleeCallSiteSummary ccss{callee, css};
    DexMethodRef* pa_method_ref = pa_method_refs.at_unsafe(ccss);
    auto* new_insn = (new IRInstruction(get_invoke_opcode(callee)))
                         ->set_method(pa_method_ref);
    new_insn->set_srcs_size(insn->srcs_size() - css->arguments.size());
    param_index_t idx = 0;
    for (param_index_t i = 0; i < insn->srcs_size(); i++) {
      if (css->arguments.get(i).is_top()) {
        new_insn->set_src(idx++, insn->src(i));
      }
    }
    always_assert(idx == new_insn->srcs_size());
    return new_insn;
  };

  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    if (selected_callers.count(caller) == 0u) {
      return;
    }
    always_assert(!caller->rstate.no_optimizations());
    bool any_changes{false};
    auto& cfg = code.cfg();
    cfg::CFGMutation mutation(cfg);
    auto ii = InstructionIterable(cfg);
    size_t removed_srcs{0};
    UnorderedSet<DexMethodRef*> pas;
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* new_invoke_insn =
          make_partial_application_invoke_insn(caller, it->insn);
      if (new_invoke_insn == nullptr) {
        continue;
      }
      removed_srcs += it->insn->srcs_size() - new_invoke_insn->srcs_size();
      std::vector<IRInstruction*> new_insns{new_invoke_insn};
      auto move_result_it = cfg.move_result_of(it);
      if (!move_result_it.is_end()) {
        new_insns.push_back(new IRInstruction(*move_result_it->insn));
      }
      auto* pa = new_invoke_insn->get_method();
      if (pas.insert(pa).second) {
        pa_callers->update(
            pa, [caller](auto*, auto& vec, bool) { vec.push_back(caller); });
      }
      // Remember how hot this particular call-site is, so that the helper
      // method can be given a matching source block. The block covering the
      // call-site is a much better estimate than the caller's entry block: a
      // hot method may well reach this callee only from a cold path. Unlike
      // pa_callers, this is deliberately not deduplicated per caller: the
      // helper runs once per call-site execution, so every call-site
      // contributes its own count.
      if (pa_call_site_source_blocks != nullptr) {
        auto* call_site_sb = source_blocks::get_last_source_block_before(
            it.block(), it.unwrap());
        if (call_site_sb != nullptr) {
          // Copy outside the update callback, which holds a lock. Dropping the
          // chain first keeps that copy to a single source block; the chain is
          // irrelevant here, as the synthetic clone drops it anyway.
          SourceBlock sb_copy(*call_site_sb);
          sb_copy.next.reset();
          pa_call_site_source_blocks->update(
              pa,
              [&sb_copy](auto*, auto& vec, bool) { vec.push_back(sb_copy); });
        }
      }
      // Scheduled last: the source-block read above must see the block as it
      // is now, rather than relying on CFGMutation deferring its edits.
      mutation.replace(it, new_insns);
      any_changes = true;
    }
    mutation.flush();
    if (any_changes) {
      TRACE(PA, 6, "[PartialApplication] Rewrote %s:\n%s", SHOW(caller),
            SHOW(cfg));
      shrinker.shrink_method(caller);
      (*removed_args) += removed_srcs;
    }
  });
}

// Helper used to build the partial-assignment helper methods.
void push_callee_arg(EnumUtilsCache& enum_utils_cache,
                     const DexType* type,
                     const ConstantValue& value,
                     MethodCreator* method_creator,
                     MethodBlock* main_block,
                     std::vector<Location>* callee_args) {
  if (const auto& signed_value = value.maybe_get<SignedConstantDomain>()) {
    auto c = signed_value->get_constant();
    always_assert(c);
    auto tmp = method_creator->make_local(type);
    main_block->load_const(tmp, *c, type);
    callee_args->push_back(tmp);
  } else if (const auto& singleton_value =
                 value.maybe_get<SingletonObjectDomain>()) {
    auto c = singleton_value->get_constant();
    always_assert(c);
    const auto* field = *c;
    always_assert(is_static(field));
    auto tmp = method_creator->make_local(type);
    main_block->sfield_op(opcode::sget_opcode_for_field(field),
                          const_cast<DexField*>(field), tmp);
    callee_args->push_back(tmp);
  } else if (const auto& obj_or_none =
                 value.maybe_get<ObjectWithImmutAttrDomain>()) {
    auto object = obj_or_none->get_constant();
    always_assert(object);
    if (DexField* field =
            try_get_enum_utils_f_field(enum_utils_cache, *object)) {
      auto tmp = method_creator->make_local(field->get_type());
      main_block->sfield_op(opcode::sget_opcode_for_field(field), field, tmp);
      callee_args->push_back(tmp);
    } else {
      always_assert(object->jvm_cached_singleton);
      const auto& attribute = only(object->attributes);
      auto* valueOf = type::get_value_of_method_for_type(object->type);
      const auto* valueOf_arg_type = valueOf->get_proto()->get_args()->at(0);
      auto tmp = method_creator->make_local(valueOf_arg_type);
      const auto& signed_value2 =
          attribute.value.maybe_get<SignedConstantDomain>();
      always_assert(signed_value2);
      auto c = signed_value2->get_constant();
      always_assert(c);
      main_block->load_const(tmp, *c, valueOf_arg_type);
      main_block->invoke(OPCODE_INVOKE_STATIC, valueOf, {tmp});
      tmp = method_creator->make_local(type);
      main_block->move_result(tmp, type);
      callee_args->push_back(tmp);
    }
  } else {
    not_reached_log("unexpected value: %s", SHOW(value));
  }
}

// Create all new helper methods that bind constant arguments
void create_partial_application_methods(
    EnumUtilsCache& enum_utils_cache,
    PaMethodRefs& pa_method_refs,
    PaCallSiteSourceBlocks& pa_call_site_source_blocks) {
  Timer t("create_partial_application_methods");
  std::map<DexMethodRef*, const CalleeCallSiteSummary*, dexmethods_comparator>
      inverse_ordered_pa_method_refs;
  for (auto& p : UnorderedIterable(pa_method_refs)) {
    bool success =
        inverse_ordered_pa_method_refs.emplace(p.second, &p.first).second;
    always_assert(success);
  }
  for (auto& p : inverse_ordered_pa_method_refs) {
    auto* pa_method_ref = p.first;
    const auto* callee = p.second->method;
    auto* cls = type_class(callee->get_class());
    always_assert(cls);
    const auto* css = p.second->call_site_summary;
    auto access = callee->get_access() & ~(ACC_ABSTRACT | ACC_NATIVE);
    if (callee->is_virtual()) {
      access |= ACC_FINAL;
    }
    MethodCreator method_creator(pa_method_ref, access);
    auto* main_block = method_creator.get_main_block();
    std::vector<Location> callee_args;
    param_index_t offset = 0;
    param_index_t next_arg_idx = 0;
    if (!is_static(callee)) {
      always_assert(css->arguments.get(0).is_top());
      offset++;
      callee_args.push_back(method_creator.get_local(next_arg_idx++));
    }
    auto* proto = callee->get_proto();
    const auto* args = proto->get_args();
    for (param_index_t i = 0; i < args->size(); i++) {
      const auto& value = css->arguments.get(offset + i);
      if (value.is_top()) {
        callee_args.push_back(method_creator.get_local(next_arg_idx++));
      } else {
        push_callee_arg(enum_utils_cache, args->at(i), value, &method_creator,
                        main_block, &callee_args);
      }
    }
    main_block->invoke(get_invoke_opcode(callee),
                       const_cast<DexMethod*>(callee), callee_args);
    if (css->result_used) {
      auto tmp = method_creator.make_local(proto->get_rtype());
      main_block->move_result(tmp, proto->get_rtype());
      main_block->ret(tmp);
    } else {
      main_block->ret_void();
    }
    auto* pa_method = method_creator.create();
    pa_method->rstate.set_generated();
    pa_method->rstate.set_dont_inline();
    if (!is_static(callee) && is_public(callee)) {
      pa_method->set_virtual(true);
    }
    pa_method->set_deobfuscated_name(show_deobfuscated(pa_method));
    pa_method->get_code()->build_cfg();
    // The helper method is only ever reached from the call-sites we rewrote, so
    // derive its hotness from theirs. Without source blocks, later passes and
    // profile-guided layout would have no hotness information at all for these
    // methods, even though they sit on the path of every call-site they serve.
    // Empty unless the fix is enabled, in which case rewrite_callers gathered
    // a source block per call-site this helper serves.
    auto* call_site_sbs = pa_call_site_source_blocks.get_unsafe(pa_method_ref);
    if (call_site_sbs != nullptr && !call_site_sbs->empty()) {
      std::vector<SourceBlock*> sbs;
      sbs.reserve(call_site_sbs->size());
      for (auto& sb : *call_site_sbs) {
        sbs.push_back(&sb);
      }
      source_blocks::insert_synthetic_source_blocks_in_method(
          pa_method, [pa_method, &sbs]() {
            // N:1: the helper method is reached from every call-site it serves,
            // so its count is about the SUM of theirs, not the max.
            return source_blocks::clone_as_synthetic_summing(sbs.front(),
                                                             pa_method, sbs);
          });
    }
    cls->add_method(pa_method);
    TRACE(PA, 5, "[PartialApplication] Created %s binding %s:\n%s",
          SHOW(pa_method), css->get_key().c_str(),
          SHOW(pa_method->get_code()->cfg()));
  }
}

size_t derive_method_profiles_stats(ConfigFiles& config,
                                    const PaCallers& pa_callers) {
  auto& method_profiles = config.get_method_profiles();
  size_t res = 0;
  for (const auto& [pa_method_ref, callers] : UnorderedIterable(pa_callers)) {
    auto* pa_method = pa_method_ref->as_def();
    always_assert(pa_method);
    res += method_profiles.derive_stats(pa_method, callers);
  }
  return res;
}

} // namespace

void PartialApplicationPass::bind_config() {
  bind("cost_method", m_cost_config.cost_method, m_cost_config.cost_method,
       "Overhead of introducing a typical new helper method and its metadata.");
  bind("const_signed_cost_base", m_cost_config.const_signed_cost_base,
       m_cost_config.const_signed_cost_base);
  bind("const_signed_cost_addon_1", m_cost_config.const_signed_cost_addon_1,
       m_cost_config.const_signed_cost_addon_1);
  bind("const_signed_cost_addon_2", m_cost_config.const_signed_cost_addon_2,
       m_cost_config.const_signed_cost_addon_2);
  bind("const_signed_cost_addon_3", m_cost_config.const_signed_cost_addon_3,
       m_cost_config.const_signed_cost_addon_3);
  bind("const_singleton_cost", m_cost_config.const_singleton_cost,
       m_cost_config.const_singleton_cost);
  bind("const_obj_or_none_cost_1", m_cost_config.const_obj_or_none_cost_1,
       m_cost_config.const_obj_or_none_cost_1);
  bind("const_obj_or_none_cost_2", m_cost_config.const_obj_or_none_cost_2,
       m_cost_config.const_obj_or_none_cost_2);

  auto& pg = m_profile_guidance_config;
  bind("use_method_profiles", pg.use_method_profiles, pg.use_method_profiles,
       "Whether to use provided method-profiles configuration data to "
       "determine if certain code should not be outlined from a method");
  bind("enable_hotness_propagation", pg.enable_hotness_propagation,
       pg.enable_hotness_propagation,
       "Whether to propagate method hotness (and warmness) to cold callees "
       "if the call site blocks were executed.");
  bind("method_profiles_appear_percent", pg.method_profiles_appear_percent,
       pg.method_profiles_appear_percent,
       "Cut off when a method in a method profile is deemed relevant");
  bind("throughput_interaction_name_pattern",
       pg.throughput_interaction_name_pattern,
       pg.throughput_interaction_name_pattern,
       "Regular expression identifying throughput interaction names");
  bind("method_profiles_throughput_hot_call_count",
       pg.method_profiles_throughput_hot_call_count,
       pg.method_profiles_throughput_hot_call_count,
       "No code is outlined out of methods in throughput interactions");
  bind("method_profiles_hot_call_count",
       pg.method_profiles_hot_call_count,
       pg.method_profiles_hot_call_count,
       "No code is outlined out of hot methods");
  bind("method_profiles_warm_call_count",
       pg.method_profiles_warm_call_count,
       pg.method_profiles_warm_call_count,
       "Loops are not outlined from warm methods");
  bind("fix_missing_source_blocks",
       m_fix_missing_source_blocks,
       m_fix_missing_source_blocks,
       "Whether to fix up generated helper methods to have source blocks, "
       "derived from the call-sites they serve. Off by default, as it makes "
       "the helpers visible to profile-guided decisions such as inlining, "
       "which can move size and performance. TODO: Remove this option, and "
       "always fix up the source blocks, once the impact has been assessed");
  bind("derive_method_profiles_stats",
       m_derive_method_profiles_stats,
       m_derive_method_profiles_stats,
       "Whether to derive method profile stats for generated methods");
  std::string perf_sensitivity_str;
  bind("perf_sensitivity", "always-hot", perf_sensitivity_str);
  bind("block_profiles_hits",
       pg.block_profiles_hits,
       pg.block_profiles_hits,
       "No code is outlined out of hot blocks in hot methods");
  after_configuration(
      [this, perf_sensitivity_str = std::move(perf_sensitivity_str)]() {
        always_assert(!perf_sensitivity_str.empty());
        m_profile_guidance_config.perf_sensitivity =
            parse_perf_sensitivity(perf_sensitivity_str);
      });
}

void PartialApplicationPass::run_pass(DexStoresVector& stores,
                                      ConfigFiles& conf,
                                      PassManager& mgr) {
  const auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  auto excluded_classes = get_excluded_classes(stores);

  int min_sdk = mgr.get_redex_options().min_sdk;
  const auto* min_sdk_api = get_min_sdk_api(conf, mgr);
  XStoreRefs xstores(stores, conf.normal_primary_dex());
  // RefChecker store_idx is initialized with `largest_root_store_id()`, so that
  // it rejects all the references from stores with id larger than the largest
  // root_store id.
  RefChecker ref_checker(&xstores, xstores.largest_root_store_id(),
                         min_sdk_api);

  UnorderedSet<size_t> throughput_interaction_indices;
  UnorderedSet<std::string> throughput_interaction_ids;
  get_throughput_interactions(conf, m_profile_guidance_config,
                              &throughput_interaction_indices,
                              &throughput_interaction_ids);
  mgr.incr_metric("num_throughput_interactions",
                  throughput_interaction_ids.size());

  UnorderedSet<DexMethod*> throughput_methods;
  UnorderedSet<DexMethod*> sufficiently_warm_methods;
  UnorderedSet<DexMethod*> sufficiently_hot_methods;
  gather_sufficiently_warm_and_hot_methods(
      scope, conf, mgr, m_profile_guidance_config, throughput_interaction_ids,
      &throughput_methods, &sufficiently_warm_methods,
      &sufficiently_hot_methods);
  mgr.incr_metric("num_throughput_methods", throughput_methods.size());
  mgr.incr_metric("num_sufficiently_warm_methods",
                  sufficiently_warm_methods.size());
  mgr.incr_metric("num_sufficiently_hot_methods",
                  sufficiently_hot_methods.size());

  ShrinkerConfig shrinker_config;
  shrinker_config.run_local_dce = true;
  shrinker_config.compute_pure_methods = false;
  Shrinker shrinker(stores, scope, init_classes_with_side_effects, conf,
                    shrinker_config, min_sdk, {}, {}, {},
                    mgr.get_redex_options().package_name);

  ConcurrentSet<const IRInstruction*> excluded_invoke_insns;
  auto get_callee_fn = [&excluded_classes, &excluded_invoke_insns](
                           DexMethod* caller,
                           IRInstruction* insn) -> DexMethod* {
    if (!opcode::is_an_invoke(insn->opcode()) ||
        insn->opcode() == OPCODE_INVOKE_SUPER ||
        method::is_init(insn->get_method()) ||
        (excluded_invoke_insns.count(insn) != 0u) ||
        caller->rstate.no_optimizations() ||
        (excluded_classes.count(caller->get_class()) != 0u)) {
      return nullptr;
    }
    auto* callee = resolve_method_deprecated(insn->get_method(),
                                             opcode_to_search(insn), caller);
    if ((callee == nullptr) || callee->is_external() ||
        callee->rstate.should_not_outline()) {
      return nullptr;
    }
    auto* cls = type_class(callee->get_class());
    if ((cls == nullptr) || cls->is_external() ||
        (excluded_classes.count(cls->get_type()) != 0u)) {
      return nullptr;
    }
    // We'd add helper methods to the class, so we also want to avoid that it's
    // being used via reflection.
    if (!can_rename(cls)) {
      return nullptr;
    }
    // TODO: Support interface callees.
    if (is_interface(cls)) {
      return nullptr;
    }
    return callee;
  };

  ConcurrentMethodToMethodOccurrences callee_caller;
  ConcurrentMethodToMethodOccurrences caller_callee;
  InsnsArgExclusivity arg_exclusivity;
  CalleeCallerClasses callee_caller_classes;
  const OutlineabilityContext outlineability(
      m_profile_guidance_config, throughput_interaction_indices,
      throughput_methods, sufficiently_warm_methods, sufficiently_hot_methods);
  gather_caller_callees(outlineability, scope, get_callee_fn, &callee_caller,
                        &caller_callee, &arg_exclusivity,
                        &excluded_invoke_insns, &callee_caller_classes);

  TRACE(PA, 1, "[PartialApplication] %zu callers, %zu callees",
        caller_callee.size(), callee_caller.size());

  // By indicating to the call-site summarizer that any callee may have other
  // call-sites, we effectively disable top-down constant-propagation, as that
  // would be unlikely to find true constants, and yet would take more time by
  // limiting parallelism.
  auto has_callee_other_call_sites_fn = [](DexMethod*) -> bool { return true; };

  EnumUtilsCache enum_utils_cache;
  std::function<bool(const ConstantValue& value)> filter_fn =
      [&](const ConstantValue& value) {
        return filter(ref_checker, enum_utils_cache, value);
      };

  CallSiteSummaryStats call_site_summarizer_stats;
  CallSiteSummarizer call_site_summarizer(
      shrinker, callee_caller, caller_callee, get_callee_fn,
      has_callee_other_call_sites_fn, &filter_fn, &call_site_summarizer_stats);
  call_site_summarizer.summarize();

  std::atomic<size_t> total_estimated_savings{0};
  PaMethodRefs pa_method_refs;
  UnorderedMap<const IRInstruction*, const CallSiteSummary*> selected_invokes;
  UnorderedSet<DexMethod*> selected_callers;

  select_invokes_and_callers(
      enum_utils_cache, call_site_summarizer, callee_caller, arg_exclusivity,
      callee_caller_classes, m_iteration++, &total_estimated_savings,
      &pa_method_refs, &selected_invokes, &selected_callers, m_cost_config);

  std::atomic<size_t> removed_args{0};
  PaCallers pa_callers;
  PaCallSiteSourceBlocks pa_call_site_source_blocks;
  rewrite_callers(scope, shrinker, get_callee_fn, selected_invokes,
                  selected_callers, pa_method_refs, &removed_args, &pa_callers,
                  m_fix_missing_source_blocks ? &pa_call_site_source_blocks
                                              : nullptr);

  create_partial_application_methods(enum_utils_cache, pa_method_refs,
                                     pa_call_site_source_blocks);

  if (m_derive_method_profiles_stats) {
    size_t derived_method_profile_stats =
        derive_method_profiles_stats(conf, pa_callers);
    mgr.incr_metric("num_derived_method_profile_stats",
                    derived_method_profile_stats);
  }

  TRACE(PA, 1,
        "[PartialApplication] Created %zu methods with particular constant "
        "argument combinations, rewriting %zu invokes across %zu callers, "
        "removing %zu args, with (estimated) net savings %zu",
        pa_method_refs.size(), selected_invokes.size(), selected_callers.size(),
        (size_t)removed_args, (size_t)total_estimated_savings);
  mgr.incr_metric("total_estimated_savings", total_estimated_savings);
  mgr.incr_metric("rewritten_invokes", selected_invokes.size());
  mgr.incr_metric("removed_args", removed_args);
  mgr.incr_metric("affected_callers", selected_callers.size());
  mgr.incr_metric("partial_application_methods", pa_method_refs.size());
}

static PartialApplicationPass s_pass;
