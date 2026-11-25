/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "OutliningProfileGuidanceImpl.h"

#include <boost/regex.hpp>

#include "CallGraph.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "SourceBlocks.h"
#include "Walkers.h"

namespace outliner_impl {

using namespace outliner;

void get_throughput_interactions(
    ConfigFiles& config_files,
    const outliner::ProfileGuidanceConfig& config,
    UnorderedSet<size_t>* throughput_interaction_indices,
    UnorderedSet<std::string>* throughput_interaction_ids) {
  if (config.throughput_interaction_name_pattern.empty()) {
    return;
  }

  boost::regex rx(config.throughput_interaction_name_pattern);
  for (auto&& [interaction_id, interaction_name] :
       config_files.get_default_baseline_profile_config().interactions) {
    if (boost::regex_match(interaction_name, rx)) {
      throughput_interaction_ids->insert(interaction_id);
      auto index = g_redex->get_sb_interaction_index(interaction_id);
      if (index >= g_redex->num_sb_interaction_indices()) {
        TRACE(ISO, 1,
              "get_throughput_interactions: throughput interaction [%s] %s has "
              "no index!",
              interaction_id.c_str(), interaction_name.c_str());
        continue;
      }
      throughput_interaction_indices->insert(index);
    }
  }
}

void gather_sufficiently_warm_and_hot_methods(
    const Scope& scope,
    ConfigFiles& config_files,
    PassManager& mgr,
    const ProfileGuidanceConfig& config,
    const UnorderedSet<std::string>& throughput_interaction_ids,
    UnorderedSet<DexMethod*>* throughput_methods,
    UnorderedSet<DexMethod*>* sufficiently_warm_methods,
    UnorderedSet<DexMethod*>* sufficiently_hot_methods) {
  bool has_method_profiles{false};
  if (config.use_method_profiles) {
    auto& method_profiles = config_files.get_method_profiles();
    if (method_profiles.has_stats()) {
      has_method_profiles = true;
      for (const auto& p : method_profiles.all_interactions()) {
        bool is_throughput_interaction =
            throughput_interaction_ids.count(p.first) != 0;
        const auto& method_stats = p.second;
        walk::methods(
            scope,
            [throughput_methods, sufficiently_warm_methods,
             sufficiently_hot_methods, &method_stats, &config,
             is_throughput_interaction](DexMethod* method) {
              auto it = method_stats.find(method);
              if (it == method_stats.end()) {
                return;
              }
              if (it->second.appear_percent <
                  config.method_profiles_appear_percent) {
                return;
              }
              if (is_throughput_interaction &&
                  it->second.call_count >
                      config.method_profiles_throughput_hot_call_count) {
                throughput_methods->insert(method);
                return;
              }

              if (it->second.call_count >
                  config.method_profiles_hot_call_count) {
                sufficiently_hot_methods->insert(method);
                return;
              }

              if (it->second.call_count >=
                  config.method_profiles_warm_call_count) {
                sufficiently_warm_methods->insert(method);
              }
            });
      }
    }
  }

  UnorderedSet<DexType*> perf_sensitive_classes;
  if (mgr.interdex_has_run()) {
    walk::classes(scope, [&perf_sensitive_classes](DexClass* cls) {
      if (cls->is_perf_sensitive()) {
        perf_sensitive_classes.insert(cls->get_type());
      }
    });
  } else {
    for (const auto& str : config_files.get_coldstart_classes()) {
      DexType* type = DexType::get_type(str);
      if (type != nullptr) {
        perf_sensitive_classes.insert(type);
      }
    }
  }

  switch (config.perf_sensitivity) {
  case PerfSensitivity::kNeverUse:
    break;

  case PerfSensitivity::kWarmWhenNoProfiles:
    if (has_method_profiles) {
      break;
    }
    [[fallthrough]];
  case PerfSensitivity::kAlwaysWarm:
    walk::methods(scope,
                  [sufficiently_warm_methods,
                   &perf_sensitive_classes](DexMethod* method) {
                    if (perf_sensitive_classes.count(method->get_class()) !=
                        0u) {
                      sufficiently_warm_methods->insert(method);
                    }
                  });
    break;

  case PerfSensitivity::kHotWhenNoProfiles:
    if (has_method_profiles) {
      break;
    }
    [[fallthrough]];
  case PerfSensitivity::kAlwaysHot:
    walk::methods(
        scope,
        [sufficiently_hot_methods, &perf_sensitive_classes](DexMethod* method) {
          if (perf_sensitive_classes.count(method->get_class()) != 0u) {
            sufficiently_hot_methods->insert(method);
          }
        });
    break;
  }

  if (has_method_profiles && config.enable_hotness_propagation) {
    propagate_hotness(scope,
                      config_files,
                      sufficiently_warm_methods,
                      sufficiently_hot_methods,
                      config.block_profiles_hits);
  }
}

std::vector<DexMethod*> get_possibly_warm_or_hot_methods(
    const Scope& scope,
    ConfigFiles& config_files,
    UnorderedSet<DexMethod*>* sufficiently_warm_methods,
    UnorderedSet<DexMethod*>* sufficiently_hot_methods,
    float block_profiles_hits) {

  // This function will identify all methods, m, which were not called
  // according to method profiles, but whose entry blocks were executed
  // according to block profiles (i.e. with first source blocks in their entry
  // blocks which were executed).
  //
  // This scenario likely occurs due to inlining later on. Note that we track
  // method call counts for physical methods in the emitted dex, but block
  // coverage for blocks in pre-optimized input IR (i.e. "source blocks").
  //
  // We consider these methods "possibly warm or hot". Later, we may mark them
  // warm or hot if they have a caller which is warm or hot respectively.

  auto& method_profiles = config_files.get_method_profiles();

  struct plus_assign_vector {
    void operator()(const std::vector<DexMethod*>& addend,
                    std::vector<DexMethod*>* accumulator) {
      accumulator->insert(accumulator->end(), addend.begin(), addend.end());
    }
  };

  std::vector<DexMethod*> possibly_warm_or_hot =
      walk::parallel::methods<std::vector<DexMethod*>, plus_assign_vector>(
          scope,
          [&method_profiles, sufficiently_hot_methods,
           sufficiently_warm_methods,
           block_profiles_hits](DexMethod* m, std::vector<DexMethod*>* acc) {
            auto* code = m->get_code();
            if (code == nullptr) {
              return;
            }

            if ((sufficiently_hot_methods->count(m) != 0u) ||
                (sufficiently_warm_methods->count(m) != 0u)) {
              return;
            }

            const auto& all_interactions = method_profiles.all_interactions();
            bool in_method_profiles =
                std::any_of(all_interactions.begin(), all_interactions.end(),
                            [m](const auto& p) {
                              auto& method_stats = p.second;
                              auto it = method_stats.find(m);
                              return it != method_stats.end();
                            });

            if (in_method_profiles) {
              return;
            }

            // This method was not warm or hot, and was not called
            // according to method profiles.  See if its entry block
            // has source blocks which were executed.
            //
            // Note: from now on we can just return and process the
            // next method on success/failure, as there's no point
            // checking the same fixed condition for other
            // interactions.
            always_assert(code->cfg_built());
            auto& cfg = code->cfg();
            auto* entry_block = cfg.entry_block();
            auto* entry_sb = source_blocks::get_first_source_block(entry_block);
            if (entry_sb == nullptr) {
              return;
            }

            bool entry_hit = false;
            entry_sb->foreach_val([&entry_hit,
                                   block_profiles_hits](const auto& val_pair) {
              entry_hit |= (val_pair && val_pair->val > block_profiles_hits);
            });

            if (!entry_hit) {
              return;
            }

            acc->push_back(m);
          });

  return possibly_warm_or_hot;
}

void mark_callees_warm_or_hot(
    const Scope& scope,
    std::vector<DexMethod*>& possibly_warm_or_hot,
    UnorderedSet<DexMethod*>* sufficiently_warm_methods,
    UnorderedSet<DexMethod*>* sufficiently_hot_methods) {
  // This function will mark methods from the possibly_warm_or_hot list hot or
  // warm if they have a caller which was warm or hot. Note that if a method
  // had a hot and a warm caller, it will be considered hot.
  //
  // Since possibly warm or hot methods could be called by other possibly hot
  // or warm methods, the code also iterates until a fixpoint is hit.
  //
  // NOTE: A refinement to this would be to check if the callsite blocks were
  // executed. This isn't done yet, as getting the cfg::Block from an Edge in
  // the call graph isn't straightforward at present.

  auto mog = method_override_graph::build_graph(scope);
  call_graph::Graph cg = call_graph::multiple_callee_graph(*mog, scope, 5);

  // Defensively include a max iterations count, to avoid infinite loops if
  // there are bugs in this code.
  constexpr size_t max_iterations = 1000;
  size_t num_iterations = 0;
  size_t num_new_hot = 0;
  bool changed = true;
  while (changed && num_iterations < max_iterations) {
    num_iterations++;
    changed = false;

    for (auto it = possibly_warm_or_hot.begin();
         it != possibly_warm_or_hot.end();) {
      DexMethod* m = *it;

      if (!cg.has_node(m)) {
        it = possibly_warm_or_hot.erase(it);
        continue;
      }

      bool curr_is_warm = sufficiently_warm_methods->count(m) != 0u;

      bool erase_elem = false;

      const auto* node = cg.node(m);
      const auto& callerEdges = node->callers();
      for (const auto& callerEdge : callerEdges) {
        const auto* callerNode = callerEdge->caller();
        // call_graph::Node probably should not be holding a const DexMethod*
        auto* caller = const_cast<DexMethod*>(callerNode->method());
        if (sufficiently_hot_methods->count(caller) != 0u) {
          sufficiently_hot_methods->insert(m);
          changed = true;
          num_new_hot++;
          erase_elem = true;
          break;
        }

        if (!curr_is_warm && (sufficiently_warm_methods->count(caller) != 0u)) {
          sufficiently_warm_methods->insert(m);
          curr_is_warm = true;
          changed = true;
        }
      }
      if (erase_elem) {
        it = possibly_warm_or_hot.erase(it);
      } else {
        ++it;
      }
    }
  }

  always_assert(num_iterations < max_iterations);

  TRACE(ISO,
        2,
        "propagate_hotness: num_iterations: %zu, num_new_hot: %zu",
        num_iterations,
        num_new_hot);
}

void propagate_hotness(const Scope& scope,
                       ConfigFiles& config_files,
                       UnorderedSet<DexMethod*>* sufficiently_warm_methods,
                       UnorderedSet<DexMethod*>* sufficiently_hot_methods,
                       float block_profiles_hits) {
  // When enabled in the config, this function will propagate sufficient
  // "hotness" or "warmness" to callees of sufficiently hot and warm methods
  // whose entry blocks were executed according to block profiles.
  //
  // This is to mitigate the fact that method profiles track appearances and
  // call counts for physical methods which exist at the end of a dyna build of
  // an app, and we have no precise means of attributing these appearances/call
  // counts to methods which exist earlier in the IR, and which are later
  // inlined and only "executed" via their inlined blocks.
  //
  // For example, if, in a dyna build, foo is inlined into bar, we will only
  // have method profile info for foo in a resulting profile if it's executed,
  // and bar will appear to not be executed. In a regular/optimized build using
  // this profile, the outliner may then outline from bar, which will later be
  // inlined into foo, causing an outlined method call to appear in a
  // sufficiently hot method.

  std::vector<DexMethod*> possibly_warm_or_hot =
      get_possibly_warm_or_hot_methods(
          scope, config_files, sufficiently_warm_methods,
          sufficiently_hot_methods, block_profiles_hits);

  TRACE(ISO, 2, "propagate_hotness: possibly_warm_or_hot size=%zu",
        possibly_warm_or_hot.size());

  if (possibly_warm_or_hot.empty()) {
    return;
  }

  mark_callees_warm_or_hot(scope, possibly_warm_or_hot,
                           sufficiently_warm_methods, sufficiently_hot_methods);
}

PerfSensitivity parse_perf_sensitivity(const std::string& str) {
  if (str == "never") {
    return PerfSensitivity::kNeverUse;
  }
  if (str == "warm-when-no-profiles") {
    return PerfSensitivity::kWarmWhenNoProfiles;
  }
  if (str == "always-warm") {
    return PerfSensitivity::kAlwaysWarm;
  }
  if (str == "hot-when-no-profiles") {
    return PerfSensitivity::kHotWhenNoProfiles;
  }
  if (str == "always-hot") {
    return PerfSensitivity::kAlwaysHot;
  }
  always_assert_log(false, "Unknown perf sensitivity: %s", str.c_str());
}

CanOutlineBlockDecider::CanOutlineBlockDecider(
    const outliner::ProfileGuidanceConfig& config,
    const UnorderedSet<size_t>& throughput_interaction_indices,
    bool throughput,
    bool sufficiently_warm,
    bool sufficiently_hot)
    : m_config(config),
      m_throughput_interaction_indices(throughput_interaction_indices),
      m_throughput(throughput),
      m_sufficiently_warm(sufficiently_warm),
      m_sufficiently_hot(sufficiently_hot) {}

CanOutlineBlockDecider::Result
CanOutlineBlockDecider::can_outline_from_big_block(
    const big_blocks::BigBlock& big_block) const {
  if (!m_throughput && !m_sufficiently_hot && !m_sufficiently_warm) {
    return Result::CanOutline;
  }

  if (!m_throughput && !m_sufficiently_hot) {
    always_assert(m_sufficiently_warm);

    // Make sure m_is_in_loop is initialized
    if (!m_is_in_loop) {
      m_is_in_loop.reset(
          new LazyUnorderedMap<cfg::Block*, bool>([](cfg::Block* block) {
            UnorderedSet<cfg::Block*> visited;
            std::queue<cfg::Block*> work_queue;
            for (auto* e : block->succs()) {
              work_queue.push(e->target());
            }
            while (!work_queue.empty()) {
              auto* other_block = work_queue.front();
              work_queue.pop();
              if (visited.insert(other_block).second) {
                if (block == other_block) {
                  return true;
                }
                for (auto* e : other_block->succs()) {
                  work_queue.push(e->target());
                }
              }
            }
            return false;
          }));
    }
    if (!(*m_is_in_loop)[big_block.get_first_block()]) {
      bool has_throughput_source_block = false;
      if (!m_throughput_interaction_indices.empty()) {
        // Make sure m_is_throughput is initialized
        if (!m_is_throughput) {
          m_is_throughput.reset(new LazyUnorderedMap<cfg::Block*, bool>(
              [this](cfg::Block* block) -> bool {
                auto* sb = source_blocks::get_first_source_block(block);
                if (sb == nullptr) {
                  return false;
                }
                for (auto index :
                     UnorderedIterable(m_throughput_interaction_indices)) {
                  const auto& val_pair = sb->get_at(index);
                  if (val_pair &&
                      val_pair->val > m_config.block_profiles_hits) {
                    return true;
                  }
                }
                return false;
              }));
        }
        for (auto* block : big_block.get_blocks()) {
          if ((*m_is_throughput)[block]) {
            has_throughput_source_block = true;
            break;
          }
        }
      }

      if (!has_throughput_source_block) {
        return Result::CanOutline;
      }
    }
  }
  // If we get here,
  // - the method is throughput or hot, or
  // - the method is neither throughput nor hot but warm, and the big block is
  // in a loop or has a throughput interaction sourceblock
  if (m_config.block_profiles_hits < 0) {
    return m_throughput         ? Result::Throughput
           : m_sufficiently_hot ? Result::Hot
                                : Result::WarmLoop;
  }
  // Make sure m_max_vals is initialized
  if (!m_max_vals) {
    m_max_vals.reset(new LazyUnorderedMap<cfg::Block*, std::optional<float>>(
        [](cfg::Block* block) -> std::optional<float> {
          auto* sb = source_blocks::get_first_source_block(block);
          if (sb == nullptr) {
            return std::nullopt;
          }
          std::optional<float> max_val;
          sb->foreach_val([&](const auto& val_pair) {
            if (!val_pair) {
              return;
            }
            if (!max_val || (val_pair && val_pair->val > *max_val)) {
              max_val = val_pair->val;
            }
          });
          return max_val;
        }));
  }
  // Via m_max_vals, we consider the maximum hit number for each block.
  // Across all blocks, we are also computing the maximum value.
  std::optional<float> val;
  for (auto* block : big_block.get_blocks()) {
    auto block_val = (*m_max_vals)[block];
    if (!val || (block_val && *block_val > *val)) {
      val = block_val;
    }
  }
  if (!val) {
    return m_throughput         ? Result::ThroughputNoSourceBlocks
           : m_sufficiently_hot ? Result::HotNoSourceBlocks
                                : Result::WarmLoopNoSourceBlocks;
  }
  if (*val > m_config.block_profiles_hits) {
    return m_throughput         ? Result::ThroughputExceedsThresholds
           : m_sufficiently_hot ? Result::HotExceedsThresholds
                                : Result::WarmLoopExceedsThresholds;
  }
  return Result::CanOutline;
}

} // namespace outliner_impl
