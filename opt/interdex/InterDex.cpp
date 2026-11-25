/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InterDex.h"
#include "ControlFlow.h"

#include <algorithm>
#include <cinttypes>
#include <string>
#include <vector>

#include "CppUtil.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IOUtil.h"
#include "IRCode.h"
#include "InterDexPassPlugin.h"
#include "MethodProfiles.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"
#include "WorkQueue.h"
#include "file-utils.h"

namespace {
constexpr const char* END_MARKER_FORMAT = "LDexEndMarker";

constexpr const char* SCROLL_SET_START_FORMAT = "LScrollSetStart";
constexpr const char* SCROLL_SET_END_FORMAT = "LScrollSetEnd";

constexpr const char* BG_SET_START_FORMAT = "LBackgroundSetStart";
constexpr const char* BG_SET_END_FORMAT = "LBackgroundSetEnd";

// This is only necessary when "exclude_baseline_profile_classes" and
// "include_betamap_20pct_coldstart" are set.
constexpr const char* COLD_START_20PCT_END_FORMAT = "LColdStart20PctEnd";
constexpr const char* COLD_START_1PCT_END_FORMAT = "LColdStart1PctEnd";

constexpr const char* INTERACTION_ID_FORMAT = "LINTERACTION_ID_";
constexpr const char* START_FORMAT = "_Start;";

// Betamaps that carry no LDexEndMarker at all (e.g. Instagram) delimit the
// cold-start section with this interaction marker instead. Unlike a dex end
// marker it only ends the cold-start set; it does not terminate a dex.
constexpr const char* COLD_START_END_MARKER_FORMAT =
    "LINTERACTION_ID_ColdStart_End;";

static DexInfo EMPTY_DEX_INFO;

UnorderedSet<DexClass*> find_unrefenced_coldstart_classes(
    const Scope& scope,
    const std::vector<const DexType*>& interdex_types,
    bool static_prune_classes,
    ClassReferencesCache& class_references_cache) {
  int old_no_ref = -1;
  int new_no_ref = 0;

  UnorderedSet<const DexType*> coldstart_classes(interdex_types.begin(),
                                                 interdex_types.end());
  UnorderedSet<const DexType*> cold_cold_references;
  UnorderedSet<DexClass*> unreferenced_classes;
  Scope input_scope = scope;

  // Don't do analysis if we're not doing pruning.
  if (!static_prune_classes) {
    return unreferenced_classes;
  }

  while (old_no_ref != new_no_ref) {
    old_no_ref = new_no_ref;
    new_no_ref = 0;
    cold_cold_references.clear();
    walk::code(
        input_scope,
        [&](DexMethod* meth) {
          return coldstart_classes.count(meth->get_class()) > 0;
        },
        [&](DexMethod* meth, const IRCode& /*code*/) {
          auto* base_cls = meth->get_class();
          always_assert(meth->get_code()->cfg_built());
          auto add_reference = [&](const DexType* type) {
            if (base_cls != type && coldstart_classes.count(type) > 0) {
              cold_cold_references.insert(type);
            }
          };
          for (auto& mie : cfg::InstructionIterable(meth->get_code()->cfg())) {
            auto* inst = mie.insn;
            for_each_named_type(inst, add_reference);
            for_each_field_access(inst, [&](IROpcode, DexFieldRef* field,
                                            const DexMethodHandle*) {
              add_reference(field->get_class());
            });
            for_each_invoke(inst, [&](IROpcode, DexMethodRef* method,
                                      const DexMethodHandle*) {
              add_reference(method->get_class());
            });
          }
        });
    for (const auto& cls : scope) {
      // Make sure we don't drop classes which might be
      // called from native code.
      if (!can_rename(cls)) {
        cold_cold_references.insert(cls->get_type());
      }
    }

    // Get all classes in the reference set, even if they are not referenced by
    // opcodes directly.
    for (const auto& cls : input_scope) {
      if (cold_cold_references.count(cls->get_type()) != 0u) {
        const auto& refs = class_references_cache.get(cls);
        for (const auto& type : refs.types) {
          cold_cold_references.insert(type);
        }
      }
    }

    Scope output_scope;
    for (const auto& cls : UnorderedIterable(coldstart_classes)) {
      if (can_rename(type_class(cls)) && cold_cold_references.count(cls) == 0) {
        new_no_ref++;
        unreferenced_classes.insert(type_class(cls));
      } else {
        output_scope.push_back(type_class(cls));
      }
    }
    TRACE(IDEX, 4, "Found %d classes in coldstart with no references.",
          new_no_ref);
    input_scope = output_scope;
  }

  return unreferenced_classes;
}

void gather_refs(
    ClassReferencesCache& class_references_cache,
    const std::vector<std::unique_ptr<interdex::InterDexPassPlugin>>& plugins,
    const DexClass* cls,
    MethodRefs* mrefs,
    FieldRefs* frefs,
    TypeRefs* trefs,
    TypeRefs* itrefs) {
  const auto& refs = class_references_cache.get(cls);
  mrefs->insert(refs.method_refs.begin(), refs.method_refs.end());
  frefs->insert(refs.field_refs.begin(), refs.field_refs.end());
  trefs->insert(refs.types.begin(), refs.types.end());
  itrefs->insert(refs.init_types.begin(), refs.init_types.end());

  std::vector<DexMethodRef*> method_refs;
  std::vector<DexFieldRef*> field_refs;
  std::vector<const DexType*> type_refs;
  std::vector<const DexType*> init_type_refs;
  for (const auto& plugin : plugins) {
    plugin->gather_refs(cls, method_refs, field_refs, type_refs,
                        init_type_refs);
  }

  mrefs->insert(method_refs.begin(), method_refs.end());
  frefs->insert(field_refs.begin(), field_refs.end());
  trefs->insert(type_refs.begin(), type_refs.end());
  itrefs->insert(init_type_refs.begin(), init_type_refs.end());
}

void gather_initial_refs(
    const std::vector<std::unique_ptr<interdex::InterDexPassPlugin>>& plugins,
    DexesStructure& dexes_structure) {
  std::vector<DexMethodRef*> method_refs;
  std::vector<DexFieldRef*> field_refs;
  std::vector<const DexType*> type_refs;
  std::vector<const DexType*> init_type_refs;
  for (const auto& plugin : plugins) {
    plugin->gather_initial_refs(method_refs, field_refs, type_refs,
                                init_type_refs);
  }

  dexes_structure.add_refs_no_checks(
      MethodRefs(method_refs.begin(), method_refs.end()),
      FieldRefs(field_refs.begin(), field_refs.end()),
      TypeRefs(type_refs.begin(), type_refs.end()),
      TypeRefs(init_type_refs.begin(), init_type_refs.end()));
}

void print_stats(DexesStructure* dexes_structure) {
  TRACE(IDEX, 2, "InterDex Stats:");
  TRACE(IDEX, 2, "\t dex count: %zu", dexes_structure->get_num_dexes());
  TRACE(IDEX, 2, "\t secondary dex count: %zu",
        dexes_structure->get_num_secondary_dexes());
  TRACE(IDEX, 2, "\t coldstart dex count: %zu",
        dexes_structure->get_num_coldstart_dexes());
  TRACE(IDEX, 2, "\t extendex dex count: %zu",
        dexes_structure->get_num_extended_dexes());

  TRACE(IDEX, 2, "Global stats:");
  TRACE(IDEX, 2, "\t %zu classes", dexes_structure->get_num_classes());
  TRACE(IDEX, 2, "\t %zu mrefs", dexes_structure->get_num_mrefs());
  TRACE(IDEX, 2, "\t %zu frefs", dexes_structure->get_num_frefs());
  TRACE(IDEX, 2, "\t %zu dmethods", dexes_structure->get_num_dmethods());
  TRACE(IDEX, 2, "\t %zu vmethods", dexes_structure->get_num_vmethods());
  TRACE(IDEX, 2, "\t %zu mrefs", dexes_structure->get_num_mrefs());
}

/**
 * Order the classes in `scope` according to the`coldstart_class_names`.
 */
void do_order_classes(const std::vector<std::string>& coldstart_class_names,
                      Scope* scope) {
  UnorderedMap<const DexClass*, uint32_t> class_to_priority;
  uint32_t priority = 0;
  for (const auto& class_name : coldstart_class_names) {
    if (DexType* type = DexType::get_type(class_name)) {
      if (auto* cls = type_class(type)) {
        class_to_priority[cls] = priority++;
        cls->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
      }
    }
  }
  TRACE(IDEX, 3, "IDEX: Ordered around %u classes at the beginning", priority);
  std::stable_sort(
      scope->begin(), scope->end(),
      [&class_to_priority](const DexClass* left, const DexClass* right) {
        uint32_t left_priority = std::numeric_limits<uint32_t>::max();
        uint32_t right_priority = std::numeric_limits<uint32_t>::max();
        auto it = class_to_priority.find(left);
        if (it != class_to_priority.end()) {
          left_priority = it->second;
        }
        it = class_to_priority.find(right);
        if (it != class_to_priority.end()) {
          right_priority = it->second;
        }
        return left_priority < right_priority;
      });
}

// Perf sensitive classes and all the classes they reference via super classes
// cannot be dynamically_dead.
void exclude_extra_dynamically_dead_class(
    const std::vector<DexClass*>& candidates) {
  for (auto const& cls : candidates) {
    DexType* super_type;
    super_type = cls->get_super_class();
    while (super_type != nullptr) {
      DexClass* super_cls = type_class(super_type);
      if (super_cls->is_dynamically_dead()) {
        super_cls->set_dynamically_dead(false);
      }
      super_type = super_cls->get_super_class();
    }
  }
}

bool is_interaction_id_start_marker(std::string_view betamap_entry) {
  return betamap_entry.starts_with(INTERACTION_ID_FORMAT) &&
         betamap_entry.ends_with(START_FORMAT);
}

} // namespace

namespace interdex {

void InterDex::get_movable_coldstart_classes(
    const std::vector<const DexType*>& interdex_types,
    UnorderedMap<const DexClass*, std::string>& move_coldstart_classes) {
  auto class_freqs = m_conf.get_class_frequencies();
  const std::vector<std::string>& interactions = m_conf.get_interactions();
  always_assert_log(!class_freqs.empty(), "empty class freqs map");
  // all betamaps should have a ColdStart section, so this is a sanity check
  auto coldstart_it =
      std::find(interactions.begin(), interactions.end(), "ColdStart");
  always_assert_log(coldstart_it != interactions.end(),
                    "no ColdStart in class frequencies");
  size_t coldstart_idx = std::distance(interactions.begin(), coldstart_it);
  auto backgroundset_it =
      std::find(interactions.begin(), interactions.end(), "BackgroundSet");
  size_t backgroundset_idx =
      backgroundset_it != interactions.end()
          ? std::distance(interactions.begin(), backgroundset_it)
          : interactions.size();
  size_t curr_idx = coldstart_idx;

  initialize_baseline_profile_classes();

  for (const auto* type : interdex_types) {
    DexClass* cls = type_class(type);
    if (cls == nullptr) {
      auto index_it = interactions.end();
      auto cls_name = type->get_name()->str();
      if (is_interaction_id_start_marker(cls_name)) {
        index_it = std::find(
            interactions.begin(), interactions.end(),
            cls_name.substr(strlen(INTERACTION_ID_FORMAT),
                            cls_name.size() - strlen(INTERACTION_ID_FORMAT) -
                                strlen(START_FORMAT)));
      }
      if (index_it == interactions.end()) {
        continue;
      }
      curr_idx = std::distance(interactions.begin(), index_it);
      continue;
    }
    if (class_freqs.count(cls->get_name()) != 1 ||
        this->is_baseline_profile_class(type)) {
      continue;
    }
    auto freqs = class_freqs.at(cls->get_name());
    if (freqs.size() <= curr_idx) {
      continue;
    }
    auto curr_interaction_freq = freqs.at(curr_idx);
    if (curr_interaction_freq == 0 ||
        move_coldstart_classes.find(cls) != move_coldstart_classes.end() ||
        (curr_idx == coldstart_idx &&
         curr_interaction_freq > m_max_betamap_move_threshold)) {
      continue;
    }
    if (curr_idx == backgroundset_idx) {
      size_t max_idx = curr_idx;
      bool move_class = false;

      for (size_t i = 0; i < freqs.size(); i++) {
        auto freq = freqs.at(i);
        if (i != backgroundset_idx && freq > m_min_betamap_move_threshold) {
          if (move_class) {
            move_class = false;
            break;
          } else if (freq > freqs.at(curr_idx)) {
            move_class = true;
            max_idx = i;
          }
        }
      }
      if (move_class && max_idx != curr_idx) {
        move_coldstart_classes.emplace(cls, interactions.at(max_idx));
        TRACE(IDEX, 3, "moving %s from backgroundset to %s", SHOW(cls),
              interactions.at(max_idx).c_str());
      }
    } else {
      auto max_freq = freqs.at(curr_idx);
      size_t max_idx = curr_idx;

      for (size_t i = 0; i < freqs.size(); i++) {
        auto freq = freqs.at(i);
        // backgroundset classes are deduped from coldstart classes, so do
        // not check the backgorundset frequencies when moving coldstart
        // classes. The backgroundset threshold is 10%, so if the backgroundset
        // frequency is at least 10%, we've already seen the class before and do
        // not need to consider it again.
        if (curr_idx != coldstart_idx &&
            ((i == coldstart_idx && freq > m_max_betamap_move_threshold) ||
             (i == backgroundset_idx && freq > 10))) {
          max_idx = i;
          break;
        }
        if (freq > max_freq) {
          max_freq = freq;
          max_idx = i;
        }
      }
      if (curr_idx == coldstart_idx) {
        if (max_freq > curr_interaction_freq &&
            max_freq > m_min_betamap_move_threshold &&
            max_idx != backgroundset_idx) {
          move_coldstart_classes.emplace(cls, interactions.at(max_idx));
          TRACE(IDEX, 3, "moving %s from coldstart to %s", SHOW(cls),
                interactions.at(max_idx).c_str());
        }
      } else if (max_idx != coldstart_idx && max_idx != backgroundset_idx &&
                 max_freq > m_max_betamap_move_threshold) {
        if (max_idx != curr_idx) {
          move_coldstart_classes.emplace(cls, interactions.at(max_idx));
          TRACE(IDEX, 3, "moving %s from %s to %s", SHOW(cls),
                interactions.at(curr_idx).c_str(),
                interactions.at(max_idx).c_str());
        }
      }
    }
  }
}

bool InterDex::should_skip_class_due_to_dynamically_dead(
    DexClass* clazz) const {
  return clazz->is_dynamically_dead();
}

bool InterDex::should_skip_class_due_to_plugin(DexClass* clazz) const {
  for (const auto& plugin : m_plugins) {
    if (plugin->should_skip_class(clazz)) {
      TRACE(IDEX, 4, "IDEX: Skipping class from %s :: %s",
            plugin->name().c_str(), SHOW(clazz));
      return true;
    }
  }

  return false;
}

InterDex::EmitResult InterDex::emit_class(
    EmittingState& emitting_state,
    DexInfo& dex_info,
    DexClass* clazz,
    bool check_if_skip,
    bool perf_sensitive,
    DexClass** canary_cls,
    std::optional<FlushOutDexResult>* opt_fodr,
    bool skip_dynamically_dead) const {
  if (is_canary(clazz)) {
    // Nothing to do here.
    return {false, false};
  }

  if (emitting_state.dexes_structure.has_class(clazz)) {
    TRACE(IDEX, 6, "Trying to re-add class %s!", SHOW(clazz));
    return {false, false};
  }

  if (check_if_skip && should_skip_class_due_to_plugin(clazz)) {
    return {false, false};
  }

  if (perf_sensitive) {
    clazz->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
  }

  if (m_reorder_dynamically_dead_classes && skip_dynamically_dead &&
      should_skip_class_due_to_dynamically_dead(clazz)) {
    return {false, false};
  }

  // Calculate the extra method and field refs that we would need to add to
  // the current dex if we defined clazz in it.
  MethodRefs clazz_mrefs;
  FieldRefs clazz_frefs;
  TypeRefs clazz_trefs;
  TypeRefs clazz_itrefs;
  gather_refs(m_class_references_cache, m_plugins, clazz, &clazz_mrefs,
              &clazz_frefs, &clazz_trefs, &clazz_itrefs);

  bool fits_current_dex =
      emitting_state.dexes_structure.add_class_to_current_dex(
          clazz_mrefs, clazz_frefs, clazz_trefs, clazz_itrefs, clazz);
  if (!fits_current_dex) {
    auto fodr = flush_out_dex(emitting_state, dex_info, *canary_cls);
    *canary_cls = get_canary_cls(emitting_state, dex_info);

    if (opt_fodr != nullptr) {
      *opt_fodr = fodr;
      return {false, true};
    }

    post_process_dex(emitting_state, fodr);

    emitting_state.dexes_structure.add_class_no_checks(
        clazz_mrefs, clazz_frefs, clazz_trefs, clazz_itrefs, clazz);
  }
  return {true, !fits_current_dex};
}

void InterDex::emit_primary_dex(
    const DexClasses& primary_dex,
    const std::vector<const DexType*>& interdex_order,
    const UnorderedSet<DexClass*>& unreferenced_classes) {

  UnorderedSet<DexClass*> primary_dex_set(primary_dex.begin(),
                                          primary_dex.end());

  DexInfo primary_dex_info;
  primary_dex_info.primary = true;

  size_t coldstart_classes_in_primary = 0;
  size_t coldstart_classes_skipped_in_primary = 0;

  // Sort the primary dex according to interdex order (aka emit first the
  // primary classes that appear in the interdex order, in the order that
  // they appear there).
  for (const DexType* type : interdex_order) {
    DexClass* cls = type_class(type);
    if (cls == nullptr) {
      continue;
    }

    if (primary_dex_set.count(cls) > 0) {
      if (unreferenced_classes.count(cls) > 0) {
        TRACE(IDEX, 5, "[primary dex]: %s no longer linked to coldstart set.",
              SHOW(cls));
        coldstart_classes_skipped_in_primary++;
        continue;
      }

      emit_class(m_emitting_state, primary_dex_info, cls,
                 /* check_if_skip */ true,
                 /* perf_sensitive */ true, /* canary_cls */ nullptr);
      coldstart_classes_in_primary++;
    }
  }

  // Now add the rest.
  for (DexClass* cls : primary_dex) {
    emit_class(m_emitting_state, primary_dex_info, cls,
               /* check_if_skip */ true,
               /* perf_sensitive */ false, /* canary_cls */ nullptr);
  }
  TRACE(IDEX, 2,
        "[primary dex]: %zu out of %zu classes in primary dex "
        "from interdex list.",
        coldstart_classes_in_primary, primary_dex.size());
  TRACE(IDEX, 2,
        "[primary dex]: %zu out of %zu classes in primary dex skipped "
        "from interdex list.",
        coldstart_classes_skipped_in_primary, primary_dex.size());

  auto fodr = flush_out_dex(m_emitting_state, primary_dex_info,
                            /* canary_cls */ nullptr);
  post_process_dex(m_emitting_state, fodr);

  // Double check only 1 dex was created.
  always_assert_log(
      m_emitting_state.dexes_structure.get_num_dexes() == 1,
      "[error]: Primary dex doesn't fit in only 1 dex anymore :|, but in %zu\n",
      m_emitting_state.dexes_structure.get_num_dexes());
}

void InterDex::emit_interdex_classes(
    DexInfo& dex_info,
    const std::vector<const DexType*>& interdex_types,
    const UnorderedSet<DexClass*>& unreferenced_classes,
    DexClass** canary_cls) {
  if (interdex_types.empty()) {
    TRACE(IDEX, 2, "No interdex classes passed.");
    return;
  }

  if (!m_order_interdex) {
    // We still want to mark the interdex classes as perf-sensitive, so that
    // other optimizations such as outlining and sort-remaining-classes treat
    // interdex classes appropriately.
    for (const auto* type : interdex_types) {
      DexClass* cls = type_class(type);
      if ((cls != nullptr) && (unreferenced_classes.count(cls) == 0u)) {
        cls->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
        m_interdex_order.emplace(cls, m_interdex_order.size());
      }
    }
    return;
  }

  auto class_freqs = m_conf.get_class_frequencies();
  UnorderedMap<const DexClass*, std::string> move_coldstart_classes;
  if (m_move_coldstart_classes) {
    get_movable_coldstart_classes(interdex_types, move_coldstart_classes);
  }

  // NOTE: coldstart has no interaction with extended and scroll set, but that
  //       is not true for the later 2.
  dex_info.coldstart = true;

  size_t cls_skipped_in_secondary = 0;
  std::string curr_interaction = "ColdStart";

  // The reset itself always rides on dex_info.pending_coldstart_reset, which
  // flush_out_dex consumes at whichever dex boundary comes first. This says the
  // deferral came from a dex end marker, which owes one thing more than the
  // reset: the dex boundary whose flush was skipped to let the dex keep
  // filling. Only that case may force a flush at the end of the betamap.
  bool reset_coldstart_on_overflow = false;
  for (auto it = interdex_types.begin(); it != interdex_types.end(); ++it) {
    const DexType* type = *it;
    DexClass* cls = type_class(type);
    if (cls == nullptr) {
      TRACE(IDEX, 5, "[interdex classes]: No such entry %s.", SHOW(type));
      const auto type_name = type->get_name()->str();
      if (type_name.starts_with(SCROLL_SET_START_FORMAT)) {
        always_assert_log(
            !m_emitting_scroll_set,
            "Scroll start marker discovered after another scroll start marker");
        always_assert_log(
            !m_emitting_bg_set,
            "Scroll start marker discovered between background set markers");
        m_emitting_scroll_set = true;
        TRACE(IDEX, 2, "Marking dex as scroll at betamap entry %td",
              std::distance(interdex_types.begin(), it));
        dex_info.scroll = true;
      } else if (type_name.starts_with(SCROLL_SET_END_FORMAT)) {
        always_assert_log(
            m_emitting_scroll_set,
            "Scroll end marker discovered without scroll start marker");
        m_emitting_scroll_set = false;
      } else if (type_name.starts_with(BG_SET_START_FORMAT)) {
        always_assert_log(!m_emitting_bg_set,
                          "Background start marker discovered after another "
                          "background start marker");
        always_assert_log(
            !m_emitting_scroll_set,
            "Background start marker discovered between scroll set markers");
        TRACE(IDEX, 2, "Marking dex as background at betamap entry %td",
              std::distance(interdex_types.begin(), it));
        m_emitting_bg_set = true;
        dex_info.background = true;
      } else if (type_name.starts_with(BG_SET_END_FORMAT)) {
        always_assert_log(
            m_emitting_bg_set,
            "Background end marker discovered without background start marker");
        m_emitting_bg_set = false;
        m_emitted_bg_set = true;
      } else if (m_end_markers.empty() && type == m_coldstart_end_marker) {
        // Ends the cold-start set. This is not a dex end marker: it forces no
        // dex boundary and advances no interdex group, so the current dex keeps
        // being filled. That dex still holds cold-start classes from before the
        // marker, so the reset is deferred until it is flushed -- only the
        // dexes that follow it are not cold start. Unlike a dex end marker it
        // leaves no boundary owed, so it sets nothing beyond the reset and the
        // dex may well stay open past the end of the betamap.
        TRACE(IDEX, 2, "Ending cold start set at %s", SHOW(type));
        dex_info.pending_coldstart_reset = true;
      } else {
        auto end_marker =
            std::find(m_end_markers.begin(), m_end_markers.end(), type);
        // Cold start end marker is the last dex end marker
        auto cold_start_end_marker = !m_end_markers.empty()
                                         ? m_end_markers.end() - 1
                                         : m_end_markers.end();
        if (end_marker != m_end_markers.end()) {
          always_assert_log(
              !m_emitting_scroll_set,
              "End marker discovered between scroll start/end markers");
          always_assert_log(
              !m_emitting_bg_set,
              "End marker discovered between background start/end markers");
          TRACE(IDEX, 2, "Terminating dex due to %s", SHOW(type));
          if (end_marker != cold_start_end_marker ||
              !m_fill_last_coldstart_dex || m_end_markers.size() == 1) {
            auto fodr = flush_out_dex(m_emitting_state, dex_info, *canary_cls);
            post_process_dex(m_emitting_state, fodr);
            *canary_cls = get_canary_cls(m_emitting_state, dex_info);
            if (end_marker == cold_start_end_marker) {
              dex_info.coldstart = false;
            }
          } else {
            dex_info.pending_coldstart_reset = true;
            reset_coldstart_on_overflow = true;
            TRACE(IDEX, 2, "Not flushing out marker %s to fill dex.",
                  SHOW(type));
          }
        }
        if (m_move_coldstart_classes &&
            is_interaction_id_start_marker(type->str())) {
          curr_interaction = type->str();
        }
      }
    } else {
      if (unreferenced_classes.count(cls) != 0u) {
        TRACE(IDEX, 3, "%s no longer linked to coldstart set.", SHOW(cls));
        cls_skipped_in_secondary++;
        continue;
      }
      if (m_emitted_bg_set) {
        m_emitted_bg_set = false;
        dex_info.extended = true;
        m_emitting_extended = true;
      }
      dex_info.betamap_ordered = true;

      if (m_move_coldstart_classes &&
          (move_coldstart_classes.count(cls) != 0u)) {
        auto interaction = move_coldstart_classes.at(cls);
        if (!curr_interaction.starts_with(INTERACTION_ID_FORMAT +
                                          interaction)) {
          continue;
        } else {
          TRACE(IDEX, 3, "moving %s into %s", SHOW(cls),
                SHOW(curr_interaction));
          move_coldstart_classes.erase(cls);
          dex_info.class_freqs_moved_classes += 1;
        }
      }
      emit_class(m_emitting_state, dex_info, cls, /* check_if_skip */ true,
                 /* perf_sensitive */ true, canary_cls);
    }
  }

  // Now emit the classes we omitted from the original coldstart set.
  TRACE(IDEX, 2, "Emitting %zu interdex types (pending_coldstart_reset=%d)",
        interdex_types.size(), dex_info.pending_coldstart_reset);
  for (const DexType* type : interdex_types) {
    DexClass* cls = type_class(type);

    if ((cls != nullptr) && (unreferenced_classes.count(cls) != 0u)) {
      emit_class(m_emitting_state, dex_info, cls, /* check_if_skip */ true,
                 /* perf_sensitive */ false, canary_cls);
    }
  }

  TRACE(IDEX, 3,
        "[interdex order]: %zu classes are unreferenced from the interdex "
        "order in secondary dexes.",
        cls_skipped_in_secondary);

  // TODO: check for unterminated markers
  always_assert_log(!m_emitting_scroll_set, "Unterminated scroll set marker");
  always_assert_log(!m_emitting_bg_set, "Unterminated background set marker");

  m_emitting_extended = false;

  // Honor the boundary the deferred dex end marker still owes. If an overflow
  // got there first it already created one and consumed the pending reset with
  // it, so there is nothing left to do.
  if (reset_coldstart_on_overflow && dex_info.pending_coldstart_reset) {
    TRACE(IDEX, 2, "No overflow after cold-start dex, flushing now.");
    auto fodr = flush_out_dex(m_emitting_state, dex_info, *canary_cls);
    post_process_dex(m_emitting_state, fodr);
    *canary_cls = get_canary_cls(m_emitting_state, dex_info);
  }
}

namespace {

/**
 * Grab classes that should end up in a pre-defined interdex group.
 */
std::vector<std::vector<DexType*>> get_extra_classes_per_interdex_group(
    const Scope& scope, const bool is_root_store) {
  std::vector<std::vector<DexType*>> res(MAX_DEX_NUM);

  InterdexSubgroupIdx num_interdex_groups = 0;
  walk::classes(scope, [&](const DexClass* cls) {
    // Interdex grouping is only relevant for root stores.
    if (is_root_store && cls->rstate.has_interdex_subgroup()) {
      InterdexSubgroupIdx interdex_subgroup =
          cls->rstate.get_interdex_subgroup();
      res[interdex_subgroup].push_back(cls->get_type());
      num_interdex_groups =
          std::max(num_interdex_groups, interdex_subgroup + 1);
    }
  });
  TRACE(IDEX, 3,
        "  Populated interdex group with extra classes: num_interdex_groups %u",
        num_interdex_groups);

  res.resize(num_interdex_groups);

  return res;
}

} // namespace

void InterDex::load_interdex_types() {
  always_assert(m_interdex_types.empty());

  const std::vector<std::string>& interdexorder =
      m_conf.get_coldstart_classes();

  // Find generated classes that should be in the interdex order.
  std::vector<std::vector<DexType*>> interdex_group_classes =
      get_extra_classes_per_interdex_group(m_scope, m_is_root_store);
  size_t curr_interdex_group = 0;

  UnorderedSet<DexClass*> classes(m_scope.begin(), m_scope.end());

  UnorderedSet<const DexType*> all_set{};

  if (m_transitively_close_interdex_order && !m_force_single_dex) {
    for (auto* cls : m_dexen[0]) {
      all_set.insert(cls->get_type()); // Ignore primary.
    }
  }

  UnorderedSet<const DexType*> moved_or_double{};
  UnorderedSet<const DexType*> transitive_added{};

  for (const auto& entry : interdexorder) {
    DexType* type = DexType::get_type(entry);
    if (type == nullptr) {
      if (entry.starts_with(END_MARKER_FORMAT)) {
        type = DexType::make_type(entry);
        m_end_markers.emplace_back(type);

        if (interdex_group_classes.size() > curr_interdex_group) {
          for (DexType* extra_type :
               interdex_group_classes.at(curr_interdex_group)) {
            m_interdex_types.emplace_back(extra_type);
          }
          curr_interdex_group++;
        }

        TRACE(IDEX, 4, "[interdex order]: Found class end marker %s.",
              entry.c_str());
      } else if (entry.starts_with(SCROLL_SET_START_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4,
              "[interdex order]: Found scroll set start class marker %s.",
              entry.c_str());
      } else if (entry.starts_with(SCROLL_SET_END_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4,
              "[interdex order]: Found scroll set end class marker %s.",
              entry.c_str());
      } else if (entry.starts_with(BG_SET_START_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4, "[interdex order]: Found bg set start class marker %s.",
              entry.c_str());
      } else if (entry.starts_with(BG_SET_END_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4, "[interdex order]: Found bg set end class marker %s.",
              entry.c_str());
      } else if (entry.starts_with(COLD_START_20PCT_END_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4,
              "[interdex order]: Found 20pct cold start end class marker %s.",
              entry.c_str());
      } else if (entry.starts_with(COLD_START_1PCT_END_FORMAT)) {
        type = DexType::make_type(entry);
        TRACE(IDEX, 4,
              "[interdex order]: Found 1pct cold start end class marker %s.",
              entry.c_str());
      } else if (entry == COLD_START_END_MARKER_FORMAT) {
        type = DexType::make_type(entry);
        m_coldstart_end_marker = type;
        TRACE(IDEX, 4,
              "[interdex order]: Found cold start end class marker %s.",
              entry.c_str());
        // trim off the _Start suffix to get the interaction name
      } else if (is_interaction_id_start_marker(entry)) {
        type = DexType::make_type(entry);
      } else {
        continue;
      }
    } else {
      DexClass* cls = type_class(type);
      if ((cls == nullptr) || classes.count(cls) == 0) {
        continue;
      }

      if (cls->rstate.has_interdex_subgroup()) {
        // Skipping generated classes that should end up in a specific group.
        continue;
      }

      if (m_transitively_close_interdex_order) {
        if (all_set.count(type) != 0) {
          // Moved earlier.
          moved_or_double.insert(type);
          continue;
        }

        // Transitive closure.
        self_recursive_fn(
            [&](const auto& self, const DexType* cur, bool add_self) {
              DexClass* cur_cls = type_class(cur);
              if (!cur_cls || classes.count(cur_cls) == 0 ||
                  all_set.count(cur) != 0 ||
                  cur_cls->rstate.has_interdex_subgroup()) {
                return;
              }
              all_set.insert(cur);
              if (add_self) {
                transitive_added.insert(cur);
              }

              // Superclass first.
              self(self, cur_cls->get_super_class(), true);
              // Then interfaces.
              for (const auto* intf : *cur_cls->get_interfaces()) {
                self(self, intf, true);
              }

              // Then self.
              if (add_self) {
                m_interdex_types.emplace_back(cur);
              }
            },
            type, false);
      }
    }

    m_interdex_types.emplace_back(type);
  }

  // We still want to add the ones in the last interdex group, if any.
  always_assert_log(interdex_group_classes.size() <= curr_interdex_group + 2,
                    "Too many interdex subgroups! interdex group size %zu; "
                    "curr_interdex_group %zu\n",
                    interdex_group_classes.size(), curr_interdex_group);
  if (interdex_group_classes.size() > curr_interdex_group) {
    for (DexType* type : interdex_group_classes.at(curr_interdex_group)) {
      // TODO: Does the above need to filter? Do we need to transitively close
      //       here, too?
      if (!m_transitively_close_interdex_order || all_set.count(type) == 0) {
        m_interdex_types.push_back(type);
      }
    }
  }

  if (m_transitively_close_interdex_order) {
    UnorderedSet<const DexType*> transitive_moved;
    for (const auto* t : UnorderedIterable(moved_or_double)) {
      if (transitive_added.count(t) != 0) {
        transitive_moved.insert(t);
        transitive_added.erase(t);
      }
    }

    m_transitive_closure_added = transitive_added.size();
    m_transitive_closure_moved = transitive_moved.size();
  }
}

void InterDex::update_interdexorder(
    const DexClasses& dex, std::vector<const DexType*>* interdex_types) {
  std::vector<DexType*> primary_dex;
  for (DexClass* cls : dex) {
    primary_dex.emplace_back(cls->get_type());
  }

  // We keep the primary classes untouched - at the beginning of
  // the interdex list.
  interdex_types->insert(interdex_types->begin(), primary_dex.begin(),
                         primary_dex.end());
}

void InterDex::init_cross_dex_ref_minimizer() {
  TRACE(IDEX, 2,
        "[dex ordering] Cross-dex-ref-minimizer active with method ref weight "
        "%" PRIu64 ", field ref weight %" PRIu64 ", type ref weight %" PRIu64
        ", large string ref weight %" PRIu64
        ", small string ref weight %" PRIu64 ", method seed weight %" PRIu64
        ", field seed weight %" PRIu64 ", type seed weight %" PRIu64
        ", large string seed weight %" PRIu64
        ", small string seed weight %" PRIu64 ".",
        m_cross_dex_ref_minimizer.get_config().method_ref_weight,
        m_cross_dex_ref_minimizer.get_config().field_ref_weight,
        m_cross_dex_ref_minimizer.get_config().type_ref_weight,
        m_cross_dex_ref_minimizer.get_config().large_string_ref_weight,
        m_cross_dex_ref_minimizer.get_config().small_string_ref_weight,
        m_cross_dex_ref_minimizer.get_config().method_seed_weight,
        m_cross_dex_ref_minimizer.get_config().field_seed_weight,
        m_cross_dex_ref_minimizer.get_config().type_seed_weight,
        m_cross_dex_ref_minimizer.get_config().large_string_seed_weight,
        m_cross_dex_ref_minimizer.get_config().small_string_seed_weight);

  std::vector<DexClass*> classes_to_insert;
  // Emit classes using some algorithm to group together classes which
  // tend to share the same refs.
  for (DexClass* cls : m_scope) {
    // Don't bother with classes that emit_class will skip anyway.
    if (is_canary(cls) || m_emitting_state.dexes_structure.has_class(cls)) {
      continue;
    }

    // Don't bother with classes that emit_class will skip anyway
    if (should_skip_class_due_to_plugin(cls)) {
      // Skipping a class due to a plugin might mean that (members of) of the
      // class will get emitted later via the additional-class mechanism.
      // So we'll also sample those classes here.
      m_cross_dex_ref_minimizer.sample(cls);
      continue;
    }

    // Don't bother with these classes which will be emitted at the end of
    // dexes.
    if (m_reorder_dynamically_dead_classes &&
        should_skip_class_due_to_dynamically_dead(cls)) {
      continue;
    }

    classes_to_insert.emplace_back(cls);
  }

  // Initialize ref frequency counts
  for (DexClass* cls : classes_to_insert) {
    m_cross_dex_ref_minimizer.sample(cls);
  }

  // Emit classes using some algorithm to group together classes which
  // tend to share the same refs.
  for (DexClass* cls : classes_to_insert) {
    m_cross_dex_ref_minimizer.insert(cls);
  }

  // A few classes might have already been emitted to the current dex which we
  // are about to fill up. Make it so that the minimizer knows that all the refs
  // of those classes have already been emitted.
  for (auto* cls :
       m_emitting_state.dexes_structure.get_current_dex().get_classes()) {
    m_cross_dex_ref_minimizer.sample(cls);
    m_cross_dex_ref_minimizer.insert(cls);
    m_cross_dex_ref_minimizer.erase(cls, /* emitted */ true);
  }
}

std::vector<DexClasses> InterDex::get_stable_partitions() {
  always_assert(m_stable_partitions > 0);
  auto remaining_classes = m_scope;
  std::erase_if(remaining_classes, [&](auto* cls) {
    return is_canary(cls) || m_emitting_state.dexes_structure.has_class(cls) ||
           should_skip_class_due_to_plugin(cls);
  });
  std::vector<DexClasses> partitions(m_stable_partitions);
  auto partition_it = partitions.begin();
  size_t partition_target_size =
      (remaining_classes.size() + m_stable_partitions - 1) /
      m_stable_partitions;
  for (auto* cls : remaining_classes) {
    always_assert(partition_it < partitions.end());
    partition_it->push_back(cls);
    if (partition_it->size() >= partition_target_size) {
      partition_it++;
    }
  }
  return partitions;
}

void InterDex::emit_remaining_classes(DexInfo& dex_info,
                                      DexClass** canary_cls) {
  m_current_classes_when_emitting_remaining =
      m_emitting_state.dexes_structure.get_current_dex().size();

  if (!m_minimize_cross_dex_refs) {
    auto emit_classes = [&](const DexClasses& classes) {
      for (DexClass* cls : classes) {
        emit_class(m_emitting_state, dex_info, cls, /* check_if_skip */ true,
                   /* perf_sensitive */ false, canary_cls, nullptr,
                   /* skip_dynamically_dead */ true);
      }
    };

    if (m_stable_partitions > 0) {
      auto partitions = get_stable_partitions();
      for (auto& partition : partitions) {
        if (partition.empty()) {
          continue;
        }
        if (!m_emitting_state.dexes_structure.get_current_dex().empty()) {
          auto fodr = flush_out_dex(m_emitting_state, dex_info, *canary_cls);
          post_process_dex(m_emitting_state, fodr);
          *canary_cls = nullptr;
        }
        emit_classes(partition);
      }
      return;
    }

    emit_classes(m_scope);
    return;
  }

  init_cross_dex_ref_minimizer();

  if (m_minimize_cross_dex_refs_explore_alternatives <= 1) {
    emit_remaining_classes_legacy(dex_info, canary_cls);
  } else {
    emit_remaining_classes_exploring_alternatives(dex_info, canary_cls);
  }
}

void InterDex::emit_remaining_classes_legacy(DexInfo& dex_info,
                                             DexClass** canary_cls) {
  // Strategy for picking the next class to emit:
  // - at the beginning of a new dex, pick the "worst" class, i.e. the class
  //   with the most (adjusted) unapplied refs
  // - otherwise, pick the "best" class according to the priority scheme that
  //   prefers classes that share many applied refs and bring in few unapplied
  //   refs
  bool pick_worst = true;
  while (!m_cross_dex_ref_minimizer.empty()) {
    DexClass* cls{nullptr};
    if (pick_worst) {
      // Figure out which class has the most unapplied references
      auto* worst = m_cross_dex_ref_minimizer.worst();
      // Use that worst class if it has more unapplied refs than already applied
      // refs
      if (m_cross_dex_ref_minimizer.get_unapplied_refs(worst) >
          m_cross_dex_ref_minimizer.get_applied_refs()) {
        cls = worst;
      }
    }
    if (cls == nullptr) {
      // Default case
      cls = m_cross_dex_ref_minimizer.front();
    }

    std::optional<FlushOutDexResult> opt_fodr;
    auto res =
        emit_class(m_emitting_state, dex_info, cls, /* check_if_skip */ false,
                   /* perf_sensitive */ false, canary_cls, &opt_fodr,
                   /* skip_dynamically_dead */ true);
    if (opt_fodr) {
      always_assert(!res.emitted);
      post_process_dex(m_emitting_state, *opt_fodr);
      m_cross_dex_ref_minimizer.reset();
      pick_worst = true;
      continue;
    }

    m_cross_dex_ref_minimizer.erase(cls, res.emitted);

    pick_worst = pick_worst && !res.emitted;
  }
}

void InterDex::emit_remaining_classes_exploring_alternatives(
    DexInfo& dex_info, DexClass** canary_cls) {
  // Strategy for picking the next class to emit in a dex:
  // - at the beginning of a new dex, consider a "seed" class, i.e. a class
  //   with a high seed weight
  // - otherwise, pick the "best" class according to the priority scheme that
  //   prefers classes that share many applied refs and bring in few unapplied
  //   refs
  // For each dex, we explore a set of alternatives in parallel, choosing the
  // "best" one to continue with. We use a cost function that tries to minimize
  // the remaining "difficulty" of assigning the remaining classes to dexes.

  struct Alternative {
    EmittingState emitting_state;
    DexInfo dex_info;
    cross_dex_ref_minimizer::CrossDexRefMinimizer cross_dex_ref_minimizer;
    DexClass* canary_cls;
    std::vector<FlushOutDexResult> fodrs;

    double fill_current_dex(const InterDex* inter_dex, DexClass* seed_cls) {
      while (!cross_dex_ref_minimizer.empty()) {
        DexClass* cls;
        if (seed_cls != nullptr) {
          cls = seed_cls;
          seed_cls = nullptr;
        } else {
          // Default case
          cls = cross_dex_ref_minimizer.front();
        }

        std::optional<FlushOutDexResult> opt_fodr;
        auto res =
            inter_dex->emit_class(emitting_state, dex_info, cls,
                                  /* check_if_skip */ false,
                                  /* perf_sensitive */ false, &canary_cls,
                                  &opt_fodr, /* skip_dynamically_dead */ true);
        if (opt_fodr) {
          always_assert(!res.emitted);
          cross_dex_ref_minimizer.reset();
          fodrs.push_back(*opt_fodr);
          break;
        }

        cross_dex_ref_minimizer.erase(cls, res.emitted);
      }
      return cross_dex_ref_minimizer.get_remaining_difficulty();
    }
  };

  TRACE(IDEX, 1,
        "Finding cross-dex-ref-minimization solutions, considering %" PRId64
        " alternatives at each step",
        m_minimize_cross_dex_refs_explore_alternatives);

  auto best = std::make_unique<Alternative>(
      (Alternative){std::move(m_emitting_state), dex_info,
                    std::move(m_cross_dex_ref_minimizer), *canary_cls,
                    /* fodrs */ {}});

  bool first = true;
  while (!best->cross_dex_ref_minimizer.empty()) {
    auto worst_classes = best->cross_dex_ref_minimizer.worst(
        m_minimize_cross_dex_refs_explore_alternatives);
    if (first) {
      first = false;
      worst_classes.push_back(nullptr);
    }

    best->cross_dex_ref_minimizer.compact();
    std::unique_ptr<Alternative> last;
    std::swap(last, best);
    std::mutex best_mutex;
    double best_remaining_difficulty = 0;
    size_t best_index = 0;

    workqueue_run_for<size_t>(
        0, worst_classes.size(),
        [this, &worst_classes, &last, &best, &best_remaining_difficulty,
         &best_index, &best_mutex](size_t index) {
          auto* seed_cls = worst_classes.at(index);

          auto alt = std::make_unique<Alternative>(*last);
          auto remaining_difficulty = alt->fill_current_dex(this, seed_cls);

          TRACE(IDEX, 2,
                "Found cross-dex-ref-minimization solution with %f remaining "
                "difficulty at index %zu",
                remaining_difficulty, index);
          {
            std::lock_guard<std::mutex> lock_guard(best_mutex);
            if (!best || remaining_difficulty < best_remaining_difficulty ||
                (remaining_difficulty == best_remaining_difficulty &&
                 index < best_index)) {
              // swap so that we destroy the dead alternative outside of the
              // lock
              std::swap(best, alt);
              best_remaining_difficulty = remaining_difficulty;
              best_index = index;
            }
          }
        });
  }

  m_emitting_state = std::move(best->emitting_state);
  dex_info = best->dex_info;
  m_cross_dex_ref_minimizer = std::move(best->cross_dex_ref_minimizer);
  *canary_cls = best->canary_cls;
  for (const auto& fodr : best->fodrs) {
    post_process_dex(m_emitting_state, fodr);
  }
}

void InterDex::run_in_force_single_dex_mode() {
  auto scope = build_class_scope(m_dexen);

  const std::vector<std::string>& coldstart_class_names =
      m_conf.get_coldstart_classes();
  DexInfo dex_info;
  dex_info.primary = true;
  if (coldstart_class_names.empty()) {
    TRACE(IDEX, 3, "IDEX single dex mode: No coldstart_classes");
  } else {
    dex_info.coldstart = true;
    do_order_classes(coldstart_class_names, &scope);
  }

  // Add all classes into m_dexes_structure without further checking when
  // force_single_dex is on. The overflow checking will be done later on at
  // the end of the pipeline (e.g. write_classes_to_dex).
  gather_initial_refs(m_plugins, m_emitting_state.dexes_structure);
  for (DexClass* cls : scope) {
    MethodRefs clazz_mrefs;
    FieldRefs clazz_frefs;
    TypeRefs clazz_trefs;
    TypeRefs clazz_itrefs;
    gather_refs(m_class_references_cache, m_plugins, cls, &clazz_mrefs,
                &clazz_frefs, &clazz_trefs, &clazz_itrefs);

    m_emitting_state.dexes_structure.add_class_no_checks(
        clazz_mrefs, clazz_frefs, clazz_trefs, clazz_itrefs, cls);
  }

  // Emit all no matter what it is.
  if (!m_emitting_state.dexes_structure.get_current_dex().empty()) {
    auto fodr =
        flush_out_dex(m_emitting_state, dex_info, /* canary_cls */ nullptr);
    post_process_dex(m_emitting_state, fodr);
  }

  TRACE(IDEX, 7, "IDEX: force_single_dex dex number: %zu",
        m_emitting_state.dexes_structure.get_num_dexes());
  print_stats(&m_emitting_state.dexes_structure);
}

void InterDex::run() {
  TRACE(IDEX, 2, "IDEX: Running on root store");
  if (m_force_single_dex) {
    run_in_force_single_dex_mode();
    return;
  }

  auto unreferenced_classes = find_unrefenced_coldstart_classes(
      m_scope, m_interdex_types, m_static_prune_classes,
      m_class_references_cache);

  gather_initial_refs(m_plugins, m_emitting_state.dexes_structure);

  const auto& primary_dex = m_dexen[0];

  if (m_normal_primary_dex) {
    // NOTE: If primary dex is treated as a normal dex, we are going to modify
    //       it too, based on coldstart classes. If we can't remove the classes
    //       from the primary dex, we need to update the coldstart list to
    //       respect the primary dex.
    if (m_keep_primary_order && !m_interdex_types.empty()) {
      update_interdexorder(primary_dex, &m_interdex_types);
    }
  }

  if (m_order_interdex && m_exclude_baseline_profile_classes) {
    // Mutates m_interdex_types, removing baseline profile classes.
    // Note that in normal_primary_dex mode, this can remove classes from the
    // first/"primary" dex file (i.e. by removing them from m_interdex_types).
    // This should be fine, because this is not a special primary dex, and we
    // know these classes will end up in the app image.
    this->exclude_baseline_profile_classes();
  }

  // We have a bunch of special logic for the primary dex which we only use if
  // we can't touch the primary dex.
  if (!m_normal_primary_dex) {
    emit_primary_dex(primary_dex, m_interdex_types, unreferenced_classes);
  }

  // Emit interdex classes, if any.
  DexInfo dex_info;
  DexClass* canary_cls = get_canary_cls(m_emitting_state, dex_info);
  emit_interdex_classes(dex_info, m_interdex_types, unreferenced_classes,
                        &canary_cls);

  auto* json_classes = m_cross_dex_ref_minimizer.get_json_classes();
  Json::Value json_first_dex;
  if (json_classes != nullptr) {
    json_first_dex = m_cross_dex_ref_minimizer.get_json_class_indices(
        m_emitting_state.dexes_structure.get_current_dex().get_classes());
  }

  // Unmark dynamically_dead flag if a class is perf sensitive.
  if (m_reorder_dynamically_dead_classes) {
    std::vector<DexClass*> excluded_dead_classes;
    for (DexClass* cls : m_scope) {
      if (cls->get_perf_sensitive() == PerfSensitiveGroup::BETAMAP_ORDERED &&
          cls->is_dynamically_dead()) {
        cls->set_dynamically_dead(false);
        excluded_dead_classes.push_back(cls);
      }
    }
    if (!excluded_dead_classes.empty()) {
      exclude_extra_dynamically_dead_class(excluded_dead_classes);
    }
  }

  // Now emit the classes that weren't specified in the head or primary list.
  auto remaining_classes_first_dex_idx = m_emitting_state.outdex.size();
  emit_remaining_classes(dex_info, &canary_cls);

  // Emit what is left, if any.
  if (!m_emitting_state.dexes_structure.get_current_dex().empty()) {
    auto fodr = flush_out_dex(m_emitting_state, dex_info, canary_cls);
    post_process_dex(m_emitting_state, fodr);
    canary_cls = nullptr;
  }

  // Emit the rest dynamically_dead classes, if there is any.
  if (m_reorder_dynamically_dead_classes) {
    bool any_dynamically_dead = false;
    // The following dexes should contains dynamically_dead classes only.
    // Therefore, for any additional generated classes, we mark them
    // dynamically_dead by setting m_emitting_dynamically_dead_dex true.
    m_emitting_dynamically_dead_dex = true;
    canary_cls = get_canary_cls(m_emitting_state, EMPTY_DEX_INFO);
    for (DexClass* cls : m_scope) {
      if (!cls->is_dynamically_dead()) {
        continue;
      }
      if (m_emitting_state.dexes_structure.has_class(cls)) {
        // This class is already added. Ignore.
        continue;
      }
      emit_class(m_emitting_state, dex_info, cls, /*check_if_skip*/ false,
                 /*perf_sensitive*/ false, &canary_cls, /*opt_fodr*/ nullptr);
      any_dynamically_dead = true;
    }

    if (any_dynamically_dead) {
      // Emit what is left, if any.
      if (!m_emitting_state.dexes_structure.get_current_dex().empty()) {
        auto fodr = flush_out_dex(m_emitting_state, dex_info, canary_cls);
        post_process_dex(m_emitting_state, fodr);
        canary_cls = nullptr;
      }
    }
  }

  if (json_classes != nullptr) {
    Json::Value json_solution = Json::arrayValue;
    for (size_t dex_idx = remaining_classes_first_dex_idx;
         dex_idx < m_emitting_state.outdex.size();
         dex_idx++) {
      auto& dex = m_emitting_state.outdex.at(dex_idx);
      if (!dex.empty()) {
        json_solution.append(
            m_cross_dex_ref_minimizer.get_json_class_indices(dex));
      }
    }
    Json::Value json_limits;
    json_limits["types"] =
        int(m_emitting_state.dexes_structure.get_trefs_limit());
    json_limits["fields"] =
        int(m_emitting_state.dexes_structure.get_frefs_limit());
    json_limits["methods"] =
        int(m_emitting_state.dexes_structure.get_mrefs_limit());
    Json::Value json_file;
    json_file["limits"] = json_limits;
    json_file["first_dex"] = json_first_dex;
    json_file["solution"] = json_solution;
    json_file["mapping"] = m_cross_dex_ref_minimizer.get_json_mapping();
    json_file["classes"] = *json_classes;
    write_string_to_file(
        m_conf.metafile("interdex-cross-ref-minimization.json"),
        json_file.toStyledString());
  }

  // Emit dex info manifest
  if (m_asset_manager.has_secondary_dex_dir()) {
    auto mixed_mode_file = m_asset_manager.new_asset_file("dex_manifest.txt");
    auto mixed_mode_fh = FileHandle(*mixed_mode_file);
    mixed_mode_fh.seek_end();
    std::stringstream ss;
    int ordinal = 0;
    for (const auto& info : m_emitting_state.dex_infos) {
      const auto& flags = std::get<1>(info);
      ss << std::get<0>(info) << ",ordinal=" << ordinal++
         << ",coldstart=" << flags.coldstart << ",extended=" << flags.extended
         << ",primary=" << flags.primary << ",scroll=" << flags.scroll
         << ",background=" << flags.background << '\n';
    }
    write_str(mixed_mode_fh, ss.str());
    *mixed_mode_file = nullptr;
  }

  always_assert_log(!m_emit_canaries ||
                        m_emitting_state.dexes_structure.get_num_dexes() <
                            MAX_DEX_NUM,
                    "Bailing, max dex number surpassed %zu\n",
                    m_emitting_state.dexes_structure.get_num_dexes());

  print_stats(&m_emitting_state.dexes_structure);
}

void InterDex::run_on_nonroot_store() {
  TRACE(IDEX, 2, "IDEX: Running on non-root store");
  auto* canary_cls = get_canary_cls(m_emitting_state, EMPTY_DEX_INFO);
  for (DexClass* cls : m_scope) {
    emit_class(m_emitting_state, EMPTY_DEX_INFO, cls,
               /* check_if_skip */ false,
               /* perf_sensitive */ false, &canary_cls);
  }

  // Emit what is left, if any.
  if (!m_emitting_state.dexes_structure.get_current_dex().empty()) {
    auto fodr = flush_out_dex(m_emitting_state, EMPTY_DEX_INFO, canary_cls);
    post_process_dex(m_emitting_state, fodr);
  }

  print_stats(&m_emitting_state.dexes_structure);
}

void InterDex::add_dexes_from_store(const DexStore& store) {
  auto* canary_cls = get_canary_cls(m_emitting_state, EMPTY_DEX_INFO);
  const auto& dexes = store.get_dexen();
  for (const DexClasses& classes : dexes) {
    for (DexClass* cls : classes) {
      emit_class(m_emitting_state, EMPTY_DEX_INFO, cls,
                 /* check_if_skip */ false,
                 /* perf_sensitive */ false, &canary_cls);
    }
  }
  auto fodr = flush_out_dex(m_emitting_state, EMPTY_DEX_INFO, canary_cls);
  post_process_dex(m_emitting_state, fodr);
}

// Creates a canary class if necessary. (In particular, the primary dex never
// has a canary class.) This method should be called after flush_out_dex when
// beginning a new dex. As canary classes are added in the end without checks,
// the implied references are added here immediately to ensure that we don't
// exceed limits.
DexClass* InterDex::get_canary_cls(EmittingState& emitting_state,
                                   DexInfo& dex_info) const {
  if (!m_emit_canaries || dex_info.primary) {
    return nullptr;
  }
  size_t dexnum =
      static_cast<int>(emitting_state.dexes_structure.get_num_dexes());
  DexClass* canary_cls;
  {
    static std::mutex canary_mutex;
    std::lock_guard<std::mutex> lock_guard(canary_mutex);
    canary_cls = create_canary(static_cast<int>(dexnum));
  }
  MethodRefs clazz_mrefs;
  FieldRefs clazz_frefs;
  TypeRefs clazz_trefs;
  std::vector<const DexType*> clazz_itrefs;
  canary_cls->gather_methods(clazz_mrefs);
  canary_cls->gather_fields(clazz_frefs);
  canary_cls->gather_types(clazz_trefs);
  canary_cls->gather_init_classes(clazz_itrefs);
  emitting_state.dexes_structure.add_refs_no_checks(
      clazz_mrefs, clazz_frefs, clazz_trefs,
      TypeRefs(clazz_itrefs.begin(), clazz_itrefs.end()));
  return canary_cls;
}

/**
 * This needs to be called before getting to the next dex.
 */
InterDex::FlushOutDexResult InterDex::flush_out_dex(
    EmittingState& emitting_state,
    DexInfo& dex_info,
    DexClass* canary_cls) const {

  // This dex is the last one of the cold-start set, so it is still recorded as
  // cold start below; the reset only applies from the next dex on. Take it off
  // dex_info first so that it never reaches a recorded dex.
  const bool ends_coldstart_set = dex_info.pending_coldstart_reset;
  dex_info.pending_coldstart_reset = false;

  if (dex_info.primary) {
    TRACE(IDEX, 2, "Writing out primary dex with %zu classes.",
          emitting_state.dexes_structure.get_current_dex().size());
  } else {
    TRACE(IDEX, 2,
          "Writing out secondary dex number %zu, which is %s of coldstart, "
          "%s of extended set, %s of background set, %s scroll "
          "classes and has %zu classes.",
          emitting_state.dexes_structure.get_num_secondary_dexes() + 1,
          (dex_info.coldstart ? "part of" : "not part of"),
          (dex_info.extended ? "part of" : "not part of"),
          (dex_info.background ? "part of" : "not part of"),
          (dex_info.scroll ? "has" : "doesn't have"),
          emitting_state.dexes_structure.get_current_dex().size());
  }

  // Add the Canary class, if any.
  if (canary_cls != nullptr) {
    always_assert(emitting_state.dexes_structure.current_dex_has_tref(
        canary_cls->get_type()));

    // Properly try to insert the class.

    MethodRefs clazz_mrefs;
    FieldRefs clazz_frefs;
    TypeRefs clazz_trefs;
    TypeRefs clazz_itrefs;
    gather_refs(m_class_references_cache, m_plugins, canary_cls, &clazz_mrefs,
                &clazz_frefs, &clazz_trefs, &clazz_itrefs);

    bool canary_added = emitting_state.dexes_structure.add_class_to_current_dex(
        clazz_mrefs, clazz_frefs, clazz_trefs, clazz_itrefs, canary_cls);
    always_assert(canary_added);

    emitting_state.dex_infos.emplace_back(canary_cls->get_name()->str_copy(),
                                          dex_info);
  }

  FlushOutDexResult fodr{emitting_state.outdex.size(),
                         dex_info.primary || dex_info.betamap_ordered};
  auto classes = emitting_state.dexes_structure.end_dex(dex_info);
  emitting_state.outdex.emplace_back(std::move(classes));

  if (!m_emitting_scroll_set) {
    dex_info.scroll = false;
  }
  if (!m_emitting_bg_set) {
    dex_info.background = false;
  }
  if (!m_emitting_extended) {
    dex_info.extended = false;
  }
  if (ends_coldstart_set) {
    dex_info.coldstart = false;
  }

  // This is false by default and set to true everytime
  // a DEX contains classes already ordered by the betamap.
  // This resets the flag as this method advances to the next
  // writable DEX.
  dex_info.betamap_ordered = false;

  return fodr;
}

void InterDex::post_process_dex(EmittingState& emitting_state,
                                const FlushOutDexResult& fodr) const {
  auto& classes = emitting_state.outdex.at(fodr.dex_count);

  for (auto& plugin : m_plugins) {
    for (auto* cls : plugin->additional_classes(fodr.dex_count, classes)) {
      TRACE(IDEX, 4, "IDEX: Emitting %s-plugin-generated class :: %s",
            plugin->name().c_str(), SHOW(cls));
      classes.push_back(cls);
      // For the plugin cls, make sure all methods are cfg built.
      for (auto* m : cls->get_all_methods()) {
        if (m->get_code() == nullptr) {
          continue;
        }
        m->get_code()->build_cfg();
      }

      // If this is the primary dex, or if there are any betamap-ordered
      // classes in this dex, then we treat the additional classes as
      // perf-sensitive, to be conservative.
      if (fodr.primary_or_betamap_ordered) {
        cls->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
      }

      // If this is dynamically_dead dex, we treat the additional classes as
      // dynamically_dead.
      if (m_emitting_dynamically_dead_dex) {
        cls->set_dynamically_dead();
      }
    }
  }

  if (!m_order_interdex && !m_interdex_order.empty()) {
    // BETAMAP_ORDERED classes didn't get ordered yet, let's at least establish
    // their relative order within this dex
    auto get_index = [this](const DexClass* cls) {
      auto it = m_interdex_order.find(cls);
      return it == m_interdex_order.end() ? std::numeric_limits<size_t>::max()
                                          : it->second;
    };
    std::stable_sort(classes.begin(), classes.end(),
                     [&get_index](const DexClass* a, const DexClass* b) {
                       return get_index(a) < get_index(b);
                     });
  }
}

void InterDex::exclude_baseline_profile_classes() {
  always_assert(m_exclude_baseline_profile_classes);
  initialize_baseline_profile_classes();

  // Loop through, still setting baseline profile classes to perf sensitive,
  // and erasing them from m_interdex_types.
  for (auto it = m_interdex_types.begin(); it != m_interdex_types.end();) {
    const auto* dex_type = *it;
    if (!this->is_baseline_profile_class(dex_type)) {
      ++it;
      continue;
    }

    if (auto* cls = type_class(dex_type)) {
      cls->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
    }

    it = m_interdex_types.erase(it);
  }

  // Also remove any DexEndMarkers which would otherwise create initial empty
  // dexes. Mostly handles the case when classes which would have otherwise
  // been in the first dex with the 20% cold start set are all in the baseline
  // profile.
  auto it = m_interdex_types.begin();
  while (it != m_interdex_types.end() &&
         (*it)->get_name()->str().starts_with(END_MARKER_FORMAT)) {
    it = m_interdex_types.erase(it);
  }
}

void InterDex::initialize_baseline_profile_classes() {
  always_assert(m_exclude_baseline_profile_classes || m_move_coldstart_classes);
  if (m_baseline_profile_classes) {
    return;
  }

  m_baseline_profile_classes = UnorderedSet<const DexType*>();

  // If the 20% cold start set from the betamap is included in the baseline
  // profile, read and insert  all classes in the betamap up until the 20% cold
  // start end marker.
  if (m_baseline_profile_config.options.include_betamap_20pct_coldstart) {
    auto it = m_interdex_types.begin();

    for (; it != m_interdex_types.end(); ++it) {
      const auto* dex_type = *it;
      m_baseline_profile_classes->insert(dex_type);
      if (dex_type->get_name()->str().starts_with(
              COLD_START_20PCT_END_FORMAT)) {
        break;
      }
    }

    always_assert_log(it != m_interdex_types.end(),
                      "include_betamap_20pct_coldstart is set, but %s marker "
                      "not found in betamap",
                      COLD_START_20PCT_END_FORMAT);

    if (m_baseline_profile_config.options.betamap_include_coldstart_1pct) {
      for (; it != m_interdex_types.end(); ++it) {
        const auto* dex_type = *it;
        m_baseline_profile_classes->insert(dex_type);
        if (dex_type->get_name()->str().starts_with(
                COLD_START_1PCT_END_FORMAT)) {
          break;
        }
      }

      always_assert_log(it != m_interdex_types.end(),
                        "betamap_include_coldstart_1pct is set, but %s marker "
                        "not found in betamap",
                        COLD_START_1PCT_END_FORMAT);
    }
  }

  // Handle deep data profiles
  const auto& method_profiles = m_conf.get_method_profiles();
  for (const auto& [interaction_id, _] :
       m_baseline_profile_config.interactions) {
    auto it =
        m_baseline_profile_config.interaction_configs.find(interaction_id);
    always_assert_log(it != m_baseline_profile_config.interaction_configs.end(),
                      "%s\n", interaction_id.c_str());
    const auto& interaction_config = it->second;
    if (!interaction_config.classes) {
      continue;
    }

    const auto& method_stats = method_profiles.method_stats(interaction_id);
    for (const auto& [method, stat] : UnorderedIterable(method_stats)) {
      if (stat.appear_percent >=
              static_cast<double>(interaction_config.threshold) &&
          stat.call_count >=
              static_cast<double>(interaction_config.call_threshold)) {
        auto* dex_type = method->get_class();
        always_assert(dex_type);
        m_baseline_profile_classes->insert(dex_type);
      }
    }
  }

  // TODO: Not handling the manual profile yet.
}

} // namespace interdex
