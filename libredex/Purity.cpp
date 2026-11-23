/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Purity.h"

#include <algorithm>
#include <iterator>
#include <vector>

#include <sparta/WeakTopologicalOrdering.h>

#include "Debug.h"
#include "DexClass.h"
#include "EditableCfgAdapter.h"
#include "IRInstruction.h"
#include "Resolver.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "Walkers.h"
#include "WorkQueue.h"

namespace {

constexpr double kWtoOrderingThreshold = 50.0;

} // namespace

std::ostream& operator<<(std::ostream& o, const CseLocation& l) {
  switch (l.special_location) {
  case CseSpecialLocations::GENERAL_MEMORY_BARRIER:
    o << "*";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_INT:
    o << "(int[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_BYTE:
    o << "(byte[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_CHAR:
    o << "(char[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_WIDE:
    o << "(long|double[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_SHORT:
    o << "(short[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_OBJECT:
    o << "(Object[])[.]";
    break;
  case CseSpecialLocations::ARRAY_COMPONENT_TYPE_BOOLEAN:
    o << "(boolean[])[.]";
    break;
  default:
    o << SHOW(l.field);
    break;
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const CseUnorderedLocationSet& ls) {
  o << "{";
  bool first = true;
  for (const auto& l : UnorderedIterable(ls)) {
    if (first) {
      first = false;
    } else {
      o << ", ";
    }
    o << l;
  }
  o << "}";
  return o;
}

CseLocation get_field_location(IROpcode opcode, const DexField* field) {
  always_assert(opcode::is_an_ifield_op(opcode) ||
                opcode::is_an_sfield_op(opcode));
  if (field != nullptr && !is_volatile(field)) {
    return CseLocation(field);
  }

  return CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER);
}

CseLocation get_field_location(IROpcode opcode, const DexFieldRef* field_ref) {
  always_assert(opcode::is_an_ifield_op(opcode) ||
                opcode::is_an_sfield_op(opcode));
  DexField* field = resolve_field(field_ref, opcode::is_an_sfield_op(opcode)
                                                 ? FieldSearch::Static
                                                 : FieldSearch::Instance);
  return get_field_location(opcode, field);
}

CseLocation get_read_array_location(IROpcode opcode) {
  switch (opcode) {
  case OPCODE_AGET:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_INT);
  case OPCODE_AGET_BYTE:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_BYTE);
  case OPCODE_AGET_CHAR:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_CHAR);
  case OPCODE_AGET_WIDE:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_WIDE);
  case OPCODE_AGET_SHORT:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_SHORT);
  case OPCODE_AGET_OBJECT:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_OBJECT);
  case OPCODE_AGET_BOOLEAN:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_BOOLEAN);
  default:
    not_reached();
  }
}

CseLocation get_read_location(const IRInstruction* insn) {
  if (opcode::is_an_aget(insn->opcode())) {
    return get_read_array_location(insn->opcode());
  } else if (opcode::is_an_iget(insn->opcode()) ||
             opcode::is_an_sget(insn->opcode())) {
    return get_field_location(insn->opcode(), insn->get_field());
  } else {
    return CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER);
  }
}

static const std::string_view pure_method_names[] = {
    "Ljava/lang/Boolean;.booleanValue:()Z",
    "Ljava/lang/Boolean;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Boolean;.getBoolean:(Ljava/lang/String;)Z",
    "Ljava/lang/Boolean;.hashCode:()I",
    "Ljava/lang/Boolean;.toString:()Ljava/lang/String;",
    "Ljava/lang/Boolean;.toString:(Z)Ljava/lang/String;",
    "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;",
    "Ljava/lang/Boolean;.valueOf:(Ljava/lang/String;)Ljava/lang/Boolean;",
    "Ljava/lang/Byte;.byteValue:()B",
    "Ljava/lang/Byte;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Byte;.toString:()Ljava/lang/String;",
    "Ljava/lang/Byte;.toString:(B)Ljava/lang/String;",
    "Ljava/lang/Byte;.valueOf:(B)Ljava/lang/Byte;",
    "Ljava/lang/Character;.valueOf:(C)Ljava/lang/Character;",
    "Ljava/lang/Character;.charValue:()C",
    "Ljava/lang/Class;.getName:()Ljava/lang/String;",
    "Ljava/lang/Class;.getSimpleName:()Ljava/lang/String;",
    "Ljava/lang/Double;.compare:(DD)I",
    "Ljava/lang/Double;.doubleValue:()D",
    "Ljava/lang/Double;.doubleToLongBits:(D)J",
    "Ljava/lang/Double;.doubleToRawLongBits:(D)J",
    "Ljava/lang/Double;.floatValue:()F",
    "Ljava/lang/Double;.hashCode:()I",
    "Ljava/lang/Double;.intValue:()I",
    "Ljava/lang/Double;.isInfinite:(D)Z",
    "Ljava/lang/Double;.isNaN:(D)Z",
    "Ljava/lang/Double;.longBitsToDouble:(J)D",
    "Ljava/lang/Double;.longValue:()J",
    "Ljava/lang/Double;.toString:(D)Ljava/lang/String;",
    "Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;",
    "Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Enum;.name:()Ljava/lang/String;",
    "Ljava/lang/Enum;.ordinal:()I",
    "Ljava/lang/Enum;.toString:()Ljava/lang/String;",
    "Ljava/lang/Float;.doubleValue:()D",
    "Ljava/lang/Float;.floatToRawIntBits:(F)I",
    "Ljava/lang/Float;.floatValue:()F",
    "Ljava/lang/Float;.compare:(FF)I",
    "Ljava/lang/Float;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Float;.hashCode:()I",
    "Ljava/lang/Float;.intBitsToFloat:(I)F",
    "Ljava/lang/Float;.intValue:()I",
    "Ljava/lang/Float;.floatToIntBits:(F)I",
    "Ljava/lang/Float;.isInfinite:(F)Z",
    "Ljava/lang/Float;.isNaN:(F)Z",
    "Ljava/lang/Float;.valueOf:(F)Ljava/lang/Float;",
    "Ljava/lang/Float;.toString:(F)Ljava/lang/String;",
    "Ljava/lang/Integer;.bitCount:(I)I",
    "Ljava/lang/Integer;.byteValue:()B",
    "Ljava/lang/Integer;.compareTo:(Ljava/lang/Integer;)I",
    "Ljava/lang/Integer;.doubleValue:()D",
    "Ljava/lang/Integer;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Integer;.hashCode:()I",
    "Ljava/lang/Integer;.highestOneBit:(I)I",
    "Ljava/lang/Integer;.intValue:()I",
    "Ljava/lang/Integer;.longValue:()J",
    "Ljava/lang/Integer;.lowestOneBit:(I)I",
    "Ljava/lang/Integer;.numberOfLeadingZeros:(I)I",
    "Ljava/lang/Integer;.numberOfTrailingZeros:(I)I",
    "Ljava/lang/Integer;.shortValue:()S",
    "Ljava/lang/Integer;.signum:(I)I",
    "Ljava/lang/Integer;.toBinaryString:(I)Ljava/lang/String;",
    "Ljava/lang/Integer;.toHexString:(I)Ljava/lang/String;",
    "Ljava/lang/Integer;.toString:()Ljava/lang/String;",
    "Ljava/lang/Integer;.toString:(I)Ljava/lang/String;",
    "Ljava/lang/Integer;.toString:(II)Ljava/lang/String;",
    "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;",
    "Ljava/lang/Long;.bitCount:(J)I",
    "Ljava/lang/Long;.compareTo:(Ljava/lang/Long;)I",
    "Ljava/lang/Long;.doubleValue:()D",
    "Ljava/lang/Long;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Long;.hashCode:()I",
    "Ljava/lang/Long;.intValue:()I",
    "Ljava/lang/Long;.highestOneBit:(J)J",
    "Ljava/lang/Long;.longValue:()J",
    "Ljava/lang/Long;.numberOfTrailingZeros:(J)I",
    "Ljava/lang/Long;.signum:(J)I",
    "Ljava/lang/Long;.toBinaryString:(J)Ljava/lang/String;",
    "Ljava/lang/Long;.toHexString:(J)Ljava/lang/String;",
    "Ljava/lang/Long;.toString:()Ljava/lang/String;",
    "Ljava/lang/Long;.toString:(J)Ljava/lang/String;",
    "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;",
    "Ljava/lang/Math;.IEEEremainder:(DD)D",
    "Ljava/lang/Math;.abs:(J)J",
    "Ljava/lang/Math;.abs:(I)I",
    "Ljava/lang/Math;.abs:(F)F",
    "Ljava/lang/Math;.abs:(D)D",
    "Ljava/lang/Math;.acos:(D)D",
    "Ljava/lang/Math;.asin:(D)D",
    "Ljava/lang/Math;.atan:(D)D",
    "Ljava/lang/Math;.atan2:(DD)D",
    "Ljava/lang/Math;.cbrt:(D)D",
    "Ljava/lang/Math;.ceil:(D)D",
    "Ljava/lang/Math;.copySign:(FF)F",
    "Ljava/lang/Math;.copySign:(DD)D",
    "Ljava/lang/Math;.cos:(D)D",
    "Ljava/lang/Math;.cosh:(D)D",
    "Ljava/lang/Math;.exp:(D)D",
    "Ljava/lang/Math;.expm1:(D)D",
    "Ljava/lang/Math;.floor:(D)D",
    "Ljava/lang/Math;.floorDiv:(II)I",
    "Ljava/lang/Math;.floorDiv:(JJ)J",
    "Ljava/lang/Math;.floorMod:(JJ)J",
    "Ljava/lang/Math;.floorMod:(II)I",
    "Ljava/lang/Math;.getExponent:(D)I",
    "Ljava/lang/Math;.getExponent:(F)I",
    "Ljava/lang/Math;.hypot:(DD)D",
    "Ljava/lang/Math;.log:(D)D",
    "Ljava/lang/Math;.log10:(D)D",
    "Ljava/lang/Math;.log1p:(D)D",
    "Ljava/lang/Math;.max:(II)I",
    "Ljava/lang/Math;.max:(JJ)J",
    "Ljava/lang/Math;.max:(FF)F",
    "Ljava/lang/Math;.max:(DD)D",
    "Ljava/lang/Math;.min:(FF)F",
    "Ljava/lang/Math;.min:(DD)D",
    "Ljava/lang/Math;.min:(II)I",
    "Ljava/lang/Math;.min:(JJ)J",
    "Ljava/lang/Math;.nextAfter:(DD)D",
    "Ljava/lang/Math;.nextAfter:(FD)F",
    "Ljava/lang/Math;.nextDown:(D)D",
    "Ljava/lang/Math;.nextDown:(F)F",
    "Ljava/lang/Math;.nextUp:(F)F",
    "Ljava/lang/Math;.nextUp:(D)D",
    "Ljava/lang/Math;.pow:(DD)D",
    "Ljava/lang/Math;.random:()D",
    "Ljava/lang/Math;.rint:(D)D",
    "Ljava/lang/Math;.round:(D)J",
    "Ljava/lang/Math;.round:(F)I",
    "Ljava/lang/Math;.scalb:(FI)F",
    "Ljava/lang/Math;.scalb:(DI)D",
    "Ljava/lang/Math;.signum:(D)D",
    "Ljava/lang/Math;.signum:(F)F",
    "Ljava/lang/Math;.sin:(D)D",
    "Ljava/lang/Math;.sinh:(D)D",
    "Ljava/lang/Math;.sqrt:(D)D",
    "Ljava/lang/Math;.tan:(D)D",
    "Ljava/lang/Math;.tanh:(D)D",
    "Ljava/lang/Math;.toDegrees:(D)D",
    "Ljava/lang/Math;.toRadians:(D)D",
    "Ljava/lang/Math;.ulp:(D)D",
    "Ljava/lang/Math;.ulp:(F)F",
    "Ljava/lang/Object;.getClass:()Ljava/lang/Class;",
    "Ljava/lang/Short;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/Short;.shortValue:()S",
    "Ljava/lang/Short;.toString:(S)Ljava/lang/String;",
    "Ljava/lang/Short;.valueOf:(S)Ljava/lang/Short;",
    "Ljava/lang/String;.compareTo:(Ljava/lang/String;)I",
    "Ljava/lang/String;.compareToIgnoreCase:(Ljava/lang/String;)I",
    "Ljava/lang/String;.concat:(Ljava/lang/String;)Ljava/lang/String;",
    "Ljava/lang/String;.endsWith:(Ljava/lang/String;)Z",
    "Ljava/lang/String;.equals:(Ljava/lang/Object;)Z",
    "Ljava/lang/String;.equalsIgnoreCase:(Ljava/lang/String;)Z",
    "Ljava/lang/String;.hashCode:()I",
    "Ljava/lang/String;.indexOf:(I)I",
    "Ljava/lang/String;.isEmpty:()Z",
    "Ljava/lang/String;.indexOf:(Ljava/lang/String;)I",
    "Ljava/lang/String;.indexOf:(II)I",
    "Ljava/lang/String;.indexOf:(Ljava/lang/String;I)I",
    "Ljava/lang/String;.lastIndexOf:(I)I",
    "Ljava/lang/String;.lastIndexOf:(II)I",
    "Ljava/lang/String;.lastIndexOf:(Ljava/lang/String;)I",
    "Ljava/lang/String;.lastIndexOf:(Ljava/lang/String;I)I",
    "Ljava/lang/String;.length:()I",
    "Ljava/lang/String;.replace:(CC)Ljava/lang/String;",
    "Ljava/lang/String;.startsWith:(Ljava/lang/String;)Z",
    "Ljava/lang/String;.startsWith:(Ljava/lang/String;I)Z",
    "Ljava/lang/String;.toLowerCase:()Ljava/lang/String;",
    "Ljava/lang/String;.toLowerCase:(Ljava/util/Locale;)Ljava/lang/String;",
    "Ljava/lang/String;.toString:()Ljava/lang/String;",
    "Ljava/lang/String;.toUpperCase:()Ljava/lang/String;",
    "Ljava/lang/String;.toUpperCase:(Ljava/util/Locale;)Ljava/lang/String;",
    "Ljava/lang/String;.trim:()Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(C)Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(D)Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(F)Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(I)Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(J)Ljava/lang/String;",
    "Ljava/lang/String;.valueOf:(Z)Ljava/lang/String;",
    "Ljava/lang/System;.identityHashCode:(Ljava/lang/Object;)I",
    "Ljava/lang/Thread;.currentThread:()Ljava/lang/Thread;",
};

UnorderedSet<DexMethodRef*> get_pure_methods() {
  UnorderedSet<DexMethodRef*> pure_methods;
  for (auto const pure_method_name : pure_method_names) {
    auto* method_ref = DexMethod::get_method(pure_method_name);
    if (method_ref == nullptr) {
      TRACE(CSE, 1, "[get_pure_methods]: Could not find pure method %s",
            str_copy(pure_method_name).c_str());
      continue;
    }

    pure_methods.insert(method_ref);
  }
  return pure_methods;
}

UnorderedSet<DexMethod*> get_immutable_getters(const Scope& scope) {
  UnorderedSet<DexMethod*> pure_methods;
  walk::methods(scope, [&](DexMethod* method) {
    if (method->rstate.immutable_getter()) {
      pure_methods.insert(method);
    }
  });
  return pure_methods;
}

namespace {

MethodOverrideAction get_base_or_overriding_method_action_impl(
    const DexMethod* method,
    const UnorderedSet<const DexMethod*>* methods_to_ignore,
    bool ignore_methods_with_assumenosideeffects) {
  if (method == nullptr || method::is_clinit(method) ||
      method->rstate.no_optimizations()) {
    return MethodOverrideAction::UNKNOWN;
  }

  if ((method->is_virtual() && is_interface(type_class(method->get_class()))) &&
      (root(method) || !can_rename(method))) {
    // We cannot rule out that there are dynamically added classes, created via
    // Proxy.newProxyInstance, that override this method.
    // So we assume the worst.
    return MethodOverrideAction::UNKNOWN;
  }

  if ((methods_to_ignore != nullptr) &&
      (methods_to_ignore->count(method) != 0u)) {
    return MethodOverrideAction::EXCLUDE;
  }

  if (ignore_methods_with_assumenosideeffects && assumenosideeffects(method)) {
    return MethodOverrideAction::EXCLUDE;
  }

  if (method->is_external() || is_native(method)) {
    return MethodOverrideAction::UNKNOWN;
  }

  if (is_abstract(method)) {
    return MethodOverrideAction::EXCLUDE;
  }

  return MethodOverrideAction::INCLUDE;
}

} // namespace

MethodOverrideAction get_base_or_overriding_method_action(
    const DexMethod* method,
    const UnorderedSet<const DexMethod*>* methods_to_ignore,
    bool ignore_methods_with_assumenosideeffects) {
  return get_base_or_overriding_method_action_impl(
      method, methods_to_ignore, ignore_methods_with_assumenosideeffects);
}

namespace {

template <typename HandlerFunc>
bool process_base_and_overriding_methods_impl(
    const method_override_graph::Graph* method_override_graph,
    const DexMethod* method,
    const UnorderedSet<const DexMethod*>* methods_to_ignore,
    bool ignore_methods_with_assumenosideeffects,
    const HandlerFunc& handler_func) {
  auto action = get_base_or_overriding_method_action_impl(
      method, methods_to_ignore, ignore_methods_with_assumenosideeffects);
  if (action == MethodOverrideAction::UNKNOWN ||
      (action == MethodOverrideAction::INCLUDE &&
       !handler_func(const_cast<DexMethod*>(method)))) {
    return false;
  }
  // When the method isn't virtual, there are no overridden methods to consider.
  if (!method->is_virtual()) {
    return true;
  }
  // But even if there are overridden methods, don't look further when the
  // method is to be ignored.
  if (methods_to_ignore && methods_to_ignore->count(method)) {
    return true;
  }
  if (ignore_methods_with_assumenosideeffects && assumenosideeffects(method)) {
    return true;
  }

  // When we don't have a method-override graph, let's be conservative and give
  // up.
  if (!method_override_graph) {
    return false;
  }

  // Okay, let's process all overridden methods just like the base method.
  return method_override_graph::all_overriding_methods(
      *method_override_graph, method, [&](const DexMethod* overriding_method) {
        action = get_base_or_overriding_method_action(
            overriding_method, methods_to_ignore,
            ignore_methods_with_assumenosideeffects);
        return !static_cast<bool>(
            action == MethodOverrideAction::UNKNOWN ||
            (action == MethodOverrideAction::INCLUDE &&
             !handler_func(const_cast<DexMethod*>(overriding_method))));
      });
  return true;
}

} // namespace

bool process_base_and_overriding_methods(
    const method_override_graph::Graph* method_override_graph,
    const DexMethod* method,
    const UnorderedSet<const DexMethod*>* methods_to_ignore,
    bool ignore_methods_with_assumenosideeffects,
    const std::function<bool(DexMethod*)>& handler_func) {
  return process_base_and_overriding_methods_impl(
      method_override_graph,
      method,
      methods_to_ignore,
      ignore_methods_with_assumenosideeffects,
      handler_func);
}

namespace {

AccumulatingTimer s_wto_timer("compute_locations_closure_wto");

class WtoOrdering {
  static constexpr const DexMethod* WTO_ROOT = nullptr;

  struct FirstIterationData {
    std::vector<const DexMethod*> root_cache;
    UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
        inverse_dependencies;
    const std::vector<const DexMethod*> empty;

    const std::vector<const DexMethod*>& get(const DexMethod* m) {
      if (m == WTO_ROOT) {
        // Pre-initialized and pre-sorted
        return root_cache;
      }
      auto it = inverse_dependencies.find(m);
      if (it != inverse_dependencies.end()) {
        // Pre-sorted
        return it->second;
      }
      return empty;
    }
  };

  static FirstIterationData create_first_iteration_data(
      UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
          inverse_dependencies,
      const UnorderedSet<const DexMethod*>& impacted_methods) {
    std::vector<const DexMethod*> wto_nodes{WTO_ROOT};
    wto_nodes.reserve(wto_nodes.size() + impacted_methods.size());
    insert_unordered_iterable(wto_nodes, wto_nodes.end(), impacted_methods);

    // In the first iteration, besides computing the sorted root successors, we
    // also sort all inverse_dependencies entries in-place. They represent the
    // full successor vectors.
    std::vector<const DexMethod*> root_cache;
    workqueue_run<const DexMethod*>(
        [&inverse_dependencies, &root_cache,
         &impacted_methods](const DexMethod* m) {
          if (m == WTO_ROOT) {
            root_cache = get_sorted_impacted_methods(impacted_methods);
            return;
          }
          auto it = inverse_dependencies.find(m);
          if (it != inverse_dependencies.end()) {
            auto& entries = it->second;
            entries.shrink_to_fit();
            std::sort(entries.begin(), entries.end(), compare_dexmethods);
          }
        },
        wto_nodes);

    return {std::move(root_cache), inverse_dependencies, {}};
  }

  struct OtherIterationData {
    InsertOnlyConcurrentMap<const DexMethod*, std::vector<const DexMethod*>>
        concurrent_cache;

    const std::vector<const DexMethod*>& get(const DexMethod* const& m) {
      return concurrent_cache.at_unsafe(m);
    }
  };

  static OtherIterationData create_other_iteration_data(
      UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
          inverse_dependencies,
      const UnorderedSet<const DexMethod*>& impacted_methods) {
    std::vector<const DexMethod*> wto_nodes{WTO_ROOT};
    wto_nodes.reserve(wto_nodes.size() + impacted_methods.size());
    insert_unordered_iterable(wto_nodes, wto_nodes.end(), impacted_methods);

    // In subsequent iteration, besides computing the sorted root successors
    // again, we also filter all previously sorted inverse_dependencies entries.
    InsertOnlyConcurrentMap<const DexMethod*, std::vector<const DexMethod*>>
        concurrent_cache;
    workqueue_run<const DexMethod*>(
        [&impacted_methods, &concurrent_cache,
         &inverse_dependencies](const DexMethod* m) {
          std::vector<const DexMethod*> successors;
          if (m == WTO_ROOT) {
            // Re-initialize and re-sort
            successors = get_sorted_impacted_methods(impacted_methods);
          }
          auto it = inverse_dependencies.find(m);
          if (it != inverse_dependencies.end()) {
            // Note that we are filtering on an already pre-sorted vector
            for (const auto* n : it->second) {
              if (impacted_methods.count(n) != 0u) {
                successors.push_back(n);
              }
            }
          }
          auto [_, emplaced] =
              concurrent_cache.emplace(m, std::move(successors));
          always_assert(emplaced);
        },
        wto_nodes);

    return {std::move(concurrent_cache)};
  }

  static std::vector<const DexMethod*> get_sorted_impacted_methods(
      const UnorderedSet<const DexMethod*>& impacted_methods) {
    return unordered_to_ordered(impacted_methods, compare_dexmethods);
  }

  static std::vector<const DexMethod*> sort_by_inverse_deps(
      const UnorderedSet<const DexMethod*>& impacted_methods,
      const UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
          inverse_dependencies) {
    // First translate to pair to avoid repeated map lookups.
    std::vector<std::pair<const DexMethod*, size_t>> sorted_by_inv_deps;
    sorted_by_inv_deps.reserve(impacted_methods.size());
    unordered_transform(
        impacted_methods, std::back_inserter(sorted_by_inv_deps),
        [&inverse_dependencies](auto* m) {
          auto it = inverse_dependencies.find(m);
          return std::make_pair(
              m, it != inverse_dependencies.end() ? it->second.size() : 0);
        });
    std::sort(sorted_by_inv_deps.begin(), sorted_by_inv_deps.end(),
              [](const std::pair<const DexMethod*, size_t>& lhs,
                 const std::pair<const DexMethod*, size_t>& rhs) {
                if (lhs.second != rhs.second) {
                  return lhs.second > rhs.second;
                }
                return compare_dexmethods(lhs.first, rhs.first);
              });
    std::vector<const DexMethod*> res;
    res.reserve(impacted_methods.size());
    std::transform(sorted_by_inv_deps.begin(), sorted_by_inv_deps.end(),
                   std::back_inserter(res),
                   [](const auto& p) { return p.first; });
    return res;
  }

  // We saw big slowdowns when there are too many components, possibly
  // driven by the fact there is a lot of dependencies.
  template <typename SuccFn>
  static void run_wto(const SuccFn& succ_fn,
                      std::vector<const DexMethod*>& ordered_impacted_methods) {
    sparta::WeakTopologicalOrdering<const DexMethod*> wto(WTO_ROOT, succ_fn);
    wto.visit_depth_first([&ordered_impacted_methods](const DexMethod* m) {
      if (m) {
        ordered_impacted_methods.push_back(m);
      }
    });
  }

  static bool should_use_wto(
      const UnorderedSet<const DexMethod*>& impacted_methods,
      const UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
          inverse_dependencies) {
    size_t impacted_methods_size = impacted_methods.size();
    size_t inv_dep_sum{0}, inv_dep_max{0};
    for (const auto& entry : UnorderedIterable(inverse_dependencies)) {
      inv_dep_sum += entry.second.size();
      inv_dep_max = std::max(inv_dep_max, entry.second.size());
    }
    auto inv_dep_avg = static_cast<double>(inv_dep_sum) /
                       static_cast<double>(inverse_dependencies.size());
    // Purity is too low-level for nice configuration switches. Think
    // about it.
    TRACE(CSE, 4,
          "UseWto: impacted methods = %zu inverse_deps_max = %zu "
          "inverse_deps avg = %.2f",
          impacted_methods_size, inv_dep_max, inv_dep_avg);
    return inv_dep_avg < kWtoOrderingThreshold;
  }

 public:
  static std::vector<const DexMethod*> order_impacted_methods(
      const UnorderedSet<const DexMethod*>& impacted_methods,
      UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>&
          inverse_dependencies,
      size_t iterations) {
    Timer prepare_wto{"Prepare Ordering"};
    auto wto_timer_scope = s_wto_timer.scope();

    std::vector<const DexMethod*> ordered_impacted_methods;

    // To avoid std::function overhead we have to split here.
    if (iterations == 1 &&
        should_use_wto(impacted_methods, inverse_dependencies)) {
      auto first_data =
          create_first_iteration_data(inverse_dependencies, impacted_methods);
      run_wto(
          [&first_data](
              const DexMethod* m) -> const std::vector<const DexMethod*>& {
            return first_data.get(m);
          },
          ordered_impacted_methods);
    } else if (iterations == 1) {
      // Simple sorting for determinism.
      ordered_impacted_methods =
          sort_by_inverse_deps(impacted_methods, inverse_dependencies);
    } else {
      auto other_data =
          create_other_iteration_data(inverse_dependencies, impacted_methods);
      run_wto(
          [&other_data](
              const DexMethod* m) -> const std::vector<const DexMethod*>& {
            return other_data.get(m);
          },
          ordered_impacted_methods);
    }

    return ordered_impacted_methods;
  }
};

template <typename InitFuncT>
size_t compute_locations_closure_impl(
    const Scope& scope,
    const method_override_graph::Graph* /*method_override_graph*/,
    const InitFuncT& init_func,
    UnorderedMap<const DexMethod*, CseUnorderedLocationSet>* result) {
  // 1. Let's initialize known method read locations and dependencies by
  //    scanning method bodies
  InsertOnlyConcurrentMap<const DexMethod*, LocationsAndDependencies>
      method_lads;
  {
    Timer t{"Initialize LADS"};
    walk::parallel::methods(scope, [&](DexMethod* method) {
      auto lads = init_func(method);
      if (lads) {
        method_lads.emplace(method, std::move(*lads));
      }
    });
  }

  // 2. Compute inverse dependencies so that we know what needs to be recomputed
  // during the fixpoint computation, and determine set of methods that are
  // initially "impacted" in the sense that they have dependencies.
  UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>
      inverse_dependencies;
  UnorderedSet<const DexMethod*> impacted_methods;
  {
    Timer t{"Compute inverse dependencies"};
    for (auto&& [method, lads] : UnorderedIterable(method_lads)) {
      if (!lads.dependencies.empty()) {
        for (const auto* d : UnorderedIterable(lads.dependencies)) {
          inverse_dependencies[d].push_back(method);
        }
        impacted_methods.insert(method);
      }
    }
  }

  // 3. Let's try to (semantically) inline locations, computing a fixed
  //    point. Methods for which information is directly or indirectly absent
  //    are equivalent to a general memory barrier, and are systematically
  //    pruned.

  // TODO: Instead of custom fixpoint computation using WTO, consider using the
  // MonotonicFixpointIterator, operating on a callgraph, capture the
  // dependencies, and have the Locations as the abstract domain.

  size_t iterations = 0;
  while (!impacted_methods.empty()) {
    iterations++;
    Timer t{std::string("Iteration ") + std::to_string(iterations)};

    // We order the impacted methods in a deterministic way that's likely
    // helping to reduce the number of needed iterations.
    auto ordered_impacted_methods = WtoOrdering::order_impacted_methods(
        impacted_methods, inverse_dependencies, iterations);
    impacted_methods.clear();

    std::vector<const DexMethod*> changed_methods;
    for (const DexMethod* method : ordered_impacted_methods) {
      auto& lads = method_lads.at_unsafe(method);
      bool unknown = false;
      size_t lads_locations_size = lads.locations.size();
      for (const DexMethod* d : UnorderedIterable(lads.dependencies)) {
        if (d == method) {
          continue;
        }
        auto it = method_lads.find(d);
        if (it == method_lads.end()) {
          unknown = true;
          break;
        }
        const auto& other_locations = it->second.locations;
        insert_unordered_iterable(lads.locations, other_locations);
      }
      if (unknown || lads_locations_size < lads.locations.size()) {
        // something changed
        changed_methods.push_back(method);
        if (unknown) {
          method_lads.erase_unsafe(method);
        }
      }
    }

    // Given set of changed methods, determine set of dependents for which
    // we need to re-run the analysis in another iteration.
    for (const auto* changed_method : changed_methods) {
      auto it = inverse_dependencies.find(changed_method);
      if (it == inverse_dependencies.end()) {
        continue;
      }

      // remove inverse dependency entries as appropriate
      auto& entries = it->second;
      std::erase_if(entries,
                    [&](auto* m) { return !method_lads.count_unsafe(m); });

      if (entries.empty()) {
        // remove inverse dependency
        inverse_dependencies.erase(changed_method);
      } else {
        // add inverse dependencies entries to impacted methods
        impacted_methods.insert(entries.begin(), entries.end());
      }
    }
  }

  // For all methods which have a known set of locations at this point,
  // persist that information
  for (auto&& [method, lads] : UnorderedIterable(method_lads)) {
    result->emplace(method, std::move(lads.locations));
  }

  return iterations;
}

} // namespace

size_t compute_locations_closure(
    const Scope& scope,
    const method_override_graph::Graph* method_override_graph,
    const std::function<std::optional<LocationsAndDependencies>(DexMethod*)>&
        init_func,
    UnorderedMap<const DexMethod*, CseUnorderedLocationSet>* result) {
  return compute_locations_closure_impl(scope, method_override_graph, init_func,
                                        result);
}

// Helper function that invokes compute_locations_closure, providing initial
// set of locations indicating whether a function only reads locations (and
// doesn't write). Via additional flags it can be selected whether...
// - [ignore_methods_with_assumenosideeffects] to ignore invoked methods that
//   are marked with assumenosideeffects
// - [for_conditional_purity] instructions that rule out conditional purity
//   should cause methods to be treated like methods with unknown behavior; in
//   particular, this rules out instructions that create new object instances,
//   as those may leak, and thus multiple invocations of such a method could
//   never be reduced by CSE.
// - [compute_locations] the actual locations that are being read are computed
//   and returned; if false, then an empty set indicates that a particular
//   function only reads (some unknown set of) locations.
static size_t analyze_read_locations(
    const Scope& scope,
    const method_override_graph::Graph* method_override_graph,
    const method::ClInitHasNoSideEffectsPredicate& clinit_has_no_side_effects,
    const UnorderedSet<DexMethodRef*>& pure_methods,
    bool ignore_methods_with_assumenosideeffects,
    bool for_conditional_purity,
    bool compute_locations,
    UnorderedMap<const DexMethod*, CseUnorderedLocationSet>* result) {
  UnorderedSet<const DexMethod*> pure_methods_closure;
  {
    Timer t{"Pure methods closure"};
    for (auto* pure_method_ref : UnorderedIterable(pure_methods)) {
      auto* pure_method = pure_method_ref->as_def();
      if (pure_method == nullptr) {
        continue;
      }
      pure_methods_closure.insert(pure_method);
      if (pure_method->is_virtual() && (method_override_graph != nullptr)) {
        const auto overriding_methods =
            method_override_graph::get_overriding_methods(
                *method_override_graph, pure_method);
        insert_unordered_iterable(pure_methods_closure, overriding_methods);
      }
    }
  }

  return compute_locations_closure_impl(
      scope, method_override_graph,
      [&](DexMethod* method) -> std::optional<LocationsAndDependencies> {
        auto action = get_base_or_overriding_method_action_impl(
            method, &pure_methods_closure,
            ignore_methods_with_assumenosideeffects);

        if (action == MethodOverrideAction::UNKNOWN) {
          return std::nullopt;
        }

        LocationsAndDependencies lads;
        if (!process_base_and_overriding_methods_impl(
                method_override_graph, method, &pure_methods_closure,
                ignore_methods_with_assumenosideeffects,
                [&](DexMethod* other_method) {
                  if (other_method != method) {
                    lads.dependencies.insert(other_method);
                  }
                  return true;
                })) {
          return std::nullopt;
        }

        if (action == MethodOverrideAction::EXCLUDE) {
          return lads;
        }

        bool unknown = false;
        cfg_adapter::iterate_with_iterator(
            method->get_code(), [&](const IRList::iterator& it) {
              auto* insn = it->insn;
              auto opcode = insn->opcode();
              switch (opcode) {
              case OPCODE_MONITOR_ENTER:
              case OPCODE_MONITOR_EXIT:
              case OPCODE_FILL_ARRAY_DATA:
              case OPCODE_THROW:
              case IOPCODE_INIT_CLASS:
              case IOPCODE_WRITE_BARRIER:
                unknown = true;
                break;
              case OPCODE_NEW_INSTANCE:
                if (for_conditional_purity ||
                    !clinit_has_no_side_effects(insn->get_type())) {
                  unknown = true;
                }
                break;
              case OPCODE_NEW_ARRAY:
              case OPCODE_FILLED_NEW_ARRAY:
                if (for_conditional_purity) {
                  unknown = true;
                }
                break;
              case OPCODE_INVOKE_SUPER:
                // TODO: Support properly.
                unknown = true;
                break;
              default:
                if (opcode::is_an_aput(opcode) || opcode::is_an_iput(opcode) ||
                    opcode::is_an_sput(opcode)) {
                  unknown = true;
                } else if (opcode::is_an_aget(opcode) ||
                           opcode::is_an_iget(opcode) ||
                           opcode::is_an_sget(opcode)) {
                  auto location = get_read_location(insn);
                  if (location ==
                      CseLocation(
                          CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
                    unknown = true;
                  } else {
                    if (opcode::is_an_sget(opcode) &&
                        (!clinit_has_no_side_effects(
                            location.get_field()->get_class()))) {
                      unknown = true;
                    } else if (compute_locations) {
                      lads.locations.insert(location);
                    }
                  }
                } else if (opcode::is_a_method_invoke(opcode)) {
                  auto* invoke_method = resolve_method_deprecated(
                      insn->get_method(), opcode_to_search(opcode), method);
                  if (((invoke_method != nullptr) &&
                       opcode::is_invoke_static(opcode) &&
                       (!clinit_has_no_side_effects(
                           invoke_method->get_class()))) ||
                      !process_base_and_overriding_methods_impl(
                          method_override_graph, invoke_method,
                          &pure_methods_closure,
                          ignore_methods_with_assumenosideeffects,
                          [&](DexMethod* other_method) {
                            if (other_method != method) {
                              lads.dependencies.insert(other_method);
                            }
                            return true;
                          })) {
                    unknown = true;
                  }
                }
                break;
              }

              return unknown ? cfg_adapter::LOOP_BREAK
                             : cfg_adapter::LOOP_CONTINUE;
            });

        if (unknown) {
          return std::nullopt;
        }

        return lads;
      },
      result);
}

size_t compute_conditionally_pure_methods(
    const Scope& scope,
    const method_override_graph::Graph* method_override_graph,
    const method::ClInitHasNoSideEffectsPredicate& clinit_has_no_side_effects,
    const UnorderedSet<DexMethodRef*>& pure_methods,
    UnorderedMap<const DexMethod*, CseUnorderedLocationSet>* result) {
  Timer t("compute_conditionally_pure_methods");
  auto iterations = analyze_read_locations(
      scope, method_override_graph, clinit_has_no_side_effects, pure_methods,
      /* ignore_methods_with_assumenosideeffects */ false,
      /* for_conditional_purity */ true,
      /* compute_locations */ true, result);
  for (auto& p : UnorderedIterable(*result)) {
    TRACE(CSE, 4, "[CSE] conditionally pure method %s: %s", SHOW(p.first),
          SHOW(&p.second));
  }
  return iterations;
}

size_t compute_no_side_effects_methods(
    const Scope& scope,
    const method_override_graph::Graph* method_override_graph,
    const method::ClInitHasNoSideEffectsPredicate& clinit_has_no_side_effects,
    const UnorderedSet<DexMethodRef*>& pure_methods,
    UnorderedSet<const DexMethod*>* result) {
  Timer t("compute_no_side_effects_methods");
  UnorderedMap<const DexMethod*, CseUnorderedLocationSet> method_locations;
  auto iterations = analyze_read_locations(
      scope, method_override_graph, clinit_has_no_side_effects, pure_methods,
      /* ignore_methods_with_assumenosideeffects */ true,
      /* for_conditional_purity */ false,
      /* compute_locations */ false, &method_locations);
  for (auto& p : UnorderedIterable(method_locations)) {
    TRACE(CSE, 4, "[CSE] no side effects method %s", SHOW(p.first));
    result->insert(p.first);
  }
  return iterations;
}

bool has_implementor(const method_override_graph::Graph* method_override_graph,
                     const DexMethod* method) {
  // For methods of an annotation interface, a synthetic trivial implementation
  // is generated by the runtime.
  if (is_annotation(type_class(method->get_class()))) {
    return true;
  }
  bool found_implementor = false;
  auto res = process_base_and_overriding_methods_impl(
      method_override_graph, method, /* methods_to_ignore */ nullptr,
      /* ignore_methods_with_assumenosideeffects */ false, [&](DexMethod*) {
        found_implementor = true;
        return true;
      });
  return !res || found_implementor;
}
