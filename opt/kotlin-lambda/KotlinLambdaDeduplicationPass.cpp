/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "KotlinLambdaDeduplicationPass.h"

#include <algorithm>
#include <limits>
#include <ranges>
#include <unordered_set>

#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexMemberRefs.h"
#include "DexUtil.h"
#include "KotlinLambdaAnalyzer.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeReference.h"
#include "TypeUtil.h"
#include "UniqueMethodTracker.h"
#include "Walkers.h"

namespace {

// Get the INSTANCE field from a lambda class.
DexField* get_singleton_field(DexClass* cls, const DexString* instance_name) {
  const auto& sfields = cls->get_sfields();
  auto it =
      std::ranges::find_if(sfields, [cls, instance_name](DexField* field) {
        return field->get_name() == instance_name &&
               field->get_type() == cls->get_type();
      });
  return it != sfields.end() ? *it : nullptr;
}

// Get the no-arg constructor of a lambda class. Returns nullptr if there's not
// exactly one constructor, or if the constructor has parameters (capturing
// lambda).
// TODO(T251573078): Support capturing lambdas with matching constructor
// signatures.
DexMethod* get_no_arg_constructor(DexClass* cls) {
  const auto& dmethods = cls->get_dmethods();
  auto it = std::ranges::find_if(dmethods, method::is_init);
  if (it == dmethods.end()) {
    return nullptr;
  }
  DexMethod* ctor = *it;
  // Ensure there's only one constructor.
  if (std::ranges::any_of(it + 1, dmethods.end(), method::is_init)) {
    return nullptr;
  }
  // Check that the constructor has no parameters (non-capturing lambda).
  if (!ctor->get_proto()->get_args()->empty()) {
    return nullptr;
  }
  return ctor;
}

// Collect lambda types from a tracker's duplicate groups.
void collect_lambda_types_from_tracker(
    const UniqueMethodTracker& tracker,
    size_t min_duplicate_group_size,
    std::unordered_set<const DexType*>& lambda_types) {
  for (const auto& [key, methods] : UnorderedIterable(tracker.groups())) {
    if (methods.size() >= min_duplicate_group_size) {
      for (const auto* method : UnorderedIterable(methods)) {
        lambda_types.insert(method->get_class());
      }
    }
  }
}

// Build a map from lambda class types to their dex indices.
// Lower index means earlier dex file (e.g., classes.dex < classes2.dex).
// We pick the canonical lambda from the lowest-indexed dex because
// higher-indexed dexes can reference lower-indexed ones, but not vice versa.
//
// We don't use XDexRefs here because it builds a map for all classes, whereas
// we only need entries for lambda types in duplicate groups.
std::unordered_map<const DexType*, size_t> build_class_to_dex_idx_map(
    const DexStoresVector& stores,
    const UniqueMethodTracker& singleton_tracker,
    const UniqueMethodTracker& non_singleton_tracker,
    size_t min_duplicate_group_size) {
  // Collect the lambda types we care about from both trackers.
  std::unordered_set<const DexType*> lambda_types;
  collect_lambda_types_from_tracker(singleton_tracker, min_duplicate_group_size,
                                    lambda_types);
  collect_lambda_types_from_tracker(non_singleton_tracker,
                                    min_duplicate_group_size, lambda_types);

  // Find the dex index for each lambda type.
  std::unordered_map<const DexType*, size_t> result;
  size_t global_dex_idx = 0;
  for (const auto& store : stores) {
    for (const auto& dex : store.get_dexen()) {
      for (const auto* cls : dex) {
        if (lambda_types.contains(cls->get_type())) {
          result.emplace(cls->get_type(), global_dex_idx);
        }
      }
      global_dex_idx++;
    }
  }
  return result;
}

// Find the canonical lambda class from a group of methods.
// The canonical is the one in the lowest-indexed dex file.
DexClass* find_canonical_class(
    const UnorderedSet<const DexMethod*>& methods,
    const std::unordered_map<const DexType*, size_t>& class_to_dex_idx) {
  DexClass* canonical = nullptr;
  size_t min_dex_idx = std::numeric_limits<size_t>::max();
  for (const auto* method : UnorderedIterable(methods)) {
    auto* lambda_cls = type_class(method->get_class());
    auto it = class_to_dex_idx.find(lambda_cls->get_type());
    size_t dex_idx = (it != class_to_dex_idx.end())
                         ? it->second
                         : std::numeric_limits<size_t>::max();
    if (dex_idx < min_dex_idx) {
      min_dex_idx = dex_idx;
      canonical = lambda_cls;
    }
  }
  return canonical;
}

// Result of processing singleton duplicate groups.
struct SingletonDeduplicationResult {
  // Map from original INSTANCE field to the canonical's renamed field.
  std::unordered_map<DexFieldRef*, DexFieldRef*> field_redirect_map;
  // Map from non-canonical lambda type to the canonical's type.
  // Used to redirect type references (invoke-virtual, check-cast, etc.).
  UnorderedMap<const DexType*, DexType*> type_redirect_map;
  size_t lambdas_deduplicated = 0;
  size_t duplicate_group_count = 0;
};

// Process singleton duplicate groups. For each group, redirect all usages to
// the canonical lambda's INSTANCE field. We rename the canonical's INSTANCE
// field to prevent KotlinStatelessLambdaSingletonRemovalPass from processing
// it.
SingletonDeduplicationResult process_singleton_duplicates(
    const UniqueMethodTracker& tracker,
    const std::unordered_map<const DexType*, size_t>& class_to_dex_idx,
    size_t min_group_size) {
  SingletonDeduplicationResult result;

  const auto* const instance_name = DexString::make_string("INSTANCE");
  const auto* const deduped_instance_name = DexString::make_string(
      KotlinLambdaDeduplicationPass::kDedupedInstanceName);

  for (const auto& [key, methods] : UnorderedIterable(tracker.groups())) {
    if (methods.size() < min_group_size) {
      continue;
    }
    result.duplicate_group_count++;

    // Find the lambda in the lowest-indexed dex to use as canonical.
    DexClass* canonical = find_canonical_class(methods, class_to_dex_idx);
    always_assert(canonical != nullptr);

    DexField* canonical_instance =
        get_singleton_field(canonical, instance_name);
    always_assert(canonical_instance != nullptr);

    // Rename the canonical's INSTANCE field to prevent
    // KotlinStatelessLambdaSingletonRemovalPass (if ever run after this pass)
    // from processing it.
    DexFieldSpec new_spec{canonical_instance->get_class(),
                          deduped_instance_name,
                          canonical_instance->get_type()};
    canonical_instance->change(new_spec);

    // Map non-canonical lambdas in this group to use the canonical's field.
    // The canonical's field is renamed in place, so no redirect is needed for
    // code that already references it.
    for (const auto* method : UnorderedIterable(methods)) {
      auto* lambda_cls = type_class(method->get_class());
      if (lambda_cls == canonical) {
        continue;
      }
      DexField* instance_field = get_singleton_field(lambda_cls, instance_name);
      always_assert(instance_field != nullptr);
      result.field_redirect_map[instance_field] = canonical_instance;
      result.type_redirect_map[lambda_cls->get_type()] = canonical->get_type();
      result.lambdas_deduplicated++;
    }

    TRACE(KOTLIN_INSTANCE, 2,
          "KotlinLambdaDeduplication: Singleton group with %zu lambdas, "
          "canonical = %s",
          methods.size(), SHOW(canonical));
  }

  return result;
}

// Result of processing non-singleton duplicate groups.
struct NonSingletonDeduplicationResult {
  // Map from original lambda type to the canonical's type.
  UnorderedMap<const DexType*, DexType*> type_redirect_map;
  // Map from original constructor to the canonical's constructor.
  std::unordered_map<DexMethodRef*, DexMethodRef*> ctor_redirect_map;
  size_t lambdas_deduplicated = 0;
  size_t duplicate_group_count = 0;
};

// Process non-singleton duplicate groups. For each group, redirect all usages
// to the canonical lambda's type.
NonSingletonDeduplicationResult process_non_singleton_duplicates(
    const UniqueMethodTracker& tracker,
    const std::unordered_map<const DexType*, size_t>& class_to_dex_idx,
    size_t min_group_size) {
  NonSingletonDeduplicationResult result;

  for (const auto& [key, methods] : UnorderedIterable(tracker.groups())) {
    if (methods.size() < min_group_size) {
      continue;
    }
    result.duplicate_group_count++;

    // Find the lambda in the lowest-indexed dex to use as canonical.
    DexClass* canonical = find_canonical_class(methods, class_to_dex_idx);
    always_assert(canonical != nullptr);

    DexMethod* canonical_ctor = get_no_arg_constructor(canonical);
    always_assert(canonical_ctor != nullptr);

    // Map non-canonical lambdas in this group to use the canonical's type.
    // All lambdas in this group have no-arg constructors (verified during
    // collection), so they all have the same constructor signature.
    for (const auto* method : UnorderedIterable(methods)) {
      auto* lambda_cls = type_class(method->get_class());
      if (lambda_cls == canonical) {
        continue;
      }
      DexMethod* ctor = get_no_arg_constructor(lambda_cls);
      always_assert(ctor != nullptr);

      result.type_redirect_map[lambda_cls->get_type()] = canonical->get_type();
      result.ctor_redirect_map[ctor] = canonical_ctor;
      result.lambdas_deduplicated++;
    }

    TRACE(KOTLIN_INSTANCE, 2,
          "KotlinLambdaDeduplication: Non-singleton group with %zu lambdas, "
          "canonical = %s",
          methods.size(), SHOW(canonical));
  }

  return result;
}

} // namespace

void KotlinLambdaDeduplicationPass::run_pass(DexStoresVector& stores,
                                             ConfigFiles& /* conf */,
                                             PassManager& mgr) {
  Scope scope = build_class_scope(stores);

  // Cache string lookups to avoid repeated hash table lookups.
  const auto* const instance_name = DexString::make_string("INSTANCE");

  // Step 5 redirects the type, field and method operands of instructions. It
  // cannot redirect what method handles, method types and call sites name: a
  // handle's call or field access, its call-site prototype and the code around
  // it would have to change together. Lambdas that those name, in code, static
  // field values or annotations, stay out of deduplication.
  ConcurrentSet<const DexType*> indirectly_named_types;
  auto record_indirectly_named_type = [&](const DexType* type) {
    // A type that is not an array is its own element type; null means an
    // array whose element type does not exist, so no class has it.
    if (const auto* element_type = type::get_element_type_if_array(type)) {
      indirectly_named_types.insert(element_type);
    }
  };
  walk::parallel::opcodes(scope, [&](DexMethod*, IRInstruction* insn) {
    for_each_indirectly_named_type(insn, record_indirectly_named_type);
  });
  walk::parallel::encoded_values(scope, [&](const Gatherable& value) {
    for_each_indirectly_named_type(value, record_indirectly_named_type);
  });

  // Step 1: Collect all lambdas and insert their invoke methods.
  // We track singleton lambdas (with INSTANCE field) and non-singleton lambdas
  // (without INSTANCE field) separately.
  UniqueMethodTracker singleton_tracker;
  UniqueMethodTracker non_singleton_tracker;

  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (!can_rename(cls) || !can_delete(cls) ||
        indirectly_named_types.count(cls->get_type()) != 0u) {
      return;
    }

    auto analyzer = KotlinLambdaAnalyzer::for_class(cls);
    if (!analyzer.has_value()) {
      return;
    }

    DexMethod* invoke = analyzer->get_invoke_method();
    if (invoke == nullptr) {
      return;
    }

    if (get_singleton_field(cls, instance_name) != nullptr) {
      // Singleton lambda with INSTANCE field.
      singleton_tracker.insert(invoke);
    } else {
      // Non-singleton lambda without INSTANCE field.
      // Only track non-capturing lambdas.
      if (analyzer->is_non_capturing()) {
        non_singleton_tracker.insert(invoke);
      }
    }
  });

  // Step 2: Check if any duplicate groups exist.
  size_t singleton_distinct_code = singleton_tracker.size();
  size_t non_singleton_distinct_code = non_singleton_tracker.size();

  auto has_duplicates_in_tracker = [min_duplicate_group_size =
                                        m_min_duplicate_group_size](
                                       const UniqueMethodTracker& tracker) {
    return std::any_of(UnorderedIterable(tracker.groups()).begin(),
                       UnorderedIterable(tracker.groups()).end(),
                       [min_duplicate_group_size](const auto& entry) {
                         return entry.second.size() >= min_duplicate_group_size;
                       });
  };

  bool has_singleton_duplicates = has_duplicates_in_tracker(singleton_tracker);
  bool has_non_singleton_duplicates =
      has_duplicates_in_tracker(non_singleton_tracker);

  if (!has_singleton_duplicates && !has_non_singleton_duplicates) {
    mgr.incr_metric("singleton_distinct_code", singleton_distinct_code);
    mgr.incr_metric("non_singleton_distinct_code", non_singleton_distinct_code);
    mgr.incr_metric("duplicate_groups", 0);
    mgr.incr_metric("lambdas_deduped", 0);
    TRACE(KOTLIN_INSTANCE, 1,
          "KotlinLambdaDeduplication: No duplicate lambdas found.");
    return;
  }

  // Step 3: Build a map from lambda types to their dex indices. We pick the
  // canonical lambda from the lowest-indexed dex (e.g., classes.dex <
  // classes2.dex) because higher-indexed dexes can reference lower-indexed
  // ones but not vice versa.
  const auto class_to_dex_idx = build_class_to_dex_idx_map(
      stores, singleton_tracker, non_singleton_tracker,
      m_min_duplicate_group_size);

  // Step 4: Process duplicate groups.
  auto singleton_result = process_singleton_duplicates(
      singleton_tracker, class_to_dex_idx, m_min_duplicate_group_size);
  auto non_singleton_result = process_non_singleton_duplicates(
      non_singleton_tracker, class_to_dex_idx, m_min_duplicate_group_size);

  // Step 5: Rewrite all usages.
  // - For both singleton and non-singleton lambdas: redirect all type
  //   references (new-instance, check-cast, etc.) and method references
  //   (invoke-virtual, invoke-interface, etc.) on non-canonical lambda types
  //   to the canonical. This is necessary because IntraDexClassMergingPass
  //   runs after this pass and may merge the canonical and non-canonical
  //   lambdas into different shape types. Any unrewritten reference to a
  //   non-canonical type would then point to the wrong shape.
  // - For singleton lambdas: redirect sget on INSTANCE fields.
  // - For non-singleton lambdas: additionally redirect invoke-direct <init>.
  // We count singleton and non-singleton rewrites separately. For non-singleton
  // lambdas, each usage consists of new-instance + invoke-direct, so we only
  // count new-instance rewrites to get the usage count.

  // Build a combined type redirect map covering both singleton and
  // non-singleton non-canonical lambda types.
  auto type_redirect_map = std::move(singleton_result.type_redirect_map);
  insert_unordered_iterable(type_redirect_map,
                            non_singleton_result.type_redirect_map);

  struct RewriteCounts {
    size_t singleton = 0;
    size_t non_singleton = 0;
    RewriteCounts& operator+=(const RewriteCounts& other) {
      singleton += other.singleton;
      non_singleton += other.non_singleton;
      return *this;
    }
  };
  const auto rewrite_counts = walk::parallel::methods<RewriteCounts>(
      scope,
      [&field_redirect_map = std::as_const(singleton_result.field_redirect_map),
       &type_redirect_map = std::as_const(type_redirect_map),
       &ctor_redirect_map = std::as_const(
           non_singleton_result.ctor_redirect_map)](DexMethod* meth) {
        RewriteCounts counts;
        auto* code = meth->get_code();
        if (code == nullptr) {
          return counts;
        }

        // Skip methods belonging to non-canonical lambda classes. Their code
        // is dead after dedup (all usage sites have been redirected), and
        // rewriting self-referencing method calls (e.g., the bridge invoke
        // calling this.invoke()) would create type inconsistencies.
        if (type_redirect_map.count(meth->get_class()) != 0u) {
          return counts;
        }

        always_assert(code->cfg_built());
        auto& cfg = code->cfg();

        for (auto& mie : cfg::InstructionIterable(cfg)) {
          auto* insn = mie.insn;
          auto opcode = insn->opcode();

          // Redirect sget on INSTANCE fields (singleton lambdas).
          if (opcode::is_an_sget(opcode)) {
            auto* field = insn->get_field();
            if (const auto it = field_redirect_map.find(field);
                it != field_redirect_map.end()) {
              insn->set_field(it->second);
              counts.singleton++;
            }
            continue;
          }

          // Redirect type operands: new-instance, check-cast, instance-of,
          // const-class, new-array (non-singleton lambdas). An array of a
          // folded lambda, at any depth, becomes an array of the canonical.
          if (insn->has_type()) {
            const auto* type = insn->get_type();
            if (auto* new_type =
                    type_reference::get_new_type(type, type_redirect_map);
                new_type != type) {
              insn->set_type(new_type);
              if (opcode == OPCODE_NEW_INSTANCE) {
                counts.non_singleton++;
              }
            }
          }

          // Redirect method ref operands.
          if (insn->has_method()) {
            auto* method_ref = insn->get_method();
            // For invoke-direct, first try the constructor redirect map.
            if (opcode == OPCODE_INVOKE_DIRECT) {
              if (const auto it = ctor_redirect_map.find(method_ref);
                  it != ctor_redirect_map.end()) {
                insn->set_method(it->second);
                continue;
              }
            }
            // Redirect by declaring type (covers invoke-virtual,
            // invoke-interface, invoke-direct on private methods, etc.).
            // An array declares no methods, so a reference such as
            // `[LT;.clone()` on the canonical's array type need not exist
            // yet: make it instead of looking it up.
            const auto* declaring_type = method_ref->get_class();
            if (auto* new_declaring_type = type_reference::get_new_type(
                    declaring_type, type_redirect_map);
                new_declaring_type != declaring_type) {
              auto* redirected =
                  type::is_array(new_declaring_type)
                      ? DexMethod::make_method(new_declaring_type,
                                               method_ref->get_name(),
                                               method_ref->get_proto())
                      : DexMethod::get_method(new_declaring_type,
                                              method_ref->get_name(),
                                              method_ref->get_proto());
              always_assert(redirected != nullptr);
              insn->set_method(redirected);
            }
          }
        }
        return counts;
      });

  // Report metrics.
  size_t total_duplicate_groups = singleton_result.duplicate_group_count +
                                  non_singleton_result.duplicate_group_count;
  size_t total_lambdas_deduped = singleton_result.lambdas_deduplicated +
                                 non_singleton_result.lambdas_deduplicated;

  mgr.incr_metric("singleton_distinct_code", singleton_distinct_code);
  mgr.incr_metric("non_singleton_distinct_code", non_singleton_distinct_code);
  mgr.incr_metric("singleton_duplicate_groups",
                  singleton_result.duplicate_group_count);
  mgr.incr_metric("non_singleton_duplicate_groups",
                  non_singleton_result.duplicate_group_count);
  mgr.incr_metric("duplicate_groups", total_duplicate_groups);
  mgr.incr_metric("singleton_lambdas_deduped",
                  singleton_result.lambdas_deduplicated);
  mgr.incr_metric("non_singleton_lambdas_deduped",
                  non_singleton_result.lambdas_deduplicated);
  mgr.incr_metric("lambdas_deduped", total_lambdas_deduped);
  mgr.incr_metric("singleton_usages_rewritten", rewrite_counts.singleton);
  mgr.incr_metric("non_singleton_usages_rewritten",
                  rewrite_counts.non_singleton);

  TRACE(KOTLIN_INSTANCE, 1,
        "KotlinLambdaDeduplication: %zu singleton + %zu non-singleton distinct "
        "signatures",
        singleton_distinct_code, non_singleton_distinct_code);
  TRACE(KOTLIN_INSTANCE, 1,
        "KotlinLambdaDeduplication: %zu duplicate groups (%zu singleton, %zu "
        "non-singleton)",
        total_duplicate_groups, singleton_result.duplicate_group_count,
        non_singleton_result.duplicate_group_count);
  TRACE(KOTLIN_INSTANCE, 1,
        "KotlinLambdaDeduplication: %zu lambdas deduped (%zu singleton, %zu "
        "non-singleton)",
        total_lambdas_deduped, singleton_result.lambdas_deduplicated,
        non_singleton_result.lambdas_deduplicated);
  TRACE(KOTLIN_INSTANCE, 1,
        "KotlinLambdaDeduplication: usages rewritten (%zu singleton, %zu "
        "non-singleton)",
        rewrite_counts.singleton, rewrite_counts.non_singleton);
}

static KotlinLambdaDeduplicationPass s_pass;
