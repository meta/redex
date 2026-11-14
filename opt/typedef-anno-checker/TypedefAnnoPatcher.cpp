/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypedefAnnoPatcher.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace typedef_anno {
bool is_int(const type_inference::TypeEnvironment& env, reg_t reg) {
  return env.get_dex_type(reg) != std::nullopt &&
         type::is_int(*env.get_dex_type(reg));
}

// if there's no dex type, the value is null, and the checker does not enforce
// nullability
bool is_string(const type_inference::TypeEnvironment& env, reg_t reg) {
  return env.get_dex_type(reg) != std::nullopt
             ? *env.get_dex_type(reg) == type::java_lang_String()
             : true;
}

bool is_not_str_nor_int(const type_inference::TypeEnvironment& env, reg_t reg) {
  return !is_string(env, reg) && !is_int(env, reg);
}

bool has_typedef_annos(const ParamAnnotations* param_annos,
                       const UnorderedSet<const DexType*>& typedef_annos) {
  if (param_annos == nullptr) {
    return false;
  }
  for (const auto& anno : *param_annos) {
    const auto& anno_set = anno.second;
    auto typedef_anno = type_inference::get_typedef_annotation(
        anno_set->get_annotations(), typedef_annos);
    if (typedef_anno != std::nullopt) {
      return true;
    }
  }
  return false;
}

} // namespace typedef_anno

namespace {

DexMethod* resolve_method(DexMethod* caller, IRInstruction* insn) {
  auto* def_method = resolve_method_deprecated(insn->get_method(),
                                               opcode_to_search(insn), caller);
  if (def_method == nullptr && insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
    def_method = resolve_method_deprecated(insn->get_method(),
                                           MethodSearch::InterfaceVirtual);
  }
  return def_method;
}

// Type inference attaches a typedef annotation only to a typedef param, a read
// of a typedef field or the result of a call to a typedef-annotated method, and
// every candidate needs one of those or a write to a typedef field. A method
// with none of them cannot yield a candidate, so it is not analyzed.
bool may_have_candidates(
    DexMethod* m, const UnorderedSet<const TypedefAnnoType*>& typedef_annos) {
  if (m->get_code() == nullptr) {
    return false;
  }
  if (typedef_anno::has_typedef_annos(m->get_param_anno(), typedef_annos)) {
    return true;
  }
  auto is_typedef_method = [&](const DexMethod* method) {
    return method != nullptr && (type_inference::get_typedef_anno_from_member(
                                     method, typedef_annos) ||
                                 typedef_anno::has_typedef_annos(
                                     method->get_param_anno(), typedef_annos));
  };
  for (const auto& mie : cfg::InstructionIterable(m->get_code()->cfg())) {
    auto* insn = mie.insn;
    if (insn->has_field()) {
      if (type_inference::get_typedef_anno_from_member(insn->get_field(),
                                                       typedef_annos)) {
        return true;
      }
    } else if (insn->has_method()) {
      auto* callee = insn->get_method();
      if ((callee->is_def() && is_typedef_method(callee->as_def())) ||
          is_typedef_method(resolve_method(m, insn))) {
        return true;
      }
    }
  }
  return false;
}

/**
 * Helper class that encapsulates type inference and use-def/def-use chain
 * creation for a method. Provides lazy initialization of chains to avoid
 * unnecessary computation when they're not needed.
 */
class MethodAnalysis {
 public:
  /**
   * Factory method that creates a MethodAnalysis if the method has code and
   * a built CFG. Returns nullptr otherwise.
   */
  static std::unique_ptr<MethodAnalysis> create(
      DexMethod* m,
      const UnorderedSet<const TypedefAnnoType*>& typedef_annos,
      const method_override_graph::Graph& method_override_graph) {
    IRCode* code = m->get_code();
    if (code == nullptr) {
      return nullptr;
    }
    always_assert_log(code->cfg_built(), "%s has no cfg built", SHOW(m));
    return std::unique_ptr<MethodAnalysis>(new MethodAnalysis(
        code->cfg(), m, typedef_annos, method_override_graph));
  }

  cfg::ControlFlowGraph& cfg() { return m_cfg; }
  TypeEnvironments& envs() { return m_inference.get_type_environments(); }
  type_inference::TypeInference& inference() { return m_inference; }

  live_range::UseDefChains& use_def_chains() {
    ensure_chains();
    return *m_ud_chains;
  }

 private:
  MethodAnalysis(cfg::ControlFlowGraph& cfg,
                 DexMethod* m,
                 const UnorderedSet<const TypedefAnnoType*>& typedef_annos,
                 const method_override_graph::Graph& method_override_graph)
      : m_cfg(cfg),
        m_inference(cfg, false, typedef_annos, &method_override_graph) {
    m_inference.run(m);
  }

  void ensure_chains() {
    if (!m_chains.has_value()) {
      m_chains.emplace(m_cfg);
      m_ud_chains.emplace(m_chains->get_use_def_chains());
    }
  }

  cfg::ControlFlowGraph& m_cfg;
  type_inference::TypeInference m_inference;
  std::optional<live_range::MoveAwareChains> m_chains;
  std::optional<live_range::UseDefChains> m_ud_chains;
};

// make the methods and fields temporarily synthetic to add annotations
template <typename DexMember>
bool add_annotation_set_impl(DexMember* member,
                             DexAnnotationSet* anno_set,
                             Stats& class_stats) {
  if (member && member->is_def()) {
    auto* def_member = member->as_def();
    auto existing_annos = def_member->get_anno_set();
    if (existing_annos) {
      size_t anno_size = existing_annos->get_annotations().size();
      existing_annos->combine_with(*anno_set);
      if (existing_annos->get_annotations().size() != anno_size) {
        class_stats.num_patched_fields_and_methods += 1;
        TRACE(TAC, 3, "[patcher] patched member %s w/ %s", SHOW(member),
              SHOW(anno_set));
      }
    } else {
      DexAccessFlags access = def_member->get_access();
      def_member->set_access(ACC_SYNTHETIC);
      auto res = def_member->attach_annotation_set(
          std::make_unique<DexAnnotationSet>(*anno_set));
      always_assert(res);
      def_member->set_access(access);
      class_stats.num_patched_fields_and_methods += 1;
      TRACE(TAC, 3, "[patcher] patched member %s w/ %s", SHOW(member),
            SHOW(anno_set));
    }
    return true;
  }
  return false;
}

template <typename DexMember>
bool add_annotation_impl(DexMember* member,
                         const TypedefAnnoType* anno,
                         Stats& class_stats) {
  DexAnnotationSet anno_set = DexAnnotationSet();
  anno_set.add_annotation(std::make_unique<DexAnnotation>(
      const_cast<TypedefAnnoType*>(anno), DAV_RUNTIME));
  return add_annotation_set_impl(member, &anno_set, class_stats);
}

bool add_param_annotation_set(DexMethod* m,
                              DexAnnotationSet* anno_set,
                              size_t param,
                              Stats& class_stats) {
  bool added = false;
  int param_idx = static_cast<int>(param);
  if (m->get_param_anno() != nullptr) {
    if (m->get_param_anno()->count(param_idx) == 1) {
      std::unique_ptr<DexAnnotationSet>& param_anno_set =
          m->get_param_anno()->at(param_idx);
      if (param_anno_set != nullptr) {
        size_t anno_size = param_anno_set->get_annotations().size();
        param_anno_set->combine_with(*anno_set);
        if (param_anno_set->get_annotations().size() != anno_size) {
          class_stats.num_patched_parameters += 1;
          added = true;
        }
        return added;
      }
    }
  }
  DexAccessFlags access = m->get_access();
  m->set_access(ACC_SYNTHETIC);
  m->attach_param_annotation_set(param_idx,
                                 std::make_unique<DexAnnotationSet>(*anno_set));
  m->set_access(access);
  return true;
}

bool add_param_annotation(DexMethod* m,
                          const TypedefAnnoType* anno,
                          size_t param,
                          Stats& class_stats) {
  DexAnnotationSet anno_set = DexAnnotationSet();
  anno_set.add_annotation(std::make_unique<DexAnnotation>(
      const_cast<TypedefAnnoType*>(anno), DAV_RUNTIME));
  return add_param_annotation_set(m, &anno_set, param, class_stats);
}

// Run usedefs to see if the source of the annotated value is a parameter
// If it is, add the param to the patching candidates.
void find_patchable_parameters(DexMethod* m,
                               IRInstruction* insn,
                               src_index_t arg_index,
                               const TypedefAnnoType* typedef_anno,
                               live_range::UseDefChains* ud_chains,
                               PatchingCandidates& param_candidates) {
  // Patch missing parameter annotations from accessed fields
  live_range::Use use_of_id{insn, arg_index};
  auto udchains_it = ud_chains->find(use_of_id);
  auto defs_set = udchains_it->second;

  for (auto* def : defs_set) {
    if (!opcode::is_a_load_param(def->opcode())) {
      continue;
    }
    auto param_index = 0;
    for (const auto& mie :
         InstructionIterable(m->get_code()->cfg().get_param_instructions())) {
      if (mie.insn == def) {
        if (!is_static(m)) {
          param_index -= 1;
        }
        param_candidates.add_param_candidate(m, typedef_anno, param_index);
        return;
      }
      param_index += 1;
    }
  }
}

void patch_param_from_method_invoke(TypeEnvironments& envs,
                                    type_inference::TypeInference& inference,
                                    DexMethod* caller,
                                    IRInstruction* invoke,
                                    live_range::UseDefChains* ud_chains,
                                    PatchingCandidates& candidates) {
  always_assert(opcode::is_an_invoke(invoke->opcode()));
  auto* def_method = resolve_method(caller, invoke);
  if ((def_method == nullptr) || ((def_method->get_param_anno() == nullptr) &&
                                  (def_method->get_anno_set() == nullptr))) {
    // callee cannot be resolved, has no param annotation, or has no return
    // annotation
    return;
  }

  auto& invoke_env = envs.find(invoke)->second;
  if (def_method->get_param_anno() == nullptr) {
    return;
  }
  for (auto const& param_anno : *def_method->get_param_anno()) {
    auto param_typedef_anno = type_inference::get_typedef_annotation(
        param_anno.second->get_annotations(), inference.get_annotations());
    if (!param_typedef_anno) {
      continue;
    }
    int arg_index = invoke->opcode() == OPCODE_INVOKE_STATIC
                        ? param_anno.first
                        : param_anno.first + 1;
    reg_t arg_reg = invoke->src(arg_index);
    auto arg_anno = invoke_env.get_annotation(arg_reg);
    if (arg_anno && arg_anno == param_typedef_anno) {
      // Safe assignment. Nothing to do.
      continue;
    }
    find_patchable_parameters(caller, invoke, arg_index, *param_typedef_anno,
                              ud_chains, candidates);
    TRACE(TAC, 2, "Missing param annotation %s in %s", SHOW(param_anno.second),
          SHOW(caller));
  }
}

/*
 * Collect missing param Typedef annotation if the current method writes to an
 * annotated field thru a value passed from param.
 */
void collect_setter_missing_param_annos(
    type_inference::TypeInference& inference,
    DexMethod* setter,
    IRInstruction* insn,
    live_range::UseDefChains* ud_chains,
    PatchingCandidates& candidates) {
  always_assert(opcode::is_an_iput(insn->opcode()) ||
                opcode::is_an_sput(insn->opcode()));
  auto* field_ref = insn->get_field();
  auto field_anno = type_inference::get_typedef_anno_from_member(
      field_ref, inference.get_annotations());
  if (!field_anno) {
    return;
  }

  find_patchable_parameters(setter, insn, 0, *field_anno, ud_chains,
                            candidates);
}

void collect_param_candidates_impl(DexMethod* m,
                                   PatchingCandidates& candidates,
                                   MethodAnalysis& analysis) {
  auto& envs = analysis.envs();
  auto& ud_chains = analysis.use_def_chains();

  for (cfg::Block* b : analysis.cfg().blocks()) {
    for (auto& mie : InstructionIterable(b)) {
      auto* insn = mie.insn;
      IROpcode opcode = insn->opcode();
      if (opcode::is_an_invoke(opcode)) {
        patch_param_from_method_invoke(envs, analysis.inference(), m, insn,
                                       &ud_chains, candidates);
      } else if (opcode::is_an_iput(opcode) || opcode::is_an_sput(opcode)) {
        collect_setter_missing_param_annos(analysis.inference(), m, insn,
                                           &ud_chains, candidates);
      }
    }
  }
}

// Core logic of collect_return_candidates.
void collect_return_candidates_impl(DexMethod* m,
                                    PatchingCandidates& candidates,
                                    MethodAnalysis& analysis) {
  auto& envs = analysis.envs();
  std::optional<const TypedefAnnoType*> anno = std::nullopt;
  bool patch_return = true;
  for (cfg::Block* b : analysis.cfg().blocks()) {
    for (auto& mie : InstructionIterable(b)) {
      auto* insn = mie.insn;
      IROpcode opcode = insn->opcode();
      if ((opcode == OPCODE_RETURN_OBJECT || opcode == OPCODE_RETURN)) {
        auto return_anno = envs.at(insn).get_annotation(insn->src(0));
        if (return_anno == std::nullopt ||
            (anno != std::nullopt && return_anno != anno)) {
          patch_return = false;
        } else {
          anno = return_anno;
        }
      }
    }
  }

  if (patch_return && anno != std::nullopt) {
    candidates.add_method_candidate(m, *anno);
  }
}

} // namespace

void PatchingCandidates::apply_patching(Stats& class_stats) {
  for (auto* field :
       unordered_to_ordered_keys(m_field_candidates, compare_dexfields)) {
    const auto* anno = m_field_candidates.at(field);
    add_annotation_impl(field, anno, class_stats);
  }
  for (auto* method :
       unordered_to_ordered_keys(m_method_candidates, compare_dexmethods)) {
    const auto* anno = m_method_candidates.at(method);
    add_annotation_impl(method, anno, class_stats);
  }
  for (auto& pc :
       unordered_to_ordered_keys(m_param_candidates, compare_param_candidate)) {
    const auto* anno = m_param_candidates.at(pc);
    add_param_annotation(pc.method, anno, pc.index, class_stats);
  }
}

// Kotlin enum constructors have two synthetic parameters prepended by the
// compiler: (String name, int ordinal). User-defined parameters start at
// index 2. This function propagates typedef annotations from the logical
// user-param position to the actual bytecode position (offset by 2).
//
// Example:
//   Source:   enum class MyEnum(@TypedefAnno val value: Int)
//   Bytecode: <init>(String name, int ordinal, int value)
//                    ^0           ^1           ^2
//
// The annotation found at logical index 0 needs to be copied to bytecode
// index 2.
void TypedefAnnoPatcher::fix_kt_enum_ctor_param(const DexClass* cls,
                                                Stats& class_stats) {
  // Kotlin enum constructors prepend (String name, int ordinal) before
  // user-defined parameters.
  constexpr size_t kKotlinEnumSyntheticParamCount = 2;

  for (auto* ctor : cls->get_ctors()) {
    if (is_synthetic(ctor)) {
      continue;
    }

    auto* param_annos = ctor->get_param_anno();
    if (param_annos == nullptr) {
      continue;
    }

    const DexTypeList* args = ctor->get_proto()->get_args();
    for (const auto& [param_idx, anno_set] : *param_annos) {
      auto annotation = type_inference::get_typedef_annotation(
          anno_set->get_annotations(), m_typedef_annos);
      if (annotation == std::nullopt) {
        continue;
      }

      // Offset by synthetic param count to get the actual bytecode position.
      size_t patch_idx = param_idx + kKotlinEnumSyntheticParamCount;
      if (patch_idx >= args->size()) {
        continue;
      }

      // Only patch parameters that are valid typedef targets (int or String).
      const DexType* param_type = args->at(patch_idx);
      if (!type::is_int(param_type) && param_type != type::java_lang_String()) {
        continue;
      }

      if (add_param_annotation(ctor, *annotation, patch_idx, class_stats)) {
        TRACE(TAC, 2,
              "[patcher] Fixed Kotlin enum ctor param w/ %s at %zu on %s",
              SHOW(anno_set), patch_idx, SHOW(ctor));
      }
    }
  }
}

// If a method overrides an interface/base method that has typedef annotations,
// propagate those annotations to the overriding method. This covers SAM
// conversions, Kotlin delegation on named classes, and any other case where
// the implementation method lacks annotations that the interface declares.
void TypedefAnnoPatcher::collect_overriding_method_candidates(
    DexMethod* m, PatchingCandidates& candidates) {
  auto overriddens = mog::get_overridden_methods(m_method_override_graph, m,
                                                 true /*include_interfaces*/);
  if (overriddens.empty()) {
    return;
  }

  // An override inherits a return typedef only when every overridden method
  // that declares one agrees.
  if (type_inference::get_typedef_anno_from_member(m, m_typedef_annos) ==
      std::nullopt) {
    UnorderedSet<const TypedefAnnoType*> inherited_returns;
    for (const auto* overridden : UnorderedIterable(overriddens)) {
      if (auto return_anno = type_inference::get_typedef_anno_from_member(
              overridden, m_typedef_annos)) {
        inherited_returns.insert(*return_anno);
      }
    }
    if (inherited_returns.size() == 1) {
      candidates.add_method_candidate(m, *unordered_any(inherited_returns));
    }
  }

  for (const auto* overridden : UnorderedIterable(overriddens)) {
    // Collect parameter annotation candidates.
    if (overridden->get_param_anno() == nullptr) {
      continue;
    }
    for (const auto& [param_idx, anno_set] : *overridden->get_param_anno()) {
      auto annotation = type_inference::get_typedef_annotation(
          anno_set->get_annotations(), m_typedef_annos);
      if (annotation == std::nullopt) {
        continue;
      }
      // Skip if this param already has a typedef annotation.
      if (m->get_param_anno() != nullptr &&
          m->get_param_anno()->count(param_idx) == 1) {
        auto existing = type_inference::get_typedef_annotation(
            m->get_param_anno()->at(param_idx)->get_annotations(),
            m_typedef_annos);
        if (existing != std::nullopt) {
          continue;
        }
      }
      candidates.add_param_candidate(m, *annotation, param_idx);
    }
  }
}

void TypedefAnnoPatcher::run(const Scope& scope) {
  PatchingCandidates candidates;
  const auto phase_one = [this, &scope, &candidates]() {
    m_patcher_stats += walk::parallel::classes<Stats>(
        scope, [this, &candidates](DexClass* cls) {
          // All the updates happening in this walk is local to the current
          // class. Therefore, there's no race condition between individual
          // annotation patching.
          Stats class_stats;
          if (is_enum(cls) && type::is_kotlin_class(cls)) {
            fix_kt_enum_ctor_param(cls, class_stats);
          }
          for (auto* m : cls->get_all_methods()) {
            auto analysis =
                may_have_candidates(m, m_typedef_annos)
                    ? MethodAnalysis::create(m, m_typedef_annos,
                                             m_method_override_graph)
                    : nullptr;
            if (analysis) {
              collect_param_candidates_impl(m, candidates, *analysis);
              collect_return_candidates_impl(m, candidates, *analysis);
            }
            collect_overriding_method_candidates(m, candidates);
            if (is_constructor(m) &&
                typedef_anno::has_typedef_annos(m->get_param_anno(),
                                                m_typedef_annos)) {
              patch_synth_cls_fields_from_ctor_param(m, class_stats);
            }
          }
          return class_stats;
        });

    size_t candidates_size = candidates.candidates_size();
    if (candidates_size == 0) {
      // Nothing to patch.
      TRACE(TAC, 2, "[patcher] Nothing to patch");
      return false;
    }
    Stats new_stats = {};
    candidates.apply_patching(new_stats);
    TRACE(TAC, 2,
          "[patcher] Phase 1: Patches %zu candidates; patched params %zu; "
          "patched field/methods %zu",
          candidates_size, new_stats.num_patched_parameters,
          new_stats.num_patched_fields_and_methods);
    candidates = {};
    if (new_stats.not_zero()) {
      m_patcher_stats += new_stats;
      return true;
    }

    // All candidates are patched. Nothing to do.
    return false;
  };

  // Fix point iteration on phase one.
  for (size_t i = 0;; i++) {
    if (!phase_one()) {
      break;
    }
    if (i >= m_max_iteration) {
      always_assert_log(
          false, "[patcher] Too many iterations to stabilize. Giving up.");
    }
  }
}

// Propagates typedef annotations from constructor parameters to class fields.
// In Kotlin synthetic classes, annotations on properties are only applied to
// ctor parameters at bytecode level. This patches the backing field so that
// the fixed-point loop can discover getter/setter annotations in subsequent
// iterations via collect_return/param_candidates_impl.
void TypedefAnnoPatcher::patch_synth_cls_fields_from_ctor_param(
    DexMethod* ctor, Stats& class_stats) {
  auto analysis =
      MethodAnalysis::create(ctor, m_typedef_annos, m_method_override_graph);
  if (!analysis) {
    return;
  }

  auto& envs = analysis->envs();

  for (cfg::Block* b : analysis->cfg().blocks()) {
    for (auto& mie : InstructionIterable(b)) {
      auto* insn = mie.insn;

      if (insn->opcode() != OPCODE_IPUT &&
          insn->opcode() != OPCODE_IPUT_OBJECT) {
        continue;
      }

      DexField* field = insn->get_field()->as_def();
      if (field == nullptr) {
        continue;
      }

      auto& env = envs.at(insn);
      reg_t src_reg = insn->src(0);
      if (!typedef_anno::is_int(env, src_reg) &&
          !typedef_anno::is_string(env, src_reg)) {
        continue;
      }

      auto annotation = env.get_annotation(src_reg);
      if (annotation == std::nullopt) {
        continue;
      }

      add_annotation_impl(field, *annotation, class_stats);
    }
  }
}

void TypedefAnnoPatcher::print_stats(PassManager& mgr) {
  mgr.set_metric("total_member_patched",
                 m_patcher_stats.num_patched_fields_and_methods);
  mgr.set_metric("total_param_patched", m_patcher_stats.num_patched_parameters);
  TRACE(TAC, 1, "[patcher] total_member_patched %zu",
        m_patcher_stats.num_patched_fields_and_methods);
  TRACE(TAC, 1, "[patcher] total_param_patched %zu",
        m_patcher_stats.num_patched_parameters);
}
