/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <functional>
#include <memory>
#include <stdio.h>
#include <string>

#include "CFGMutation.h"
#include "CheckCastAnalysis.h"
#include "CheckCastTransform.h"
#include "ClassHierarchy.h"
#include "Debug.h"
#include "IRCode.h"
#include "IRList.h"
#include "LocalDce.h"
#include "MethodProfiles.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "SingleImpl.h"
#include "SingleImplDefs.h"
#include "Trace.h"
#include "TypeReference.h"
#include "WorkQueue.h"

namespace {

/**
 * Rewrite all typerefs from the interfaces to the concrete type.
 */
void set_type_refs(const DexType* intf, const SingleImplData& data) {
  for (auto* opcode : data.typerefs) {
    TRACE(INTF, 3, "(TREF) %s", SHOW(opcode));
    redex_assert(opcode->get_type() == intf);
    opcode->set_type(data.cls);
    TRACE(INTF, 3, "(TREF) \t=> %s", SHOW(opcode));
  }
}

/**
 * Get or create a new proto given an original proto and an interface to be
 * substituted by an implementation.
 */
DexProto* get_or_make_proto(const DexType* intf,
                            const DexType* impl,
                            DexProto* proto,
                            bool skip_args = false) {
  const DexType* rtype = proto->get_rtype();
  if (rtype == intf) {
    rtype = impl;
  }
  DexTypeList* new_args = nullptr;
  auto* const args = proto->get_args();
  DexTypeList::ContainerType new_arg_list;
  for (const auto* const arg : *args) {
    new_arg_list.push_back(arg == intf ? impl : arg);
  }
  if (skip_args) {
    new_args = args;
  } else {
    new_args = DexTypeList::make_type_list(std::move(new_arg_list));
  }
  return DexProto::make_proto(rtype, new_args, proto->get_shorty());
}

/**
 * Given a new method and a corresponding existing, set up the new method
 * with everything from the original one.
 */
void setup_method(DexMethod* orig_method, DexMethod* new_method) {
  auto* method_anno = orig_method->get_anno_set();
  if (method_anno != nullptr) {
    auto res = new_method->attach_annotation_set(
        std::make_unique<DexAnnotationSet>(*method_anno));
    always_assert(res);
  }
  const auto& params_anno = orig_method->get_param_anno();
  if (params_anno != nullptr) {
    for (auto const& param_anno : *params_anno) {
      new_method->attach_param_annotation_set(
          param_anno.first,
          std::make_unique<DexAnnotationSet>(*param_anno.second));
    }
  }
  new_method->make_concrete(orig_method->get_access(),
                            orig_method->release_code(),
                            orig_method->is_virtual());
}

/**
 * Takes the annotations from the interface and combines them into the class,
 * excepting EnclosingClass, InnerClass (since that would make little sense to
 * haul over and could lead to surprise class loading attempts for dangling
 * outer class).
 */
void combine_class_annotations(DexClass* cls, DexClass* intf_cls) {
  auto* interface_annos = intf_cls->get_anno_set();
  if (interface_annos == nullptr) {
    return;
  }
  auto* enclosing_cls = DexType::get_type("Ldalvik/annotation/EnclosingClass;");
  auto* inner_cls = DexType::get_type("Ldalvik/annotation/InnerClass;");
  if (enclosing_cls == nullptr || inner_cls == nullptr) {
    // Not expected.
    return;
  }
  DexAnnotationSet filtered;
  for (auto& anno : interface_annos->get_annotations()) {
    if (anno->type() != enclosing_cls && anno->type() != inner_cls) {
      filtered.add_annotation(std::make_unique<DexAnnotation>(anno->clone()));
    }
  }
  cls->combine_annotations_with(&filtered);
}

/**
 * Remove interfaces from classes. We walk the interface chain and move
 * down parent interfaces as needed so the contract of the class stays
 * the same.
 */
void remove_interface(const DexType* intf, const SingleImplData& data) {
  auto* cls = type_class(data.cls);
  TRACE(INTF, 3, "(REMI) %s", SHOW(intf));

  // the interface and all its methods are public, but the impl may not be.
  // We make the impl public given the impl is now a substitute of the
  // interface. Doing the analysis to see all accesses would allow us to
  // determine proper visibility but for now we conservatively flip the impl
  // to public
  set_public(cls);
  // removing interfaces may bring the same parent interface down to the
  // concrete class, so use a set to guarantee uniqueness
  UnorderedSet<const DexType*> new_intfs;
  auto collect_interfaces = [&](DexClass* impl) {
    auto* intfs = impl->get_interfaces();
    for (const auto* type : *intfs) {
      if (intf != type) {
        // make interface public if it was not already. It may happen
        // the parent interface is package protected (a type cannot be
        // private or protected) but the type implementing it is in a
        // different package. Make the interface public then
        auto* type_cls = type_class(type);
        if (type_cls != nullptr) {
          if (!is_public(cls)) {
            set_public(type_cls);
          }
          TRACE(INTF, 4, "(REMI) make PUBLIC - %s", SHOW(type));
        }
        new_intfs.insert(type);
        continue;
      }
    }
  };

  collect_interfaces(cls);
  auto* intf_cls = type_class(intf);
  collect_interfaces(intf_cls);

  auto revisited_intfs = unordered_to_ordered(new_intfs, compare_dextypes);
  cls->set_interfaces(DexTypeList::make_type_list(std::move(revisited_intfs)));
  combine_class_annotations(cls, intf_cls);
  TRACE(INTF, 3, "(REMI)\t=> %s", SHOW(cls));
}

bool must_rewrite_annotations(const SingleImplConfig& config) {
  return config.field_anno || config.intf_anno || config.meth_anno;
}

bool must_set_method_annotations(const SingleImplConfig& config) {
  return config.meth_anno;
}

bool must_set_interface_annotations(const SingleImplConfig& config) {
  return config.intf_anno;
}

/**
 * Update method proto from an old type reference to a new one. Return true if
 * the method is updated, return false if the method proto does not contain the
 * old type reference, crash if the updated method will collide with an existing
 * method.
 */
bool update_method_proto(const DexType* old_type_ref,
                         const DexType* new_type_ref,
                         DexMethodRef* method) {
  auto* proto =
      get_or_make_proto(old_type_ref, new_type_ref, method->get_proto());
  if (proto == method->get_proto()) {
    return false;
  }
  DexMethodSpec spec;
  spec.proto = proto;
  method->change(spec, false /* rename on collision */);
  return true;
}

using CheckCastSet = UnorderedSet<const IRInstruction*>;

struct OptimizationImpl {
  OptimizationImpl(std::unique_ptr<SingleImplAnalysis> analysis,
                   const ClassHierarchy& ch,
                   const api::AndroidSDK& api,
                   method_profiles::MethodProfiles& method_profiles)
      : single_impls(std::move(analysis)),
        ch(ch),
        m_api(api),
        m_method_profiles(method_profiles) {}

  OptimizeStats optimize(Scope& scope, const SingleImplConfig& config);

 private:
  EscapeReason can_optimize(const DexType* intf,
                            const SingleImplData& data,
                            bool rename_on_collision);
  CheckCastSet do_optimize(
      const DexType* intf,
      const SingleImplData& data,
      UnorderedMap<DexMethod*, cfg::CFGMutation>& method_mutations);
  EscapeReason check_field_collision(const SingleImplData& data);
  EscapeReason check_method_collision(const DexType* intf,
                                      const SingleImplData& data);
  void drop_single_impl_collision(const DexType* intf, DexMethod* method);
  void set_field_defs(const SingleImplData& data);
  void set_field_refs(const SingleImplData& data);
  CheckCastSet fix_instructions(
      const DexType* intf,
      const SingleImplData& data,
      UnorderedMap<DexMethod*, cfg::CFGMutation>& method_mutations);
  void set_method_defs(const DexType* intf, const SingleImplData& data);
  void set_method_refs(const DexType* intf, const SingleImplData& data);
  void rewrite_interface_methods(const DexType* intf,
                                 const SingleImplData& data);
  void rewrite_annotations(Scope& scope, const SingleImplConfig& config);
  void rename_possible_collisions(const DexType* intf,
                                  const SingleImplData& data);

  check_casts::impl::Stats post_process(
      const std::vector<DexMethod*>& methods,
      std::vector<IRInstruction*>* removed_instruction);

  std::unique_ptr<SingleImplAnalysis> single_impls;
  // A map from interface method to implementing method. We maintain this global
  // map for rewriting method references in annotation.
  NewMethods m_intf_meth_to_impl_meth;
  // list of optimized types
  UnorderedSet<const DexType*> optimized;
  const ClassHierarchy& ch;
  UnorderedMap<std::string_view, size_t> deobfuscated_name_counters;
  const api::AndroidSDK& m_api;
  method_profiles::MethodProfiles& m_method_profiles;
};

/**
 * Rewrite fields by creating new ones and transferring values from the
 * old fields to the new ones. Remove old field and add the new one
 * to the list of fields.
 */
void OptimizationImpl::set_field_defs(const SingleImplData& data) {
  for (const auto& field : data.fielddefs) {
    redex_assert(!single_impls->is_escaped(field->get_class()));
    auto* f = dynamic_cast<DexField*>(
        DexField::make_field(field->get_class(), field->get_name(), data.cls));
    redex_assert(f != field);
    TRACE(INTF, 3, "(FDEF) %s", SHOW(field));
    f->set_deobfuscated_name(field->get_deobfuscated_name());
    f->rstate = field->rstate;
    auto field_anno = field->release_annotations();
    if (field_anno) {
      auto res = f->attach_annotation_set(std::move(field_anno));
      always_assert(res);
    }
    f->make_concrete(field->get_access(),
                     field->get_static_value() == nullptr
                         ? std::unique_ptr<DexEncodedValue>()
                         : field->get_static_value()->clone());
    auto* cls = type_class(field->get_class());
    cls->remove_field(field);
    cls->add_field(f);
    TRACE(INTF, 3, "(FDEF)\t=> %s", SHOW(f));
  }
}

/**
 * Rewrite all fieldref.
 */
void OptimizationImpl::set_field_refs(const SingleImplData& data) {
  for (const auto& fieldrefs : UnorderedIterable(data.fieldrefs)) {
    auto* const field = fieldrefs.first;
    redex_assert(!single_impls->is_escaped(field->get_class()));
    DexFieldRef* f =
        DexField::make_field(field->get_class(), field->get_name(), data.cls);
    for (auto* const opcode : fieldrefs.second) {
      TRACE(INTF, 3, "(FREF) %s", SHOW(opcode));
      redex_assert(f != opcode->get_field());
      opcode->set_field(f);
      TRACE(INTF, 3, "(FREF) \t=> %s", SHOW(opcode));
    }
  }
}

/**
 * Change all the method definitions by updating specs.
 * We will never get collision here since we renamed potential colliding methods
 * before doing the optimization.
 */
void OptimizationImpl::set_method_defs(const DexType* intf,
                                       const SingleImplData& data) {
  for (auto* method : data.methoddefs) {
    TRACE(INTF, 3, "(MDEF) %s", SHOW(method));
    TRACE(INTF, 5, "(MDEF) Update method: %s", SHOW(method));
    bool res = update_method_proto(intf, data.cls, method);
    always_assert(res);
    TRACE(INTF, 3, "(MDEF)\t=> %s", SHOW(method));
  }
}

template <typename T, typename Fn>
void for_all_methods(const T& methods, Fn fn, bool parallel = true) {
  if (parallel) {
    workqueue_run<const DexMethod*>(fn, methods);
  } else {
    for (auto* m : methods) {
      fn(const_cast<DexMethod*>(m));
    }
  }
}

// When replacing interfaces with classes, type-correct bytecode may
// become incorrect. That is due to the relaxed nature of interface
// assignability: at the bytecode level, any reference can be assigned
// to an interface-typed entity. Actual checks happen at an eventual
// `invoke-interface`.
//
// Example:
//   void foo(ISub i) {}
//   void bar(ISuper i) {
//     foo(i); // Java source needs cast here.
//   }
//
// This method inserts check-casts for each invoke parameter and
// field value. Expectation is that unnecessary insertions (e.g.,
// duplicate check-casts) will be eliminated, for example, in
// `post_process`.
CheckCastSet OptimizationImpl::fix_instructions(
    const DexType* intf,
    const SingleImplData& data,
    UnorderedMap<DexMethod*, cfg::CFGMutation>& method_mutations) {
  if (data.referencing_methods.empty()) {
    return {};
  }
  std::vector<const DexMethod*> methods;
  methods.reserve(data.referencing_methods.size());
  unordered_transform(data.referencing_methods, std::back_inserter(methods),
                      [](auto& p) { return p.first; });
  // The typical number of methods is too small, it is actually significant
  // overhead to spin up pool threads to just let them die.
  constexpr bool PARALLEL = false;

  std::mutex ret_lock;
  CheckCastSet ret;

  for_all_methods(
      methods,
      [&](const DexMethod* caller_const) {
        auto* caller = const_cast<DexMethod*>(caller_const);
        std::vector<reg_t> temps; // Cached temps.
        auto* code = caller->get_code();
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();
        auto& mutation = method_mutations.at(caller);
        for (const auto& insn_it_pair :
             UnorderedIterable(data.referencing_methods.at(caller))) {
          auto insn_it = insn_it_pair.second;
          auto* insn = insn_it_pair.first;
          always_assert(&insn_it.cfg() == &cfg);

          auto temp_it = temps.begin();
          auto add_check_cast = [&](reg_t reg) {
            std::vector<IRInstruction*> new_insns;
            new_insns.reserve(2);
            auto* check_cast = new IRInstruction(OPCODE_CHECK_CAST);
            check_cast->set_src(0, reg);
            check_cast->set_type(data.cls);
            new_insns.push_back(check_cast);

            if (PARALLEL) {
              std::unique_lock<std::mutex> lock(ret_lock);
              ret.insert(check_cast);
            } else {
              ret.insert(check_cast);
            }

            // See if we need a new temp.
            reg_t out;
            if (temp_it == temps.end()) {
              reg_t new_temp = cfg.allocate_temp();
              temps.push_back(new_temp);
              temp_it = temps.end();
              out = new_temp;
            } else {
              out = *temp_it;
              temp_it++;
            }

            auto* pseudo_move_result =
                new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
            pseudo_move_result->set_dest(out);
            new_insns.push_back(pseudo_move_result);
            mutation.insert_before(insn_it, std::move(new_insns));
            return out;
          };

          if (opcode::is_an_invoke(insn->opcode())) {
            // We need check-casts for receiver and parameters, but not
            // return type.

            auto* mref = insn->get_method();

            // Receiver.
            if (mref->get_class() == intf) {
              reg_t new_receiver = add_check_cast(insn->src(0));
              insn->set_src(0, new_receiver);
            }

            // Parameters.
            const auto* arg_list = mref->get_proto()->get_args();
            size_t idx = insn->opcode() == OPCODE_INVOKE_STATIC ? 0 : 1;
            for (const auto* const arg : *arg_list) {
              if (arg != intf) {
                idx++;
                continue;
              }

              reg_t new_param = add_check_cast(insn->src(idx));
              insn->set_src(idx, new_param);
              idx++;
            }
            continue;
          }

          if (opcode::is_an_iput(insn->opcode()) ||
              opcode::is_an_sput(insn->opcode())) {
            // If the field type is the interface, need a check-cast.
            auto* fdef = insn->get_field();
            if (fdef->get_type() == intf) {
              reg_t new_param = add_check_cast(insn->src(0));
              insn->set_src(0, new_param);
            }
            continue;
          }

          // Return.
          if (opcode::is_return_object(insn->opcode())) {
            reg_t casted = add_check_cast(insn->src(0));
            insn->set_src(0, casted);
          }

          // Others do not need fixup.
        }
      },
      PARALLEL);

  return ret;
}

/**
 * Rewrite all method refs.
 */
void OptimizationImpl::set_method_refs(const DexType* intf,
                                       const SingleImplData& data) {
  for (const auto& mrefit : UnorderedIterable(data.methodrefs)) {
    auto* method = mrefit.first;
    TRACE(INTF, 3, "(MREF) update ref %s", SHOW(method));
    // next 2 lines will generate no new proto or method when the ref matches
    // a def, which should be very common.
    // However it does not seem too much of an overkill and more
    // straightforward that any logic that manages that.
    // Both creation of protos or methods is "interned" and so the same
    // method would be returned if there is nothing to change and create.
    // Still we need to change the opcodes where we assert the new method
    // to go in the opcode is in fact different than what was there.
    if (update_method_proto(intf, data.cls, method)) {
      TRACE(INTF, 3, "(MREF)\t=> %s", SHOW(method));
    }
  }
}

/**
 * Move all methods of the interface to the concrete (if not there already)
 * and rewrite all refs that were calling to the interface
 * (invoke-interface* -> invoke-virtual*).
 */
void OptimizationImpl::rewrite_interface_methods(const DexType* intf,
                                                 const SingleImplData& data) {
  auto* intf_cls = type_class(intf);
  auto* impl = type_class(data.cls);
  for (auto* meth : intf_cls->get_vmethods()) {
    // Given an interface method and a class determine whether the method
    // is already defined in the class and use it if so.
    // An interface method can be defined in some base class for "convenience"
    // even though the base class does not implement the interface so we walk
    // the chain looking for the method.
    // NOTICE: if we have interfaces that have methods defined up the chain
    // in some java, android, google or other library we are screwed.
    // We'll not find the method and introduce a possible abstract one that
    // will break things.
    // Hopefully we'll find that out during verification and correct things.

    // get the new method if one was created (interface method with a single
    // impl in signature)
    TRACE(INTF, 3, "(MITF) interface method %s", SHOW(meth));
    auto* new_meth =
        resolve_virtual_deprecated(impl, meth->get_name(), meth->get_proto());
    if (new_meth == nullptr) {
      new_meth = DexMethod::make_method_downcast(
          impl->get_type(), meth->get_name(), meth->get_proto());
      // new_meth may not be new, because RedexContext keeps methods around
      // after they are deleted. clear all pre-existing method state.
      // TODO: this is horrible. After we remove methods, we shouldn't
      // have these zombies lying around.
      new_meth->clear_annotations();
      new_meth->make_non_concrete();
      const auto deoob_impl_name = impl->get_deobfuscated_name_or_empty();
      auto unique = deobfuscated_name_counters[deoob_impl_name]++;
      auto new_deob_name = deoob_impl_name + "." +
                           meth->get_simple_deobfuscated_name() +
                           "$REDEX_SINGLE_IMPL$" + std::to_string(unique) +
                           ":" + show_deobfuscated(meth->get_proto());
      new_meth->set_deobfuscated_name(new_deob_name);
      new_meth->rstate = meth->rstate;
      TRACE(INTF, 5, "(MITF) created impl method %s", SHOW(new_meth));
      setup_method(meth, new_meth);
      m_method_profiles.substitute_stats(new_meth, {meth});
      redex_assert(new_meth->is_virtual());
      impl->add_method(new_meth);
      TRACE(INTF, 3, "(MITF) moved interface method %s", SHOW(new_meth));
    } else {
      TRACE(INTF, 3, "(MITF) found method impl %s", SHOW(new_meth));
    }
    always_assert(!m_intf_meth_to_impl_meth.count(meth));
    m_intf_meth_to_impl_meth[meth] = new_meth;
  }

  // rewrite invoke-interface to invoke-virtual
  for (const auto& mref_it : UnorderedIterable(data.intf_methodrefs)) {
    auto* m = mref_it.first;
    always_assert(m_intf_meth_to_impl_meth.count(m));
    auto* new_m = m_intf_meth_to_impl_meth[m];
    redex_assert(new_m && new_m != m);
    TRACE(INTF, 3, "(MITFOP) %s", SHOW(new_m));
    for (auto* mop : UnorderedIterable(mref_it.second)) {
      TRACE(INTF, 3, "(MITFOP) %s", SHOW(mop));
      mop->set_method(new_m);
      always_assert(mop->opcode() == OPCODE_INVOKE_INTERFACE);
      mop->set_opcode(OPCODE_INVOKE_VIRTUAL);
      SingleImplPass::s_invoke_intf_count++;
      TRACE(INTF, 3, "(MITFOP)\t=>%s", SHOW(mop));
    }
  }
}

/**
 * Rewrite annotations that are referring to update methods or deleted
 * interfaces.
 */
void OptimizationImpl::rewrite_annotations(Scope& scope,
                                           const SingleImplConfig& config) {
  // TODO: this is a hack to fix a problem with enclosing annotations; there are
  // more dalvik annotations that may need fixups if SystemAnnoKillPass is not
  // configured to run afterwards.
  using RewriteFn =
      std::function<void(const DexClass*, DexAnnotation*, DexEncodedValue*)>;
  UnorderedMap<DexType*, RewriteFn> types_to_rewrite;

  auto rewrite_enclosing_method = [&](const DexClass* cls, DexAnnotation* anno,
                                      DexEncodedValue* value) {
    if (value->evtype() == DexEncodedValueTypes::DEVT_METHOD) {
      auto* method_value = dynamic_cast<DexEncodedValueMethod*>(value);
      const auto& meth_it =
          m_intf_meth_to_impl_meth.find(method_value->method());
      if (meth_it == m_intf_meth_to_impl_meth.end()) {
        if (method_value->method()->is_def()) {
          return;
        }
        // All the method definitions with optimized interfaces are updated,
        // this is a pure ref, we are not sure if it's updated properly.
        TRACE(INTF, 2,
              "[SingleImpl]: Found pure methodref %s in annotation of "
              "class %s, this may not be properly supported.\n",
              SHOW(method_value->method()), SHOW(cls));
        return;
      }
      TRACE(INTF, 4, "REWRITE: %s", SHOW(anno));
      method_value->set_method(meth_it->second);
      TRACE(INTF, 4, "TO: %s", SHOW(anno));
    }
  };

  auto rewrite_enclosing_class = [&](const DexClass*, DexAnnotation* anno,
                                     DexEncodedValue* value) {
    if (value->evtype() == DexEncodedValueTypes::DEVT_TYPE) {
      auto* type_value = dynamic_cast<DexEncodedValueType*>(value);
      auto* iface = type_value->type();
      auto search = optimized.find(iface);
      if (search != optimized.end()) {
        auto& intf_data = single_impls->get_single_impl_data(iface);
        TRACE(INTF, 4, "REWRITE: %s", SHOW(anno));
        type_value->set_type(const_cast<DexType*>(intf_data.cls));
        TRACE(INTF, 4, "TO: %s", SHOW(anno));
      }
    }
  };

  auto* enclosing_method =
      DexType::get_type("Ldalvik/annotation/EnclosingMethod;");
  auto* enclosing_class =
      DexType::get_type("Ldalvik/annotation/EnclosingClass;");
  if (must_set_method_annotations(config) && enclosing_method != nullptr) {
    types_to_rewrite.emplace(enclosing_method, rewrite_enclosing_method);
  }
  if (must_set_interface_annotations(config) && enclosing_class != nullptr) {
    types_to_rewrite.emplace(enclosing_class, rewrite_enclosing_class);
  }
  if (types_to_rewrite.empty()) {
    return;
  }

  for (const auto& cls : scope) {
    auto* anno_set = cls->get_anno_set();
    if (anno_set == nullptr) {
      continue;
    }
    for (auto& anno : anno_set->get_annotations()) {
      auto search = types_to_rewrite.find(anno->type());
      if (search == types_to_rewrite.end()) {
        continue;
      }
      auto& rewrite_fn = search->second;
      const auto& elems = anno->anno_elems();
      for (const auto& elem : elems) {
        const auto& value = elem.encoded_value;
        rewrite_fn(cls, anno.get(), value.get());
      }
    }
  }
}

/**
 * Check collisions in field definition.
 */
EscapeReason OptimizationImpl::check_field_collision(
    const SingleImplData& data) {
  for (auto* const field : data.fielddefs) {
    redex_assert(!single_impls->is_escaped(field->get_class()));
    auto* collision =
        resolve_field(field->get_class(), field->get_name(), data.cls);
    if (collision != nullptr) {
      return FIELD_COLLISION;
    }
  }
  return NO_ESCAPE;
}

/**
 * Check collisions in method definition.
 */
EscapeReason OptimizationImpl::check_method_collision(
    const DexType* intf, const SingleImplData& data) {
  for (auto* method : data.methoddefs) {
    auto* proto = get_or_make_proto(intf, data.cls, method->get_proto());
    redex_assert(proto != method->get_proto());
    DexMethodRef* collision =
        DexMethod::get_method(method->get_class(), method->get_name(), proto);
    if (collision == nullptr) {
      collision = find_collision(ch,
                                 method->get_name(),
                                 proto,
                                 type_class(method->get_class()),
                                 method->is_virtual());
    }
    // For bridge method, a collision could exist with the actual implementation
    // method if the interface to be removed is also on the parameter list.
    // Example:
    //   interface Intf { Intf setup(Intf i); }
    //   class Impl {
    //     Impl setup(Intf i) {
    //       return this;
    //     }
    //   }
    //
    // The bridge method on class Impl is Intf setup(Intf).
    // The actual implementation method on class Impl is Impl setup(Intf).
    // The collision only exists if we update the proto for both methods.
    // Alternatively, for the bridge method, we can perform additional collision
    // check by only update the rtype on the proto (Impl is Impl setup(Intf) in
    // the above example) just to be conservative.
    if ((collision == nullptr) && is_bridge(method)) {
      proto = get_or_make_proto(intf, data.cls, method->get_proto(),
                                /* skip_args */ true);
      collision =
          DexMethod::get_method(method->get_class(), method->get_name(), proto);
    }
    if (collision != nullptr) {
      TRACE(INTF, 9, "Found collision %s", SHOW(method));
      TRACE(INTF, 9, "\t to %s", SHOW(collision));
      return SIG_COLLISION;
    }
  }
  return NO_ESCAPE;
}

/**
 * Move all single impl in a single impl method signature to next pass.
 * We make a single optimization per pass over any given single impl so
 * I1, I2 and void I1.m(I2)
 * the first optimization (I1 or I2) moves the other interface to next pass.
 * That is not the case for methods on non optimizable classes, so for
 * I1, I2 and void C.m(I1, I2)
 * then m is changed in a single pass for both I1 and I2.
 */
void OptimizationImpl::drop_single_impl_collision(const DexType* intf,
                                                  DexMethod* method) {
  auto check_type = [&](const DexType* type) {
    if (type != intf && single_impls->is_single_impl(type) &&
        !single_impls->is_escaped(type)) {
      single_impls->escape_interface(type, NEXT_PASS);
      always_assert(!optimized.count(type));
    }
  };

  auto* owner = method->get_class();
  if (!single_impls->is_single_impl(owner)) {
    return;
  }
  check_type(owner);
  auto* proto = method->get_proto();
  check_type(proto->get_rtype());
  auto* args_list = proto->get_args();
  for (const auto* arg : *args_list) {
    check_type(arg);
  }
}

/**
 * A single impl can be optimized if:
 * 1- there is no collision in fields rewrite
 * 2- there is no collision in methods rewrite
 */
EscapeReason OptimizationImpl::can_optimize(const DexType* intf,
                                            const SingleImplData& data,
                                            bool rename_on_collision) {
  auto escape = check_field_collision(data);
  if (escape != EscapeReason::NO_ESCAPE) {
    return escape;
  }
  escape = check_method_collision(intf, data);
  if (escape != EscapeReason::NO_ESCAPE) {
    if (rename_on_collision) {
      rename_possible_collisions(intf, data);
      escape = check_method_collision(intf, data);
    }
    if (escape != EscapeReason::NO_ESCAPE) {
      return escape;
    }
  }
  for (auto* method : data.methoddefs) {
    drop_single_impl_collision(intf, method);
  }
  auto* intf_cls = type_class(intf);
  for (auto* method : intf_cls->get_vmethods()) {
    drop_single_impl_collision(intf, method);
  }
  return NO_ESCAPE;
}

/**
 * Remove any chance for collisions.
 */
void OptimizationImpl::rename_possible_collisions(const DexType* intf,
                                                  const SingleImplData& data) {

  const auto& rename = [](DexMethodRef* meth, const DexString* name) {
    DexMethodSpec spec;
    spec.cls = meth->get_class();
    spec.name = name;
    spec.proto = meth->get_proto();
    meth->change(spec, false /* rename on collision */);
  };

  TRACE(INTF, 9, "Changing name related to %s", SHOW(intf));
  for (const auto& meth : data.methoddefs) {
    if (!can_rename(meth)) {
      TRACE(INTF, 9, "Changing name but cannot rename %s, give up", SHOW(meth));
      return;
    }
  }

  for (const auto& meth : data.methoddefs) {
    if (method::is_constructor(meth)) {
      continue;
    }
    const auto* name = type_reference::new_name(meth);
    TRACE(INTF, 9, "Changing def name for %s to %s", SHOW(meth), SHOW(name));
    rename(meth, name);
  }
  for (const auto& refs_it : UnorderedIterable(data.methodrefs)) {
    if (refs_it.first->is_def()) {
      continue;
    }
    always_assert(!method::is_init(refs_it.first));
    const auto* name = type_reference::new_name(refs_it.first);
    TRACE(INTF, 9, "Changing ref name for %s to %s", SHOW(refs_it.first),
          SHOW(name));
    rename(refs_it.first, name);
  }
}

/**
 * Perform the optimization.
 */
CheckCastSet OptimizationImpl::do_optimize(
    const DexType* intf,
    const SingleImplData& data,
    UnorderedMap<DexMethod*, cfg::CFGMutation>& method_mutations) {
  CheckCastSet ret = fix_instructions(intf, data, method_mutations);
  set_type_refs(intf, data);
  set_field_defs(data);
  set_field_refs(data);
  set_method_defs(intf, data);
  set_method_refs(intf, data);
  rewrite_interface_methods(intf, data);
  remove_interface(intf, data);
  return ret;
}

/**
 * Run an optimization step.
 */
OptimizeStats OptimizationImpl::optimize(Scope& scope,
                                         const SingleImplConfig& config) {
  TypeList to_optimize;
  single_impls->get_interfaces(to_optimize);
  std::sort(to_optimize.begin(), to_optimize.end(), compare_dextypes);

  UnorderedMap<DexMethod*, cfg::CFGMutation> method_mutations;
  std::vector<DexMethod*> mutated_methods;
  for (const auto* intf : to_optimize) {
    auto& intf_data = single_impls->get_single_impl_data(intf);
    for (auto&& [method, _] :
         UnorderedIterable(intf_data.referencing_methods)) {
      auto* code = method->get_code();
      always_assert(code->cfg_built());
      auto emplaced =
          method_mutations.emplace(method, cfg::CFGMutation(code->cfg()))
              .second;
      if (emplaced) {
        mutated_methods.push_back(method);
      }
    }
  }

  CheckCastSet inserted_check_casts;
  for (const auto* intf : to_optimize) {
    auto& intf_data = single_impls->get_single_impl_data(intf);
    if (intf_data.is_escaped()) {
      continue;
    }
    TRACE(INTF, 3, "(OPT) %s => %s", SHOW(intf), SHOW(intf_data.cls));
    auto escape = can_optimize(intf, intf_data, config.rename_on_collision);
    if (escape != EscapeReason::NO_ESCAPE) {
      single_impls->escape_interface(intf, escape);
      continue;
    }
    auto check_casts = do_optimize(intf, intf_data, method_mutations);
    insert_unordered_iterable(inserted_check_casts, check_casts);
    optimized.insert(intf);
  }

  for (auto&& [_, mutation] : UnorderedIterable(method_mutations)) {
    mutation.flush();
  }

  // make a new scope deleting all single impl interfaces
  Scope new_scope;
  for (auto* cls : scope) {
    if (optimized.find(cls->get_type()) != optimized.end()) {
      continue;
    }
    new_scope.push_back(cls);
  }
  scope.swap(new_scope);

  if (must_rewrite_annotations(config)) {
    rewrite_annotations(scope, config);
  }

  std::vector<IRInstruction*> removed_instructions;
  auto post_process_stats =
      post_process(mutated_methods, &removed_instructions);
  std::atomic<size_t> retained{0};
  {
    for_all_methods(mutated_methods, [&](const DexMethod* m) {
      const auto* code = m->get_code();
      always_assert(code->cfg_built());
      const auto& cfg = code->cfg();
      size_t found = 0;
      for (const auto& mie : InstructionIterable(cfg)) {
        if (inserted_check_casts.count(mie.insn) != 0) {
          ++found;
        }
      }
      retained += found;
    });
  }

  for (auto* insn : removed_instructions) {
    delete insn;
  }

  OptimizeStats ret;
  ret.removed_interfaces = optimized.size();
  ret.inserted_check_casts = inserted_check_casts.size();
  ret.retained_check_casts = retained.load();
  ret.post_process = post_process_stats;
  ret.deleted_removed_instructions = removed_instructions.size();
  return ret;
}

check_casts::impl::Stats OptimizationImpl::post_process(
    const std::vector<DexMethod*>& methods,
    std::vector<IRInstruction*>* removed_instructions) {
  // The analysis times the number of methods is easily expensive, run in
  // parallel.
  check_casts::impl::Stats stats;
  std::mutex mutex;
  const auto& api = m_api;
  for_all_methods(
      methods,
      [&stats, &mutex, removed_instructions, &api](const DexMethod* m_const) {
        auto* m = const_cast<DexMethod*>(m_const);
        auto* code = m->get_code();
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();
        // T131253060 If enable weaken, we are hitting an assertion in
        // CheckCastAnalysis where a definition of a value is unknown. This only
        // occurs here within SingleImplPass, but not in subsequent
        // CheckCastRemovals where weaken is enabled by default.
        check_casts::CheckCastConfig config{.weaken = false};
        check_casts::impl::CheckCastAnalysis analysis(
            config, cfg, is_static(m), m->get_class(),
            m->get_proto()->get_args(), m->get_proto()->get_rtype(),
            m->get_param_anno(), api);
        auto casts = analysis.collect_redundant_checks_replacement();
        auto local_stats = check_casts::impl::apply(cfg, casts);
        auto insns = cfg.release_removed_instructions();
        std::lock_guard<std::mutex> lock_guard(mutex);
        stats += local_stats;
        removed_instructions->insert(removed_instructions->end(), insns.begin(),
                                     insns.end());
      },
      /*parallel=*/true);
  return stats;
}

} // namespace

/**
 * Entry point for an optimization pass.
 */
OptimizeStats optimize(std::unique_ptr<SingleImplAnalysis> analysis,
                       const ClassHierarchy& ch,
                       Scope& scope,
                       const SingleImplConfig& config,
                       const api::AndroidSDK& api,
                       method_profiles::MethodProfiles& method_profiles) {
  OptimizationImpl optimizer(std::move(analysis), ch, api, method_profiles);
  return optimizer.optimize(scope, config);
}
