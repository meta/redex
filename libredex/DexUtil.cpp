/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexUtil.h"

#include <string_view>

#include "ControlFlow.h"
#include "Creators.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexStore.h"
#include "EditableCfgAdapter.h"
#include "IRInstruction.h"
#include "MethodUtil.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "TypeUtil.h"
#include "UnknownVirtuals.h"

const DexType* get_init_class_type_demand(const IRInstruction* insn) {
  switch (insn->opcode()) {
  case OPCODE_INVOKE_STATIC: {
    // It's the resolved method that counts
    auto* method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    return ((method != nullptr) && !assumenosideeffects(method))
               ? method->get_class()
               : nullptr;
  }
  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT: {
    // It's the resolved field that counts
    auto* field = resolve_field(insn->get_field(), FieldSearch::Static);
    return field != nullptr ? field->get_class() : nullptr;
  }
  case IOPCODE_INIT_CLASS:
  case OPCODE_NEW_INSTANCE: {
    return insn->get_type();
  }
  default:
    return nullptr;
  }
}

DexAccessFlags merge_visibility(uint32_t vis1, uint32_t vis2) {
  vis1 &= VISIBILITY_MASK;
  vis2 &= VISIBILITY_MASK;
  if (((vis1 & ACC_PUBLIC) != 0u) || ((vis2 & ACC_PUBLIC) != 0u)) {
    return ACC_PUBLIC;
  }
  if (vis1 == 0 || vis2 == 0) {
    return static_cast<DexAccessFlags>(0);
  }
  if (((vis1 & ACC_PROTECTED) != 0u) || ((vis2 & ACC_PROTECTED) != 0u)) {
    return ACC_PROTECTED;
  }
  return ACC_PRIVATE;
}

void create_runtime_exception_block(const DexString* except_str,
                                    std::vector<IRInstruction*>& block) {
  // clang-format off
  // new-instance v0, Ljava/lang/RuntimeException; // type@3852
  // const-string v1, "Exception String e.g. Too many args" // string@7a6d
  // invoke-direct {v0, v1}, Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V
  // throw v0
  // clang-format on
  auto* new_inst = (new IRInstruction(OPCODE_NEW_INSTANCE))
                       ->set_type(type::java_lang_RuntimeException());
  new_inst->set_dest(0);
  IRInstruction* const_inst =
      (new IRInstruction(OPCODE_CONST_STRING))->set_string(except_str);
  const_inst->set_dest(1);
  auto* ret = DexType::make_type("V");
  auto* arg = DexType::make_type("Ljava/lang/String;");
  auto* args = DexTypeList::make_type_list({arg});
  auto* proto = DexProto::make_proto(ret, args);
  auto* meth = DexMethod::make_method(type::java_lang_RuntimeException(),
                                      DexString::make_string("<init>"), proto);
  auto* invk = new IRInstruction(OPCODE_INVOKE_DIRECT);
  invk->set_method(meth);
  invk->set_srcs_size(2);
  invk->set_src(0, 0);
  invk->set_src(1, 1);
  IRInstruction* throwinst = new IRInstruction(OPCODE_THROW);
  block.emplace_back(new_inst);
  block.emplace_back(const_inst);
  block.emplace_back(invk);
  block.emplace_back(throwinst);
}

void create_abstract_method_error_block(const DexString* message,
                                        std::vector<IRInstruction*>& block,
                                        uint32_t exception_reg,
                                        uint32_t message_reg) {
  auto* ame_type = DexType::make_type("Ljava/lang/AbstractMethodError;");
  auto* new_inst = (new IRInstruction(OPCODE_NEW_INSTANCE))->set_type(ame_type);
  auto* mr_new = (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT));
  mr_new->set_dest(exception_reg);
  IRInstruction* const_inst =
      (new IRInstruction(OPCODE_CONST_STRING))->set_string(message);
  auto* mr_str = (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT));
  mr_str->set_dest(message_reg);
  auto* string_arg = DexType::make_type("Ljava/lang/String;");
  auto* args = DexTypeList::make_type_list({string_arg});
  auto* proto = DexProto::make_proto(type::_void(), args);
  auto* ctor =
      DexMethod::make_method(ame_type, DexString::make_string("<init>"), proto);
  auto* invk = new IRInstruction(OPCODE_INVOKE_DIRECT);
  invk->set_method(ctor);
  invk->set_srcs_size(2);
  invk->set_src(0, exception_reg);
  invk->set_src(1, message_reg);
  IRInstruction* throwinst = new IRInstruction(OPCODE_THROW);
  throwinst->set_srcs_size(1);
  throwinst->set_src(0, exception_reg);
  block.emplace_back(new_inst);
  block.emplace_back(mr_new);
  block.emplace_back(const_inst);
  block.emplace_back(mr_str);
  block.emplace_back(invk);
  block.emplace_back(throwinst);
}

bool passes_args_through(IRInstruction* insn,
                         const IRCode& code,
                         int ignore /* = 0 */
) {
  size_t src_idx{0};
  size_t param_count{0};
  for (const auto& mie : InstructionIterable(code.get_param_instructions())) {
    auto* load_param = mie.insn;
    ++param_count;
    if (src_idx >= insn->srcs_size()) {
      continue;
    }
    if (load_param->dest() != insn->src(src_idx++)) {
      return false;
    }
  }
  return insn->srcs_size() + ignore == param_count;
}

namespace {

size_t count_classes(const DexStoresVector& stores) {
  return unordered_accumulate(
      stores, std::size_t{0}, [](size_t acc, const auto& store) {
        return unordered_accumulate(store.get_dexen(), acc,
                                    [](auto dex_acc, const auto& classes) {
                                      return dex_acc + classes.size();
                                    });
      });
}

} // namespace

Scope build_class_scope(const DexStoresVector& stores) {
  Scope v;
  v.reserve(count_classes(stores));
  for (const auto& store : stores) {
    for (const auto& dex : store.get_dexen()) {
      v.insert(v.end(), dex.begin(), dex.end());
    }
  }

  return v;
}

namespace {

bool starts_with_any_prefix(const DexString* str,
                            const UnorderedSet<std::string>& prefixes) {
  if (str == nullptr) {
    return false;
  }
  for (const auto& prefix : UnorderedIterable(prefixes)) {
    if (str->str().starts_with(prefix)) {
      return true;
    }
  }
  return false;
}

} // namespace

Scope build_class_scope_for_packages(
    const DexStoresVector& stores,
    const UnorderedSet<std::string>& package_names) {
  Scope v;
  for (auto const& store : stores) {
    for (const auto& dex : store.get_dexen()) {
      for (const auto& clazz : dex) {
        if (starts_with_any_prefix(clazz->get_deobfuscated_name_or_null(),
                                   package_names)) {
          v.push_back(clazz);
        }
      }
    }
  }
  return v;
}

void post_dexen_changes(const Scope& v, DexStoresVector& stores) {
  DexStoreClassesIterator iter(stores);
  post_dexen_changes(v, iter);
}

void create_store(const std::string& store_name,
                  DexStoresVector& stores,
                  DexClasses classes) {
  // First, remove the classes from other stores.
  for (auto& store : stores) {
    store.remove_classes(classes);
  }

  // Create a new store and add it to the list of stores.
  DexStore store(store_name);
  store.set_generated();
  store.add_classes(std::move(classes));
  stores.emplace_back(std::move(store));
}

void relocate_field(DexField* field, DexType* to_type) {
  auto* from_cls = type_class(field->get_class());
  auto* to_cls = type_class(to_type);
  from_cls->remove_field(field);
  DexFieldSpec spec;
  spec.cls = to_type;
  field->change(spec, true /* rename on collision */);
  to_cls->add_field(field);
}

void relocate_method(DexMethod* method, DexType* to_type) {
  auto* from_cls = type_class(method->get_class());
  auto* to_cls = type_class(to_type);
  from_cls->remove_method(method);
  DexMethodSpec spec;
  spec.cls = to_type;
  method->change(spec, true /* rename on collision */);
  to_cls->add_method(method);
}

VisibilityChanges get_visibility_changes(const DexMethod* method,
                                         DexType* scope) {
  return get_visibility_changes(method->get_code(), scope, method);
}

void VisibilityChanges::insert(const VisibilityChanges& other) {
  insert_unordered_iterable(classes, other.classes);
  insert_unordered_iterable(fields, other.fields);
  insert_unordered_iterable(methods, other.methods);
}

void VisibilityChanges::clear() {
  classes.clear();
  fields.clear();
  methods.clear();
}

void VisibilityChanges::apply() const {
  for (auto* cls : UnorderedIterable(classes)) {
    set_public(cls);
  }
  for (auto* field : UnorderedIterable(fields)) {
    set_public(field);
  }
  for (auto* method : UnorderedIterable(methods)) {
    set_public(method);
  }
}

bool VisibilityChanges::empty() const {
  return classes.empty() && fields.empty() && methods.empty();
}

namespace {

struct VisibilityChangeGetter {
  VisibilityChanges& changes;
  DexType* scope;
  const DexMethod* effective_caller_resolved_from;
  void process_insn(IRInstruction* insn) {
    if (insn->has_field()) {
      auto* cls = type_class(insn->get_field()->get_class());
      if (cls != nullptr && !cls->is_external() && !is_public(cls)) {
        changes.classes.insert(cls);
      }
      auto* field = resolve_field(insn->get_field(),
                                  opcode::is_an_sfield_op(insn->opcode())
                                      ? FieldSearch::Static
                                      : FieldSearch::Instance);
      if (field != nullptr && field->is_concrete()) {
        if (!is_public(field)) {
          changes.fields.insert(field);
        }
        cls = type_class(field->get_class());
        if (!is_public(cls)) {
          changes.classes.insert(cls);
        }
      }
    } else if (insn->has_method()) {
      auto* cls = type_class(insn->get_method()->get_class());
      if (cls != nullptr && !cls->is_external() && !is_public(cls)) {
        changes.classes.insert(cls);
      }
      auto* current_method =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn),
                                    effective_caller_resolved_from);
      if (current_method != nullptr && current_method->is_concrete() &&
          (scope == nullptr || current_method->get_class() != scope)) {
        if (!is_public(current_method)) {
          changes.methods.insert(current_method);
        }
        cls = type_class(current_method->get_class());
        if (cls != nullptr && !cls->is_external() && !is_public(cls)) {
          changes.classes.insert(cls);
        }
      }
    } else if (insn->has_type()) {
      const auto* type = insn->get_type();
      auto* cls = type_class(type);
      if (cls != nullptr && !cls->is_external() && !is_public(cls)) {
        changes.classes.insert(cls);
      }
    }
  }

  void process_catch_types(const std::vector<const DexType*>& types) {
    for (const auto* type : types) {
      auto* cls = type_class(type);
      if (cls != nullptr && !cls->is_external() && !is_public(cls)) {
        changes.classes.insert(cls);
      }
    }
  }
};

} // namespace

VisibilityChanges get_visibility_changes(
    const IRCode* code,
    DexType* scope,
    const DexMethod* effective_caller_resolved_from) {
  always_assert(code != nullptr);
  VisibilityChanges changes;
  VisibilityChangeGetter getter{changes, scope, effective_caller_resolved_from};
  cfg_adapter::iterate(code, [&getter](const MethodItemEntry& mie) {
    getter.process_insn(mie.insn);
    return cfg_adapter::LOOP_CONTINUE;
  });

  std::vector<const DexType*> types;
  code->gather_catch_types(types);
  getter.process_catch_types(types);
  return changes;
}

VisibilityChanges get_visibility_changes(
    const cfg::ControlFlowGraph& cfg,
    DexType* scope,
    const DexMethod* effective_caller_resolved_from) {
  VisibilityChanges changes;
  VisibilityChangeGetter getter{changes, scope, effective_caller_resolved_from};
  for (const auto& mie : InstructionIterable(cfg)) {
    getter.process_insn(mie.insn);
  }
  std::vector<const DexType*> types;
  cfg.gather_catch_types(types);
  getter.process_catch_types(types);
  return changes;
}

// Check that visibility / accessibility changes to the current method
// won't need to change a referenced method into a virtual or static one.
bool gather_invoked_methods_that_prevent_relocation(
    const DexMethod* method,
    UnorderedSet<DexMethodRef*>* methods_preventing_relocation) {
  const auto* code = method->get_code();
  always_assert(code);
  always_assert(code->cfg_built());
  const auto& cfg = code->cfg();
  bool can_relocate = true;
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    auto opcode = insn->opcode();
    if (opcode::is_an_invoke(opcode)) {
      auto* meth = resolve_method_deprecated(insn->get_method(),
                                             opcode_to_search(insn), method);
      if ((meth == nullptr) && opcode == OPCODE_INVOKE_VIRTUAL &&
          unknown_virtuals::is_method_known_to_be_public(insn->get_method())) {
        continue;
      }
      if (meth != nullptr) {
        always_assert(meth->is_def());
        // What an invoke-super calls depends on the class that makes the call.
        if ((meth->is_external() && !is_public(meth)) ||
            (opcode == OPCODE_INVOKE_DIRECT && !method::is_init(meth)) ||
            opcode == OPCODE_INVOKE_SUPER) {
          meth = nullptr;
        }
      }
      if (meth == nullptr) {
        can_relocate = false;
        if (methods_preventing_relocation == nullptr) {
          break;
        }
        methods_preventing_relocation->emplace(insn->get_method());
      }
    }
  }

  return can_relocate;
}

bool relocate_method_if_no_changes(DexMethod* method, DexType* to_type) {
  if (!gather_invoked_methods_that_prevent_relocation(method)) {
    return false;
  }

  set_public(method);
  change_visibility(method, to_type);
  relocate_method(method, to_type);

  return true;
}

bool is_valid_identifier(std::string_view s) {
  if (s.empty()) {
    // Identifiers must not be empty.
    return false;
  }
  for (char c : s) {
    switch (c) {
    // Forbidden characters. This may not work for UTF encodings.
    case '/':
    case ';':
    case '.':
    case '[':
      return false;
    // Allow everything else.
    default:
      break;
    }
  }
  return true;
}

namespace java_names {

DexType* get_type_from_external_name(std::string_view external_name) {
  return DexType::get_type(external_to_internal(external_name));
}

DexType* get_element_type_from_external_name(std::string_view external_name) {
  auto internal_name = external_to_internal(external_name);
  auto element_pos = internal_name.find_first_not_of('[');
  if (element_pos == std::string::npos || internal_name[element_pos] != 'L') {
    return nullptr;
  }
  return DexType::get_type(std::string_view(internal_name).substr(element_pos));
}

namespace {
bool is_not_idenfitier_character(char ch) {
  return ch == '=' || ch == '+' || ch == '|' || ch == '@' || ch == '#' ||
         ch == '^' || ch == '&' || ch == '"' || ch == '\'' || ch == '`' ||
         ch == '~' || ch == '-';
}
} // namespace

// Differs from above "is_valid_identifier" function since this is for external
// names
bool is_identifier(const std::string_view& ident) {
  for (const char& ch : ident) {
    // java identifiers can be multi-lingual so membership testing is complex.
    // much simpler to test for what is definitely not an identifier and then
    // assume everything else is a legal identifier char, accepting that we
    // will have false positives.
    if (is_deliminator(ch) || is_not_idenfitier_character(ch)) {
      return false;
    }
  }
  return true;
}
} // namespace java_names

void create_object_class() {
  auto* type = type::java_lang_Object();
  if (type_class(type) != nullptr) {
    return;
  }

  std::vector<DexMethod*> object_methods;

  // required sigs
  auto* void_args = DexTypeList::make_type_list({});
  auto* void_object = DexProto::make_proto(type::java_lang_Object(), void_args);
  auto* object_bool = DexProto::make_proto(
      type::_boolean(),
      DexTypeList::make_type_list({type::java_lang_Object()}));
  auto* void_void = DexProto::make_proto(type::_void(), void_args);
  auto* void_class = DexProto::make_proto(type::java_lang_Class(), void_args);
  auto* void_int = DexProto::make_proto(type::_int(), void_args);
  auto* void_string = DexProto::make_proto(type::java_lang_String(), void_args);
  auto* long_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_long()}));
  auto* long_int_void = DexProto::make_proto(
      type::_void(),
      DexTypeList::make_type_list({type::_long(), type::_int()}));

  // required names
  const auto* clone = DexString::make_string("clone");
  const auto* equals = DexString::make_string("equals");
  const auto* finalize = DexString::make_string("finalize");
  const auto* getClass = DexString::make_string("getClass");
  const auto* hashCode = DexString::make_string("hashCode");
  const auto* notify = DexString::make_string("notify");
  const auto* notifyAll = DexString::make_string("notifyAll");
  const auto* toString = DexString::make_string("toString");
  const auto* wait = DexString::make_string("wait");

  // protected java.lang.Object.clone()Ljava/lang/Object;
  auto* method = DexMethod::make_method_downcast(type, clone, void_object);
  method->set_access(ACC_PROTECTED);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public java.lang.Object.equals(Ljava/lang/Object;)Z
  method = DexMethod::make_method_downcast(type, equals, object_bool);
  method->set_access(ACC_PUBLIC);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // protected java.lang.Object.finalize()V
  method = DexMethod::make_method_downcast(type, finalize, void_void);
  method->set_access(ACC_PROTECTED);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public final native java.lang.Object.getClass()Ljava/lang/Class;
  method = DexMethod::make_method_downcast(type, getClass, void_class);
  method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public native java.lang.Object.hashCode()I
  method = DexMethod::make_method_downcast(type, hashCode, void_int);
  method->set_access(ACC_PUBLIC | ACC_NATIVE);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  method = DexMethod::make_method_downcast(type, notify, void_void);
  method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public final native java.lang.Object.notifyAll()V
  method = DexMethod::make_method_downcast(type, notifyAll, void_void);
  method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public java.lang.Object.toString()Ljava/lang/String;
  method = DexMethod::make_method_downcast(type, toString, void_string);
  method->set_access(ACC_PUBLIC);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public final java.lang.Object.wait()V
  method = DexMethod::make_method_downcast(type, wait, void_void);
  method->set_access(ACC_PUBLIC | ACC_FINAL);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public final java.lang.Object.wait(J)V
  method = DexMethod::make_method_downcast(type, wait, long_void);
  method->set_access(ACC_PUBLIC | ACC_FINAL);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  // public final native java.lang.Object.wait(JI)V
  method = DexMethod::make_method_downcast(type, wait, long_int_void);
  method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
  method->set_virtual(true);
  method->set_external();
  object_methods.push_back(method);

  ClassCreator cc(type);
  cc.set_access(ACC_PUBLIC);
  auto* object_class = cc.create();
  for (auto const& m : object_methods) {
    object_class->add_method(m);
  }
}
