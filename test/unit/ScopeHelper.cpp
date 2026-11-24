/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ScopeHelper.h"

#include "Creators.h"

namespace {

/**
 * Build a DexClass for java.lang.Object
 */
DexClass* create_java_lang_object() {
  auto* obj_t = type::java_lang_Object();
  auto* obj_cls = type_class(obj_t);
  if (obj_cls != nullptr) {
    return obj_cls;
  }

  // create a DexClass for java.lang.Object
  ClassCreator creator(obj_t);
  creator.set_access(ACC_PUBLIC);
  creator.set_external();
  obj_cls = creator.create();

  // create the following methods:
  // protected java.lang.Object.clone()Ljava/lang/Object;
  // public java.lang.Object.equals(Ljava/lang/Object;)Z
  // protected java.lang.Object.finalize()V
  // public final native java.lang.Object.getClass()Ljava/lang/Class;
  // public native java.lang.Object.hashCode()I
  // public final native java.lang.Object.notify()V
  // public final native java.lang.Object.notifyAll()V
  // public java.lang.Object.toString()Ljava/lang/String;
  // public final java.lang.Object.wait()V
  // public final java.lang.Object.wait(J)V
  // public final native java.lang.Object.wait(JI)V

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
  auto* method = dynamic_cast<DexMethod*>(
      DexMethod::make_method(obj_t, clone, void_object));
  method->set_access(ACC_PROTECTED);
  method->set_virtual(true);
  method->set_external();
  obj_cls->add_method(method);

  // public java.lang.Object.equals(Ljava/lang/Object;)Z
  method = dynamic_cast<DexMethod*>(
      DexMethod::make_method(obj_t, equals, object_bool));
  method->set_access(ACC_PUBLIC);
  method->set_virtual(true);
  method->set_external();
  obj_cls->add_method(method);

  // protected java.lang.Object.finalize()V
  method = dynamic_cast<DexMethod*>(
      DexMethod::make_method(obj_t, finalize, void_void));
  method->set_access(ACC_PROTECTED);
  method->set_virtual(true);
  method->set_external();
  obj_cls->add_method(method);

  method = dynamic_cast<DexMethod*>(
      DexMethod::get_method(obj_t, getClass, void_class));
  if (method == nullptr) {
    // public final native java.lang.Object.getClass()Ljava/lang/Class;
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, getClass, void_class));
    method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method = dynamic_cast<DexMethod*>(
      DexMethod::get_method(obj_t, hashCode, void_int));
  if (method == nullptr) {
    // public native java.lang.Object.hashCode()I
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, hashCode, void_int));
    method->set_access(ACC_PUBLIC | ACC_NATIVE);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method =
      dynamic_cast<DexMethod*>(DexMethod::get_method(obj_t, notify, void_void));
  if (method == nullptr) {
    // public final native java.lang.Object.notify()V
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, notify, void_void));
    method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method = dynamic_cast<DexMethod*>(
      DexMethod::get_method(obj_t, notifyAll, void_void));
  if (method == nullptr) {
    // public final native java.lang.Object.notifyAll()V
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, notifyAll, void_void));
    method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method = dynamic_cast<DexMethod*>(
      DexMethod::get_method(obj_t, toString, void_string));
  if (method == nullptr) {
    // public java.lang.Object.toString()Ljava/lang/String;
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, toString, void_string));
    method->set_access(ACC_PUBLIC);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method =
      dynamic_cast<DexMethod*>(DexMethod::get_method(obj_t, wait, void_void));
  if (method == nullptr) {
    // public final java.lang.Object.wait()V
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, wait, void_void));
    method->set_access(ACC_PUBLIC | ACC_FINAL);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method =
      dynamic_cast<DexMethod*>(DexMethod::get_method(obj_t, wait, long_void));
  if (method == nullptr) {
    // public final java.lang.Object.wait(J)V
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, wait, long_void));
    method->set_access(ACC_PUBLIC | ACC_FINAL);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  method = dynamic_cast<DexMethod*>(
      DexMethod::get_method(obj_t, wait, long_int_void));
  if (method == nullptr) {
    // public final native java.lang.Object.wait(JI)V
    method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(obj_t, wait, long_int_void));
    method->set_access(ACC_PUBLIC | ACC_FINAL | ACC_NATIVE);
    method->set_virtual(true);
    method->set_external();
  }
  obj_cls->add_method(method);

  return obj_cls;
}

} // namespace

DexClass* create_class(DexType* type,
                       DexType* super,
                       const std::vector<DexType*>& interfaces,
                       DexAccessFlags access,
                       bool external) {
  ClassCreator creator(type);
  creator.set_access(access);
  if (external) {
    creator.set_external();
  }
  if (super == nullptr) {
    super = type::java_lang_Object();
  }
  creator.set_super(super);
  for (const auto& interface : interfaces) {
    creator.add_interface(interface);
  }
  return creator.create();
}

Scope create_empty_scope() {
  Scope scope;
  create_java_lang_object();
  return scope;
}

DexClass* create_internal_class(DexType* type,
                                DexType* super,
                                const std::vector<DexType*>& interfaces,
                                DexAccessFlags access /*= ACC_PUBLIC*/) {
  return create_class(type, super, interfaces, access, false);
}

DexClass* create_external_class(DexType* type,
                                DexType* super,
                                const std::vector<DexType*>& interfaces,
                                DexAccessFlags access /*= ACC_PUBLIC*/) {
  return create_class(type, super, interfaces, access, true);
}

DexMethod* create_abstract_method(DexClass* cls,
                                  const char* name,
                                  DexProto* proto,
                                  DexAccessFlags access /*= ACC_PUBLIC*/) {
  access = access | ACC_ABSTRACT;
  auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(
      cls->get_type(), DexString::make_string(name), proto));
  method->make_concrete(access, std::unique_ptr<IRCode>(nullptr), true);
  cls->add_method(method);
  return method;
}

DexMethod* create_empty_method(DexClass* cls,
                               const char* name,
                               DexProto* proto,
                               DexAccessFlags access /*= ACC_PUBLIC*/) {
  MethodCreator mcreator(cls->get_type(), DexString::make_string(name), proto,
                         access);
  auto* main_block = mcreator.get_main_block();
  auto* rtype = proto->get_rtype();
  if (rtype == type::_void()) {
    main_block->ret_void();
  } else {
    auto null_loc = mcreator.make_local(rtype);
    main_block->load_null(null_loc);
    main_block->ret(null_loc);
  }
  auto* method = mcreator.create();
  cls->add_method(method);
  return method;
}

DexMethod* create_throwing_method(DexClass* cls,
                                  const char* name,
                                  DexProto* proto,
                                  DexAccessFlags access /*= ACC_PUBLIC*/) {
  MethodCreator mcreator(cls->get_type(), DexString::make_string(name), proto,
                         access);
  auto* main_block = mcreator.get_main_block();
  auto null_loc = mcreator.make_local(type::java_lang_Object());
  main_block->load_null(null_loc);
  main_block->throwex(null_loc);
  auto* method = mcreator.create();
  cls->add_method(method);
  return method;
}
