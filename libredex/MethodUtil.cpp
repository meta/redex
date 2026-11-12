/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodUtil.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "DexAnnotation.h"
#include "EditableCfgAdapter.h"
#include "ReachableClasses.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "TypeUtil.h"

namespace {

class ClInitSideEffectsAnalysis {
 private:
  bool m_allow_benign_method_invocations;
  const method::ClInitHasNoSideEffectsPredicate* m_clinit_has_no_side_effects;
  const InsertOnlyConcurrentSet<DexMethod*>* m_non_true_virtuals;
  UnorderedSet<DexMethodRef*> m_active;
  UnorderedSet<const DexType*> m_initialized;

 public:
  explicit ClInitSideEffectsAnalysis(
      bool allow_benign_method_invocations,
      const method::ClInitHasNoSideEffectsPredicate* clinit_has_no_side_effects,
      const InsertOnlyConcurrentSet<DexMethod*>* non_true_virtuals)
      : m_allow_benign_method_invocations(allow_benign_method_invocations),
        m_clinit_has_no_side_effects(clinit_has_no_side_effects),
        m_non_true_virtuals(non_true_virtuals) {}

  const DexClass* run(const DexClass* cls) {
    std::stack<const DexClass*> stack;
    const DexClass* first_cls_with_clinit{nullptr};
    for (; (cls != nullptr) && !cls->is_external();
         cls = type_class(cls->get_super_class())) {
      stack.push(cls);
      if ((first_cls_with_clinit == nullptr) &&
          (cls->get_clinit() != nullptr)) {
        first_cls_with_clinit = cls;
      }
    }
    while (!stack.empty()) {
      cls = stack.top();
      stack.pop();
      m_initialized.insert(cls->get_type());
      if (cls->rstate.clinit_has_no_side_effects() ||
          clinit_has_no_side_effects(cls->get_type())) {
        continue;
      }

      auto* clinit = cls->get_clinit();
      if ((clinit != nullptr) && method_may_have_side_effects(clinit, clinit)) {
        return first_cls_with_clinit;
      }
    }
    always_assert(m_active.empty());
    return nullptr;
  }

 private:
  bool clinit_has_no_side_effects(const DexType* type) {
    return (m_clinit_has_no_side_effects != nullptr) &&
           (*m_clinit_has_no_side_effects)(type);
  }

  bool init_class_or_new_instance_may_have_side_effects(const DexType* type) {
    return !clinit_has_no_side_effects(type) &&
           type != type::java_lang_Object() &&
           (m_initialized.count(type) == 0u);
  }

  bool field_op_may_have_side_effects(DexMethod* effective_caller,
                                      IRInstruction* insn) {
    auto* field = insn->get_field();
    if (opcode::is_an_iget(insn->opcode())) {
      return false;
    } else if (opcode::is_an_iput(insn->opcode())) {
      return !method::is_init(effective_caller) ||
             !type::is_subclass(field->get_class(),
                                effective_caller->get_class());
    } else if (opcode::is_an_sget(insn->opcode())) {
      return init_class_or_new_instance_may_have_side_effects(
          field->get_class());
    } else {
      always_assert(opcode::is_an_sput(insn->opcode()));
      return !method::is_clinit(effective_caller) ||
             field->get_class() != effective_caller->get_class();
    }
  }

  bool invoke_may_have_side_effects(DexMethod* effective_caller,
                                    IRInstruction* insn) {
    auto* method_ref = insn->get_method();
    if (m_allow_benign_method_invocations &&
        method::is_clinit_invoked_method_benign(method_ref)) {
      return false;
    }
    if (opcode::is_invoke_interface(insn->opcode()) ||
        opcode::is_invoke_super(insn->opcode())) {
      return true;
    }
    always_assert(opcode::is_invoke_direct(insn->opcode()) ||
                  opcode::is_invoke_virtual(insn->opcode()) ||
                  opcode::is_invoke_static(insn->opcode()));
    auto* method =
        resolve_method_deprecated(method_ref, opcode_to_search(insn));
    if (method == nullptr) {
      return true;
    }
    if (opcode::is_invoke_virtual(insn->opcode()) &&
        ((m_non_true_virtuals == nullptr) ||
         (m_non_true_virtuals->count_unsafe(method) == 0u))) {
      return true;
    }
    if (opcode::is_invoke_static(insn->opcode()) &&
        init_class_or_new_instance_may_have_side_effects(method->get_class())) {
      return true;
    }
    if (method::is_init(method)) {
      effective_caller = method;
    }
    return method_may_have_side_effects(effective_caller, method);
  }

  bool method_may_have_side_effects(DexMethod* effective_caller,
                                    DexMethod* method) {
    always_assert(method::is_init(effective_caller) ||
                  method::is_clinit(effective_caller));
    if (method->is_external() || (method->get_code() == nullptr)) {
      return true;
    }
    if (!m_active.insert(method).second) {
      // recursion
      return true;
    }
    bool non_trivial = false;
    cfg_adapter::iterate_with_iterator(
        method->get_code(), [&](const IRList::iterator& it) {
          auto* insn = it->insn;
          if (opcode::is_an_invoke(insn->opcode())) {
            if (invoke_may_have_side_effects(effective_caller, insn)) {
              non_trivial = true;
              return cfg_adapter::LOOP_BREAK;
            }
          } else if (insn->opcode() == IOPCODE_INIT_CLASS ||
                     insn->opcode() == OPCODE_NEW_INSTANCE) {
            if (init_class_or_new_instance_may_have_side_effects(
                    insn->get_type())) {
              non_trivial = true;
              return cfg_adapter::LOOP_BREAK;
            }
          } else if (insn->has_field()) {
            if (field_op_may_have_side_effects(effective_caller, insn)) {
              non_trivial = true;
              return cfg_adapter::LOOP_BREAK;
            }
          }
          return cfg_adapter::LOOP_CONTINUE;
        });
    auto erased = m_active.erase(method);
    always_assert(erased);
    return non_trivial;
  }
};

} // namespace

namespace method {

bool is_init(const DexMethodRef* method) {
  return strcmp(method->get_name()->c_str(), "<init>") == 0;
}

bool is_clinit(const DexMethodRef* method) {
  return strcmp(method->get_name()->c_str(), "<clinit>") == 0;
}

bool is_argless_init(const DexMethodRef* method) {
  return is_init(method) && method->get_proto()->get_args()->empty();
}

bool is_trivial_clinit(const IRCode& code) {
  if (!code.cfg_built()) {
    auto ii = InstructionIterable(code);
    return std::none_of(ii.begin(), ii.end(), [](const MethodItemEntry& mie) {
      return mie.insn->opcode() != OPCODE_RETURN_VOID;
    });
  } else {
    const auto& cfg = code.cfg();
    auto ii = cfg::ConstInstructionIterable(cfg);
    return std::none_of(ii.begin(), ii.end(), [](const MethodItemEntry& mie) {
      return mie.insn->opcode() != OPCODE_RETURN_VOID;
    });
  }
}

bool is_clinit_invoked_method_benign(const DexMethodRef* method_ref) {
  const auto type_name = method_ref->get_class()->str();
  if (type_name == "Lcom/redex/OutlinedStringBuilders;") {
    return true;
  }

  const auto name = method_ref->get_name()->str();
  if (name == "clone" || name == "concat" || name == "append") {
    return true;
  }

  static const UnorderedSet<std::string_view> methods = {
      // clang-format off
      "Landroid/content/Context;.getApplicationContext:()Landroid/content/Context;",
      "Landroid/content/Context;.getApplicationInfo:()Landroid/content/pm/ApplicationInfo;",
      "Landroid/content/Context;.getCacheDir:()Ljava/io/File;",
      "Landroid/content/Context;.getPackageName:()Ljava/lang/String;",
      "Landroid/content/ContextWrapper;.getApplicationContext:()Landroid/content/Context;",
      "Landroid/graphics/Color;.rgb:(III)I",
      "Landroid/graphics/Path;.<init>:()V",
      "Landroid/graphics/PointF;.<init>:(FF)V",
      "Landroid/graphics/Rect;.<init>:()V",
      "Landroid/net/Uri$Builder;.appendPath:(Ljava/lang/String;)Landroid/net/Uri$Builder;",
      "Landroid/net/Uri$Builder;.build:()Landroid/net/Uri;",
      "Landroid/net/Uri;.buildUpon:()Landroid/net/Uri$Builder;",
      "Landroid/net/Uri;.parse:(Ljava/lang/String;)Landroid/net/Uri;",
      "Landroid/os/Handler;.<init>:(Landroid/os/Looper;)V",
      "Landroid/os/Looper;.getMainLooper:()Landroid/os/Looper;",
      "Landroid/os/Process;.is64Bit:()Z",
      "Landroid/os/Trace;.beginSection:(Ljava/lang/String;)V",
      "Landroid/os/Trace;.endSection:()V",
      "Landroid/os/Process;.myPid:()I",
      "Landroid/os/Process;.myUid:()I",
      "Landroid/text/TextUtils;.isEmpty:(Ljava/lang/CharSequence;)Z",
      "Landroid/text/format/Time;.<init>:()V",
      "Landroid/util/Log;.e:(Ljava/lang/String;Ljava/lang/String;)I",
      "Landroid/util/Log;.isLoggable:(Ljava/lang/String;I)Z",
      "Landroid/util/Log;.w:(Ljava/lang/String;Ljava/lang/String;)I",
      "Landroid/util/SparseArray;.<init>:()V",
      "Landroid/util/SparseArray;.<init>:(I)V",
      "Landroid/util/SparseArray;.put:(ILjava/lang/Object;)V",
      "Ljava/io/BufferedReader;.<init>:(Ljava/io/Reader;)V",
      "Ljava/io/ByteArrayOutputStream;.<init>:()V",
      "Ljava/io/ByteArrayOutputStream;.toByteArray:()[B",
      "Ljava/io/File;.equals:(Ljava/lang/Object;)Z",
      "Ljava/io/File;.getAbsolutePath:()Ljava/lang/String;",
      "Ljava/io/File;.getCanonicalPath:()Ljava/lang/String;",
      "Ljava/io/File;.getParentFile:()Ljava/io/File;",
      "Ljava/io/OutputStream;.<init>:()V",
      "Ljava/io/OutputStream;.write:([B)V",
      "Ljava/io/PrintStream;.println:(Ljava/lang/String;)V",
      "Ljava/io/PrintWriter;.<init>:(Ljava/io/Writer;)V",
      "Ljava/io/PrintWriter;.close:()V",
      "Ljava/io/PrintWriter;.println:()V",
      "Ljava/io/Writer;.<init>:()V",
      "Ljava/io/Writer;.close:()V",
      "Ljava/lang/AssertionError;.<init>:()V",
      "Ljava/lang/AssertionError;.<init>:(Ljava/lang/Object;)V",
      "Ljava/lang/Boolean;.booleanValue:()Z",
      "Ljava/lang/Boolean;.parseBoolean:(Ljava/lang/String;)Z",
      "Ljava/lang/Boolean;.valueOf:(Ljava/lang/String;)Ljava/lang/Boolean;",
      "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;",
      "Ljava/lang/CharSequence;.charAt:(I)C",
      "Ljava/lang/CharSequence;.length:()I",
      "Ljava/lang/CharSequence;.toString:()Ljava/lang/String;",
      "Ljava/lang/Character;.toLowerCase:(C)C",
      "Ljava/lang/Character;.toUpperCase:(C)C",
      "Ljava/lang/Class;.forName:(Ljava/lang/String;)Ljava/lang/Class;",
      "Ljava/lang/Class;.forName:(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;",
      "Ljava/lang/Class;.getClassLoader:()Ljava/lang/ClassLoader;",
      "Ljava/lang/Class;.getDeclaredField:(Ljava/lang/String;)Ljava/lang/reflect/Field;",
      "Ljava/lang/Class;.getDeclaredMethod:(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;",
      "Ljava/lang/Class;.getEnumConstants:()[Ljava/lang/Object;",
      "Ljava/lang/Class;.getField:(Ljava/lang/String;)Ljava/lang/reflect/Field;",
      "Ljava/lang/Class;.getMethod:(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;",
      "Ljava/lang/Class;.getName:()Ljava/lang/String;",
      "Ljava/lang/Class;.getSimpleName:()Ljava/lang/String;",
      "Ljava/lang/Class;.newInstance:()Ljava/lang/Object;",
      "Ljava/lang/Class;.toString:()Ljava/lang/String;",
      "Ljava/lang/ClassCastException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Double;.isNaN:(D)Z",
      "Ljava/lang/Double;.parseDouble:(Ljava/lang/String;)D",
      "Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;",
      "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V",
      "Ljava/lang/Enum;.name:()Ljava/lang/String;",
      "Ljava/lang/Enum;.ordinal:()I",
      "Ljava/lang/Enum;.toString:()Ljava/lang/String;",
      "Ljava/lang/Error;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Error;.<init>:(Ljava/lang/Throwable;)V",
      "Ljava/lang/Exception;.<init>:()V",
      "Ljava/lang/Float;.floatValue:()F",
      "Ljava/lang/Float;.valueOf:(F)Ljava/lang/Float;",
      "Ljava/lang/IllegalArgumentException;.<init>:()V",
      "Ljava/lang/IllegalArgumentException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/IndexOutOfBoundsException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Integer;.highestOneBit:(I)I",
      "Ljava/lang/Integer;.intValue:()I",
      "Ljava/lang/Integer;.parseInt:(Ljava/lang/String;)I",
      "Ljava/lang/Integer;.rotateLeft:(II)I",
      "Ljava/lang/Integer;.toHexString:(I)Ljava/lang/String;",
      "Ljava/lang/Integer;.toString:(I)Ljava/lang/String;",
      "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;",
      "Ljava/lang/Long;.parseLong:(Ljava/lang/String;)J",
      "Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;",
      "Ljava/lang/Math;.abs:(F)F",
      "Ljava/lang/Math;.max:(II)I",
      "Ljava/lang/Math;.min:(II)I",
      "Ljava/lang/Math;.min:(JJ)J",
      "Ljava/lang/Math;.pow:(DD)D",
      "Ljava/lang/Math;.signum:(F)F",
      "Ljava/lang/Math;.sqrt:(D)D",
      "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Number;.floatValue:()F",
      "Ljava/lang/Number;.intValue:()I",
      "Ljava/lang/Object;.<init>:()V",
      "Ljava/lang/Object;.<init>:()V",
      "Ljava/lang/Object;.equals:(Ljava/lang/Object;)Z",
      "Ljava/lang/Object;.getClass:()Ljava/lang/Class;",
      "Ljava/lang/Object;.hashCode:()I",
      "Ljava/lang/Object;.toString:()Ljava/lang/String;",
      "Ljava/lang/Runtime;.getRuntime:()Ljava/lang/Runtime;",
      "Ljava/lang/Runtime;.availableProcessors:()I",
      "Ljava/lang/RuntimeException;.<init>:()V",
      "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;Ljava/lang/Throwable;)V",
      "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/Throwable;)V",
      "Ljava/lang/StackTraceElement;.getClassName:()Ljava/lang/String;",
      "Ljava/lang/StackTraceElement;.getMethodName:()Ljava/lang/String;",
      "Ljava/lang/String;.<init>:([B)V",
      "Ljava/lang/String;.<init>:([BLjava/lang/String;)V",
      "Ljava/lang/String;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/String;.charAt:(I)C",
      "Ljava/lang/String;.contains:(Ljava/lang/CharSequence;)Z",
      "Ljava/lang/String;.equals:(Ljava/lang/Object;)Z",
      "Ljava/lang/String;.format:(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;",
      "Ljava/lang/String;.format:(Ljava/util/Locale;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;",
      "Ljava/lang/String;.getBytes:(Ljava/lang/String;)[B",
      "Ljava/lang/String;.hashCode:()I",
      "Ljava/lang/String;.indexOf:(II)I",
      "Ljava/lang/String;.indexOf:(Ljava/lang/String;I)I",
      "Ljava/lang/String;.isEmpty:()Z",
      "Ljava/lang/String;.lastIndexOf:(I)I",
      "Ljava/lang/String;.lastIndexOf:(Ljava/lang/String;)I",
      "Ljava/lang/String;.length:()I",
      "Ljava/lang/String;.replace:(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)Ljava/lang/String;",
      "Ljava/lang/String;.startsWith:(Ljava/lang/String;)Z",
      "Ljava/lang/String;.substring:(I)Ljava/lang/String;",
      "Ljava/lang/String;.substring:(II)Ljava/lang/String;",
      "Ljava/lang/String;.toCharArray:()[C",
      "Ljava/lang/String;.toLowerCase:(Ljava/util/Locale;)Ljava/lang/String;",
      "Ljava/lang/String;.toUpperCase:(Ljava/util/Locale;)Ljava/lang/String;",
      "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;",
      "Ljava/lang/String;.valueOf:([C)Ljava/lang/String;",
      "Ljava/lang/StringBuilder;.<init>:()V",
      "Ljava/lang/StringBuilder;.<init>:(I)V",
      "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;",
      "Ljava/lang/System;.arraycopy:(Ljava/lang/Object;ILjava/lang/Object;II)V",
      "Ljava/lang/System;.currentTimeMillis:()J",
      "Ljava/lang/System;.getProperties:()Ljava/util/Properties;",
      "Ljava/lang/System;.getProperty:(Ljava/lang/String;)Ljava/lang/String;",
      "Ljava/lang/System;.getProperty:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;",
      "Ljava/lang/System;.identityHashCode:(Ljava/lang/Object;)I",
      "Ljava/lang/System;.nanoTime:()J",
      "Ljava/lang/Thread;.<init>:(Ljava/lang/Runnable;Ljava/lang/String;)V",
      "Ljava/lang/Thread;.currentThread:()Ljava/lang/Thread;",
      "Ljava/lang/Thread;.getStackTrace:()[Ljava/lang/StackTraceElement;",
      "Ljava/lang/ThreadLocal;.<init>:()V",
      "Ljava/lang/Throwable;.<init>:()V",
      "Ljava/lang/Throwable;.getMessage:()Ljava/lang/String;",
      "Ljava/lang/Throwable;.getStackTrace:()[Ljava/lang/StackTraceElement;",
      "Ljava/lang/Throwable;.initCause:(Ljava/lang/Throwable;)Ljava/lang/Throwable;",
      "Ljava/lang/Throwable;.printStackTrace:()V",
      "Ljava/lang/Throwable;.setStackTrace:([Ljava/lang/StackTraceElement;)V",
      "Ljava/lang/Throwable;.toString:()Ljava/lang/String;",
      "Ljava/lang/UnsatisfiedLinkError;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/ref/ReferenceQueue;.<init>:()V",
      "Ljava/lang/reflect/Field;.get:(Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/nio/charset/Charset;.forName:(Ljava/lang/String;)Ljava/nio/charset/Charset;",
      "Ljava/nio/charset/Charset;.name:()Ljava/lang/String;",
      "Ljava/security/Provider;.<init>:(Ljava/lang/String;DLjava/lang/String;)V",
      "Ljava/text/BreakIterator;.getCharacterInstance:()Ljava/text/BreakIterator;",
      "Ljava/text/BreakIterator;.last:()I",
      "Ljava/text/BreakIterator;.setText:(Ljava/lang/String;)V",
      "Ljava/text/SimpleDateFormat;.<init>:(Ljava/lang/String;Ljava/util/Locale;)V",
      "Ljava/util/AbstractCollection;.<init>:()V",
      "Ljava/util/AbstractCollection;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/AbstractCollection;.contains:(Ljava/lang/Object;)Z",
      "Ljava/util/AbstractCollection;.size:()I",
      "Ljava/util/AbstractCollection;.toArray:()[Ljava/lang/Object;",
      "Ljava/util/AbstractCollection;.toArray:([Ljava/lang/Object;)[Ljava/lang/Object;",
      "Ljava/util/AbstractList;.get:(I)Ljava/lang/Object;",
      "Ljava/util/AbstractMap;.<init>:()V",
      "Ljava/util/AbstractMap;.get:(Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/AbstractMap;.put:(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/AbstractQueue;.<init>:()V",
      "Ljava/util/ArrayList;.<init>:()V",
      "Ljava/util/ArrayList;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/ArrayList;.get:(I)Ljava/lang/Object;",
      "Ljava/util/ArrayList;.size:()I",
      "Ljava/util/ArrayList;.toArray:([Ljava/lang/Object;)[Ljava/lang/Object;",
      "Ljava/util/Arrays;.asList:([Ljava/lang/Object;)Ljava/util/List;",
      "Ljava/util/Arrays;.copyOf:([Ljava/lang/Object;I)[Ljava/lang/Object;",
      "Ljava/util/Arrays;.copyOfRange:([BII)[B",
      "Ljava/util/Arrays;.copyOfRange:([Ljava/lang/Object;II)[Ljava/lang/Object;",
      "Ljava/util/Arrays;.fill:([II)V",
      "Ljava/util/Arrays;.fill:([Ljava/lang/Object;IILjava/lang/Object;)V",
      "Ljava/util/Arrays;.sort:([C)V",
      "Ljava/util/Arrays;.toString:([Ljava/lang/Object;)Ljava/lang/String;",
      "Ljava/util/Calendar;.getInstance:(Ljava/util/TimeZone;)Ljava/util/Calendar;",
      "Ljava/util/Collection;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/Collection;.toArray:()[Ljava/lang/Object;",
      "Ljava/util/Collections;.addAll:(Ljava/util/Collection;[Ljava/lang/Object;)Z",
      "Ljava/util/Collections;.newSetFromMap:(Ljava/util/Map;)Ljava/util/Set;",
      "Ljava/util/Collections;.singleton:(Ljava/lang/Object;)Ljava/util/Set;",
      "Ljava/util/Collections;.synchronizedMap:(Ljava/util/Map;)Ljava/util/Map;",
      "Ljava/util/Collections;.unmodifiableList:(Ljava/util/List;)Ljava/util/List;",
      "Ljava/util/Collections;.unmodifiableMap:(Ljava/util/Map;)Ljava/util/Map;",
      "Ljava/util/Collections;.unmodifiableSet:(Ljava/util/Set;)Ljava/util/Set;",
      "Ljava/util/Dictionary;.put:(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/EnumMap;.<init>:(Ljava/lang/Class;)V",
      "Ljava/util/EnumSet;.copyOf:(Ljava/util/Collection;)Ljava/util/EnumSet;",
      "Ljava/util/HashMap;.<init>:()V",
      "Ljava/util/HashMap;.<init>:(I)V",
      "Ljava/util/HashMap;.get:(Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/HashMap;.put:(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/HashSet;.<init>:()V",
      "Ljava/util/HashSet;.<init>:(I)V",
      "Ljava/util/HashSet;.<init>:(Ljava/util/Collection;)V",
      "Ljava/util/HashSet;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/HashSet;.contains:(Ljava/lang/Object;)Z",
      "Ljava/util/Iterator;.hasNext:()Z",
      "Ljava/util/Iterator;.next:()Ljava/lang/Object;",
      "Ljava/util/LinkedHashMap;.<init>:()V",
      "Ljava/util/LinkedHashMap;.<init>:(I)V",
      "Ljava/util/LinkedHashMap;.<init>:(IFZ)V",
      "Ljava/util/LinkedHashSet;.<init>:(I)V",
      "Ljava/util/LinkedList;.<init>:()V",
      "Ljava/util/Locale;.<init>:(Ljava/lang/String;Ljava/lang/String;)V",
      "Ljava/util/Locale;.getDefault:()Ljava/util/Locale;",
      "Ljava/util/Map;.containsKey:(Ljava/lang/Object;)Z",
      "Ljava/util/Map;.get:(Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/Map;.put:(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
      "Ljava/util/NoSuchElementException;.<init>:(Ljava/lang/String;)V",
      "Ljava/util/Random;.<init>:()V",
      "Ljava/util/concurrent/Semaphore;.<init>:(I)V",
      "Ljava/util/Set;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/Set;.contains:(Ljava/lang/Object;)Z",
      "Ljava/util/Set;.iterator:()Ljava/util/Iterator;",
      "Ljava/util/TimeZone;.getTimeZone:(Ljava/lang/String;)Ljava/util/TimeZone;",
      "Ljava/util/Timer;.<init>:()V",
      "Ljava/util/TreeSet;.<init>:()V",
      "Ljava/util/TreeSet;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/TreeSet;.contains:(Ljava/lang/Object;)Z",
      "Ljava/util/WeakHashMap;.<init>:()V",
      "Ljava/util/WeakHashMap;.<init>:(I)V",
      "Ljava/util/concurrent/ConcurrentHashMap;.<init>:()V",
      "Ljava/util/concurrent/ConcurrentHashMap;.<init>:(I)V",
      "Ljava/util/concurrent/ConcurrentLinkedQueue;.<init>:()V",
      "Ljava/util/concurrent/CopyOnWriteArraySet;.<init>:()V",
      "Ljava/util/concurrent/LinkedBlockingQueue;.<init>:()V",
      "Ljava/util/concurrent/TimeUnit;.toDays:(J)J",
      "Ljava/util/concurrent/TimeUnit;.toMillis:(J)J",
      "Ljava/util/concurrent/TimeUnit;.toMinutes:(J)J",
      "Ljava/util/concurrent/TimeUnit;.toNanos:(J)J",
      "Ljava/util/concurrent/TimeUnit;.toSeconds:(J)J",
      "Ljava/util/concurrent/ThreadPoolExecutor;.<init>:(IIJLjava/util/concurrent/TimeUnit;Ljava/util/concurrent/BlockingQueue;Ljava/util/concurrent/ThreadFactory;)V",
      "Ljava/util/concurrent/atomic/AtomicBoolean;.<init>:(Z)V",
      "Ljava/util/concurrent/atomic/AtomicInteger;.<init>:()V",
      "Ljava/util/concurrent/atomic/AtomicInteger;.<init>:(I)V",
      "Ljava/util/concurrent/atomic/AtomicInteger;.get:()I",
      "Ljava/util/concurrent/atomic/AtomicInteger;.getAndIncrement:()I",
      "Ljava/util/concurrent/atomic/AtomicLong;.<init>:(J)V",
      "Ljava/util/concurrent/atomic/AtomicReference;.<init>:()V",
      "Ljava/util/concurrent/atomic/AtomicReference;.<init>:(Ljava/lang/Object;)V",
      "Ljava/util/concurrent/atomic/AtomicReferenceArray;.<init>:(I)V",
      "Ljava/util/concurrent/atomic/AtomicReferenceArray;.length:()I",
      "Ljava/util/concurrent/locks/ReentrantLock;.<init>:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock$ReadLock;.lock:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock$ReadLock;.unlock:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock$WriteLock;.lock:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock$WriteLock;.unlock:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock;.<init>:()V",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock;.readLock:()Ljava/util/concurrent/locks/ReentrantReadWriteLock$ReadLock;",
      "Ljava/util/concurrent/locks/ReentrantReadWriteLock;.writeLock:()Ljava/util/concurrent/locks/ReentrantReadWriteLock$WriteLock;",
      "Ljava/util/logging/Logger;.getLogger:(Ljava/lang/String;)Ljava/util/logging/Logger;",
      "Ljava/util/logging/Logger;.log:(Ljava/util/logging/Level;Ljava/lang/String;)V",
      "Ljava/util/logging/Logger;.log:(Ljava/util/logging/Level;Ljava/lang/String;Ljava/lang/Throwable;)V",
      "Ljava/util/regex/Pattern;.compile:(Ljava/lang/String;)Ljava/util/regex/Pattern;",
      "Ljava/util/regex/Pattern;.compile:(Ljava/lang/String;I)Ljava/util/regex/Pattern;",
      "Ljava/util/regex/Pattern;.quote:(Ljava/lang/String;)Ljava/lang/String;",
      "Lredex/$EnumUtils;.values:(I)[Ljava/lang/Integer;",
      // clang-format on
  };

  return method_ref->is_def() &&
         (methods.count(
              method_ref->as_def()->get_deobfuscated_name_or_empty()) != 0u);
}

const DexClass* clinit_may_have_side_effects(
    const DexClass* cls,
    bool allow_benign_method_invocations,
    const ClInitHasNoSideEffectsPredicate* clinit_has_no_side_effects,
    const InsertOnlyConcurrentSet<DexMethod*>* non_true_virtuals) {
  ClInitSideEffectsAnalysis analysis(allow_benign_method_invocations,
                                     clinit_has_no_side_effects,
                                     non_true_virtuals);
  return analysis.run(cls);
}

bool no_invoke_super(const IRCode& code) {
  bool has_invoke_super{false};
  cfg_adapter::iterate(&code, [&](const MethodItemEntry& mie) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_INVOKE_SUPER) {
      has_invoke_super = true;
      return cfg_adapter::LOOP_BREAK;
    }
    return cfg_adapter::LOOP_CONTINUE;
  });
  return !has_invoke_super;
}

bool may_be_invoke_target(const DexMethod* method) {
  if (is_native(method) || method->is_external()) {
    // We don't know
    return true;
  }
  return !is_abstract(method) && !method->get_code()->is_unreachable();
}

bool can_change_signature(const DexMethod* method) {
  return can_rename(method) && !is_native(method) &&
         !method->rstate.no_optimizations();
}

#define DEFINE_CACHED_METHOD(func_name, _)                 \
  DexMethod* func_name() {                                 \
    return g_redex->pointers_cache().method_##func_name(); \
  }

#define FOR_EACH DEFINE_CACHED_METHOD
WELL_KNOWN_METHODS
#undef FOR_EACH

DexMethod* kotlin_jvm_internal_Intrinsics_checkParameterIsNotNull() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/"
      "Object;Ljava/lang/String;)V"));
}

DexMethod* kotlin_jvm_internal_Intrinsics_checkNotNullParameter() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/"
      "Object;Ljava/lang/String;)V"));
}

DexMethod* kotlin_jvm_internal_Intrinsics_checExpressionValueIsNotNull() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkExpressionValueIsNotNull:(Ljava/"
      "lang/Object;Ljava/lang/String;)V"));
}

DexMethod* kotlin_jvm_internal_Intrinsics_checkNotNullExpressionValue() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lkotlin/jvm/internal/Intrinsics;.checkNotNullExpressionValue:(Ljava/"
      "lang/Object;Ljava/lang/String;)V"));
}

DexMethod* kotlin_jvm_internal_Intrinsics_areEqual() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lkotlin/jvm/internal/Intrinsics;.areEqual:(Ljava/lang/Object;Ljava/"
      "lang/Object;)Z"));
}

DexMethod* redex_internal_checkObjectNotNull() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V"));
}

DexMethod* java_lang_invoke_MethodHandle_invoke() {
  return dynamic_cast<DexMethod*>(
      DexMethod::get_method("Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/"
                            "lang/Object;)Ljava/lang/Object;"));
}

DexMethod* java_lang_invoke_MethodHandle_invokeExact() {
  return dynamic_cast<DexMethod*>(DexMethod::get_method(
      "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/"
      "lang/Object;)Ljava/lang/Object;"));
}

std::optional<std::string_view> get_param_name(const DexMethod* m, size_t idx) {
  // First try to look it up from the debug info item.
  const auto* code = m->get_code();
  if ((code != nullptr) && (code->get_debug_item() != nullptr)) {
    const auto* debug_item = code->get_debug_item();
    const auto param_names = debug_item->get_param_names();
    if (idx < param_names.size() && param_names[idx] != nullptr) {
      return param_names[idx]->str();
    }
  }
  auto* anno_type = DexType::get_type("Ldalvik/annotation/MethodParameters;");
  if (anno_type == nullptr) {
    return std::nullopt;
  }

  // We are looking for MethodParameters, which is on the method, not the
  // param.
  const auto* method_annos = m->get_anno_set();
  if (method_annos == nullptr) {
    return std::nullopt;
  }

  const auto* anno = [&]() -> const DexAnnotation* {
    for (const auto& method_anno : method_annos->get_annotations()) {
      if (method_anno->type() == anno_type) {
        return method_anno.get();
      }
    }
    return nullptr;
  }();
  if (anno == nullptr) {
    return std::nullopt;
  }

  const auto* names = [&]() -> const DexEncodedValueArray* {
    for (const auto& elem : anno->anno_elems()) {
      if (elem.string->str() != "names") {
        continue;
      }
      if (elem.encoded_value == nullptr) {
        return nullptr;
      }
      if (elem.encoded_value->evtype() != DEVT_ARRAY) {
        return nullptr;
      }
      return reinterpret_cast<const DexEncodedValueArray*>(
          elem.encoded_value.get());
    }
    return nullptr;
  }();
  if (names == nullptr) {
    return std::nullopt;
  }
  always_assert(names->evalues() != nullptr);

  if (names->evalues()->size() <= idx) {
    return std::nullopt;
  }
  auto& idx_val = names->evalues()->at(idx);
  if (idx_val->evtype() != DEVT_STRING) {
    return std::nullopt;
  }
  return reinterpret_cast<const DexEncodedValueString*>(idx_val.get())
      ->string()
      ->str();
}

}; // namespace method
