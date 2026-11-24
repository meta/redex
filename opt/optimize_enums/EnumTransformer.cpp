/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumTransformer.h"

#include <vector>

#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexEncoding.h"
#include "DexUtil.h"
#include "EnumUpcastAnalysis.h"
#include "EnumUtilsHolders.h"
#include "Mutators.h"
#include "OptData.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeInference.h"
#include "TypeReference.h"
#include "UsedVarsAnalysis.h"
#include "Walkers.h"

/**
 * We already get a set of candidate enums which are safe to be replaced with
 * Integer objects from EnumUpcastAnalysis, we do the transformation in the
 * EnumTransformer in following steps.
 * 1. Create enum helper classes, LEnumUtils; and, when the values are split,
 * LEnumUtils$1; ..., with some helper methods and singleton Integer fields,
 * Integer f0, f1, f2 ....
 * 2. Update instructions.
 *  -- invoke-virtual LCandidateEnum;.ordinal()I =>
 *                    Ljava/lang/Integer;.intValue:()I
 *  -- invoke-static LCandidateEnum;.values():[LCandidateEnum; =>
 *                   LEnumUtils;.values(I)[Integer
 *  -- invoke-virtual LCandidateEnum;.compareTo:(Object)I =>
 *                    Ljava/lang/Integer;.compareTo:(Integer)I
 *  -- invoke-virtual LCandidateEnum;.equals:(Object)Z =>
 *                    Ljava/lang/Integer;.equals:(Object)Z
 *  -- sget-object LCandidateEnum;.f:LCandidateEnum; =>
 *                 LEnumUtils;.f?:Ljava/lang/Integer;
 *       or construct a new integer if the enum is allowed to be optimized
 *       unsafely.
 *  -- invoke-virtual LCandidateEnum;.name:()String =>
 *                    LCandidateEnum;.redex$OE$name:(Integer)String
 *  -- invoke-virtual LCandidateEnum;.hashCode:()I =>
 *                    LCandidateEnum;.redex$OE$hashCode:(Integer)I
 *  -- invoke-static LCandidateEnum;.valueOf:(String)LCandidateEnum; =>
 *                   LCandidateEnum;.redex$OE$valueOf:(String)Integer
 *
 *  If CandidateEnum.toString() overrides Enum.toString()
 *  -- invoke-virtual LCandidateEnum;.toString:()String =>
 *                    LCandidateEnum;.toString$REDEX$YCYa1bLthVk:(Integer)String
 *  otherwise
 *  -- invoke-virtual LCandidateEnum;.toString:()String =>
 *                    LCandidateEnum;.redex$OE$name:(Integer)String
 *
 *  We also make all virtual methods and instance direct methods to be static
 * and keep them in their original class while also changing their invocations
 * to static.
 * 3. Clean up the static fields of candidate enums and update these enum
 * classes to inherit java.lang.Object instead of java.lang.Enum.
 * 4. Update specs of methods and fields based on name mangling.
 */

namespace {
using namespace optimize_enums;
using namespace dex_asm;
using EnumAttributeMap = UnorderedMap<const DexType*, EnumAttributes>;
namespace ptrs = local_pointers;

/**
 * A structure holding the enum utils and constant values.
 */
struct EnumUtil {
  std::vector<DexFieldRef*> m_fields;

  // Store the needed helper methods for toString(), valueOf() and other
  // invocations at Code transformation phase, then implement these methods
  // later. Also stores the source block at the callsite to duplicate into these
  // methods.
  ConcurrentMap<DexMethodRef*, std::unique_ptr<SourceBlock>>
      m_substitute_methods;

  // Store virtual and direct methods of candidate enums that will be
  // made static later.
  ConcurrentSet<DexMethod*> m_instance_methods;

  // Store methods for getting instance fields to be generated later.
  InsertOnlyConcurrentMap<DexFieldRef*, DexMethodRef*>
      m_get_instance_field_methods;

  DexMethodRef* m_values_method_ref = nullptr;
  size_t m_num_holders{0};

  const Config& m_config;

  const DexString* CLINIT_METHOD_STR = DexString::make_string("<clinit>");
  const DexString* REDEX_NAME = DexString::make_string("redex$OE$name");
  const DexString* REDEX_HASHCODE = DexString::make_string("redex$OE$hashCode");
  const DexString* REDEX_STRING_VALUEOF =
      DexString::make_string("redex$OE$String_valueOf");
  const DexString* REDEX_VALUEOF = DexString::make_string("redex$OE$valueOf");
  const DexString* INIT_METHOD_STR = DexString::make_string("<init>");
  const DexString* VALUES_METHOD_STR = DexString::make_string("values");
  const DexString* VALUEOF_METHOD_STR = DexString::make_string("valueOf");

  const DexType* ENUM_TYPE = type::java_lang_Enum();
  DexType* INT_TYPE = type::_int();
  DexType* INTEGER_TYPE = type::java_lang_Integer();
  DexType* OBJECT_TYPE = type::java_lang_Object();
  DexType* STRING_TYPE = type::java_lang_String();
  DexType* SERIALIZABLE_TYPE = DexType::make_type("Ljava/io/Serializable;");
  DexType* COMPARABLE_TYPE = DexType::make_type("Ljava/lang/Comparable;");
  DexType* RTEXCEPTION_TYPE = type::java_lang_RuntimeException();
  DexType* ILLEGAL_ARG_EXCP_TYPE =
      DexType::make_type("Ljava/lang/IllegalArgumentException;");

  const DexMethodRef* ENUM_ORDINAL_METHOD = method::java_lang_Enum_ordinal();
  const DexMethodRef* ENUM_EQUALS_METHOD = method::java_lang_Enum_equals();
  const DexMethodRef* ENUM_COMPARETO_METHOD =
      method::java_lang_Enum_compareTo();
  const DexMethodRef* ENUM_TOSTRING_METHOD = method::java_lang_Enum_toString();
  const DexMethodRef* ENUM_HASHCODE_METHOD = method::java_lang_Enum_hashCode();
  const DexMethodRef* ENUM_NAME_METHOD = method::java_lang_Enum_name();
  const DexMethodRef* STRING_VALUEOF_METHOD = DexMethod::make_method(
      "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;");
  const DexMethodRef* STRINGBUILDER_APPEND_OBJ_METHOD = DexMethod::make_method(
      "Ljava/lang/StringBuilder;.append:(Ljava/lang/Object;)Ljava/lang/"
      "StringBuilder;");
  DexMethodRef* STRINGBUILDER_APPEND_STR_METHOD =
      method::java_lang_StringBuilder_append_String();
  DexMethodRef* INTEGER_INTVALUE_METHOD = method::java_lang_Integer_intValue();
  DexMethodRef* INTEGER_EQUALS_METHOD = DexMethod::make_method(
      "Ljava/lang/Integer;.equals:(Ljava/lang/Object;)Z");
  DexMethodRef* INTEGER_COMPARETO_METHOD = DexMethod::make_method(
      "Ljava/lang/Integer;.compareTo:(Ljava/lang/Integer;)I");
  DexMethodRef* INTEGER_VALUEOF_METHOD = method::java_lang_Integer_valueOf();
  DexMethodRef* ILLEGAL_ARG_CONSTRUCT_METHOD = DexMethod::make_method(
      "Ljava/lang/IllegalArgumentException;.<init>:(Ljava/lang/String;)V");
  DexMethodRef* STRING_EQ_METHOD =
      DexMethod::make_method("Ljava/lang/String;.equals:(Ljava/lang/Object;)Z");

  InsertOnlyConcurrentMap<DexClass*, DexMethod*>
      m_user_defined_tostring_method_cache;

  explicit EnumUtil(const Config& config) : m_config(config) {}

  void create_util_class(DexStoresVector* stores, uint32_t fields_count) {
    auto classes =
        make_enumutils_classes(std::min(fields_count, m_config.max_enum_size));
    m_num_holders = classes.size();
    auto& dexen = (*stores)[0].get_dexen()[0];
    dexen.insert(dexen.end(), classes.begin(), classes.end());
  }

  bool is_super_type_of_candidate_enum(const DexType* type) {
    return type == ENUM_TYPE || type == OBJECT_TYPE ||
           type == SERIALIZABLE_TYPE || type == COMPARABLE_TYPE;
  }

  void collect_callsite_source_blocks(DexMethodRef* method,
                                      SourceBlock* prev_sb) {
    m_substitute_methods.update(
        method, [method, prev_sb](auto&, auto& value, bool exists) {
          if (!exists || value == nullptr) {
            if (prev_sb == nullptr) {
              value = nullptr;
            } else {
              std::unique_ptr<SourceBlock> synthetic_block =
                  source_blocks::clone_as_synthetic(prev_sb, method->as_def());
              value = std::move(synthetic_block);
            }
          } else if (prev_sb != nullptr) {
            // Distinct candidate methods' source blocks accumulate into the one
            // substitute method, so their counts must sum (appear100 maxes).
            value->add(*prev_sb);
          }
        });
  }

  /**
   * IF LCandidateEnum; is a candidate enum:
   *  LCandidateEnum; => Ljava/lang/Integer;
   *  [LCandidateEnum; => [Ljava/lang/Integer;
   *  [[LCandidateEnum; => [[Ljava/lang/Integer;
   *  ...
   * IF it is not a candidate enum, return nullptr.
   */
  const DexType* try_convert_to_int_type(
      const EnumAttributeMap& enum_attributes_map, const DexType* type) const {
    uint32_t level = type::get_array_level(type);
    const DexType* elem_type = type;
    if (level != 0u) {
      elem_type = type::make_array_element_type(type);
    }
    if (enum_attributes_map.count(elem_type) != 0u) {
      return level != 0u ? type::make_array_type(INTEGER_TYPE, level)
                         : INTEGER_TYPE;
    }
    return nullptr;
  }

  /**
   * Return method ref to
   * LCandidateEnum;.redex$OE$String_valueOf:(Integer)String, a substitute for
   * String.valueOf:(Object) while the argument is a candidate enum object.
   * Store the method ref at the same time.
   *
   * The implementation of the substitute method depends on the substitute
   * method of LCandidateEnum;.toString:()String.
   */
  DexMethodRef* add_substitute_of_stringvalueof(const DexType* enum_type,
                                                SourceBlock* prev_sb) {
    add_substitute_of_tostring(enum_type, prev_sb);
    auto* proto = DexProto::make_proto(
        STRING_TYPE, DexTypeList::make_type_list({INTEGER_TYPE}));
    auto* method =
        DexMethod::make_method(enum_type, REDEX_STRING_VALUEOF, proto);
    collect_callsite_source_blocks(method, prev_sb);
    return method;
  }

  /**
   * Return method ref to LCandidateEnum;.redex$OE$valueOf(String):Integer, a
   * substitute for LCandidateEnum;.valueOf:(String)LCandidateEnum;.
   * Store the method ref at the same time.
   */
  DexMethodRef* add_substitute_of_valueof(DexType* enum_type,
                                          SourceBlock* prev_sb) {
    auto* proto = DexProto::make_proto(
        INTEGER_TYPE, DexTypeList::make_type_list({STRING_TYPE}));
    auto* method = DexMethod::make_method(enum_type, REDEX_VALUEOF, proto);
    collect_callsite_source_blocks(method, prev_sb);
    return method;
  }

  /**
   * If `Enum.toString` is not overridden, return method ref to
   * LCandidateEnum;.redex$OE$name:(Integer)String, a substitute for
   * LCandidateEnum;.toString:()String. Otherwise return the overriding method.
   * Store the method ref at the same time.
   */
  DexMethodRef* add_substitute_of_tostring(const DexType* enum_type,
                                           SourceBlock* prev_sb) {
    auto* method_ref = get_user_defined_tostring_method(type_class(enum_type));
    if (method_ref == nullptr) {
      return add_substitute_of_name(enum_type, prev_sb);
    } else {
      auto* method =
          resolve_method_deprecated(method_ref, MethodSearch::Virtual);
      always_assert(method);
      return method_ref;
    }
  }

  /**
   * If `Enum.toString` is not overridden, return method ref to
   * LCandidateEnum;.redex$OE$name:(Integer)String. Otherwise return the
   * overriding method.
   */
  DexMethodRef* get_substitute_of_tostring(DexType* enum_type) {
    DexMethodRef* method =
        get_user_defined_tostring_method(type_class(enum_type));
    if (method == nullptr) {
      return get_substitute_of_name(enum_type);
    }
    return method;
  }

  /**
   * Return method ref to LCandidateEnum;.redex$OE$name:(Integer)String, a
   * substitute for LCandidateEnum;.name:()String.
   * Store the method ref at the same time.
   */
  DexMethodRef* add_substitute_of_name(const DexType* enum_type,
                                       SourceBlock* prev_sb) {
    auto* method = get_substitute_of_name(enum_type);
    collect_callsite_source_blocks(method, prev_sb);
    return method;
  }

  /**
   * Return method ref to LCandidateEnum;.redex$OE$name:(Integer)String
   */
  DexMethodRef* get_substitute_of_name(const DexType* enum_type) {
    auto* proto = DexProto::make_proto(
        STRING_TYPE, DexTypeList::make_type_list({INTEGER_TYPE}));
    auto* method = DexMethod::make_method(enum_type, REDEX_NAME, proto);
    return method;
  }

  /**
   * Returns a method ref to LCandidateEnum;.redex$OE$hashCode:(Integer)I, a
   * substitute for LCandidateEnum;.hashCode:()I.
   * Store the method ref at the same time.
   */
  DexMethodRef* add_substitute_of_hashcode(const DexType* enum_type,
                                           SourceBlock* prev_sb) {
    auto* method = get_substitute_of_hashcode(enum_type);
    collect_callsite_source_blocks(method, prev_sb);
    return method;
  }

  /**
   * Returns a method ref to LCandidateEnum;.redex$OE$hashCode:(Integer)I
   */
  DexMethodRef* get_substitute_of_hashcode(const DexType* enum_type) {
    auto* proto = DexProto::make_proto(
        INT_TYPE, DexTypeList::make_type_list({INTEGER_TYPE}));
    auto* method = DexMethod::make_method(enum_type, REDEX_HASHCODE, proto);
    return method;
  }

  /**
   * Returns a method ref to LCandidateEnum;.redex$OE$get_iField:(Integer)X
   * where `X` is the type of the instance field `iField`.
   * Store the method ref at the same time.
   */
  DexMethodRef* add_get_ifield_method(DexType* enum_type, DexFieldRef* ifield) {
    return *m_get_instance_field_methods
                .get_or_create_and_assert_equal(
                    ifield,
                    [&](auto*) {
                      auto* proto = DexProto::make_proto(
                          ifield->get_type(),
                          DexTypeList::make_type_list({INTEGER_TYPE}));
                      const auto* method_name = DexString::make_string(
                          "redex$OE$get_" + ifield->str());
                      return DexMethod::make_method(enum_type, method_name,
                                                    proto);
                    })
                .first;
  }

  /**
   * Returns the `LCandidateEnum.toString()` method that overrides
   * `Enum.toString()`. Return `nullptr` if `Enum.toString()` is not overridden.
   */
  DexMethod* get_user_defined_tostring_method(DexClass* cls) {
    return *m_user_defined_tostring_method_cache
                .get_or_create_and_assert_equal(
                    cls,
                    [&](auto*) -> DexMethod* {
                      for (auto* vmethod : cls->get_vmethods()) {
                        if (method::signatures_match(vmethod,
                                                     ENUM_TOSTRING_METHOD)) {
                          return vmethod;
                        }
                      }
                      return nullptr;
                    })
                .first;
  }

 private:
  /**
   * A holder class for the boxed values [first, first + count): one fN field
   * per value and a $VALUES array of the same objects, both filled in
   * <clinit>.
   */
  struct Holder {
    DexClass* cls;
    DexFieldRef* values_field;
    uint32_t first;
    uint32_t count;
    std::vector<DexFieldRef*> fields;
  };

  /**
   * Create the helper classes holding the boxed values [0, fields_count).
   * With a positive `enum_utils_split_size`, each block of that many values
   * gets a class of its own, which the runtime initializes only when code
   * first reads one of its fields or values() needs its block. Otherwise one
   * class holds every value.
   */
  std::vector<DexClass*> make_enumutils_classes(uint32_t fields_count) {
    // Note that the EnumUtilsFieldAnalyzer recognizes the fXXX fields of these
    // classes through enum_utils, which names them.
    const uint32_t split_size = m_config.enum_utils_split_size;
    uint32_t num_holders = 1;
    if (split_size != 0 && fields_count > split_size) {
      num_holders = (fields_count + split_size - 1) / split_size;
    }
    const std::string family = enum_utils::unused_family(num_holders);

    std::vector<Holder> holders;
    holders.reserve(num_holders);
    m_fields.reserve(fields_count);
    for (uint32_t chunk = 0; chunk < num_holders; ++chunk) {
      uint32_t first = chunk * split_size;
      uint32_t count = num_holders == 1
                           ? fields_count
                           : std::min(split_size, fields_count - first);
      auto& holder = holders.emplace_back(make_holder_class(
          enum_utils::holder_name(family, chunk), first, count));
      m_fields.insert(m_fields.end(), holder.fields.begin(),
                      holder.fields.end());
    }
    // m_fields is indexed by value.
    redex_assert(m_fields.size() == fields_count);
    m_values_method_ref = make_values_method(holders, fields_count);

    std::vector<DexClass*> classes;
    classes.reserve(holders.size());
    for (const auto& holder : holders) {
      classes.push_back(holder.cls);
    }
    return classes;
  }

  Holder make_holder_class(const std::string& name,
                           uint32_t first,
                           uint32_t count) {
    DexType* type = DexType::make_type(name);
    ClassCreator cc(type);
    cc.set_access(ACC_PUBLIC | ACC_FINAL);
    cc.set_super(type::java_lang_Object());
    DexClass* cls = cc.create();
    cls->rstate.set_generated();
    cls->rstate.set_clinit_has_no_side_effects();

    // values() in the first holder reads the other holders' arrays.
    auto* values_field =
        make_values_field(cls, first == 0 ? ACC_PRIVATE : ACC_PUBLIC);
    auto* clinit_method = make_clinit_method(cls, count);
    auto* clinit_code = clinit_method->get_code();
    std::vector<DexFieldRef*> fields;
    fields.reserve(count);
    for (uint32_t i = 0; i < count; ++i) {
      fields.push_back(make_a_field(cls, first, i, clinit_code));
    }

    clinit_code->push_back(dasm(OPCODE_SPUT_OBJECT, values_field, {2_v}));
    clinit_code->push_back(dasm(OPCODE_RETURN_VOID));
    clinit_code->build_cfg();
    clinit_code->cfg().recompute_registers_size();
    return {cls, values_field, first, count, std::move(fields)};
  }

  /**
   * LEnumUtils;.$VALUES:[Ljava/lang/Integer;
   */
  DexFieldRef* make_values_field(DexClass* cls, DexAccessFlags visibility) {
    const auto* name = DexString::make_string("$VALUES");
    auto* field = DexField::make_field(cls->get_type(), name,
                                       type::make_array_type(INTEGER_TYPE))
                      ->make_concrete(visibility | ACC_FINAL | ACC_STATIC);
    cls->add_field(field);
    field->set_deobfuscated_name(show_deobfuscated(field));
    return (DexFieldRef*)field;
  }

  /**
   * Create a static final Integer field for the value `first + index` and
   * update the <clinit> code of the holder whose values start at `first` to
   * store it into the field and into $VALUES[index].
   */
  DexFieldRef* make_a_field(DexClass* cls,
                            uint32_t first,
                            uint32_t index,
                            IRCode* code) {
    uint32_t value = first + index;
    // Note that the EnumUtilsFieldAnalyzer recognizes this field through
    // enum_utils, which names it.
    const auto* name = DexString::make_string(enum_utils::field_name(value));
    auto* field = DexField::make_field(cls->get_type(), name, INTEGER_TYPE)
                      ->make_concrete(ACC_PUBLIC | ACC_FINAL | ACC_STATIC);
    cls->add_field(field);
    field->set_deobfuscated_name(show_deobfuscated(field));
    code->push_back(dasm(OPCODE_CONST, {1_v, {LITERAL, value}}));
    code->push_back(dasm(OPCODE_INVOKE_STATIC, INTEGER_VALUEOF_METHOD, {1_v}));
    code->push_back(dasm(OPCODE_MOVE_RESULT_OBJECT, {0_v}));
    code->push_back(dasm(OPCODE_SPUT_OBJECT, field, {0_v}));
    if (first == 0) {
      code->push_back(dasm(OPCODE_APUT_OBJECT, {0_v, 2_v, 1_v}));
    } else {
      code->push_back(dasm(OPCODE_CONST, {3_v, {LITERAL, index}}));
      code->push_back(dasm(OPCODE_APUT_OBJECT, {0_v, 2_v, 3_v}));
    }
    return (DexFieldRef*)field;
  }

  /**
   * Make <clinit> method.
   */
  DexMethod* make_clinit_method(DexClass* cls, uint32_t fields_count) {
    auto* proto =
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
    DexMethod* method =
        DexMethod::make_method(cls->get_type(), CLINIT_METHOD_STR, proto)
            ->make_concrete(ACC_STATIC | ACC_CONSTRUCTOR, false);
    method->set_code(std::make_unique<IRCode>());
    cls->add_method(method);
    method->set_deobfuscated_name(show_deobfuscated(method));
    auto* code = method->get_code();

    // const v2, xx
    // new-array v2, v2, [Integer
    code->push_back(dasm(OPCODE_CONST, {2_v, {LITERAL, fields_count}}));
    code->push_back(
        dasm(OPCODE_NEW_ARRAY, type::make_array_type(INTEGER_TYPE), {2_v}));
    code->push_back(dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}));
    code->set_registers_size(3);
    return method;
  }

  /**
   * LEnumUtils;.values:(I)[Ljava/lang/Integer;
   *
   * The holders' $VALUES arrays store the integers in [0, total). Copy the
   * part of them that count needs, so that the elements are the same objects
   * as the fN fields, and construct the integers beyond them. The following
   * comments are the basic blocks of this method.
   *
   * res = new Integer[count]
   * if count <= total
   *   : small_argument_block
   *   copy_size = count
   *   goto :copy_array_block
   * else
   *   : large_argument_block
   *   copy_size = total
   *   id = copy_size
   *   goto :integers_block
   *   : integers_block
   *   if id < count
   *     : one_integer_block
   *     res[id] = Integer.valueOf(id)
   *     id = id + 1
   *     goto :integers_block
   *   else
   *     goto :copy_array_block
   * : copy_array_block
   * for each holder, while copy_size > holder.first:
   *   System.arraycopy(holder.$VALUES, 0, res, holder.first,
   *                    min(copy_size - holder.first, holder.count))
   * return res
   *
   * A holder reached only when copy_size exceeds its first value is
   * initialized only then.
   */
  DexMethodRef* make_values_method(const std::vector<Holder>& holders,
                                   uint32_t total_integer_fields) {
    always_assert(!holders.empty());
    auto* cls = holders.front().cls;
    const auto* name = DexString::make_string("values");
    auto* integer_array_type = type::make_array_type(INTEGER_TYPE);
    DexProto* proto = DexProto::make_proto(
        integer_array_type, DexTypeList::make_type_list({type::_int()}));
    DexMethod* method = DexMethod::make_method(cls->get_type(), name, proto)
                            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(std::make_unique<IRCode>(method, 0));
    cls->add_method(method);
    method->set_deobfuscated_name(show_deobfuscated(method));
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    auto* entry = cfg.entry_block();
    auto* small_argument_block = cfg.create_block();
    auto* large_argument_block = cfg.create_block();
    auto* one_integer_block = cfg.create_block();
    auto* integers_block = cfg.create_block();
    auto* copy_array_block = cfg.create_block();
    cfg.add_edge(small_argument_block, copy_array_block, cfg::EDGE_GOTO);
    cfg.add_edge(large_argument_block, integers_block, cfg::EDGE_GOTO);
    cfg.add_edge(one_integer_block, integers_block, cfg::EDGE_GOTO);

    entry->push_back(
        {dasm(OPCODE_NEW_ARRAY, integer_array_type, {0_v}),
         dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
         dasm(OPCODE_CONST, {2_v, {LITERAL, total_integer_fields}})});
    cfg.create_branch(entry, dasm(OPCODE_IF_LE, {0_v, 2_v}),
                      large_argument_block, small_argument_block);

    small_argument_block->push_back(dasm(OPCODE_MOVE, {4_v, 0_v}));

    large_argument_block->push_back(
        {dasm(OPCODE_MOVE, {4_v, 2_v}), dasm(OPCODE_MOVE, {5_v, 2_v})});
    cfg.create_branch(integers_block, dasm(OPCODE_IF_LT, {5_v, 0_v}),
                      copy_array_block, one_integer_block);

    one_integer_block->push_back(
        {dasm(OPCODE_INVOKE_STATIC, INTEGER_VALUEOF_METHOD, {5_v}),
         dasm(OPCODE_MOVE_RESULT_OBJECT, {6_v}),
         dasm(OPCODE_APUT_OBJECT, {6_v, 1_v, 5_v}),
         dasm(OPCODE_ADD_INT_LIT, {5_v, 5_v, 1_L})});

    append_copy_holders(cfg, copy_array_block, holders, total_integer_fields);
    cfg.recompute_registers_size();
    return (DexMethodRef*)method;
  }

  /**
   * Append to `block` the copies out of each holder's $VALUES for values() and
   * its return, in registers v4 (copy_size) and v1 (res). A holder whose first
   * value is not below copy_size is not read. Uses v7 for a $VALUES array, v8
   * for zero, v9 for a holder's first value, v10 for a copy length, and v11 for
   * a holder's size; a single holder needs only v7 and v8.
   */
  void append_copy_holders(cfg::ControlFlowGraph& cfg,
                           cfg::Block* block,
                           const std::vector<Holder>& holders,
                           uint32_t total_integer_fields) {
    auto* copy_array_method = DexMethod::make_method(
        "Ljava/lang/System;.arraycopy:(Ljava/lang/Object;ILjava/lang/"
        "Object;II)V");
    cfg::Block* return_block = nullptr;
    for (size_t i = 0; i < holders.size(); ++i) {
      const auto& holder = holders[i];
      // Without a later holder, copy_size - first never exceeds count.
      bool needs_clamp = holder.first + holder.count < total_integer_fields;
      Operand dest = 8_v;
      Operand length = 4_v;
      if (holder.first != 0) {
        if (return_block == nullptr) {
          return_block = cfg.create_block();
          return_block->push_back(dasm(OPCODE_RETURN_OBJECT, {1_v}));
        }
        auto* next = cfg.create_block();
        block->push_back(dasm(OPCODE_CONST, {9_v, {LITERAL, holder.first}}));
        cfg.create_branch(block, dasm(OPCODE_IF_LE, {4_v, 9_v}), next,
                          return_block);
        block = next;
        block->push_back(dasm(OPCODE_SUB_INT, {10_v, 4_v, 9_v}));
        dest = 9_v;
        length = 10_v;
      } else if (needs_clamp) {
        block->push_back(dasm(OPCODE_MOVE, {10_v, 4_v}));
        length = 10_v;
      }
      if (needs_clamp) {
        auto* clamp_block = cfg.create_block();
        auto* copy_block = cfg.create_block();
        block->push_back(dasm(OPCODE_CONST, {11_v, {LITERAL, holder.count}}));
        // Clamp a length above the holder's size.
        cfg.create_branch(block, dasm(OPCODE_IF_LE, {10_v, 11_v}), clamp_block,
                          copy_block);
        clamp_block->push_back(dasm(OPCODE_MOVE, {10_v, 11_v}));
        cfg.add_edge(clamp_block, copy_block, cfg::EDGE_GOTO);
        block = copy_block;
      }
      block->push_back({dasm(OPCODE_SGET_OBJECT, holder.values_field),
                        dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {7_v}),
                        dasm(OPCODE_CONST, {8_v, 0_L}),
                        dasm(OPCODE_INVOKE_STATIC, copy_array_method,
                             {7_v, 8_v, 1_v, dest, length})});
      if (i + 1 == holders.size()) {
        block->push_back(dasm(OPCODE_RETURN_OBJECT, {1_v}));
      } else {
        auto* next = cfg.create_block();
        cfg.add_edge(block, next, cfg::EDGE_GOTO);
        block = next;
      }
    }
  }
};

struct InsnReplacement {
  cfg::InstructionIterator original_insn;
  std::vector<IRInstruction*> replacements;

  InsnReplacement(cfg::ControlFlowGraph& cfg,
                  cfg::Block* block,
                  MethodItemEntry* mie,
                  IRInstruction* new_insn)
      : original_insn(block->to_cfg_instruction_iterator(*mie)),
        replacements{new_insn} {
    push_back_move_result(cfg, new_insn);
  }
  InsnReplacement(cfg::ControlFlowGraph& cfg,
                  cfg::Block* block,
                  MethodItemEntry* mie,
                  std::vector<IRInstruction*>& new_insns)
      : original_insn(block->to_cfg_instruction_iterator(*mie)),
        replacements(std::move(new_insns)) {
    if (!replacements.empty()) {
      auto* new_insn = *replacements.rbegin();
      push_back_move_result(cfg, new_insn);
    }
  }

 private:
  /**
   * If the original instruction was paired with a `move-result`, create a new
   * one with the same destination register (and possibly the same opcode)
   * because the original one will be removed.
   */
  void push_back_move_result(cfg::ControlFlowGraph& cfg,
                             IRInstruction* new_insn) {
    auto org_move_insn_it = cfg.move_result_of(original_insn);
    if (!org_move_insn_it.is_end()) {
      auto& org_move_insn = org_move_insn_it.unwrap()->insn;
      auto& org_insn = original_insn.unwrap()->insn;
      auto org_op = org_move_insn->opcode();

      auto dest = org_move_insn->dest();
      IROpcode new_op = org_op;
      if (org_insn->has_move_result() && new_insn->has_move_result_pseudo()) {
        new_op = opcode::move_result_to_pseudo(org_op);
      } else if (org_insn->has_move_result_pseudo() &&
                 new_insn->has_move_result()) {
        new_op = opcode::pseudo_to_move_result(org_op);
      }
      replacements.push_back(dasm(new_op, {{VREG, dest}}));
    }
  }
};

/**
 * Code transformation for a method.
 */
class CodeTransformer final {
 public:
  CodeTransformer(const EnumAttributeMap& m_enum_attributes_map,
                  EnumUtil* enum_util,
                  DexMethod* method)
      : m_enum_attributes_map(m_enum_attributes_map),
        m_enum_util(enum_util),
        m_method(method) {}

  void run() {
    optimize_enums::EnumTypeEnvironment start_env =
        optimize_enums::EnumFixpointIterator::gen_env(m_method);
    cfg::ControlFlowGraph& cfg = m_method->get_code()->cfg();
    optimize_enums::EnumFixpointIterator engine(cfg, m_enum_util->m_config);
    engine.run(start_env);
    // What the verifier knows about each register, before any rewriting.
    type_inference::TypeInference verifier_types(cfg);
    verifier_types.run(m_method);
    m_verifier_envs = &verifier_types.get_type_environments();
    for (auto& block : cfg.blocks()) {
      optimize_enums::EnumTypeEnvironment env =
          engine.get_entry_state_at(block);
      SourceBlock* prev_sb = nullptr;
      for (auto it = block->begin(); it != block->end(); ++it) {
        if (it->type == MFLOW_SOURCE_BLOCK) {
          prev_sb = it->src_block.get();
        }
        if (it->type == MFLOW_OPCODE) {
          engine.analyze_instruction(it->insn, &env);
          // NOLINTNEXTLINE
          update_instructions(env, cfg, block, &(*it), prev_sb);
        }
      }
    }
    m_verifier_envs = nullptr;
    auto casts = find_integer_cast_positions();

    // We could not insert invoke-kind instructions to cfg when we
    // iterate the cfg. If we're inside a try region, inserting invoke-kind will
    // split the block and insert a move-result in the new goto successor block,
    // thus invalidating iterators into the CFG. See the comment on the
    // insertion methods in ControlFlow.h for more details.
    for (const auto& info : m_replacements) {
      cfg.replace_insns(info.original_insn, info.replacements);
    }
    insert_integer_casts(cfg, casts);
  }

 private:
  /**
   * Record that the rewritten form of `insn` takes the value of its source
   * `src_index` as an Integer. The verifier knows that value as an Integer if
   * it knew it as a candidate enum, which becomes Integer, as an Integer or as
   * null. Any other reference needs a cast. The analysis may know more about a
   * value than the verifier does: given `static Object identity(Object x)`,
   * whose parameter summary says it returns its argument, the analysis types
   * `identity(E.A)` as E, while the verifier types it as Object.
   */
  void require_integer(IRInstruction* insn, src_index_t src_index) {
    const auto reg = insn->src(src_index);
    const auto& verifier_env = m_verifier_envs->at(insn);
    // A `const 0` stays null to the verifier even after a use as a reference
    // makes TypeInference call it one.
    if (!verifier_env.get_type(reg).equals(
            type_inference::TypeDomain(IRType::REFERENCE)) ||
        verifier_env.get_type_domain(reg).is_null()) {
      return;
    }
    const auto verifier_type = verifier_env.get_dex_type(reg);
    if (verifier_type && (*verifier_type == type::java_lang_Integer() ||
                          m_enum_attributes_map.count(*verifier_type) != 0u)) {
      return;
    }
    m_integer_casts.emplace_back(insn, reg);
  }

  /**
   * The registers to cast to Integer, by the instruction to cast them before:
   * each use recorded by require_integer, or the first instruction of its
   * replacement. Must run before the replacements, whose original
   * instructions the uses refer to.
   */
  UnorderedMap<const IRInstruction*, std::vector<reg_t>>
  find_integer_cast_positions() const {
    UnorderedMap<const IRInstruction*, std::vector<reg_t>> casts;
    if (m_integer_casts.empty()) {
      return casts;
    }
    UnorderedMap<const IRInstruction*, const IRInstruction*> replaced_by;
    for (const auto& info : m_replacements) {
      if (!info.replacements.empty()) {
        replaced_by.emplace(info.original_insn->insn,
                            info.replacements.front());
      }
    }
    for (const auto& [use, reg] : m_integer_casts) {
      auto it = replaced_by.find(use);
      auto& regs = casts[it == replaced_by.end() ? use : it->second];
      if (std::find(regs.begin(), regs.end(), reg) == regs.end()) {
        regs.push_back(reg);
      }
    }
    return casts;
  }

  /**
   * Cast each register in `casts` to Integer right before its instruction.
   * The cast cannot fail: the analysis proved the value is a candidate enum
   * or null, which the transformation turns into an Integer or null.
   */
  void insert_integer_casts(
      cfg::ControlFlowGraph& cfg,
      const UnorderedMap<const IRInstruction*, std::vector<reg_t>>& casts) {
    if (casts.empty()) {
      return;
    }
    cfg::CFGMutation mutation(cfg);
    size_t found = 0;
    auto ii = cfg::InstructionIterable(cfg);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto casts_it = casts.find(it->insn);
      if (casts_it == casts.end()) {
        continue;
      }
      ++found;
      for (auto reg : casts_it->second) {
        mutation.insert_before(it,
                               make_check_cast(type::java_lang_Integer(), reg));
      }
    }
    always_assert_log(found == casts.size(),
                      "%zu of %zu instructions to cast before are gone in %s",
                      found, casts.size(), SHOW(m_method));
    mutation.flush();
  }

  void update_instructions(const optimize_enums::EnumTypeEnvironment& env,
                           cfg::ControlFlowGraph& cfg,
                           cfg::Block* block,
                           MethodItemEntry* mie,
                           SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    switch (insn->opcode()) {
    case OPCODE_SGET_OBJECT:
      update_sget_object(cfg, block, mie);
      break;
    case OPCODE_IGET:
    case OPCODE_IGET_WIDE:
    case OPCODE_IGET_OBJECT:
    case OPCODE_IGET_BOOLEAN:
    case OPCODE_IGET_BYTE:
    case OPCODE_IGET_CHAR:
    case OPCODE_IGET_SHORT:
      update_iget(cfg, block, mie);
      break;
    case OPCODE_INVOKE_VIRTUAL: {
      auto* method = insn->get_method();
      if (method::signatures_match(method, m_enum_util->ENUM_ORDINAL_METHOD)) {
        update_invoke_virtual(env, cfg, block, mie,
                              m_enum_util->INTEGER_INTVALUE_METHOD);
      } else if (method::signatures_match(method,
                                          m_enum_util->ENUM_EQUALS_METHOD)) {
        update_invoke_virtual(env, cfg, block, mie,
                              m_enum_util->INTEGER_EQUALS_METHOD);
      } else if (method::signatures_match(method,
                                          m_enum_util->ENUM_COMPARETO_METHOD)) {
        update_invoke_virtual(env, cfg, block, mie,
                              m_enum_util->INTEGER_COMPARETO_METHOD);
      } else if (method::signatures_match(method,
                                          m_enum_util->ENUM_NAME_METHOD)) {
        update_invoke_name(env, cfg, block, mie, prev_sb);
      } else if (method::signatures_match(method,
                                          m_enum_util->ENUM_HASHCODE_METHOD)) {
        update_invoke_hashcode(env, cfg, block, mie, prev_sb);
      } else if (method == m_enum_util->STRINGBUILDER_APPEND_OBJ_METHOD) {
        update_invoke_stringbuilder_append(env, cfg, block, mie, prev_sb);
      } else {
        update_invoke_user_method(env, cfg, block, mie, prev_sb);
      }
    } break;
    case OPCODE_INVOKE_DIRECT: {
      auto* method = insn->get_method();
      if (!method::is_init(method)) {
        update_invoke_user_method(env, cfg, block, mie, prev_sb);
      }
    } break;
    case OPCODE_INVOKE_STATIC: {
      auto* method = insn->get_method();
      if (method == m_enum_util->STRING_VALUEOF_METHOD) {
        update_invoke_string_valueof(env, cfg, block, mie, prev_sb);
      } else if (is_enum_values(method)) {
        update_invoke_values(env, cfg, block, mie);
      } else if (is_enum_valueof(method)) {
        update_invoke_valueof(env, cfg, block, mie, prev_sb);
      }
    } break;
    case OPCODE_NEW_ARRAY:
    case OPCODE_FILLED_NEW_ARRAY: {
      const auto* array_type = insn->get_type();
      const auto* new_type = try_convert_to_int_type(array_type);
      if (new_type != nullptr) {
        insn->set_type(new_type);
      }
    } break;
    case OPCODE_CHECK_CAST: {
      const auto* type = insn->get_type();
      const auto* new_type = try_convert_to_int_type(type);
      if (new_type != nullptr) {
        const auto& possible_src_types = env.get(insn->src(0));
        if (!possible_src_types.empty()) {
          const DexType* candidate_type =
              extract_candidate_enum_type(possible_src_types);
          always_assert(candidate_type == type);
        }
        // Empty src_types means the src register holds null object.
        insn->set_type(new_type);
      } else if (type == m_enum_util->ENUM_TYPE) {
        always_assert(!extract_candidate_enum_type(env.get(insn->src(0))));
      }
    } break;
    default: {
      if (insn->has_type() && insn->opcode() != IOPCODE_INIT_CLASS) {
        const auto* type = insn->get_type();
        always_assert_log(try_convert_to_int_type(type) == nullptr,
                          "Unhandled type %s in %s method %s\n", SHOW(type),
                          SHOW(insn), SHOW(m_method));
      }
    } break;
    }
  }

  /**
   * If the field is a candidate enum field,
   * sget-object LCandidateEnum;.f:LCandidateEnum; =>
   *   sget-object LEnumUtils;.f?:Integer
   * or
   *   const v_ordinal #??
   *   invoke-static v_ordinal Integer.valueOf:(I)Integer
   */
  void update_sget_object(cfg::ControlFlowGraph& cfg,
                          cfg::Block* block,
                          MethodItemEntry* mie) {
    auto* insn = mie->insn;
    auto* field = insn->get_field();
    if (m_enum_attributes_map.count(field->get_type()) == 0u) {
      return;
    }
    const auto& constants =
        m_enum_attributes_map.at(field->get_type()).m_constants_map;
    if (constants.count(field) == 0u) {
      return;
    }
    uint32_t ordinal = constants.at(field).ordinal;
    if (ordinal < m_enum_util->m_config.max_enum_size) {
      auto* new_field = m_enum_util->m_fields.at(constants.at(field).ordinal);
      auto* new_insn = dasm(OPCODE_SGET_OBJECT, new_field);
      m_replacements.emplace_back(cfg, block, mie, new_insn);
    } else {
      always_assert(
          m_enum_util->m_config.breaking_reference_equality_allowlist.count(
              field->get_type()));
      auto ordinal_reg = allocate_temp();
      std::vector<IRInstruction*> new_insns;
      new_insns.push_back(
          dasm(OPCODE_CONST, {{VREG, ordinal_reg}, {LITERAL, ordinal}}));
      new_insns.push_back(dasm(OPCODE_INVOKE_STATIC,
                               m_enum_util->INTEGER_VALUEOF_METHOD,
                               {{VREG, ordinal_reg}}));
      m_replacements.emplace_back(cfg, block, mie, new_insns);
    }
  }

  /**
   * If the instance field belongs to a CandidateEnum, replace the `iget`
   * instruction with a static call to the correct method.
   *
   * iget(-object|-wide)? vObj LCandidateEnum;.iField:Ltype;
   * move-result-pseudo vDest
   * =>
   * invoke-static {vObj}, LCandidateEnum;.redex$OE$get_iField:(Integer;)Ltype;
   * move-result(-object|-wide)? vDest
   */
  void update_iget(cfg::ControlFlowGraph& cfg,
                   cfg::Block* block,
                   MethodItemEntry* mie) {
    auto* insn = mie->insn;
    auto* ifield = insn->get_field();
    auto* enum_type = ifield->get_class();
    if (m_enum_attributes_map.count(enum_type) == 0u) {
      return;
    }
    auto vObj = insn->src(0);
    auto* get_ifield_method =
        m_enum_util->add_get_ifield_method(enum_type, ifield);
    require_integer(insn, 0);
    m_replacements.emplace_back(
        cfg, block, mie,
        dasm(OPCODE_INVOKE_STATIC, get_ifield_method, {{VREG, vObj}}));
  }

  /**
   * If LCandidateEnum; is a candidate enum class,
   * invoke-static LCandidateEnum;.values:()[LCandidateEnum; =>
   *   const vn, xxx
   *   invoke-static vn LEnumUtils;.values:(I)[Integer
   */
  void update_invoke_values(const optimize_enums::EnumTypeEnvironment&,
                            cfg::ControlFlowGraph& cfg,
                            cfg::Block* block,
                            MethodItemEntry* mie) {
    auto* insn = mie->insn;
    auto* method = insn->get_method();
    auto* container = method->get_class();
    auto attributes_it = m_enum_attributes_map.find(container);
    if (attributes_it != m_enum_attributes_map.end()) {
      auto reg = allocate_temp();
      uint64_t enum_size = attributes_it->second.m_constants_map.size();
      always_assert(enum_size);
      std::vector<IRInstruction*> new_insns;
      new_insns.push_back(
          dasm(OPCODE_CONST,
               {{VREG, reg}, {LITERAL, static_cast<int64_t>(enum_size)}}));
      new_insns.push_back(dasm(OPCODE_INVOKE_STATIC,
                               m_enum_util->m_values_method_ref,
                               {{VREG, reg}}));
      m_replacements.emplace_back(cfg, block, mie, new_insns);
    }
  }

  /**
   * If LCandidateEnum; is a candidate enum class,
   * invoke-static v0 LCandidateEnum;.valueOf:(String)LCandidateEnum; =>
   *   invoke-static v0 LCandidateEnum;.redex$OE$valueOf:(String)Integer
   */
  void update_invoke_valueof(const optimize_enums::EnumTypeEnvironment&,
                             cfg::ControlFlowGraph& cfg,
                             cfg::Block* block,
                             MethodItemEntry* mie,
                             SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    auto* container = insn->get_method()->get_class();
    if (m_enum_attributes_map.count(container) == 0u) {
      return;
    }
    auto* valueof_method =
        m_enum_util->add_substitute_of_valueof(container, prev_sb);
    auto reg = insn->src(0);
    m_replacements.emplace_back(
        cfg, block, mie,
        dasm(OPCODE_INVOKE_STATIC, valueof_method, {{VREG, reg}}));
  }

  /**
   * If v0 is a candidate enum,
   * invoke-virtual v0 LCandidateEnum;.name:()Ljava/lang/String; or
   * invoke-virtual v0 LCandidateEnum;.toString:()Ljava/lang/String; =>
   *    invoke-static v0 LCandidateEnum;.redex$OE$name:(Integer)String
   */
  void update_invoke_name(const optimize_enums::EnumTypeEnvironment& env,
                          cfg::ControlFlowGraph& cfg,
                          cfg::Block* block,
                          MethodItemEntry* mie,
                          SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    auto* container = insn->get_method()->get_class();
    auto reg = insn->src(0);
    const auto* candidate_type = infer_candidate_type(env.get(reg), container);
    if (candidate_type == nullptr) {
      return;
    }
    auto* helper_method =
        m_enum_util->add_substitute_of_name(candidate_type, prev_sb);
    require_integer(insn, 0);
    m_replacements.emplace_back(
        cfg, block, mie,
        dasm(OPCODE_INVOKE_STATIC, helper_method, {{VREG, reg}}));
  }

  /**
   * If v0 is a candidate enum,
   * invoke-virtual v0 LCandidateEnum;.hashCode:()I =>
   *    invoke-static v0 LCandidateEnum;.redex$OE$hashCode:(Integer)I
   */
  void update_invoke_hashcode(const optimize_enums::EnumTypeEnvironment& env,
                              cfg::ControlFlowGraph& cfg,
                              cfg::Block* block,
                              MethodItemEntry* mie,
                              SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    auto* container = insn->get_method()->get_class();
    auto src_reg = insn->src(0);
    const auto* candidate_type =
        infer_candidate_type(env.get(src_reg), container);
    if (candidate_type == nullptr) {
      return;
    }
    auto* helper_method =
        m_enum_util->add_substitute_of_hashcode(candidate_type, prev_sb);
    require_integer(insn, 0);
    m_replacements.emplace_back(
        cfg, block, mie,
        dasm(OPCODE_INVOKE_STATIC, helper_method, {{VREG, src_reg}}));
  }

  /**
   * If v0 is a candidate enum object,
   * invoke-static v0 LString;.valueOf:(LObject;)LString;
   * =>
   *   invoke-static v0 LCandidateEnum;.redex$OE$String_valueOf:(Integer)String
   */
  void update_invoke_string_valueof(
      const optimize_enums::EnumTypeEnvironment& env,
      cfg::ControlFlowGraph& cfg,
      cfg::Block* block,
      MethodItemEntry* mie,
      SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    const DexType* candidate_type =
        extract_candidate_enum_type(env.get(insn->src(0)));
    if (candidate_type == nullptr) {
      return;
    }
    DexMethodRef* string_valueof_meth =
        m_enum_util->add_substitute_of_stringvalueof(candidate_type, prev_sb);
    require_integer(insn, 0);
    m_replacements.emplace_back(cfg, block, mie,
                                dasm(OPCODE_INVOKE_STATIC, string_valueof_meth,
                                     {{VREG, insn->src(0)}}));
  }

  /**
   * If v1 is a candidate enum,
   * invoke-virtual v0 v1 LStringBuilder;.append(Object):LStringBuilder;
   * =>
   *   invoke-static v1 LCandidateEnum;.redex$OE$String_valueOf:(Integer)String
   *   move-result-object vn
   *   invoke-virtual v0 vn LStringBuilder;.append:(String)LStringBuilder;
   */
  void update_invoke_stringbuilder_append(
      const optimize_enums::EnumTypeEnvironment& env,
      cfg::ControlFlowGraph& cfg,
      cfg::Block* block,
      MethodItemEntry* mie,
      SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    const DexType* candidate_type =
        extract_candidate_enum_type(env.get(insn->src(1)));
    if (candidate_type == nullptr) {
      return;
    }
    DexMethodRef* string_valueof_meth =
        m_enum_util->add_substitute_of_stringvalueof(candidate_type, prev_sb);
    require_integer(insn, 1);
    auto reg0 = insn->src(0);
    auto reg1 = insn->src(1);
    auto str_reg = allocate_temp();
    std::vector<IRInstruction*> new_insns{
        dasm(OPCODE_INVOKE_STATIC, string_valueof_meth, {{VREG, reg1}}),
        dasm(OPCODE_MOVE_RESULT_OBJECT, {{VREG, str_reg}}),
        dasm(OPCODE_INVOKE_VIRTUAL,
             m_enum_util->STRINGBUILDER_APPEND_STR_METHOD,
             {{VREG, reg0}, {VREG, str_reg}})};
    m_replacements.emplace_back(cfg, block, mie, new_insns);
  }

  /**
   * If v0 is a candidate enum,
   * invoke-virtual v0 LCandidateEnum;.ordinal:()I =>
   * invoke-virtual v0 Integer.intValue()I,
   *
   * invoke-virtual v0, v1 LCandidateEnum;.equals:(Ljava/lang/Object;)Z =>
   * invoke-virtual v0, v1 Integer.equals(Ljava/lang/Object;)Z,
   *
   * invoke-virtual v0, v1 LCandidateEnum;.compareTo:(Ljava/lang/Object;)I =>
   * invoke-virtual v0, v1 Integer.compareTo(Ljava/lang/Integer;)I
   */
  void update_invoke_virtual(const optimize_enums::EnumTypeEnvironment& env,
                             cfg::ControlFlowGraph& cfg,
                             cfg::Block* block,
                             MethodItemEntry* mie,
                             DexMethodRef* integer_meth) {
    auto* insn = mie->insn;
    auto* container = insn->get_method()->get_class();
    auto src_reg = insn->src(0);
    const auto* candidate_type =
        infer_candidate_type(env.get(src_reg), container);
    if (candidate_type == nullptr) {
      return;
    }
    require_integer(insn, 0);
    auto* new_insn = new IRInstruction(OPCODE_INVOKE_VIRTUAL);
    new_insn->set_method(integer_meth)->set_srcs(insn->srcs());
    m_replacements.emplace_back(cfg, block, mie, new_insn);
  }

  /**
   * If this is an invocation of a user-defined virtual or direct method on a
   * CandidateEnum, then we make that method static. If that method is
   * toString(), then we call one of the appropriate methods Enum.name()
   * or CandidateEnum.toString(). Otherwise we do nothing.
   */
  void update_invoke_user_method(const optimize_enums::EnumTypeEnvironment& env,
                                 cfg::ControlFlowGraph& cfg,
                                 cfg::Block* block,
                                 MethodItemEntry* mie,
                                 SourceBlock* prev_sb) {
    auto* insn = mie->insn;
    auto* method_ref = insn->get_method();
    auto* container_type = method_ref->get_class();
    const auto* candidate_type =
        infer_candidate_type(env.get(insn->src(0)), container_type);
    if (candidate_type == nullptr) {
      return;
    }

    // If this is toString() and there is no CandidateEnum.toString(), then we
    // call Enum.name() instead.
    DexMethod* method = nullptr;
    if (method::signatures_match(method_ref,
                                 m_enum_util->ENUM_TOSTRING_METHOD)) {
      method = m_enum_util->get_user_defined_tostring_method(
          type_class(candidate_type));
      if (method == nullptr) {
        update_invoke_name(env, cfg, block, mie, prev_sb);
        return;
      }
    }
    if (method == nullptr) {
      method = resolve_method_deprecated(method_ref, opcode_to_search(insn));
    }
    always_assert(method);
    always_assert_log(
        !method->is_external() || is_static(method),
        "[%s] with candidate type %s resolved to external non-static method %s",
        SHOW(insn), SHOW(candidate_type), SHOW(method));
    require_integer(insn, 0);
    auto* new_insn = (new IRInstruction(*insn))
                         ->set_opcode(OPCODE_INVOKE_STATIC)
                         ->set_method(method);
    m_replacements.emplace_back(cfg, block, mie, new_insn);
  }

  /**
   * Infer a candidate type from an instruction like
   * `invoke-virtual vReg, Target.method()`
   *
   * Return a candidate type if we can get only one, return null if all these
   * types are not related to our candidate types. Bail out if the type are
   * mixed (our analysis part should have excluded this case).
   */
  const DexType* infer_candidate_type(const EnumTypes& reg_types,
                                      const DexType* target_type) {
    const DexType* candidate_type = nullptr;
    if (is_a_candidate(target_type)) {
      candidate_type = target_type;
    } else if (!m_enum_util->is_super_type_of_candidate_enum(target_type)) {
      return nullptr;
    }
    const auto& type_set = reg_types.elements();
    if (type_set.empty()) {
      // Register holds null value, we infer the type in instruction.
      return candidate_type;
    } else if (candidate_type != nullptr) {
      always_assert_log(type_set.size() == 1 &&
                            *type_set.begin() == candidate_type,
                        "%s != %s", SHOW(type_set), SHOW(candidate_type));
      return candidate_type;
    } else if (type_set.size() == 1) {
      candidate_type = *type_set.begin();
      return is_a_candidate(candidate_type) ? candidate_type : nullptr;
    } else {
      for (const auto* t : type_set) {
        always_assert_log(!is_a_candidate(t), "%s\n", SHOW(t));
      }
      return nullptr;
    }
  }

  /**
   * Return nullptr if the types contain none of the candidate enums,
   * return the candidate type if types only contain one candidate enum and do
   * not contain other types,
   * or assertion failure when the types are mixed.
   */
  const DexType* extract_candidate_enum_type(const EnumTypes& types) {
    return infer_candidate_type(types, m_enum_util->OBJECT_TYPE);
  }

  const DexType* try_convert_to_int_type(const DexType* type) {
    return m_enum_util->try_convert_to_int_type(m_enum_attributes_map, type);
  }

  bool is_a_candidate(const DexType* type) const {
    const auto* elem_type = type::make_element_type_if_array(type);
    return m_enum_attributes_map.count(elem_type) != 0u;
  }

  reg_t allocate_temp() { return m_method->get_code()->cfg().allocate_temp(); }

  const EnumAttributeMap& m_enum_attributes_map;
  EnumUtil* m_enum_util;
  DexMethod* m_method;
  std::vector<InsnReplacement> m_replacements;
  // The verifier's types before each instruction, while run() rewrites them.
  const UnorderedMap<const IRInstruction*, type_inference::TypeEnvironment>*
      m_verifier_envs{nullptr};
  // Uses that rewritten instructions take as an Integer and the registers
  // they read, where the verifier does not know the value as one.
  std::vector<std::pair<const IRInstruction*, reg_t>> m_integer_casts;
};

/**
 * Transform enum usages in the stores.
 */
class EnumTransformer final {
 public:
  /**
   * EnumTransformer constructor. Analyze <clinit> of candidate enums.
   */
  EnumTransformer(const Config& config,
                  DexStoresVector* stores,
                  bool disable_violation_fixes)
      : m_stores(*stores),
        m_int_objs(0),
        m_disable_violation_fixes(disable_violation_fixes) {
    m_enum_util = std::make_unique<EnumUtil>(config);
    always_assert(config.override_graph != nullptr);
    optimize_enums::ConstantReadSummaries reads(*config.override_graph);
    for (const auto& enum_type : UnorderedIterable(config.candidate_enums)) {
      auto* enum_cls = type_class(enum_type);
      auto attributes = optimize_enums::analyze_enum_clinit(
          enum_cls, config.support_kt_19_enum_entries, &reads);
      size_t num_enum_constants = attributes.m_constants_map.size();
      if (num_enum_constants == 0) {
        TRACE(ENUM, 2, "\tCannot analyze enum %s : ord %zu sfields %zu",
              SHOW(enum_cls), num_enum_constants,
              enum_cls->get_sfields().size());
        continue;
      } else if (num_enum_constants > config.max_enum_size) {
        if (config.breaking_reference_equality_allowlist.count(enum_type) ==
            0u) {
          TRACE(ENUM, 2, "\tSkip %s %zu values", SHOW(enum_cls),
                num_enum_constants);
          continue;
        } else {
          TRACE(ENUM, 2,
                "\tOptimize %s (%zu values) but object equality is not "
                "guaranteed",
                SHOW(enum_cls), num_enum_constants);
        }
      }
      m_int_objs = std::max<uint32_t>(
          m_int_objs, static_cast<uint32_t>(num_enum_constants));
      m_enum_objs += static_cast<uint32_t>(num_enum_constants);
      m_enum_attributes_map.emplace(enum_type, attributes);
      TRACE(ENUM, 2, "\tcleaning enum %s with num const values %zu",
            SHOW(enum_cls), num_enum_constants);
      clean_generated_methods_fields(enum_cls);
      opt_metadata::log_opt(ENUM_OPTIMIZED, enum_cls);
      TRACE(ENUM, 2, "\tOptimized %s to %zu Integers", SHOW(enum_cls),
            num_enum_constants);
      if (enum_cls->rstate.is_cls_kotlin()) {
        m_kotlin_enum_classes++;
      }
    }
    m_enum_util->create_util_class(stores, m_int_objs);
  }

  EnumTransformer(const EnumTransformer&) = delete;
  EnumTransformer& operator=(const EnumTransformer&) = delete;

  void run() {
    auto scope = build_class_scope(m_stores);
    // Update all the instructions.
    walk::parallel::code(
        scope,
        [&](DexMethod* method) {
          if ((m_enum_attributes_map.count(method->get_class()) != 0u) &&
              is_generated_enum_method(method)) {
            return false;
          }
          std::vector<const DexType*> types;
          method->gather_types(types);
          return std::any_of(types.begin(), types.end(),
                             [this](const DexType* type) {
                               return (bool)try_convert_to_int_type(type);
                             });
        },
        [&](DexMethod* method, IRCode& /*code*/) {
          if ((m_enum_attributes_map.count(method->get_class()) != 0u) &&
              (!is_constructor(method) && !is_static(method))) {
            m_enum_util->m_instance_methods.insert(method);
          }
          CodeTransformer code_updater(m_enum_attributes_map, m_enum_util.get(),
                                       method);
          code_updater.run();
        });
    create_substitute_methods(m_enum_util->m_substitute_methods);
    auto instance_methods = unordered_to_ordered(
        m_enum_util->m_instance_methods, dexmethods_comparator());
    for (auto* method : instance_methods) {
      mutators::make_static(method);
    }
    std::map<DexFieldRef*, DexMethodRef*, dexfields_comparator> field_to_method;
    insert_unordered_iterable(field_to_method,
                              m_enum_util->m_get_instance_field_methods);
    for (auto& pair : field_to_method) {
      create_get_instance_field_method(pair.second, pair.first);
    }
    post_update_enum_classes(scope);
    // Update all methods and fields references by replacing the candidate enum
    // types with Integer type.
    UnorderedMap<DexType*, DexType*> type_mapping;
    for (auto& pair : UnorderedIterable(m_enum_attributes_map)) {
      type_mapping[const_cast<DexType*>(pair.first)] =
          m_enum_util->INTEGER_TYPE;
    }
    type_reference::TypeRefUpdater updater(type_mapping);
    updater.update_methods_fields(scope);
    if (!m_enum_util->m_config.skip_sanity_check) {
      sanity_check(scope);
    }
  }

  uint32_t get_int_objs_count() { return m_int_objs; }
  size_t get_enum_utils_holders_count() { return m_enum_util->m_num_holders; }
  uint32_t get_enum_objs_count() { return m_enum_objs; }
  size_t get_enum_attributes_map_size() { return m_enum_attributes_map.size(); }
  size_t get_eliminated_kotlin_enum_classes() { return m_kotlin_enum_classes; }

 private:
  /**
   * Go through all instructions and check that all the methods, fields, and
   * types they reference actually exist.
   */
  void sanity_check(Scope& scope) {
    walk::parallel::code(scope, [this](DexMethod* method, IRCode& code) {
      if (method->get_code() == nullptr) {
        return;
      }
      for (auto& mie : InstructionIterable(code.cfg())) {
        auto* insn = mie.insn;
        if (insn->has_method()) {
          auto* method_ref = insn->get_method();
          auto* container = method_ref->get_class();
          if (m_enum_attributes_map.count(container) != 0u) {
            always_assert_log(method_ref->is_def(), "Invalid insn %s in %s\n",
                              SHOW(insn), SHOW(method));
          }
        } else if (insn->has_field()) {
          auto* field_ref = insn->get_field();
          auto* container = field_ref->get_class();
          if (m_enum_attributes_map.count(container) != 0u) {
            always_assert_log(field_ref->is_def(), "Invalid insn %s in %s\n",
                              SHOW(insn), SHOW(method));
          }
        } else if (insn->has_type() && insn->opcode() != IOPCODE_INIT_CLASS) {
          const auto* type_ref = insn->get_type();
          always_assert_log(!try_convert_to_int_type(type_ref),
                            "Invalid insn %s in %s\n", SHOW(insn),
                            SHOW(method));
        }
      }
    });
  }

  void create_substitute_methods(
      const ConcurrentMap<DexMethodRef*, std::unique_ptr<SourceBlock>>&
          methods) {
    DexMethod* created_method = nullptr;
    for (const auto& entry : UnorderedIterable(methods)) {
      DexMethodRef* ref = entry.first;
      SourceBlock* source_block = entry.second.get();
      if (ref->get_name() == m_enum_util->REDEX_NAME) {
        created_method = create_name_method(ref);
      } else if (ref->get_name() == m_enum_util->REDEX_HASHCODE) {
        created_method = create_hashcode_method(ref);
      } else if (ref->get_name() == m_enum_util->REDEX_VALUEOF) {
        created_method = create_valueof_method(ref);
      } else if (ref->get_name() == m_enum_util->REDEX_STRING_VALUEOF) {
        created_method = create_stringvalueof_method(ref);
      }

      if ((created_method != nullptr) && !m_disable_violation_fixes) {
        if (source_block == nullptr) {
          // If the source block is a nullptr, try to insert a hot source block
          // instead
          size_t interaction_size = 0;
          if (g_redex != nullptr) {
            interaction_size = g_redex->num_sb_interaction_indices();
          }

          if (interaction_size == 0) {
            continue;
          }
          source_blocks::insert_synthetic_source_blocks_in_method(
              created_method, [created_method, interaction_size]() {
                std::vector<SourceBlock::Val> hot_values(
                    interaction_size, SourceBlock::Val(1, 1));

                return std::make_unique<SourceBlock>(
                    &created_method->get_deobfuscated_name(),
                    SourceBlock::kSyntheticId,
                    hot_values);
              });
        } else {
          // Otherwise duplicate the existing block
          source_blocks::insert_synthetic_source_blocks_in_method(
              created_method, [&]() {
                return source_blocks::clone_as_synthetic(source_block,
                                                         created_method);
              });
        }
      }
    }
  }

  /**
   * Substitute for String.valueOf(Object obj).
   *
   * public static String redex$OE$String_valueOf(Integer obj) {
   *   if (obj == null) {
   *     return "null";
   *   }
   *   return CandidateEnum.toString(obj);
   * }
   */
  DexMethod* create_stringvalueof_method(DexMethodRef* ref) {
    MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC);
    auto* method = mc.create();
    auto* cls = type_class(ref->get_class());
    cls->add_method(method);
    auto* code = method->get_code();
    code->build_cfg();
    auto& cfg = code->cfg();
    auto* entry = cfg.entry_block();
    auto* return_null_block = cfg.create_block();
    return_null_block->push_back(
        {dasm(OPCODE_CONST_STRING, DexString::make_string("null")),
         dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
         dasm(OPCODE_RETURN_OBJECT, {1_v})});
    auto* obj_tostring_block = cfg.create_block();
    {
      auto* tostring_meth =
          m_enum_util->get_substitute_of_tostring(ref->get_class());
      obj_tostring_block->push_back(
          {dasm(OPCODE_INVOKE_STATIC, tostring_meth, {0_v}),
           dasm(OPCODE_MOVE_RESULT_OBJECT, {1_v}),
           dasm(OPCODE_RETURN_OBJECT, {1_v})});
    }
    cfg.create_branch(entry, dasm(OPCODE_IF_EQZ, {0_v}), obj_tostring_block,
                      return_null_block);
    cfg.recompute_registers_size();
    return method;
  }

  /**
   * Substitute for LCandidateEnum;.valueOf(String s)
   *
   * public static Integer redex$OE$valueOf(String s) {
   *   if (s == "xxx") {
   *     return f0;
   *   } else if (s == "y") {
   *     return f1;
   *   } ...
   *   } else {
   *     throw new IllegalArgumentException(s);
   *   }
   * }
   *
   * Note that the string of the exception is shortened.
   */
  DexMethod* create_valueof_method(DexMethodRef* ref) {
    MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC);
    auto* method = mc.create();
    auto* cls = type_class(ref->get_class());
    cls->add_method(method);
    auto* code = method->get_code();
    code->build_cfg();
    auto& cfg = code->cfg();
    auto* prev_block = cfg.entry_block();
    for (auto& pair :
         m_enum_attributes_map[ref->get_class()].get_ordered_names()) {
      prev_block->push_back({dasm(OPCODE_CONST_STRING, pair.second),
                             dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
                             dasm(OPCODE_INVOKE_VIRTUAL,
                                  m_enum_util->STRING_EQ_METHOD, {0_v, 1_v}),
                             dasm(OPCODE_MOVE_RESULT, {3_v})});

      auto* equal_block = cfg.create_block();
      if (pair.first < m_enum_util->m_config.max_enum_size) {
        auto* obj_field = m_enum_util->m_fields.at(pair.first);
        equal_block->push_back({dasm(OPCODE_SGET_OBJECT, obj_field),
                                dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {2_v}),
                                dasm(OPCODE_RETURN_OBJECT, {2_v})});
      } else {
        // Ordinals at or above `max_enum_size` (allowlisted enums only) have
        // no `$EnumUtils` field; box them as `update_sget_object` does.
        equal_block->push_back(
            {dasm(OPCODE_CONST,
                  {2_v, {LITERAL, static_cast<int64_t>(pair.first)}}),
             dasm(OPCODE_INVOKE_STATIC, m_enum_util->INTEGER_VALUEOF_METHOD,
                  {2_v}),
             dasm(OPCODE_MOVE_RESULT_OBJECT, {2_v}),
             dasm(OPCODE_RETURN_OBJECT, {2_v})});
      }
      auto* ne_block = cfg.create_block();
      cfg.create_branch(prev_block, dasm(OPCODE_IF_EQZ, {3_v}), equal_block,
                        ne_block);
      prev_block = ne_block;
    }
    prev_block->push_back(
        {dasm(OPCODE_NEW_INSTANCE, m_enum_util->ILLEGAL_ARG_EXCP_TYPE, {}),
         dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
         dasm(OPCODE_INVOKE_DIRECT,
              m_enum_util->ILLEGAL_ARG_CONSTRUCT_METHOD,
              {1_v, 0_v}),
         dasm(OPCODE_THROW, {1_v})});
    cfg.recompute_registers_size();
    return method;
  }

  /**
   * Substitute for LCandidateEnum;.name()
   *
   * public static String redex$OE$name(Integer obj) {
   *   switch(obj.intValue()) {
   *     case 0 : ...;
   *     case 1 : ...;
   *     ...
   *   }
   * }
   */
  DexMethod* create_name_method(DexMethodRef* ref) {
    MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC);
    auto* method = mc.create();
    auto* cls = type_class(ref->get_class());
    cls->add_method(method);
    auto* code = method->get_code();
    code->build_cfg();
    auto& cfg = code->cfg();
    auto* entry = cfg.entry_block();
    entry->push_back({dasm(OPCODE_INVOKE_VIRTUAL,
                           m_enum_util->INTEGER_INTVALUE_METHOD, {0_v}),
                      dasm(OPCODE_MOVE_RESULT, {0_v})});

    std::vector<std::pair<int32_t, cfg::Block*>> cases;
    for (auto& pair :
         m_enum_attributes_map[ref->get_class()].get_ordered_names()) {
      auto* block = cfg.create_block();
      cases.emplace_back(pair.first, block);
      block->push_back({dasm(OPCODE_CONST_STRING, pair.second),
                        dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
                        dasm(OPCODE_RETURN_OBJECT, {1_v})});
    }
    // This goto edge should never be taken, but we need a goto edge because the
    // switch is not a valid way to end a method. A switch cannot end a block
    // because the on-device dex verifier is unable to prove if the switch is
    // exhaustive.
    //
    // Arbitrarily choose the first case block.
    always_assert(!cases.empty());
    cfg.create_branch(entry, dasm(OPCODE_SWITCH, {0_v}), cases.front().second,
                      cases);
    cfg.recompute_registers_size();
    return method;
  }

  /**
   * Substitute for LCandidateEnum:.hashCode()
   *
   * `Enum.hashCode()` is the identity hash code, whose value the Java spec
   * leaves unspecified, so any deterministic value is a valid implementation.
   *
   * public static int redex$OE$hashCode(Integer obj) {
   *   int h = obj.intValue() * HASHCODE_MULTIPLIER + <seed of CandidateEnum>;
   *   return h ^ (h >>> 16);
   * }
   *
   * The result must not be linear in the ordinal. A Kotlin data class with two
   * fields of one enum computes `31 * first.hashCode() + second.hashCode()`,
   * and for any linear hash, the ordinals (1, 0) and (0, 31) then share a
   * hash. The final xor with the upper half removes that structure.
   *
   * The constants of one enum still get distinct hashes. The multiplier is
   * odd, which is what power-of-two tables such as `HashMap`'s need (primality
   * would add nothing): `h` is distinct modulo every power of two at least as
   * large as the enum. The xor step can be undone, and `HashMap` applies the
   * same step before picking a bucket, which undoes it: keys whose hash is one
   * enum's hash fill distinct buckets. The seed keeps constants of different
   * enums with the same ordinal apart.
   */
  DexMethod* create_hashcode_method(DexMethodRef* ref) {
    MethodCreator mc(ref, ACC_STATIC | ACC_PUBLIC);
    auto* method = mc.create();
    auto* cls = type_class(ref->get_class());
    cls->add_method(method);
    auto* code = method->get_code();
    code->build_cfg();
    auto& cfg = code->cfg();
    auto* entry = cfg.entry_block();
    entry->push_back({
        dasm(OPCODE_INVOKE_VIRTUAL, m_enum_util->INTEGER_INTVALUE_METHOD,
             {0_v}),
        dasm(OPCODE_MOVE_RESULT, {1_v}),
        dasm(OPCODE_MUL_INT_LIT, {1_v, 1_v})->set_literal(HASHCODE_MULTIPLIER),
        dasm(OPCODE_ADD_INT_LIT, {1_v, 1_v})
            ->set_literal(get_hashcode_seed(ref->get_class())),
        dasm(OPCODE_USHR_INT_LIT, {2_v, 1_v})->set_literal(16),
        dasm(OPCODE_XOR_INT, {1_v, 1_v, 2_v}),
        dasm(OPCODE_RETURN, {1_v}),
    });
    cfg.recompute_registers_size();
    return method;
  }

  // 0x9E37, the top 16 bits of the 32-bit golden ratio, as a signed literal
  // of `mul-int/lit16`.
  static constexpr int16_t HASHCODE_MULTIPLIER = -25033;

  /**
   * A constant in [1, -HASHCODE_MULTIPLIER - 1] derived from the enum's
   * deobfuscated name, so that it does not depend on renaming done by Redex
   * and fits the literal of `add-int/lit16`. A seed in that range gives no
   * constant the hash 0, which a Kotlin data class uses for a null field: `h`
   * of ordinal `o` is 0 only when the seed is `o * -HASHCODE_MULTIPLIER`, and
   * the final xor step turns only 0 into 0.
   */
  static int16_t get_hashcode_seed(const DexType* enum_type) {
    constexpr uint32_t seed_count = -HASHCODE_MULTIPLIER - 1;
    const auto hash = static_cast<uint32_t>(
        java_hashcode_of_utf8_string(show_deobfuscated(enum_type).c_str()));
    return static_cast<int16_t>(1 + hash % seed_count);
  }

  /**
   * Create a helper method to replace `iget` instructions that returns an
   * instance field value given the enum ordinal.
   *
   * public static [type] redex$OE$get_instanceField(Integer obj) {
   *   switch (obj.intValue()) {
   *     case 0: return value0;
   *     case 1: return value1;
   *     ...
   *   }
   * }
   */
  void create_get_instance_field_method(DexMethodRef* method_ref,
                                        DexFieldRef* ifield_ref) {
    MethodCreator mc(method_ref, ACC_STATIC | ACC_PUBLIC);
    auto* method = mc.create();
    auto* cls = type_class(method_ref->get_class());
    cls->add_method(method);
    auto* code = method->get_code();
    code->build_cfg();
    auto& cfg = code->cfg();
    auto* entry = cfg.entry_block();
    entry->push_back({dasm(OPCODE_INVOKE_VIRTUAL,
                           m_enum_util->INTEGER_INTVALUE_METHOD, {0_v}),
                      dasm(OPCODE_MOVE_RESULT, {0_v})});
    auto* ifield_type = ifield_ref->get_type();
    std::vector<std::pair<int32_t, cfg::Block*>> cases;
    for (auto& pair :
         m_enum_attributes_map[cls->get_type()].m_field_map[ifield_ref]) {
      auto ordinal = pair.first;
      auto* block = cfg.create_block();
      cases.emplace_back(ordinal, block);
      if (ifield_type == type::java_lang_String()) {
        const DexString* value = pair.second.string_value;
        if (value != nullptr) {
          block->push_back({dasm(OPCODE_CONST_STRING, value),
                            dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {1_v}),
                            dasm(OPCODE_RETURN_OBJECT, {1_v})});
        } else {
          // The `Ljava/lang/String` value is a `null` constant.
          block->push_back({dasm(OPCODE_CONST, {1_v, 0_L}),
                            dasm(OPCODE_RETURN_OBJECT, {1_v})});
        }
      } else if (pair.second.is_resource_id) {
        int64_t value = pair.second.primitive_value;
        block->push_back({dasm(IOPCODE_R_CONST, {1_v, {LITERAL, value}}),
                          dasm(OPCODE_RETURN, {1_v})});
      } else {
        int64_t value = pair.second.primitive_value;
        if (type::is_wide_type(ifield_type)) {
          block->push_back({dasm(OPCODE_CONST_WIDE, {1_v, {LITERAL, value}}),
                            dasm(OPCODE_RETURN_WIDE, {1_v})});
        } else {
          block->push_back({dasm(OPCODE_CONST, {1_v, {LITERAL, value}}),
                            dasm(OPCODE_RETURN, {1_v})});
        }
      }
    }
    // Arbitrarily choose the first case block as the default case.
    always_assert(!cases.empty());
    cfg.create_branch(entry, dasm(OPCODE_SWITCH, {0_v}), cases.front().second,
                      cases);
    cfg.recompute_registers_size();
  }

  /**
   * 1. Erase the enum instance fields and synthetic array field which is
   * usually `$VALUES`.
   * 2. Delete <init>, values() and valueOf(String) methods, and delete
   * instructions that construct these fields from <clinit>.
   */
  void clean_generated_methods_fields(DexClass* enum_cls) {
    auto& sfields = enum_cls->get_sfields();
    auto& enum_constants =
        m_enum_attributes_map[enum_cls->get_type()].m_constants_map;
    auto synth_field_access = synth_access();
    UnorderedSet<DexField*> synth_fields;

    std::erase_if(sfields, [&](auto* field) {
      if (enum_constants.count(field)) {
        return true;
      }
      if (check_required_access_flags(synth_field_access,
                                      field->get_access())) {
        always_assert(synth_fields.size() < 2);
        TRACE(ENUM, 5, "erasing field %s", SHOW(field));
        synth_fields.insert(field);
        if (synth_fields.size() == 2) {
          always_assert(m_enum_util->m_config.support_kt_19_enum_entries);
        }
        return true;
      }
      return false;
    });

    always_assert(!synth_fields.empty());
    auto& dmethods = enum_cls->get_dmethods();
    // Delete <init>, values() and valueOf(String) methods, and clean <clinit>.
    std::erase_if(dmethods, [&, this](auto* method) {
      if (method::is_clinit(method)) {
        clean_clinit(enum_constants, enum_cls, method, synth_fields);
        return empty(method->get_code());
      }
      return this->is_generated_enum_method(method);
    });
  }

  /**
   * Erase enum construction code. Erase the put instructions that write enum
   * values and synthetic $VALUES array, then erase the dead instructions.
   *
   * The code before the transformation:
   *
   * new-instance v0 LCandidateEnum;
   * invoke-direct v0 v1 v2 Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V
   * sput-object v0 LCandidateEnum;.f:LCandidateEnum;
   * ... // maybe more objects construction.
   * sput-object v3 LCandidateEnum;.$VALUES:[LCandidateEnum;
   * ... // register v0 may be used.
   *
   * The code after the transformation:
   *
   * // Deleted. new-instance v0 LCandidateEnum;
   * // Deleted. invoke-direct v0 v1 v2
   * Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V
   * // Deleted. sput-object v0 LCandidateEnum;.f:LCandidateEnum;
   * sget-object v0 LCandidateEnum;.f:LCandidateEnum;
   * ... // maybe more objects construction.
   * // Deleted. sput-object v3 LCandidateEnum;.$VALUES:[LCandidateEnum;
   * ... // register v0 may be used.
   */
  static void clean_clinit(const EnumConstantsMap& enum_constants,
                           DexClass* enum_cls,
                           DexMethod* clinit,
                           const UnorderedSet<DexField*>& synth_fields) {
    auto* code = clinit->get_code();
    auto ctors = enum_cls->get_ctors();
    auto* ctor = only(ctors);
    side_effects::InvokeToSummaryMap summaries;
    auto& cfg = code->cfg();
    auto ii = InstructionIterable(cfg);
    cfg::CFGMutation m(cfg);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      auto* insn = it->insn;
      if (opcode::is_an_sput(insn->opcode())) {
        auto* field = resolve_field(insn->get_field());
        if ((field != nullptr) && (enum_constants.count(field) != 0u)) {
          cfg.insert_before(it, dasm(OPCODE_SGET_OBJECT, field));
          cfg.insert_before(
              it,
              dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {{VREG, insn->src(0)}}));
          m.remove(it);
        } else if (synth_fields.count(field) != 0u) {
          m.remove(it);
        }
      } else if ((opcode::is_invoke_direct(insn->opcode()) &&
                  insn->get_method() == ctor) ||
                 (opcode::is_invoke_static(insn->opcode()) &&
                  is_kt_enum_entries_factory(insn->get_method())) ||
                 (opcode::is_invoke_direct(insn->opcode()) &&
                  is_kt_enum_entries_list_ctor(insn->get_method()))) {
        // The enum constructor is side-effect free (see is_safe_enum), and
        // `enumEntries`, or its inlined body, only wraps an array for
        // `$ENTRIES`.
        summaries.emplace(insn, side_effects::Summary());
      }
    }
    m.flush();

    cfg.calculate_exit_block();
    ptrs::FixpointIterator fp_iter(cfg);
    fp_iter.run(ptrs::Environment());
    used_vars::FixpointIterator uv_fpiter(fp_iter, summaries, cfg, ctor);
    uv_fpiter.run(used_vars::UsedVarsSet());
    auto dead_instructions = used_vars::get_dead_instructions(cfg, uv_fpiter);
    for (const auto& insn : dead_instructions) {
      cfg.remove_insn(insn);
    }

    // Assert no instruction about the $VALUES field.
    for (auto& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      always_assert_log(!insn->has_field() ||
                            !synth_fields.count(insn->get_field()->as_def()),
                        "%s can not be deleted", SHOW(insn));
    }
  }

  /**
   * Only use for <clinit> code.
   */
  static bool empty(IRCode* code) {
    auto iterable = InstructionIterable(code->cfg());
    auto begin = iterable.begin();
    return opcode::is_return_void(begin->insn->opcode());
  }

  /**
   * Whether a method is <init>, values() or valueOf(String).
   */
  bool is_generated_enum_method(DexMethodRef* method) {
    const auto* name = method->get_name();
    return name == m_enum_util->INIT_METHOD_STR || is_enum_values(method) ||
           is_enum_valueof(method);
  }

  /**
   * Change candidates' superclass from Enum to Object.
   */
  void post_update_enum_classes(Scope& scope) {
    for (auto* cls : scope) {
      if (m_enum_attributes_map.count(cls->get_type()) == 0u) {
        continue;
      }
      always_assert_log(cls->get_super_class() == m_enum_util->ENUM_TYPE,
                        "%s super %s\n",
                        SHOW(cls),
                        SHOW(cls->get_super_class()));
      cls->set_super_class(m_enum_util->OBJECT_TYPE);
      cls->set_access(cls->get_access() & ~ACC_ENUM);
    }
  }

  const DexType* try_convert_to_int_type(const DexType* type) {
    return m_enum_util->try_convert_to_int_type(m_enum_attributes_map, type);
  }

  DexStoresVector& m_stores;
  uint32_t m_int_objs{0}; // Generated Integer objects.
  uint32_t m_enum_objs{0}; // Eliminated Enum objects.
  bool m_disable_violation_fixes{false};
  EnumAttributeMap m_enum_attributes_map;
  std::unique_ptr<EnumUtil> m_enum_util;
  size_t m_kotlin_enum_classes{0};
};
} // namespace

namespace optimize_enums {
/**
 * Transform enums to Integer objects, return the total number of eliminated
 * enum objects.
 */
Stats transform_enums(PassManager& mgr,
                      const Config& config,
                      DexStoresVector* stores,
                      bool disable_violation_fixes) {

  Stats stats;
  if (config.candidate_enums.empty()) {
    return stats;
  }

  EnumTransformer transformer(config, stores, disable_violation_fixes);
  transformer.run();
  stats.num_eliminated_enum_classes =
      transformer.get_enum_attributes_map_size();
  mgr.incr_metric("num_eliminated_enum_classes",
                  stats.num_eliminated_enum_classes);
  TRACE(ENUM, 2, "optimize enums : num_eliminated_enum_classes %zu",
        stats.num_eliminated_enum_classes);
  stats.num_eliminated_kotlin_enum_classes =
      transformer.get_eliminated_kotlin_enum_classes();
  mgr.incr_metric("num_eliminated_kotlin_enum_classes",
                  stats.num_eliminated_kotlin_enum_classes);
  TRACE(ENUM, 2, "optimize enums : num_eliminated_kotlin_enum_classes %zu",
        stats.num_eliminated_kotlin_enum_classes);
  stats.num_erased_enum_objs = transformer.get_enum_objs_count();
  stats.num_int_objs = transformer.get_int_objs_count();
  mgr.incr_metric("num_enum_utils_holders",
                  transformer.get_enum_utils_holders_count());
  return stats;
}
} // namespace optimize_enums
