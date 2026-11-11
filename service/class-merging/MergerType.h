/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/functional/hash.hpp>

#include "ClassHierarchy.h"
#include "DexClass.h"
#include "TypeUtil.h"

namespace class_merging {

std::string get_type_name_tag(const DexType* root_type);

using FieldsMap = UnorderedMap<const DexType*, std::vector<DexField*>>;
using ConstTypeVector = std::vector<const DexType*>;

/**
 * A type that "represents" a set of other types that can be coalesced.
 * During class merging a set of mergers are built that will containing
 * the set of type that can be merged into one.
 * The merger will also carry all the information needed to generate
 * a proper DexClass and make the proper changes in the code while
 * erasing coalesced types.
 */
struct MergerType {

  // Model virtual methods belonging to the same VirtualScope on the MergerType
  // we are creating.
  struct VirtualMethod {
    // Base implementation on the base type.
    DexMethod* base;
    // Overrides in mergeable types.
    std::vector<DexMethod*> overrides;

    explicit VirtualMethod(DexMethod* base) : base(base) {}
    VirtualMethod(DexMethod* base, const std::vector<DexMethod*>& lst)
        : base(base) {
      overrides.insert(overrides.begin(), lst.begin(), lst.end());
    }
  };

  /**
   * Merged types may have implementation of interfaces that need to be
   * merged. An InterfaceMethod for a given method retaines the set
   * of interfaces that define that method and all the implementation
   * across the methods.
   * Example:
   * interface I1 { void m(); }
   * interface I2 { void m(); void f(); }
   * say we have 2 types that can be erased
   * class A implements I1, I2 { void m() {} void f() {} }
   * class B implements I1, I2 { void m() {} void f() {} }
   * The merger will have 2 InterfaceMethod
   * InterfaceMethod { {I1, I2}, [A.m(), B.m()]}
   * InterfaceMethod { {I2}, [A.f(), B.f()]}
   */
  struct InterfaceMethod {
    TypeSet interfaces;
    DexMethod* overridden_meth;
    std::vector<DexMethod*> methods;
  };

  /**
   * A Shape is a tuple containing the number of fields of a given type
   * coming from the type to be erased.
   * When generating a merger class, fields are created in the order and
   * number of the shape.
   * So for Shape{1, 1, 0, 1, 1, 0, 1} the DexClass created will have
   * class Shape {
   *   String field0;
   *   Object field1;
   *   int field2;
   *   long field3;
   *   float field4;
   * }
   */
  struct Shape {
    // a string field: Ljava/lang/String;
    int string_fields{0};
    // a reference field: any type starting with 'L' or '['
    int reference_fields{0};
    // a boolean field: 'Z'
    int bool_fields{0};
    // a primitive field that fits into an int: 'B', 'S', 'C', 'I'
    int int_fields{0};
    // a long field: 'J':
    int long_fields{0};
    // a double field: 'D':
    int double_fields{0};
    // a float field: 'F':
    int float_fields{0};

    Shape() {}
    /**
     * Construct a Shape object for the fields.
     */
    explicit Shape(const std::vector<DexField*>&);

    /**
     * Build a suitable and unique type name for a shape.
     */
    std::string build_type_name(
        const std::string& prefix,
        const DexType* root_type,
        const ConstTypeVector& mergeables_set,
        const TypeSet& intf_set,
        size_t group_count,
        const std::optional<size_t>& opt_dex_id,
        const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
        UnorderedSet<size_t>& hash_cache) const;

    std::string build_type_name_legacy(
        const std::string& prefix,
        const DexType* root_type,
        const TypeSet& intf_set,
        const std::optional<size_t>& opt_dex_id,
        size_t count,
        const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
        const InterdexSubgroupIdx subgroup_idx) const;

    /**
     * Returns if this shape includes another shape
     */
    bool includes(const Shape& other) const {
      return (string_fields >= other.string_fields &&
              reference_fields >= other.reference_fields &&
              bool_fields >= other.bool_fields &&
              int_fields >= other.int_fields &&
              long_fields >= other.long_fields &&
              double_fields >= other.double_fields &&
              float_fields >= other.float_fields);
    }

    /**
     * Comparator
     */
    bool operator==(const Shape& other) const {
      return (string_fields == other.string_fields &&
              reference_fields == other.reference_fields &&
              bool_fields == other.bool_fields &&
              int_fields == other.int_fields &&
              long_fields == other.long_fields &&
              double_fields == other.double_fields &&
              float_fields == other.float_fields);
    }

    std::string to_string() const;

    int field_count() const {
      return (string_fields + reference_fields + bool_fields + int_fields +
              long_fields + double_fields + float_fields);
    }
  };

  // std::map comparator function
  struct ShapeComp {
    bool operator()(const Shape& left, const Shape& right) const {
      if (left.string_fields < right.string_fields) {
        return true;
      }
      if (left.string_fields > right.string_fields) {
        return false;
      }
      if (left.reference_fields < right.reference_fields) {
        return true;
      }
      if (left.reference_fields > right.reference_fields) {
        return false;
      }
      if (left.bool_fields < right.bool_fields) {
        return true;
      }
      if (left.bool_fields > right.bool_fields) {
        return false;
      }
      if (left.int_fields < right.int_fields) {
        return true;
      }
      if (left.int_fields > right.int_fields) {
        return false;
      }
      if (left.long_fields < right.long_fields) {
        return true;
      }
      if (left.long_fields > right.long_fields) {
        return false;
      }
      if (left.double_fields < right.double_fields) {
        return true;
      }
      if (left.double_fields > right.double_fields) {
        return false;
      }
      if (left.float_fields < right.float_fields) {
        return true;
      }
      return false;
    }
  };

  using InterfaceGroups = std::map<TypeSet, TypeSet>;
  struct ShapeHierarchy {
    TypeSet types;
    InterfaceGroups groups;
  };
  using ShapeCollector =
      std::map<MergerType::Shape, ShapeHierarchy, MergerType::ShapeComp>;

  // The DexType behind this MergerType. The type may or may not be
  // backed by a DexClass already
  const DexType* type;
  // Suggested dex to store the merger class.
  std::optional<size_t> dex_id;
  // The set of mergeable types. Those are effectively the types that
  // will be erased.
  // Notice: a merger may be defined that does not have any mergeable types
  // and only needed to split the set of classes into a more manageable
  // hierarchy
  TypeSet mergeables;
  // The Shape of this merger if any
  Shape shape;
  // for every mergeable type has the sorted array of mergeable type
  // fields to merger fields. The order follows the shape definition
  // (strings, refs, booleans, ints, longs, doubles, floats).
  // Example:
  // class A { int i; List l; }
  // class B { Map m; int x; }
  // and say the 2 types are mergeable into
  // class Shape { Object field0; int field1; }
  // The layout of Shape follows that of the Shape struct so, here,
  // ref first and int next.
  // The field_map is as follow
  // { A: [A.l, A.i], B: [B.m, B.x]}
  // so field in first pos will map to the shape first field, etc.
  // The order follows the definition in the DexClass for the mergeable type
  // TODO: make order based on field position if a proper annotation is
  // defined
  FieldsMap field_map;
  // if this was created while "shaping" the model
  bool from_shape{false};
  // a dummy merger is used only for analysis sake but makes no
  // change to the underlying type
  bool dummy{false};
  // The list of dmethods for this merger.
  // If the merger is backed by a DexClass this list will contain the
  // methods of that class too
  std::vector<DexMethod*> dmethods;
  // The list of non virtual methods for this merger.
  // Those are vmethods that could be devirtualized
  std::vector<DexMethod*> non_virt_methods;
  // The list of virtual methods that can be merged.
  // Each entry contains a pair of the overridden method
  // and a list of virtual methods coming from the types to be erased.
  // class Base { void m() {} }
  // class A extends Base { void m() {} }
  // class B extends Base { void m() {} }
  // class C extends Base {}
  // and let's say A, B and C can be erased (merged)
  // The vmethods entry will have one element
  // [(Base.m(), [A.m(), B.m()])]
  // implying that A.m() and B.m() need to be merged into one implementation.
  // and that Base.m() will be used for the default case.
  //
  // Conceptually we need to do the following
  // class Merged {
  //   void A_m() {}
  //   void B_m() {}
  //   void m() {
  //     if (a_type) A_m();
  //     else if (b_type) B.m();
  //     else Base.m();
  //   }
  // }
  std::vector<VirtualMethod> vmethods;
  // The list of interface methods that can be merged.
  // Each entry is a list of interface methods coming from the type
  // to be erased.
  // Check InterfaceMethod above for details.
  std::vector<InterfaceMethod> intfs_methods;
  // InterDex subgroup id, if any.
  std::optional<InterdexSubgroupIdx> interdex_subgroup;

  /**
   * Return whether this MergerType is a shape or not.
   * Notice that s shape may have no fields.
   */
  bool is_shape() const { return from_shape; }

  /**
   * Return the number of fields for this merger.
   */
  int field_count() const { return shape.field_count(); }

  /**
   * Return the starting position in the list of fields for a field
   * of the given type.
   */
  int start_index_for_string() const { return 0; }

  int start_index_for_ref() const { return shape.string_fields; }

  int start_index_for_bool() const {
    return shape.string_fields + shape.reference_fields;
  }

  int start_index_for_int() const {
    return shape.string_fields + shape.reference_fields + shape.bool_fields;
  }

  int start_index_for_long() const {
    return shape.string_fields + shape.reference_fields + shape.bool_fields +
           shape.int_fields;
  }

  int start_index_for_double() const {
    return shape.string_fields + shape.reference_fields + shape.bool_fields +
           shape.int_fields + shape.long_fields;
  }

  int start_index_for_float() const {
    return shape.string_fields + shape.reference_fields + shape.bool_fields +
           shape.int_fields + shape.long_fields + shape.double_fields;
  }

  int start_index_for(const DexType* t) const {
    auto* const string_type = type::java_lang_String();
    if (t == string_type) {
      return 0;
    }
    switch (type::type_shorty(t)) {
    case 'L':
    case '[':
      return start_index_for_ref();
    case 'Z':
      return start_index_for_bool();
    case 'B':
    case 'S':
    case 'C':
    case 'I':
      return start_index_for_int();
    case 'J':
      return start_index_for_long();
    case 'D':
      return start_index_for_double();
    case 'F':
      return start_index_for_float();
    default:
      not_reached();
    }
  }

  /**
   * Returns the type of the field given a position
   */
  DexType* field_type_at(int pos) {
    if (pos >= start_index_for_string() && pos < start_index_for_ref()) {
      return type::java_lang_String();
    } else if (pos >= start_index_for_ref() && pos < start_index_for_bool()) {
      return type::java_lang_Object();
    } else if (pos >= start_index_for_bool() && pos < start_index_for_int()) {
      return type::_boolean();
    } else if (pos >= start_index_for_int() && pos < start_index_for_long()) {
      return type::_int();
    } else if (pos >= start_index_for_long() &&
               pos < start_index_for_double()) {
      return type::_long();
    } else if (pos >= start_index_for_double() &&
               pos < start_index_for_float()) {
      return type::_double();
    } else if (pos >= start_index_for_float() && pos < field_count()) {
      return type::_float();
    } else {
      not_reached();
    }
  }

  bool has_mergeables() const { return !mergeables.empty(); }

  bool has_fields() const { return !field_map.empty(); }
};

} // namespace class_merging

/**
 * Hash funtion for using Shape as a key in UnorderedMap
 */
namespace std {

template <>
struct hash<class_merging::MergerType::Shape> {
  std::size_t operator()(const class_merging::MergerType::Shape& s) const {
    using boost::hash_combine;
    using boost::hash_value;

    std::size_t seed = 0;
    hash_combine(seed, hash_value(s.string_fields));
    hash_combine(seed, hash_value(s.reference_fields));
    hash_combine(seed, hash_value(s.bool_fields));
    hash_combine(seed, hash_value(s.int_fields));
    hash_combine(seed, hash_value(s.long_fields));
    hash_combine(seed, hash_value(s.double_fields));
    hash_combine(seed, hash_value(s.float_fields));
    return seed;
  }
};

} // namespace std
