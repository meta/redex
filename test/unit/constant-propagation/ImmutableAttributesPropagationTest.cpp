/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <sparta/S_Expression.h>

#include "ConstantPropagationTestUtil.h"
#include "ConstructorParams.h"
#include "Creators.h"
#include "Debug.h"
#include "IRAssembler.h"
#include "JarLoader.h"

using ImmutableAnalyzer =
    InstructionAnalyzerCombiner<cp::StringAnalyzer,
                                cp::ImmutableAttributeAnalyzer,
                                cp::PrimitiveAnalyzer>;
using namespace sparta;

struct ImmutableTest : public ConstantPropagationTest {
 public:
  ImmutableTest() {
    always_assert(load_class_file(std::getenv("enum_class_file")));
    m_config.replace_move_result_with_consts = true;
    std::array<DexType*, 2> boxed_types = {type::java_lang_Integer(),
                                           type::java_lang_Character()};
    for (auto& type : boxed_types) {
      auto* valueOf =
          dynamic_cast<DexMethod*>(type::make_value_of_method_for_type(type));
      auto* getter_method =
          dynamic_cast<DexMethod*>(type::make_unboxing_method_for_type(type));
      // The intValue of integer is initialized through the static invocation.
      m_immut_analyzer_state.add_initializer(valueOf, getter_method)
          .set_src_id_of_attr(0)
          .set_obj_to_dest();
      m_immut_analyzer_state.add_cached_boxed_objects(valueOf, -128, 128);
    }
    m_analyzer = ImmutableAnalyzer(nullptr, &m_immut_analyzer_state, nullptr);
  }

  cp::ImmutableAttributeAnalyzerState m_immut_analyzer_state;
  ImmutableAnalyzer m_analyzer;
  cp::Transform::Config m_config;
  UnorderedSet<DexMethodRef*> m_pure_methods;

  // Interprocedural constant propagation replaces call results only for
  // registered getters and pure methods. Its pure methods include the
  // registered getters of the JDK, as these tests' getters are taken to be.
  cp::Transform::Config ipcp_config(
      const cp::ImmutableAttributeAnalyzerState& state) {
    cp::Transform::Config config;
    config.getter_methods_for_immutable_fields = &state.attribute_methods;
    for (auto* getter : UnorderedIterable(state.attribute_methods)) {
      m_pure_methods.insert(getter);
    }
    config.pure_methods = &m_pure_methods;
    return config;
  }
  cp::Transform::Config ipcp_config() {
    return ipcp_config(m_immut_analyzer_state);
  }

  static ObjectWithImmutAttrDomain create_integer_abstract_value(long value,
                                                                 bool cached) {
    return create_object(R"((
    "Ljava/lang/Integer;"
    (
      ("intValue:()I" )" + std::to_string(value) +
                             R"()
    )
    ))",
                         cached);
  }

  static ObjectWithImmutAttrDomain create_char_100() {
    return create_object(R"((
    "Ljava/lang/Character;"
    (
      ("charValue:()C" 100)
    )
    ))");
  }

  /**
   * Example :
   * ( "ClassName" (
   *    ( "FieldName1" "Value1" )
   *    ( "FieldName2" "Value2" )
   *  )
   * )
   */
  static ObjectWithImmutAttrDomain create_object(const std::string& s,
                                                 bool cached = false) {
    std::istringstream input(s);
    s_expr_istream s_expr_input(input);
    s_expr expr;
    s_expr_input >> expr;
    std::string class_name;
    s_expr fields_expr;
    s_patn({s_patn(&class_name), s_patn(fields_expr)})
        .must_match(expr, "Need a class name");
    auto* type = DexType::make_type(DexString::make_string(class_name));
    ObjectWithImmutAttr obj(type, fields_expr.size());
    obj.jvm_cached_singleton = cached;

    std::vector<std::pair<ImmutableAttr::Attr, AttrDomain>> attrs;

    for (size_t i = 0; i < fields_expr.size(); i++) {
      std::string member_name;
      s_expr value;
      auto matched =
          s_patn({s_patn(&member_name)}, value).match_with(fields_expr[i]);
      always_assert_log(matched,
                        "Need a pair of field_name(or method_name) and value");
      auto it = member_name.find(":(");
      auto attr = [&]() {
        if (it == std::string::npos) {
          auto* field = dynamic_cast<DexField*>(
              DexField::make_field(class_name + "." + member_name));
          return ImmutableAttr::Attr(field);
        } else {
          auto* method = dynamic_cast<DexMethod*>(
              DexMethod::make_method(class_name + "." + member_name));
          return ImmutableAttr::Attr(method);
        }
      }();
      always_assert_log(value.size() == 1,
                        "Only accept string or integer or integer range");
      auto get_val = [&]() -> AttrDomain {
        if (value[0].is_int32()) {
          return SignedConstantDomain(value[0].get_int32());
        } else if (value[0].is_string()) {
          auto value_s = value[0].get_string();
          // "T" is special, it means Top.
          if (value_s == "T") {
            return AttrDomain::top();
          } else {
            return StringDomain(DexString::make_string(value_s));
          }
        } else if (value[0].is_list()) {
          always_assert_log(value[0].size() == 2, "expected two elements");
          always_assert_log(value[0][0].is_int32(), "expected int32");
          always_assert_log(value[0][1].is_int32(), "expected int32");
          return SignedConstantDomain(value[0][0].get_int32(),
                                      value[0][1].get_int32());
        } else {
          always_assert_log(false, "value is not supported");
        };
      };
      attrs.emplace_back(attr, get_val());
    }

    // Need to sort attrs before inserting.
    std::sort(attrs.begin(), attrs.end(), [](const auto& lhs, const auto& rhs) {
      return lhs.first < rhs.first;
    });

    for (auto& p : attrs) {
      obj.write_value(p.first, p.second);
    }

    return ObjectWithImmutAttrDomain(std::move(obj));
  }
};

TEST_F(ImmutableTest, abstract_domain) {
  // meet
  {
    // Integer{100} meet Integer{100} => Integer{100}
    auto i100 = create_integer_abstract_value(100, false);
    auto x = i100;
    x.meet_with(i100);
    EXPECT_TRUE(x.equals(i100));
  }
  {
    // Integer{100} meet CachedInteger{100} => CachedInteger{100}
    auto i100 = create_integer_abstract_value(100, false);
    auto ci100 = create_integer_abstract_value(100, true);
    auto x = ci100;
    x.meet_with(i100);
    EXPECT_TRUE(x.equals(ci100));
  }
  {
    // CachedInteger{100} meet CachedInteger{100} => CachedInteger{100}
    auto ci100 = create_integer_abstract_value(100, true);
    auto x = ci100;
    x.meet_with(ci100);
    EXPECT_TRUE(x.equals(ci100));
  }
  {
    // Integer{200} meet CatchedInteger{100} => bottom
    auto integer_200 = create_integer_abstract_value(200, false);
    auto cached_integer_100 = create_integer_abstract_value(100, true);
    integer_200.meet_with(cached_integer_100);
    EXPECT_TRUE(integer_200.is_bottom());
  }
  {
    auto a_1_b_2 = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("b:I" 2)
      )
    ))");
    auto a_1_b_3 = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("b:I" 3)
      )
    ))");
    a_1_b_2.meet_with(a_1_b_3);
    EXPECT_TRUE(a_1_b_2.is_bottom());
    EXPECT_TRUE(a_1_b_3.is_value());
    auto obj = a_1_b_3.get_constant();
    auto y_object = create_object(R"((
      "LY;" (
        ("a:I" 1)
        ("b:I" 3)
      )
    ))");
    y_object.meet_with(a_1_b_3);
    // Different types, we don't know their relationship.
    EXPECT_TRUE(y_object.is_top());
  }
  {
    auto a_1_c_1 = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("c:I" 1)
      )
    ))");
    // We don't know if X class has other instance fields or not.
    EXPECT_TRUE(a_1_c_1.get_constant()->runtime_equals(
                    *a_1_c_1.get_constant()) == TriState::Unknown);
    auto b_1_c_2 = create_object(R"((
      "LX;" (
        ("b:I" 1)
        ("c:I" 2)
      )
    ))");
    EXPECT_EQ(a_1_c_1.get_constant()->runtime_equals(*b_1_c_2.get_constant()),
              TriState::False)
        << a_1_c_1 << " vs " << b_1_c_2;
  }
  // join
  {
    // Integer{100} join CachedInteger{100} => Integer{100}
    auto integer_100 = create_integer_abstract_value(100, false);
    auto cached_integer_100 = create_integer_abstract_value(100, true);
    cached_integer_100.join_with(integer_100);
    ASSERT_TRUE(cached_integer_100.is_value());
    EXPECT_FALSE(cached_integer_100.get_constant()->jvm_cached_singleton);
  }
  {
    // Integer{200} join CachedInteger{100} => Integer{T}
    auto integer_200 = create_integer_abstract_value(200, false);
    auto cached_integer_100 = create_integer_abstract_value(100, true);
    integer_200.join_with(cached_integer_100);
    EXPECT_TRUE(integer_200.is_value());
    auto constant = integer_200.get_constant();
    EXPECT_FALSE(constant->jvm_cached_singleton);
    const auto& field_value =
        constant->attributes[0].value.maybe_get<SignedConstantDomain>();
    EXPECT_TRUE(!field_value->get_constant());
  }
  {
    // Integer{100} join Char{100} => top
    auto integer_100 = create_integer_abstract_value(100, false);
    auto char_100 = create_char_100();
    integer_100.join_with(char_100);
    EXPECT_TRUE(integer_100.is_top());
  }
  {
    auto a_1_b_2 = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("b:I" 2)
      )
    ))");
    auto a_1_b_3 = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("b:I" 3)
      )
    ))");
    a_1_b_2.join_with(a_1_b_3);
    EXPECT_TRUE(a_1_b_2.is_value());
    auto expect = create_object(R"((
      "LX;" (
        ("a:I" 1)
        ("b:I" "T")
      )
    ))");
    EXPECT_TRUE(a_1_b_2.equals(expect));
    auto y_object = create_object(R"((
      "LY;" (
        ("a:I" 1)
        ("b:I" 3)
      )
    ))");
    y_object.join_with(a_1_b_3);
    EXPECT_TRUE(y_object.is_top());
  }
  // leq
  {
    auto c_1 = create_object(R"((
      "LX;" (
        ("c:I" #1)
      )
    ))");
    auto c_12 = create_object(R"((
      "LX;" (
        ("c:I" (#1 #2))
      )
    ))");
    // c_1 is strictly less than c_12
    EXPECT_TRUE(c_1.leq(c_12));
    EXPECT_TRUE(!c_12.leq(c_1));
  }
}

TEST_F(ImmutableTest, integer) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
      (return-void)
    )
  )");

  do_const_prop(code.get(), m_analyzer, m_config);
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (const v0 100)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

namespace {

// Creates the external class `type` declaring the virtual method `method`,
// implementing `intf` when it is not null.
void create_external_class_with_method(DexType* type,
                                       DexType* super,
                                       DexAccessFlags class_access,
                                       const char* method,
                                       DexAccessFlags method_access,
                                       DexType* intf = nullptr) {
  ClassCreator creator(type);
  creator.set_super(super);
  creator.set_access(class_access);
  if (intf != nullptr) {
    creator.add_interface(intf);
  }
  creator.set_external();
  auto* m = dynamic_cast<DexMethod*>(DexMethod::make_method(method));
  m->set_access(method_access);
  m->set_virtual(true);
  m->set_external();
  creator.add_method(m);
  creator.create();
}

void create_number_and_integer() {
  create_external_class_with_method(
      DexType::make_type("Ljava/lang/Number;"), type::java_lang_Object(),
      ACC_PUBLIC | ACC_ABSTRACT, "Ljava/lang/Number;.intValue:()I", ACC_PUBLIC);
  create_external_class_with_method(
      type::java_lang_Integer(), DexType::make_type("Ljava/lang/Number;"),
      ACC_PUBLIC | ACC_FINAL, "Ljava/lang/Integer;.intValue:()I", ACC_PUBLIC);
}

size_t count_number_int_value_calls(IRCode* code) {
  const auto* number_int_value =
      DexMethod::get_method("Ljava/lang/Number;.intValue:()I");
  size_t count = 0;
  for (const auto& mie : InstructionIterable(code)) {
    if (mie.insn->has_method() && mie.insn->get_method() == number_int_value) {
      ++count;
    }
  }
  return count;
}

bool has_const(IRCode* code, reg_t dest, int64_t value) {
  for (const auto& mie : InstructionIterable(code)) {
    if (mie.insn->opcode() == OPCODE_CONST && mie.insn->dest() == dest &&
        mie.insn->get_literal() == value) {
      return true;
    }
  }
  return false;
}

} // namespace

// `Number.intValue()` on a boxed Integer dispatches to `Integer.intValue()`:
// Integer is final, so no subclass can override it.
TEST_F(ImmutableTest, integer_through_supertype) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (move-result v0)
      (return-void)
    )
  )");

  do_const_prop(code.get(), m_analyzer, m_config);
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (const v0 100)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// A direct call to the registered getter is replaced the same way.
TEST_F(ImmutableTest, direct_getter_call_removed) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
      (return v0)
    )
  )");

  do_const_prop(code.get(), m_analyzer, ipcp_config());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (const v0 100)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// Without knowing that the getter has no side effects, the call stays.
TEST_F(ImmutableTest, getter_call_not_known_pure_kept) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (move-result v0)
      (return v0)
    )
  )");
  auto config = ipcp_config();
  UnorderedSet<DexMethodRef*> no_pure_methods;
  config.pure_methods = &no_pure_methods;

  do_const_prop(code.get(), m_analyzer, config);
  EXPECT_EQ(count_number_int_value_calls(code.get()), 1);
}

// The call through the supertype reaches the registered getter, so a constant
// result replaces the whole call.
TEST_F(ImmutableTest, call_through_supertype_removed) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (move-result v0)
      (return v0)
    )
  )");

  do_const_prop(code.get(), m_analyzer, ipcp_config());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (const v0 100)
      (return v0)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// Inside a try, the call ends its block and its result starts the next one.
TEST_F(ImmutableTest, call_through_supertype_in_try_removed) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (.try_start a)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (move-result v0)
      (.try_end a)
      (return v0)
      (.catch (a))
      (const v0 -1)
      (return v0)
    )
  )");

  do_const_prop(code.get(), m_analyzer, ipcp_config());
  EXPECT_EQ(count_number_int_value_calls(code.get()), 0);
  EXPECT_TRUE(has_const(code.get(), 0, 100));
}

// An Integer whose value differs between two paths: the call stays.
TEST_F(ImmutableTest, call_through_supertype_with_unknown_result_kept) {
  create_number_and_integer();
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (if-eqz v2 :other)
      (const v1 7)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (goto :call)
      (:other)
      (const v1 8)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v0)
      (:call)
      (invoke-virtual (v0) "Ljava/lang/Number;.intValue:()I")
      (move-result v0)
      (return v0)
    )
  )");

  do_const_prop(code.get(), m_analyzer, ipcp_config());
  EXPECT_EQ(count_number_int_value_calls(code.get()), 1);
}

// A string result replaces the call with a `const-string`.
TEST_F(ImmutableTest, call_through_supertype_with_string_result_removed) {
  create_external_class_with_method(
      DexType::make_type("LSuperLabel;"), type::java_lang_Object(),
      ACC_PUBLIC | ACC_ABSTRACT, "LSuperLabel;.label:()Ljava/lang/String;",
      ACC_PUBLIC);
  create_external_class_with_method(
      DexType::make_type("LLabel;"), DexType::make_type("LSuperLabel;"),
      ACC_PUBLIC | ACC_FINAL, "LLabel;.label:()Ljava/lang/String;", ACC_PUBLIC);
  cp::ImmutableAttributeAnalyzerState analyzer_state;
  analyzer_state
      .add_initializer(dynamic_cast<DexMethod*>(DexMethod::make_method(
                           "LLabel;.<init>:(Ljava/lang/String;)V")),
                       dynamic_cast<DexMethod*>(DexMethod::get_method(
                           "LLabel;.label:()Ljava/lang/String;")))
      .set_src_id_of_attr(1)
      .set_src_id_of_obj(0);
  auto code = assembler::ircode_from_string(R"(
    (
      (const-string "x")
      (move-result-pseudo-object v1)
      (new-instance "LLabel;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LLabel;.<init>:(Ljava/lang/String;)V")
      (invoke-virtual (v0) "LSuperLabel;.label:()Ljava/lang/String;")
      (move-result-object v2)
      (return-object v2)
    )
  )");
  do_const_prop(code.get(),
                ImmutableAnalyzer(nullptr, &analyzer_state, nullptr),
                ipcp_config(analyzer_state));
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "x")
      (move-result-pseudo-object v1)
      (new-instance "LLabel;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LLabel;.<init>:(Ljava/lang/String;)V")
      (const-string "x")
      (move-result-pseudo-object v2)
      (return-object v2)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

namespace {

// Creates the abstract class `LSuper;` declaring `value()` with `access` and
// returns its type.
DexType* create_super(DexAccessFlags access = ACC_PUBLIC) {
  auto* type = DexType::make_type("LSuper;");
  create_external_class_with_method(type, type::java_lang_Object(),
                                    ACC_PUBLIC | ACC_ABSTRACT,
                                    "LSuper;.value:()I", access);
  return type;
}

// Creates the interface `LNamed;` declaring `value()` with `access` and
// returns its type.
DexType* create_interface(DexAccessFlags access = ACC_PUBLIC | ACC_ABSTRACT) {
  auto* type = DexType::make_type("LNamed;");
  create_external_class_with_method(type, type::java_lang_Object(),
                                    ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT,
                                    "LNamed;.value:()I", access);
  return type;
}

// Returns whether `call`, an invoke of a `value()` method on an object that
// `LBase;.<init>(I)V` initialized with 7, folds to 7. `getter` is the attribute
// getter `LBase;.<init>` initializes.
bool call_on_base_folds(const char* getter, const std::string& call) {
  cp::ImmutableAttributeAnalyzerState analyzer_state;
  analyzer_state
      .add_initializer(dynamic_cast<DexMethod*>(
                           DexMethod::make_method("LBase;.<init>:(I)V")),
                       dynamic_cast<DexMethod*>(DexMethod::get_method(getter)))
      .set_src_id_of_attr(1)
      .set_src_id_of_obj(0);
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 7)
      (new-instance "LBase;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LBase;.<init>:(I)V")
      )" + call + R"(
      (move-result v2)
      (return v2)
    )
  )");
  cp::Transform::Config config;
  config.replace_move_result_with_consts = true;
  ConstantPropagationTest::do_const_prop(
      code.get(), ImmutableAnalyzer(nullptr, &analyzer_state, nullptr), config);
  for (const auto& mie : InstructionIterable(code.get())) {
    if (mie.insn->opcode() == OPCODE_CONST && mie.insn->get_literal() == 7 &&
        mie.insn->dest() == 2) {
      return true;
    }
  }
  return false;
}

// An object initialized by `Base.<init>` may be an instance of a subclass of
// Base, which can override the getter `Base.value()`. Base extends
// `called_class`, or implements it when it is an interface. Returns whether the
// call `called_class.value()` on such an object folds to the value
// `Base.<init>` recorded.
bool getter_through_supertype_folds(DexAccessFlags base_access,
                                    DexAccessFlags getter_access,
                                    DexType* called_class) {
  auto* called_cls = type_class(called_class);
  const bool through_interface =
      called_cls != nullptr && is_interface(called_cls);
  create_external_class_with_method(
      DexType::make_type("LBase;"),
      through_interface ? type::java_lang_Object() : called_class, base_access,
      "LBase;.value:()I", getter_access,
      through_interface ? called_class : nullptr);
  return call_on_base_folds(
      "LBase;.value:()I",
      std::string("(") +
          (through_interface ? "invoke-interface" : "invoke-virtual") +
          " (v0) \"" + called_class->str() + ".value:()I\")");
}

} // namespace

TEST_F(ImmutableTest, getter_through_supertype_on_final_class) {
  EXPECT_TRUE(getter_through_supertype_folds(ACC_PUBLIC | ACC_FINAL, ACC_PUBLIC,
                                             create_super()));
}

TEST_F(ImmutableTest, final_getter_through_supertype) {
  EXPECT_TRUE(getter_through_supertype_folds(ACC_PUBLIC, ACC_PUBLIC | ACC_FINAL,
                                             create_super()));
}

TEST_F(ImmutableTest, protected_getter_through_supertype) {
  EXPECT_TRUE(getter_through_supertype_folds(
      ACC_PUBLIC | ACC_FINAL, ACC_PROTECTED, create_super(ACC_PROTECTED)));
}

TEST_F(ImmutableTest, getter_through_interface_on_final_class) {
  EXPECT_TRUE(getter_through_supertype_folds(ACC_PUBLIC | ACC_FINAL, ACC_PUBLIC,
                                             create_interface()));
}

TEST_F(ImmutableTest, overridable_getter_through_interface) {
  EXPECT_FALSE(getter_through_supertype_folds(ACC_PUBLIC, ACC_PUBLIC,
                                              create_interface()));
}

TEST_F(ImmutableTest, final_getter_through_interface) {
  EXPECT_TRUE(getter_through_supertype_folds(ACC_PUBLIC, ACC_PUBLIC | ACC_FINAL,
                                             create_interface()));
}

// An invoke-virtual of `Abstract.value()`, which only the interface Named
// declares, dispatches to the getter `Base.value()` like the interface call.
TEST_F(ImmutableTest, getter_through_method_declared_only_by_interface) {
  auto* intf = create_interface();
  auto* abstract_type = DexType::make_type("LAbstract;");
  ClassCreator abstract_creator(abstract_type);
  abstract_creator.set_super(type::java_lang_Object());
  abstract_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  abstract_creator.add_interface(intf);
  abstract_creator.set_external();
  abstract_creator.create();
  create_external_class_with_method(DexType::make_type("LBase;"), abstract_type,
                                    ACC_PUBLIC | ACC_FINAL, "LBase;.value:()I",
                                    ACC_PUBLIC);
  EXPECT_TRUE(call_on_base_folds(
      "LBase;.value:()I", R"((invoke-virtual (v0) "LAbstract;.value:()I"))"));
}

// As above, but `Abstract` extends `Hidden`, which is missing from the input.
// `Hidden` could declare a package-private `value()` that the invoke-virtual
// reaches instead of the getter, so the call is left alone.
TEST_F(ImmutableTest, getter_through_interface_method_with_missing_superclass) {
  auto* intf = create_interface();
  auto* abstract_type = DexType::make_type("LAbstract;");
  ClassCreator abstract_creator(abstract_type);
  abstract_creator.set_super(DexType::make_type("LHidden;"));
  abstract_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  abstract_creator.add_interface(intf);
  abstract_creator.set_external();
  abstract_creator.create();
  create_external_class_with_method(DexType::make_type("LBase;"), abstract_type,
                                    ACC_PUBLIC | ACC_FINAL, "LBase;.value:()I",
                                    ACC_PUBLIC);
  EXPECT_FALSE(call_on_base_folds(
      "LBase;.value:()I", R"((invoke-virtual (v0) "LAbstract;.value:()I"))"));
}

// The getter search does not look at the default methods of interfaces, so an
// interface missing from the input does not stop it.
TEST_F(ImmutableTest, default_method_of_interface_not_searched) {
  auto* intf = create_interface(ACC_PUBLIC);
  ClassCreator creator(DexType::make_type("LBase;"));
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC | ACC_FINAL);
  creator.add_interface(intf);
  creator.add_interface(DexType::make_type("LMissing;"));
  creator.set_external();
  auto* other =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LBase;.other:()I"));
  other->set_access(ACC_PUBLIC);
  other->set_virtual(true);
  other->set_external();
  creator.add_method(other);
  creator.create();
  EXPECT_FALSE(call_on_base_folds(
      "LBase;.other:()I", R"((invoke-interface (v0) "LNamed;.value:()I"))"));
}

// Only a public method implements an interface method.
TEST_F(ImmutableTest, protected_getter_through_interface) {
  EXPECT_FALSE(getter_through_supertype_folds(
      ACC_PUBLIC | ACC_FINAL, ACC_PROTECTED, create_interface()));
}

TEST_F(ImmutableTest, overridable_getter_through_supertype) {
  EXPECT_FALSE(
      getter_through_supertype_folds(ACC_PUBLIC, ACC_PUBLIC, create_super()));
}

// A getter that is neither public nor protected is not known to override the
// called method, so the call is left alone even though the getter is final.
TEST_F(ImmutableTest, package_private_getter_through_supertype) {
  EXPECT_FALSE(
      getter_through_supertype_folds(ACC_PUBLIC, ACC_FINAL, create_super()));
}

// Whether a getter overrides a package-private called method depends on the
// packages, so the call is left alone.
TEST_F(ImmutableTest, getter_through_package_private_supertype_method) {
  EXPECT_FALSE(getter_through_supertype_folds(
      ACC_PUBLIC | ACC_FINAL, ACC_PUBLIC, create_super(DexAccessFlags(0))));
}

// A called method without a definition, such as one declared in a class
// missing from the input, has no known access flags, so it is not known to be
// overridden by the getter, and the call is left alone.
TEST_F(ImmutableTest, getter_through_undefined_method) {
  EXPECT_FALSE(getter_through_supertype_folds(
      ACC_PUBLIC | ACC_FINAL, ACC_PUBLIC, DexType::make_type("LUndefined;")));
}

// An interface call that reaches the registered getter is replaced by its
// constant result too.
TEST_F(ImmutableTest, interface_call_through_supertype_removed) {
  create_external_class_with_method(DexType::make_type("LBase;"),
                                    type::java_lang_Object(),
                                    ACC_PUBLIC | ACC_FINAL, "LBase;.value:()I",
                                    ACC_PUBLIC, create_interface());
  cp::ImmutableAttributeAnalyzerState analyzer_state;
  analyzer_state
      .add_initializer(
          dynamic_cast<DexMethod*>(
              DexMethod::make_method("LBase;.<init>:(I)V")),
          dynamic_cast<DexMethod*>(DexMethod::get_method("LBase;.value:()I")))
      .set_src_id_of_attr(1)
      .set_src_id_of_obj(0);
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 7)
      (new-instance "LBase;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LBase;.<init>:(I)V")
      (invoke-interface (v0) "LNamed;.value:()I")
      (move-result v2)
      (return v2)
    )
  )");
  do_const_prop(code.get(),
                ImmutableAnalyzer(nullptr, &analyzer_state, nullptr),
                ipcp_config(analyzer_state));
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 7)
      (new-instance "LBase;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LBase;.<init>:(I)V")
      (const v2 7)
      (return v2)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ImmutableTest, cached_identity) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 100)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v1)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v2)
      (if-eq v1 v2 :target)
      (const v0 42)
      (goto :end)
      (:target)
      (const v0 23)
      (:end)
      (return-void)
    )
  )");

  do_const_prop(code.get(), m_analyzer, m_config);
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 100)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v1)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v2)
      (const v0 23)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ImmutableTest, not_cached_identity) {
  std::string code_str = R"(
    (
      (const v0 1000)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v1)
      (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result-object v2)
      (if-eq v1 v2 :target)
      (const v0 42)
      (:end)
      (return-void)
      (:target)
      (const v0 23)
      (goto :end)
    )
  )";
  auto code = assembler::ircode_from_string(code_str);

  do_const_prop(code.get(), m_analyzer, m_config);
  auto expected_code = assembler::ircode_from_string(code_str);
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ImmutableTest, integer_join) {
  std::string code_str = R"(
    (
      (load-param v2)
      (load-param v3)

      (if-nez v2 :if-true-label)
      (const v1 100)
      (invoke-static (v1) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result v0)

      (:end)
      (invoke-virtual (v0) "Ljava/lang/Integer;.intValue:()I")
      (move-result v0)
      (return-void)

      (:if-true-label)
      (invoke-static (v2) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
      (move-result v0)
      (goto :end)
    )
  )";
  auto code = assembler::ircode_from_string(code_str);

  do_const_prop(code.get(), m_analyzer, m_config);
  auto expected_code = assembler::ircode_from_string(code_str);
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

/**
 * Java class `Data` has two immutable fields, one is non-private field `id`,
 * another one is a hidden field and we visit it through a function call.
 */
TEST_F(ImmutableTest, object) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (const-string "ValueA")
      (move-result-pseudo-object v2)
      (new-instance "LData;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v2 v1) "LData;.<init>:(Ljava/lang/String;I)V")
      (iget v0 "LData;.id:I")
      (move-result-pseudo-object v3)
      (invoke-virtual (v0) "LData;.toString:()Ljava/lang/String;")
      (move-result v4)
      (return-void)
    )
  )");

  cp::ImmutableAttributeAnalyzerState analyzer_state;
  {
    // Add initializer for Data
    auto* constructor = dynamic_cast<DexMethod*>(
        DexMethod::make_method("LData;.<init>:(Ljava/lang/String;I)V"));
    auto* int_field =
        dynamic_cast<DexField*>(DexField::make_field("LData;.id:I"));
    // Assume we do not know the implementation of this method but we know that
    // the method always returns a hidden immutable field.
    auto* method_ref =
        DexMethod::make_method("LData;.toString:()Ljava/lang/String;");
    always_assert(
        !method_ref->is_def() &&
        !resolve_method_deprecated(method_ref, MethodSearch::Virtual));
    auto* string_getter = dynamic_cast<DexMethod*>(method_ref);
    analyzer_state.add_initializer(constructor, int_field)
        .set_src_id_of_attr(2)
        .set_src_id_of_obj(0);
    analyzer_state.add_initializer(constructor, string_getter)
        .set_src_id_of_attr(1)
        .set_src_id_of_obj(0);
  }
  do_const_prop(code.get(),
                ImmutableAnalyzer(nullptr, &analyzer_state, nullptr),
                m_config);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 100)
      (const-string "ValueA")
      (move-result-pseudo-object v2)
      (new-instance "LData;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v2 v1) "LData;.<init>:(Ljava/lang/String;I)V")
      (const v3 100)
      (invoke-virtual (v0) "LData;.toString:()Ljava/lang/String;")
      (const-string "ValueA")
      (move-result-pseudo-object v4)
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ImmutableTest, enum_constructor) {
  auto* method = assembler::method_from_string(R"(
    (method (private constructor) "LFoo;.<init>:(Ljava/lang/String;I)V"
    (
      (load-param-object v0)
      (load-param-object v1)
      (load-param v2)
      (invoke-direct (v0 v1 v2) "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V")
      (return-void)
    )
    )
  )");
  method->get_code()->build_cfg();
  auto creator = ClassCreator(method->get_class());
  creator.set_super(type::java_lang_Enum());
  creator.set_access(ACC_PUBLIC | ACC_ENUM);
  creator.add_method(method);
  auto* foo_cls = creator.create();
  cp::ImmutableAttributeAnalyzerState analyzer_state;
  cp::immutable_state::analyze_constructors({foo_cls}, &analyzer_state);
  EXPECT_EQ(analyzer_state.method_initializers.count(method), 1);

  // Enum immutable attributes 'name' and 'ordinal' can be propagated.
  auto code = assembler::ircode_from_string(R"(
  (
    (const v0 0)
    (const-string "A")
    (move-result-pseudo-object v1)
    (new-instance "LFoo;")
    (move-result-pseudo-object v2)
    (invoke-direct (v2 v1 v0) "LFoo;.<init>:(Ljava/lang/String;I)V")
    (invoke-virtual (v2) "LFoo;.name:()Ljava/lang/String;")
    (move-result-object v3)
    (invoke-virtual (v2) "LFoo;.ordinal:()I")
    (move-result-object v4)
      (return-void)
  )
  )");
  do_const_prop(code.get(),
                ImmutableAnalyzer(nullptr, &analyzer_state, nullptr),
                m_config);

  auto expected_code = assembler::ircode_from_string(R"(
  (
    (const v0 0)
    (const-string "A")
    (move-result-pseudo-object v1)
    (new-instance "LFoo;")
    (move-result-pseudo-object v2)
    (invoke-direct (v2 v1 v0) "LFoo;.<init>:(Ljava/lang/String;I)V")
    (invoke-virtual (v2) "LFoo;.name:()Ljava/lang/String;")
    (const-string "A")
    (move-result-pseudo-object v3)
    (invoke-virtual (v2) "LFoo;.ordinal:()I")
    (const v4 0)
    (return-void)
  )
  )");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}
