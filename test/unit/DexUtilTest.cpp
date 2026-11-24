/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexUtil.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "IRAssembler.h"
#include "IRInstruction.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "TypeUtil.h"

class DexUtilTest : public RedexTest {};

TEST_F(DexUtilTest, test_java_name_internal_to_external) {
  using namespace java_names;
  EXPECT_EQ("java.lang.String", internal_to_external("Ljava/lang/String;"));
  EXPECT_EQ("[Ljava.lang.String;", internal_to_external("[Ljava/lang/String;"));
  EXPECT_EQ("[[Ljava.lang.String;",
            internal_to_external("[[Ljava/lang/String;"));
  EXPECT_EQ("int", internal_to_external("I"));
  EXPECT_EQ("[I", internal_to_external("[I"));
  EXPECT_EQ("[[I", internal_to_external("[[I"));
  EXPECT_EQ("MyClass", internal_to_external("LMyClass;"));
  EXPECT_EQ("[LMyClass;", internal_to_external("[LMyClass;"));
  EXPECT_EQ("[[LMyClass;", internal_to_external("[[LMyClass;"));
}

TEST_F(DexUtilTest, test_java_name_external_to_internal) {
  using namespace java_names;
  EXPECT_EQ("Ljava/lang/String;", external_to_internal("java.lang.String"));
  EXPECT_EQ("[Ljava/lang/String;", external_to_internal("[Ljava.lang.String;"));
  EXPECT_EQ("[[Ljava/lang/String;",
            external_to_internal("[[Ljava.lang.String;"));

  EXPECT_EQ("I", external_to_internal("int"));
  EXPECT_EQ("LI;", external_to_internal("I"));
  EXPECT_EQ("[I", external_to_internal("[I"));
  EXPECT_EQ("[[I", external_to_internal("[[I"));
  EXPECT_EQ("[[LI;", external_to_internal("[[LI;"));

  EXPECT_EQ("LMyClass;", external_to_internal("MyClass"));
  EXPECT_EQ("[LMyClass;", external_to_internal("[LMyClass;"));
  EXPECT_EQ("[[LMyClass;", external_to_internal("[[LMyClass;"));
  EXPECT_EQ("L;", external_to_internal(""));
  EXPECT_EQ("[[;", external_to_internal("[["));
}

TEST_F(DexUtilTest, test_java_name_get_type_from_external_name) {
  using namespace java_names;
  auto* type = DexType::make_type("LMyClass;");
  auto* array_type = DexType::make_type("[LMyClass;");
  EXPECT_EQ(type, get_type_from_external_name("MyClass"));
  EXPECT_EQ(array_type, get_type_from_external_name("[LMyClass;"));
  EXPECT_EQ(nullptr, get_type_from_external_name("MissingClass"));
}

TEST_F(DexUtilTest, test_java_name_get_element_type_from_external_name) {
  using namespace java_names;
  auto* type = DexType::make_type("LElementOnly;");
  EXPECT_EQ(type, get_element_type_from_external_name("ElementOnly"));
  EXPECT_EQ(type, get_element_type_from_external_name("[LElementOnly;"));
  EXPECT_EQ(type, get_element_type_from_external_name("[[LElementOnly;"));
  EXPECT_EQ(nullptr, get_element_type_from_external_name("[I"));
  EXPECT_EQ(nullptr, get_element_type_from_external_name("MissingClass"));
}

TEST_F(DexUtilTest, test_java_name_internal_to_simple) {
  using namespace java_names;
  EXPECT_EQ("String", internal_to_simple("Ljava/lang/String;"));
  EXPECT_EQ("String[]", internal_to_simple("[Ljava/lang/String;"));
  EXPECT_EQ("String[][]", internal_to_simple("[[Ljava/lang/String;"));
  EXPECT_EQ("int", internal_to_simple("I"));
  EXPECT_EQ("int[]", internal_to_simple("[I"));
  EXPECT_EQ("int[][]", internal_to_simple("[[I"));
  EXPECT_EQ("MyClass", internal_to_simple("LMyClass;"));
  EXPECT_EQ("MyClass[]", internal_to_simple("[LMyClass;"));
  EXPECT_EQ("MyClass[][]", internal_to_simple("[[LMyClass;"));
  EXPECT_EQ("MyClass", internal_to_simple("Lcom/facebook/OuterClass$MyClass;"));
  EXPECT_EQ("MyClass", internal_to_simple("LOuterClassA$OuterClassB$MyClass;"));
  EXPECT_EQ("MyClass[][]", internal_to_simple("[[LOuterClass$MyClass;"));
  EXPECT_EQ("", internal_to_simple("Lcom/facebook/packagename$1;"));
  EXPECT_EQ("NonAnonClass1", internal_to_simple("LOuterClass$NonAnonClass1;"));
  EXPECT_EQ("1NonAnonClass", internal_to_simple("LOuterClass$1NonAnonClass;"));
}

TEST_F(DexUtilTest, is_valid_identifier) {
  EXPECT_TRUE(is_valid_identifier("FooBar123$Hello_World-Test"));

  // TODO: Add support for UTF.
  // TODO: Add support for different dex versions.

  EXPECT_FALSE(is_valid_identifier("[Foo"));
  EXPECT_FALSE(is_valid_identifier("Foo;"));
  EXPECT_FALSE(is_valid_identifier("foo.bar"));
  EXPECT_FALSE(is_valid_identifier("foo/bar"));
}

TEST_F(DexUtilTest, is_valid_identifier_range) {
  std::string s = ";[FooBar123$Hello_World-Test./";
  EXPECT_TRUE(is_valid_identifier(s.substr(2, s.length() - 4)));

  EXPECT_FALSE(is_valid_identifier(s.substr(s.length() - 4)));
  EXPECT_FALSE(is_valid_identifier(s.substr(2, s.length() - 3)));

  EXPECT_FALSE(is_valid_identifier(s.substr(2, 0)));

  std::string mod = s;
  mod[mod.length() / 2] = ';';
  EXPECT_FALSE(is_valid_identifier(mod.substr(2, mod.length() - 4)));
}

// Verifies that create_abstract_method_error_block emits the exact 6
// instructions, in order, with the expected types/methods/registers wired up.
// This is the bytecode that BridgeSynthInlinePass uses to replace the body of
// synthetic bridge methods whose body is invoke-super to an abstract method
// (which would itself throw AbstractMethodError if dispatched).
TEST_F(DexUtilTest, create_abstract_method_error_block_emits_throw_sequence) {
  std::vector<IRInstruction*> block;
  const auto* msg = DexString::make_string("redex-synthesized: LFoo;.bar:()V");
  create_abstract_method_error_block(msg, block);

  ASSERT_EQ(block.size(), 6u);

  // 1: new-instance Ljava/lang/AbstractMethodError;
  EXPECT_EQ(block[0]->opcode(), OPCODE_NEW_INSTANCE);
  ASSERT_NE(block[0]->get_type(), nullptr);
  EXPECT_STREQ(block[0]->get_type()->c_str(),
               "Ljava/lang/AbstractMethodError;");

  // 2: move-result-pseudo-object v0  (captures the new-instance)
  EXPECT_EQ(block[1]->opcode(), IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  EXPECT_EQ(block[1]->dest(), 0u);

  // 3: const-string "<message>"
  EXPECT_EQ(block[2]->opcode(), OPCODE_CONST_STRING);
  EXPECT_EQ(block[2]->get_string(), msg);

  // 4: move-result-pseudo-object v1  (captures the const-string)
  EXPECT_EQ(block[3]->opcode(), IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  EXPECT_EQ(block[3]->dest(), 1u);

  // 5: invoke-direct {v0, v1},
  // Ljava/lang/AbstractMethodError;.<init>:(Ljava/lang/String;)V
  EXPECT_EQ(block[4]->opcode(), OPCODE_INVOKE_DIRECT);
  EXPECT_EQ(block[4]->srcs_size(), 2u);
  EXPECT_EQ(block[4]->src(0), 0u);
  EXPECT_EQ(block[4]->src(1), 1u);
  ASSERT_NE(block[4]->get_method(), nullptr);
  EXPECT_STREQ(block[4]->get_method()->get_class()->c_str(),
               "Ljava/lang/AbstractMethodError;");
  EXPECT_STREQ(block[4]->get_method()->get_name()->c_str(), "<init>");
  ASSERT_NE(block[4]->get_method()->get_proto(), nullptr);
  EXPECT_EQ(block[4]->get_method()->get_proto()->get_rtype(), type::_void());
  ASSERT_NE(block[4]->get_method()->get_proto()->get_args(), nullptr);
  EXPECT_EQ(block[4]->get_method()->get_proto()->get_args()->size(), 1u);

  // 6: throw v0
  EXPECT_EQ(block[5]->opcode(), OPCODE_THROW);
  EXPECT_EQ(block[5]->srcs_size(), 1u);
  EXPECT_EQ(block[5]->src(0), 0u);

  // create_abstract_method_error_block returns owned IRInstructions for the
  // caller to insert into an IRCode/CFG; free them here since the test never
  // hands them off.
  for (auto* insn : block) {
    delete insn;
  }
}

// Moving a method body that calls a method handle to another class needs no
// visibility change for `MethodHandle.invokeExact`, which is public.
TEST_F(DexUtilTest, visibility_changes_of_invoke_polymorphic) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.call:(Ljava/lang/invoke/MethodHandle;I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(I)V")
      (return-void)
     )
    )
  )");
  ClassCreator cc(DexType::make_type("LFoo;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(method);
  cc.create();
  method->get_code()->build_cfg();
  EXPECT_TRUE(
      get_visibility_changes(method, DexType::make_type("LBar;")).empty());
}

// An invoke-super calls the closest method above the class that makes the call,
// so code that makes one cannot move to another class.
TEST_F(DexUtilTest, invoke_super_prevents_relocation) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.m:()V"
     ((load-param-object v0) (return-void)))
  )"));
  base.create();
  ClassCreator sub(DexType::make_type("LSub;"));
  sub.set_super(DexType::make_type("LBase;"));
  auto* f = assembler::method_from_string(R"(
    (method (public) "LSub;.f:()V"
     (
      (load-param-object v0)
      (invoke-super (v0) "LBase;.m:()V")
      (return-void)
     )
    )
  )");
  sub.add_method(f);
  sub.create();
  f->get_code()->build_cfg();
  EXPECT_FALSE(gather_invoked_methods_that_prevent_relocation(f));
}

namespace {

// `LChild;` with a private instance method `priv`, a private static method
// `spriv` and a private static field `sfield`, and `LTarget;` to move code to.
struct RelocationFixture {
  DexMethod* priv;
  DexMethod* spriv;
  DexField* sfield;
  DexType* target;
};

RelocationFixture make_relocation_fixture() {
  ClassCreator child(DexType::make_type("LChild;"));
  child.set_super(type::java_lang_Object());
  auto* priv = assembler::method_from_string(R"(
    (method (private) "LChild;.priv:()V"
     ((load-param-object v0) (return-void)))
  )");
  child.add_method(priv);
  auto* spriv = assembler::method_from_string(R"(
    (method (private static) "LChild;.spriv:()V"
     ((return-void)))
  )");
  child.add_method(spriv);
  auto* sfield = DexField::make_field("LChild;.sfield:I")
                     ->make_concrete(ACC_PRIVATE | ACC_STATIC);
  child.add_field(sfield);
  child.create();
  ClassCreator target(DexType::make_type("LTarget;"));
  target.set_super(type::java_lang_Object());
  return {priv, spriv, sfield, target.create()->get_type()};
}

// Adds the public static method `LChild;.user:()V` with `body`.
DexMethod* add_user(const std::string& body) {
  auto* user = DexMethod::make_method("LChild;.user:()V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                   assembler::ircode_from_string(body),
                                   /* is_virtual */ false);
  type_class(DexType::make_type("LChild;"))->add_method(user);
  return user;
}

} // namespace

// A method handle of kind invoke-direct calls a private instance method like
// invoke-direct does, so a body that holds one cannot move to another class.
TEST_F(DexUtilTest, invoke_direct_method_handle_prevents_relocation) {
  make_relocation_fixture();
  auto* user = add_user(R"((
    (const-method-handle invoke-direct "LChild;.priv:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  user->get_code()->build_cfg();
  UnorderedSet<DexMethodRef*> preventing;
  EXPECT_FALSE(
      gather_invoked_methods_that_prevent_relocation(user, &preventing));
  EXPECT_EQ(preventing.size(), 1u);
  EXPECT_EQ(preventing.count(DexMethod::get_method("LChild;.priv:()V")), 1u);
}

// ART calls an invoke-direct method handle of a method that is not private
// without virtual dispatch, picking the target by the class holding the handle
// (see `resolve_method_handle`), so a body that holds one cannot move to
// another class.
TEST_F(DexUtilTest, nonvirtual_method_handle_prevents_relocation) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (public) "LBase;.m:()V"
     ((load-param-object v0) (return-void)))
  )"));
  base.create();
  ClassCreator child(DexType::make_type("LChild;"));
  child.set_super(DexType::make_type("LBase;"));
  child.create();
  auto* user = add_user(R"((
    (const-method-handle invoke-direct "LBase;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  user->get_code()->build_cfg();
  EXPECT_FALSE(gather_invoked_methods_that_prevent_relocation(user));
}

// A method handle of a private static method is checked for access when it is
// resolved, so moving the body that loads it makes the method public.
TEST_F(DexUtilTest, relocation_makes_method_handle_target_public) {
  auto f = make_relocation_fixture();
  auto* user = add_user(R"((
    (const-method-handle invoke-static "LChild;.spriv:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  user->get_code()->build_cfg();
  ASSERT_TRUE(relocate_method_if_no_changes(user, f.target));
  EXPECT_EQ(user->get_class(), f.target);
  EXPECT_TRUE(is_public(f.spriv));
}

TEST_F(DexUtilTest, visibility_changes_of_field_method_handle) {
  auto f = make_relocation_fixture();
  auto* user = add_user(R"((
    (const-method-handle static-get "LChild;.sfield:I")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  user->get_code()->build_cfg();
  auto changes = get_visibility_changes(user, f.target);
  EXPECT_EQ(changes.fields.size(), 1u);
  EXPECT_EQ(changes.fields.count(f.sfield), 1u);
}

// The bootstrap method of an invoke-custom receives a lookup in the class of
// the code that holds it, so a body that holds one cannot move to another
// class.
TEST_F(DexUtilTest, invoke_custom_prevents_relocation) {
  make_relocation_fixture();
  auto* user = add_user(R"((
    (invoke-static () "LBoot;.placeholder:()Ljava/lang/Runnable;")
    (move-result-object v0)
    (return-void)
  ))");
  redex::make_invoke_custom(user->get_code(), "run", "()Ljava/lang/Runnable;");
  user->get_code()->build_cfg();
  EXPECT_FALSE(gather_invoked_methods_that_prevent_relocation(user));
}

// A bytecode tool can emit an invoke-custom whose bootstrap arguments hold an
// invoke-static handle of a private static method.
TEST_F(DexUtilTest, visibility_changes_of_invoke_custom_bootstrap_argument) {
  auto f = make_relocation_fixture();
  auto* user = add_user(R"((
    (invoke-static () "LBoot;.placeholder:()Ljava/lang/Runnable;")
    (move-result-object v0)
    (return-void)
  ))");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LChild;.spriv:()V")));
  redex::make_invoke_custom(user->get_code(), "run", "()Ljava/lang/Runnable;",
                            std::move(args));
  user->get_code()->build_cfg();
  auto changes = get_visibility_changes(user, f.target);
  EXPECT_EQ(changes.methods.size(), 1u);
  EXPECT_EQ(changes.methods.count(f.spriv), 1u);
}

// ART runs an invoke-direct method handle of a method that is not private and
// that the class holding the handle declares by calling that method itself, so
// moving the body makes that method public, not the one invoke-super would
// call.
TEST_F(DexUtilTest, visibility_changes_of_method_handle_of_own_method) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (protected) "LBase;.m:()V"
     ((load-param-object v0) (return-void)))
  )"));
  base.create();
  ClassCreator child(DexType::make_type("LChild;"));
  child.set_super(DexType::make_type("LBase;"));
  auto* own = assembler::method_from_string(R"(
    (method (protected) "LChild;.m:()V"
     ((load-param-object v0) (return-void)))
  )");
  child.add_method(own);
  child.create();
  ClassCreator target(DexType::make_type("LTarget;"));
  target.set_super(type::java_lang_Object());
  auto* target_type = target.create()->get_type();
  auto* user = add_user(R"((
    (const-method-handle invoke-direct "LChild;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  user->get_code()->build_cfg();
  auto changes = get_visibility_changes(user->get_code(), target_type, user);
  EXPECT_EQ(changes.methods.size(), 1u);
  EXPECT_EQ(changes.methods.count(own), 1u);
}
