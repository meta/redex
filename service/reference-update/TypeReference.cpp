/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeReference.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "MethodHandleRewriter.h"
#include "MethodReference.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
/**
 * The old types should all have definitions so that it's unlikely that we are
 * trying to update a virtual method that may override any external virtual
 * method.
 */
template <typename T>
void assert_old_types_have_definitions(const T& old_to_new) {
  for (const auto& pair : UnorderedIterable(old_to_new)) {
    auto* cls = type_class(pair.first);
    always_assert_log(cls && cls->is_def(),
                      "\t[type-reference] Old type %s should have definition\n",
                      SHOW(pair.first));
  }
}

const DexString* gen_new_name(const std::string_view org_name, size_t seed) {
  constexpr const char* mangling_affix = "$REDEX$";
  auto end = org_name.find(mangling_affix);
  std::string new_name = str_copy(org_name.substr(0, end));
  new_name.append(mangling_affix);
  while (seed != 0u) {
    int d = static_cast<int>(seed % 62);
    if (d < 10) {
      new_name.push_back(static_cast<char>(d + '0'));
    } else if (d < 36) {
      new_name.push_back(static_cast<char>(d - 10 + 'a'));
    } else {
      new_name.push_back(static_cast<char>(d - 36 + 'A'));
    }
    seed /= 62;
  }
  return DexString::make_string(new_name);
}

/**
 * Hash the string representation of the signature of the method.
 */
size_t hash_signature(const DexMethodRef* method) {
  size_t seed = 0;
  auto* proto = method->get_proto();
  boost::hash_combine(seed, method->str());
  boost::hash_combine(seed, proto->get_rtype()->str());
  for (const DexType* arg : *proto->get_args()) {
    boost::hash_combine(seed, arg->str());
  }
  return seed;
}

/**
 * A collection of methods that have the same signatures and ready for type
 * reference updating on their signatures.
 * A method may be in multiple groups if its signature contains multiple old
 * type references that require updating.
 */
struct VMethodGroup {
  // The possible new name. We may not need it if the later updating would not
  // lead any collision or shadowing.
  const DexString* possible_new_name{nullptr};
  DexType* old_type_ref{nullptr};
  DexType* new_type_ref{nullptr};
  UnorderedSet<DexMethod*> methods;
};

/**
 * We group the methods by the old type that their signatures contain and
 * signature hash.
 */
using VMethodGroupKey = size_t;

VMethodGroupKey cal_group_key(DexType* old_type_ref,
                              size_t org_signature_hash) {
  VMethodGroupKey key = org_signature_hash;
  boost::hash_combine(key, old_type_ref->str());
  return key;
}

using VMethodsGroups = std::map<VMethodGroupKey, VMethodGroup>;

void add_vmethod_to_group(DexType* old_type_ref,
                          DexType* new_type_ref,
                          const DexString* possible_new_name,
                          DexMethod* method,
                          VMethodGroup* group) {
  if (group->possible_new_name != nullptr) {
    always_assert(possible_new_name == group->possible_new_name);
    always_assert(old_type_ref == group->old_type_ref);
    always_assert(new_type_ref == group->new_type_ref);
  } else {
    group->possible_new_name = possible_new_name;
    group->old_type_ref = old_type_ref;
    group->new_type_ref = new_type_ref;
  }
  group->methods.insert(method);
}

/**
 * Key of groups is hash result of old type ref and original signature hash.
 */
void add_vmethod_to_groups(
    const UnorderedMap<const DexType*, DexType*>& old_to_new,
    DexMethod* method,
    VMethodsGroups* groups) {
  size_t org_signature_hash = hash_signature(method);
  const auto* possible_new_name =
      gen_new_name(method->str(), org_signature_hash);

  auto* proto = method->get_proto();
  auto* rtype = const_cast<DexType*>(
      type::make_element_type_if_array(proto->get_rtype()));
  if (old_to_new.count(rtype) != 0u) {
    VMethodGroupKey key = cal_group_key(rtype, org_signature_hash);
    auto& group = (*groups)[key];
    add_vmethod_to_group(
        rtype, old_to_new.at(rtype), possible_new_name, method, &group);
  }
  for (const auto* const arg_type : *proto->get_args()) {
    auto* extracted_arg_type =
        const_cast<DexType*>(type::make_element_type_if_array(arg_type));
    if (old_to_new.count(extracted_arg_type) != 0u) {
      VMethodGroupKey key =
          cal_group_key(extracted_arg_type, org_signature_hash);
      auto& group = (*groups)[key];
      add_vmethod_to_group(extracted_arg_type,
                           old_to_new.at(extracted_arg_type),
                           possible_new_name,
                           method,
                           &group);
    }
  }
}

DexProto* get_new_proto(const DexProto* proto,
                        const DexType* old_type_ref,
                        DexType* new_type_ref) {
  return type_reference::get_new_proto(
      proto,
      UnorderedMap<const DexType*, const DexType*>{
          {old_type_ref, new_type_ref}});
}

/**
 * :group We collect methods with exactly the same signatures into a group.
 * Only replace one old type reference with a new old type ref for the group,
 * if the type reference updating would let any one of them collide with
 * existing methods in its hierarchy, we simply rename all the methods by
 * hashing their string representation of signature, so they would also be the
 * same signatures after the updating and we will never break virtual scopes.
 */
void update_vmethods_group_one_type_ref(const VMethodGroup& group,
                                        const SubtypeMaps& subtype_maps) {
  auto* proto = (*unordered_any(group.methods))->get_proto();
  auto* new_proto =
      get_new_proto(proto, group.old_type_ref, group.new_type_ref);
  bool need_rename = false;
  for (auto* method : UnorderedIterable(group.methods)) {
    if (has_signature_collision(subtype_maps, method, new_proto)) {
      need_rename = true;
      break;
    }
  }
  DexMethodSpec spec;
  if (need_rename) {
    for (auto* method : UnorderedIterable(group.methods)) {
      always_assert_log(
          can_rename(method), "Can not rename %s\n", SHOW(method));
    }
    spec.name = group.possible_new_name;
  }
  spec.proto = new_proto;
  for (auto* method : UnorderedIterable(group.methods)) {
    TRACE(REFU,
          8,
          "sig: updating virtual method %s to %s:%s",
          SHOW(method),
          SHOW(spec.name),
          SHOW(spec.proto));
    method->change(spec, false /* rename on collision */);
  }
}
} // namespace

namespace type_reference {

namespace {

// `type` with its type, or element type, replaced if `old_to_new` maps it.
template <typename MapT>
DexType* get_new_type_impl(const DexType* type, const MapT& old_to_new) {
  auto it = old_to_new.find(
      const_cast<DexType*>(type::make_element_type_if_array(type)));
  if (it == old_to_new.end()) {
    return const_cast<DexType*>(type);
  }
  return type::make_array_type(it->second, type::get_array_level(type));
}

// `proto` with every type that `old_to_new` maps, or an array of it, replaced.
template <typename MapT>
DexProto* get_new_proto_impl(const DexProto* proto, const MapT& old_to_new) {
  auto convert = [&](const DexType* type) {
    return get_new_type_impl(type, old_to_new);
  };
  DexTypeList::ContainerType args;
  for (const auto* arg : *proto->get_args()) {
    args.push_back(convert(arg));
  }
  return DexProto::make_proto(convert(proto->get_rtype()),
                              DexTypeList::make_type_list(std::move(args)));
}

/**
 * Replaces by `new_proto(proto)` each prototype that the code in `scope` names
 * other than through a method reference: that of const-method-type, the
 * call-site prototype of invoke-polymorphic, and the method type and
 * method-type arguments of a call site. They describe the methods being called
 * or looked up, so they must change together with those methods' prototypes.
 */
template <typename NewProtoFn>
void update_named_protos(const Scope& scope, const NewProtoFn& new_proto) {
  MethodHandleRewriter callsite_rewriter(
      {.method_type = [&](DexProto* proto) { return new_proto(proto); }});
  walk::parallel::opcodes(scope, [&](DexMethod* method, IRInstruction* insn) {
    if (insn->has_proto()) {
      insn->set_proto(new_proto(insn->get_proto()));
    } else if (insn->has_signature_polymorphic()) {
      insn->set_signature_polymorphic(
          insn->get_signature_polymorphic()->method(),
          new_proto(insn->get_callsite_proto()));
    } else {
      callsite_rewriter.rewrite(insn, method);
    }
  });
}

template <typename MapT>
class TypeRefUpdaterImpl {
 public:
  explicit TypeRefUpdaterImpl(const MapT& old_to_new)
      : m_old_to_new(old_to_new) {}

  void update_methods_fields(const Scope& scope) {
    // Change specs of all the other methods and fields if their specs contain
    // any candidate types.
    walk::parallel::methods(scope, [this](DexMethod* method) {
      if (mangling(method)) {
        always_assert_log(
            can_rename(method), "Method %s can not be renamed\n", SHOW(method));
      }
    });
    walk::parallel::fields(scope, [this](DexField* field) {
      if (mangling(field)) {
        always_assert_log(
            can_rename(field), "Field %s can not be renamed\n", SHOW(field));
      }
    });
    // Update all the method refs and field refs.
    ConcurrentSet<DexMethodRef*> methods;
    ConcurrentSet<DexFieldRef*> fields;
    walk::parallel::code(scope, [&](DexMethod* /*method*/, IRCode& code) {
      std::vector<DexFieldRef*> code_fields;
      std::vector<DexMethodRef*> code_methods;
      if (code.cfg_built()) {
        for (auto& mie : InstructionIterable(code.cfg())) {
          mie.insn->gather_fields(code_fields);
          mie.insn->gather_methods(code_methods);
        }
      } else {
        for (auto& mie : InstructionIterable(code)) {
          mie.insn->gather_fields(code_fields);
          mie.insn->gather_methods(code_methods);
        }
      }
      for (auto* field : code_fields) {
        fields.insert(field);
      }
      for (auto* method : code_methods) {
        methods.insert(method);
      }
    });
    workqueue_run<DexFieldRef*>([this](DexFieldRef* field) { mangling(field); },
                                fields);
    workqueue_run<DexMethodRef*>(
        [this](DexMethodRef* method) { mangling(method); }, methods);
    update_named_protos(scope, [this](const DexProto* proto) {
      return get_new_proto_impl(proto, m_old_to_new);
    });

    std::map<DexMethod*, DexProto*, dexmethods_comparator> inits;
    insert_unordered_iterable(inits, m_inits);
    std::vector<std::pair<DexMethod*, DexProto*>> colliding_inits;
    for (auto& pair : inits) {
      auto* method = pair.first;
      auto* new_proto = pair.second;
      if (DexMethod::get_method(
              method->get_class(), method->get_name(), new_proto) == nullptr) {
        DexMethodSpec spec;
        spec.proto = new_proto;
        method->change(spec, false /* rename on collision */);
        TRACE(REFU, 9, "Update ctor %s ", SHOW(method));
      } else {
        colliding_inits.emplace_back(method->as_def(), new_proto);
      }
    }
    fix_colliding_dmethods(scope, colliding_inits);
  }

 private:
  /**
   * Try to convert "type" to a new type. Return nullptr if it's not found in
   * the old_to_new mapping. LOld; => LNew; [LOld; => [LNew;
   * [[LOld; => [[LNew;
   * ...
   */
  DexType* try_convert_to_new_type(DexType* type) {
    uint32_t level = type::get_array_level(type);
    DexType* elem_type = type;
    if (level != 0u) {
      elem_type = type::make_array_element_type(type);
    }
    if (m_old_to_new.count(elem_type) != 0u) {
      auto* new_type = m_old_to_new.at(elem_type);
      return level != 0u ? type::make_array_type(new_type, level) : new_type;
    }
    return nullptr;
  }

  /**
   * Change a field to new type if its original type is a candidate.
   * Return true if the field is updated.
   */
  bool mangling(DexFieldRef* field) {
    DexType* new_type = try_convert_to_new_type(field->get_type());
    if (new_type != nullptr) {
      size_t seed = 0;
      boost::hash_combine(seed, field->get_type()->str());
      boost::hash_combine(seed, field->str());
      DexFieldSpec spec;
      spec.name = gen_new_name(field->str(), seed);
      spec.type = new_type;
      field->change(spec);
      TRACE(REFU, 9, "Update field %s ", SHOW(field));
      return true;
    }
    return false;
  }

  /**
   * Change proto of a method if its proto contains any candidate.
   */
  bool mangling(DexMethodRef* method) {
    size_t seed = 0;
    DexProto* proto = method->get_proto();
    DexType* rtype = try_convert_to_new_type(proto->get_rtype());
    if (rtype != nullptr) {
      boost::hash_combine(seed, -1);
      boost::hash_combine(seed, proto->get_rtype()->str());
    } else { // Keep unchanged.
      rtype = proto->get_rtype();
    }
    DexTypeList::ContainerType new_args;
    size_t id = 0;
    for (const DexType* arg : *proto->get_args()) {
      // TODO: Remove const-cast when ready.
      const DexType* new_arg =
          try_convert_to_new_type(const_cast<DexType*>(arg));
      if (new_arg != nullptr) {
        boost::hash_combine(seed, id);
        boost::hash_combine(seed, arg->str());
      } else { // Keep unchanged.
        new_arg = arg;
      }
      new_args.push_back(new_arg);
      ++id;
    }
    // Do not need update the signature.
    if (seed == 0) {
      return false;
    }
    DexProto* new_proto = DexProto::make_proto(
        rtype, DexTypeList::make_type_list(std::move(new_args)));
    if (method::is_init(method)) {
      // Handle <init> method definitions separately because their names must be
      // "<init>"
      if (method->is_def()) {
        // Don't check for init collisions here, since mangling() can execute in
        // a parallel context.
        m_inits.emplace(method->as_def(), new_proto);
      } else {
        // TODO(fengliu): Work on D19340102 to figure out these cases.
        TRACE(REFU,
              2,
              "[Warning] Method ref %s has no definition but has internal type "
              "reference in its signature",
              SHOW(method));
        DexMethodSpec spec;
        spec.proto = new_proto;
        method->change(spec, false /* rename on collision */);
      }
    } else {
      DexMethodSpec spec;
      spec.proto = new_proto;
      boost::hash_combine(seed, method->str());
      spec.name = gen_new_name(method->str(), seed);
      method->change(spec, false /* rename on collision */);
      TRACE(REFU, 9, "Update method %s ", SHOW(method));
    }
    return true;
  }

  InsertOnlyConcurrentMap<DexMethod*, DexProto*> m_inits;
  const MapT& m_old_to_new;
};

} // namespace

void TypeRefUpdater::update_methods_fields(const Scope& scope) {
  if (m_old_to_new) {
    TypeRefUpdaterImpl(m_old_to_new->get()).update_methods_fields(scope);
  } else {
    TypeRefUpdaterImpl(m_old_to_new_const->get()).update_methods_fields(scope);
  }
}

TypeRefUpdater::TypeRefUpdater(
    const UnorderedMap<DexType*, DexType*>& old_to_new)
    : m_old_to_new(old_to_new) {
  assert_old_types_have_definitions(old_to_new);
}

TypeRefUpdater::TypeRefUpdater(
    const UnorderedMap<const DexType*, DexType*>& old_to_new)
    : m_old_to_new_const(old_to_new) {
  assert_old_types_have_definitions(old_to_new);
}

const DexString* new_name(const DexMethodRef* method) {
  return gen_new_name(method->str(), hash_signature(method));
}

const DexString* new_name(const DexFieldRef* field) {
  size_t seed = 0;
  boost::hash_combine(seed, field->str());
  boost::hash_combine(seed, field->get_type()->str());
  return gen_new_name(field->str(), seed);
}

std::string get_method_signature(const DexMethod* method) {
  std::ostringstream ss;
  auto* proto = method->get_proto();
  ss << show(proto->get_rtype()) << " ";
  ss << method->get_simple_deobfuscated_name();
  auto* arg_list = proto->get_args();
  if (!arg_list->empty()) {
    ss << "(";
    for (const auto* t : *arg_list) {
      ss << show(t) << ", ";
    }
    ss.seekp(-2, std::ios_base::end);
    ss << ")";
  }

  return ss.str();
}

bool proto_has_reference_to(const DexProto* proto,
                            const UnorderedTypeSet& targets) {
  const auto* rtype = type::make_element_type_if_array(proto->get_rtype());
  if (targets.count(rtype) != 0u) {
    return true;
  }
  for (const auto* const arg_type : *proto->get_args()) {
    const auto* extracted_arg_type = type::make_element_type_if_array(arg_type);
    if (targets.count(extracted_arg_type) != 0u) {
      return true;
    }
  }
  return false;
}

DexProto* get_new_proto(
    const DexProto* proto,
    const UnorderedMap<const DexType*, DexType*>& old_to_new) {
  return get_new_proto_impl(proto, old_to_new);
}

DexProto* get_new_proto(
    const DexProto* proto,
    const UnorderedMap<const DexType*, const DexType*>& old_to_new) {
  return get_new_proto_impl(proto, old_to_new);
}

DexType* get_new_type(
    const DexType* type,
    const UnorderedMap<const DexType*, DexType*>& old_to_new) {
  return get_new_type_impl(type, old_to_new);
}

void update_method_signature_type_references(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& old_to_new,
    const SubtypeMaps& subtype_maps,
    std::optional<std::reference_wrapper<UnorderedMap<DexMethod*, std::string>>>
        method_debug_map) {
  // Virtual methods.
  // The key is the hash of signature and an old type reference. Group the
  // methods by key.
  VMethodsGroups vmethods_groups;
  // Colliding direct methods.
  std::vector<std::pair<DexMethod*, DexProto*>> colliding_directs;

  // Callback for updating method debug map.
  std::function<void(DexMethod*)> update_method_debug_map = [](DexMethod*) {};
  if (method_debug_map != std::nullopt) {
    update_method_debug_map = [&method_debug_map](DexMethod* method) {
      method_debug_map->get()[method] = get_method_signature(method);
    };
  }

  UnorderedTypeSet old_types;
  for (const auto& pair : UnorderedIterable(old_to_new)) {
    old_types.insert(pair.first);
  }

  walk::methods(scope, [&](DexMethod* method) {
    auto* proto = method->get_proto();
    if (!proto_has_reference_to(proto, old_types)) {
      return;
    }
    update_method_debug_map(method);
    if (!method->is_virtual()) {
      auto* new_proto = get_new_proto(proto, old_to_new);
      /// A. For direct methods:
      // If there is no collision, update spec directly.
      // If it's not constructor and renamable, rename on collision.
      // Otherwise, add it to colliding_directs.
      auto* collision = DexMethod::get_method(
          method->get_class(), method->get_name(), new_proto);
      if ((collision == nullptr) ||
          (!method::is_init(method) && can_rename(method))) {
        TRACE(REFU, 8, "sig: updating direct method %s", SHOW(method));
        DexMethodSpec spec;
        spec.proto = new_proto;
        method->change(spec, true /* rename on collision */);
      } else {
        colliding_directs.emplace_back(method, new_proto);
      }
      return;
    }
    // B. For virtual methods: Collect the methods that reference the old
    // types to oldtype_to_vmethods. Calculate new proto for each method and
    // store to method_to_new_proto.
    add_vmethod_to_groups(old_to_new, method, &vmethods_groups);
  });

  // Solve updating collision for direct methods by appending primitive
  // arguments.
  fix_colliding_dmethods(scope, colliding_directs);

  // Update virtual methods group by group.
  for (auto& key_and_group : vmethods_groups) {
    auto& group = key_and_group.second;
    update_vmethods_group_one_type_ref(group, subtype_maps);
  }

  update_named_protos(scope, [&old_to_new](const DexProto* proto) {
    return get_new_proto(proto, old_to_new);
  });

  // Ensure that no method references left that still refer old types.
  walk::parallel::code(scope, [&old_types](DexMethod*, IRCode& code) {
    std::vector<DexMethodRef*> methods;
    auto check = [&](const IRInstruction* insn) {
      methods.clear();
      insn->gather_methods(methods);
      for (const auto* method : methods) {
        always_assert_log(
            !proto_has_reference_to(method->get_proto(), old_types),
            "Find old type in method reference %s, please make sure that "
            "ReBindRefsPass is enabled before the crashed pass.\n",
            SHOW(insn));
      }
    };
    if (code.cfg_built()) {
      auto& cfg = code.cfg();
      for (auto& mie : InstructionIterable(cfg)) {
        check(mie.insn);
      }
    } else {
      for (auto& mie : InstructionIterable(code)) {
        check(mie.insn);
      }
    }
  });
}

void update_field_type_references(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& old_to_new) {
  TRACE(REFU, 4, " updating field refs");
  const auto update_field = [&](DexFieldRef* field) {
    auto* const ref_type = field->get_type();
    const auto* const type = type::make_element_type_if_array(ref_type);
    if (old_to_new.count(type) == 0) {
      return;
    }
    DexFieldSpec spec;
    auto* new_type = old_to_new.at(type);
    auto level = type::get_array_level(ref_type);
    auto* new_type_incl_array = type::make_array_type(new_type, level);
    spec.type = new_type_incl_array;
    field->change(spec);
    TRACE(REFU, 9, " updating field ref to %s", SHOW(type));
  };
  walk::parallel::fields(scope, update_field);

  walk::parallel::code(scope, [&old_to_new](DexMethod*, IRCode& code) {
    std::vector<DexFieldRef*> fields;
    auto check = [&](const IRInstruction* insn) {
      fields.clear();
      insn->gather_fields(fields);
      for (const auto* field : fields) {
        const auto* const type =
            type::make_element_type_if_array(field->get_type());
        always_assert_log(
            old_to_new.count(type) == 0,
            "Find old type in field reference %s, please make sure that "
            "ReBindRefsPass is enabled before ClassMergingPass\n",
            SHOW(insn));
      }
    };
    if (code.cfg_built()) {
      auto& cfg = code.cfg();
      for (auto& mie : InstructionIterable(cfg)) {
        check(mie.insn);
      }
    } else {
      for (auto& mie : InstructionIterable(code)) {
        check(mie.insn);
      }
    }
  });
}

void fix_colliding_dmethods(
    const Scope& scope,
    const std::vector<std::pair<DexMethod*, DexProto*>>& colliding_methods) {
  if (colliding_methods.empty()) {
    return;
  }
  // Fix colliding methods by appending an additional param.
  TRACE(REFU, 9, "sig: colliding_methods %zu", colliding_methods.size());
  UnorderedMap<DexMethod*, size_t> num_additional_args;
  for (auto it : colliding_methods) {
    auto* meth = it.first;
    auto* new_proto = it.second;
    auto* new_arg_list = new_proto->get_args()->push_back(type::_int());
    new_proto = DexProto::make_proto(new_proto->get_rtype(), new_arg_list);
    size_t arg_count = 1;
    while (DexMethod::get_method(
               meth->get_class(), meth->get_name(), new_proto) != nullptr) {
      new_arg_list = new_proto->get_args()->push_back(type::_int());
      new_proto = DexProto::make_proto(new_proto->get_rtype(), new_arg_list);
      ++arg_count;
    }

    DexMethodSpec spec;
    spec.proto = new_proto;
    meth->change(spec, false /* rename on collision */);
    num_additional_args[meth] = arg_count;

    auto* code = meth->get_code();
    if (code->cfg_built()) {
      auto& cfg = code->cfg();
      auto* block = cfg.entry_block();
      auto last_loading = block->get_last_param_loading_insn();
      for (size_t i = 0; i < arg_count; ++i) {
        auto new_param_reg = cfg.allocate_temp();
        auto* new_param_load = new IRInstruction(IOPCODE_LOAD_PARAM);
        new_param_load->set_dest(new_param_reg);
        if (last_loading != block->end()) {
          cfg.insert_after(block->to_cfg_instruction_iterator(last_loading),
                           new_param_load);
        } else {
          cfg.insert_before(block->to_cfg_instruction_iterator(
                                block->get_first_non_param_loading_insn()),
                            new_param_load);
        }
        last_loading = block->get_last_param_loading_insn();
      }
    } else {
      for (size_t i = 0; i < arg_count; ++i) {
        auto new_param_reg = code->allocate_temp();
        auto params = code->get_param_instructions();
        auto* new_param_load = new IRInstruction(IOPCODE_LOAD_PARAM);
        new_param_load->set_dest(new_param_reg);
        code->insert_before(params.end(), new_param_load);
      }
    }
    TRACE(REFU,
          9,
          "sig: patching colliding method %s with %zu additional args",
          SHOW(meth),
          arg_count);
  }

  walk::parallel::code(scope, [&](DexMethod* meth, IRCode& code) {
    method_reference::CallSites callsites;
    if (code.cfg_built()) {
      auto& cfg = code.cfg();
      for (auto& mie : InstructionIterable(cfg)) {
        auto* insn = mie.insn;
        if (!insn->has_method()) {
          continue;
        }
        auto* const callee = resolve_method_deprecated(
            insn->get_method(), opcode_to_search(insn), meth);
        if (callee == nullptr ||
            num_additional_args.find(callee) == num_additional_args.end()) {
          continue;
        }
        callsites.emplace_back(meth, &mie, insn, callee);
      }
    } else {
      for (auto& mie : InstructionIterable(code)) {
        auto* insn = mie.insn;
        if (!insn->has_method()) {
          continue;
        }
        auto* const callee = resolve_method_deprecated(
            insn->get_method(), opcode_to_search(insn), meth);
        if (callee == nullptr ||
            num_additional_args.find(callee) == num_additional_args.end()) {
          continue;
        }
        callsites.emplace_back(meth, &mie, insn, callee);
      }
    }

    for (const auto& callsite : callsites) {
      auto* callee = callsite.callee;
      always_assert(callee != nullptr);
      TRACE(REFU,
            9,
            "sig: patching colliding method callsite to %s in %s",
            SHOW(callee),
            SHOW(meth));
      // 42 is a dummy int val as the additional argument to the patched
      // colliding method.
      std::vector<uint32_t> additional_args;
      additional_args.reserve(num_additional_args.at(callee));
      for (size_t i = 0; i < num_additional_args.at(callee); ++i) {
        additional_args.push_back(42);
      }
      method_reference::NewCallee new_callee(callee, additional_args);
      method_reference::patch_callsite(callsite, new_callee);
    }
  });
}

} // namespace type_reference
