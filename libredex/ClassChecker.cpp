/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <iterator>
#include <mutex>
#include <optional>
#include <string>
#include <vector>

#include "ClassChecker.h"
#include "ClassHierarchy.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "RedexContext.h"
#include "Show.h"
#include "Timer.h"
#include "TypeUtil.h"
#include "Walkers.h"
#include "WorkQueue.h"

namespace {

constexpr const size_t MAX_ITEMS_TO_PRINT = 20;
constexpr const char* INDENTATION = "    ";

template <typename Collection>
void print_failed_things(const Collection& items, std::ostringstream* oss) {
  size_t counter = 0;
  for (auto& fail : UnorderedIterable(items)) {
    auto cls_name = show(fail);
    *oss << cls_name;
    if (cls_name != fail->get_deobfuscated_name_or_empty_copy()) {
      *oss << " (deobfuscated: " << fail->get_deobfuscated_name_or_empty_copy()
           << ')';
    }
    *oss << '\n';
    counter++;
    if (counter == MAX_ITEMS_TO_PRINT) {
      if (items.size() > MAX_ITEMS_TO_PRINT) {
        *oss << "...truncated...\n";
      }
      break;
    }
  }
}

void print_failed_external_check(
    const ConcurrentMap<const DexClass*,
                        InsertOnlyConcurrentSet<const DexType*>>&
        failed_classes_external_check,
    std::ostringstream* oss) {
  size_t counter = 0;
  for (const auto& pair : UnorderedIterable(failed_classes_external_check)) {
    auto cls_name = show(pair.first);
    *oss << "Internal class " << cls_name;
    if (cls_name != pair.first->get_deobfuscated_name_or_empty_copy()) {
      *oss << " (deobfuscated: "
           << pair.first->get_deobfuscated_name_or_empty_copy() << ')';
    }
    *oss << "\n  has external children:\n";
    for (const auto* type : UnorderedIterable(pair.second)) {
      *oss << INDENTATION << show(type) << '\n';
    }
    counter++;
    if (counter == MAX_ITEMS_TO_PRINT) {
      if (failed_classes_external_check.size() > MAX_ITEMS_TO_PRINT) {
        *oss << "...truncated...\n";
      }
      break;
    }
  }
}

void print_failed_definition_check(
    const ConcurrentMap<const DexClass*,
                        InsertOnlyConcurrentSet<const DexType*>>&
        failed_classes_definition_check,
    std::ostringstream* oss) {
  size_t counter = 0;
  for (const auto& pair : UnorderedIterable(failed_classes_definition_check)) {
    auto cls_name = show(pair.first);
    *oss << "Internal class " << cls_name;
    if (cls_name != pair.first->get_deobfuscated_name_or_empty_copy()) {
      *oss << " (deobfuscated: "
           << pair.first->get_deobfuscated_name_or_empty_copy() << ')';
    }
    *oss << "\n  references type not defined internally or externally:\n";
    for (const auto* type : UnorderedIterable(pair.second)) {
      *oss << INDENTATION << show(type) << '\n';
    }

    counter++;
    if (counter == MAX_ITEMS_TO_PRINT) {
      if (failed_classes_definition_check.size() > MAX_ITEMS_TO_PRINT) {
        *oss << "...truncated...\n";
      }
      break;
    }
  }
}

struct NameAndProto {
  const DexString* name;
  const DexProto* proto;
  explicit NameAndProto(const DexMethod* m)
      : name(m->get_name()), proto(m->get_proto()) {}
};

struct compare_name_and_proto {
  bool operator()(const NameAndProto& l, const NameAndProto& r) const {
    if (l.name == r.name) {
      return compare_dexprotos(l.proto, r.proto);
    }
    return compare_dexstrings(l.name, r.name);
  }
};

using NamedMethodMap =
    std::map<NameAndProto, const DexMethod*, compare_name_and_proto>;

template <typename Collection>
bool has_colliding_methods(const DexClass* cls,
                           const NamedMethodMap& final_methods,
                           const DexClass* child_cls,
                           Collection* failures) {
  bool result{false};
  for (const auto& v : child_cls->get_vmethods()) {
    NameAndProto np(v);
    auto search = final_methods.find(np);
    if (search != final_methods.end()) {
      // Check package visibility rules per
      // https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-5.html#jvms-5.4.5
      const auto* super_method = search->second;
      if (is_public(super_method) || is_protected(super_method) ||
          type::same_package(cls->get_type(), child_cls->get_type())) {
        result = true;
        failures->insert(v);
      }
    }
  }
  return result;
}

// The type and, if it has a definition, where that comes from.
std::string describe(const DexType* type) {
  std::string res = show(type);
  const auto* cls = type_class(type);
  if (cls != nullptr && cls->get_location() != nullptr &&
      !cls->get_location()->get_file_name().empty()) {
    res += " (from " + cls->get_location()->get_file_name() + ")";
  }
  return res;
}

std::vector<const DexClass*> get_defined_supertypes(const DexClass* cls) {
  std::vector<const DexClass*> res;
  if (cls->get_super_class() != nullptr) {
    const auto* super_cls = type_class(cls->get_super_class());
    if (super_cls != nullptr) {
      res.push_back(super_cls);
    }
  }
  for (const auto* intf : *cls->get_interfaces()) {
    const auto* intf_cls = type_class(intf);
    if (intf_cls != nullptr) {
      res.push_back(intf_cls);
    }
  }
  return res;
}

// Describes a cycle of defined supertypes for each supertype edge that closes
// one, searching depth-first from `classes` with an explicit stack, as
// hierarchies can be deep.
void find_supertype_cycles(const std::vector<const DexClass*>& classes,
                           std::vector<std::string>* errors) {
  enum class State { kOnStack, kDone };
  UnorderedMap<const DexClass*, State> states;
  struct Frame {
    const DexClass* cls;
    std::vector<const DexClass*> supertypes;
    size_t next{0};
  };
  for (const auto* root : classes) {
    if (states.find(root) != states.end()) {
      continue;
    }
    std::vector<Frame> stack;
    stack.push_back({root, get_defined_supertypes(root)});
    states.emplace(root, State::kOnStack);
    while (!stack.empty()) {
      auto& frame = stack.back();
      if (frame.next == frame.supertypes.size()) {
        states[frame.cls] = State::kDone;
        stack.pop_back();
        continue;
      }
      const auto* super_cls = frame.supertypes[frame.next++];
      auto it = states.find(super_cls);
      if (it == states.end()) {
        states.emplace(super_cls, State::kOnStack);
        stack.push_back({super_cls, get_defined_supertypes(super_cls)});
        continue;
      }
      if (it->second == State::kDone) {
        continue;
      }
      if (super_cls == frame.cls) {
        // The superclass, when defined, comes first in `supertypes`.
        bool via_superclass =
            frame.next == 1 && frame.cls->get_super_class() != nullptr &&
            type_class(frame.cls->get_super_class()) == frame.cls;
        errors->push_back(
            "Class " + describe(super_cls->get_type()) +
            (via_superclass ? " extends itself" : " implements itself"));
        continue;
      }
      auto start =
          std::find_if(stack.begin(), stack.end(),
                       [&](const Frame& f) { return f.cls == super_cls; });
      std::string cycle;
      for (auto f = start; f != stack.end(); ++f) {
        cycle += describe(f->cls->get_type()) + " -> ";
      }
      cycle += show(super_cls);
      errors->push_back("Class " + show(super_cls) +
                        " is its own supertype: " + cycle);
    }
  }
}

} // namespace

std::optional<std::string> check_class_hierarchy(const Scope& scope) {
  std::vector<const DexClass*> classes(scope.begin(), scope.end());
  const auto& external_classes = g_redex->external_classes();
  classes.insert(classes.end(), external_classes.begin(),
                 external_classes.end());
  std::sort(classes.begin(), classes.end(), compare_dexclasses);
  classes.erase(std::unique(classes.begin(), classes.end()), classes.end());

  // The messages follow ART's ClassLinker. Each class's messages go to its own
  // slot, so that the report does not depend on thread scheduling.
  std::vector<std::vector<std::string>> errors_by_class(classes.size());
  workqueue_run_for<size_t>(0, classes.size(), [&](size_t i) {
    const auto* cls = classes[i];
    auto& errors = errors_by_class[i];
    const auto* super = cls->get_super_class();
    if (is_interface(cls)) {
      if (super != type::java_lang_Object()) {
        errors.push_back(
            "Interface " + describe(cls->get_type()) +
            (super == nullptr ? std::string(" has no superclass")
                              : " has superclass " + describe(super)) +
            ", but interfaces must have java.lang.Object as superclass");
      }
    } else if (super != nullptr) {
      const auto* super_cls = type_class(super);
      if (super_cls != nullptr && is_interface(super_cls)) {
        errors.push_back("Superclass " + describe(super) + " of " +
                         describe(cls->get_type()) + " is an interface");
      } else if (super_cls != nullptr && is_final(super_cls)) {
        errors.push_back("Superclass " + describe(super) + " of " +
                         describe(cls->get_type()) + " is declared final");
      }
    }
    for (const auto* intf : *cls->get_interfaces()) {
      const auto* intf_cls = type_class(intf);
      if (intf_cls != nullptr && !is_interface(intf_cls)) {
        errors.push_back("Class " + describe(cls->get_type()) +
                         " implements non-interface class " + describe(intf));
      }
    }
  });
  std::vector<std::string> errors;
  for (auto& class_errors : errors_by_class) {
    errors.insert(errors.end(), std::make_move_iterator(class_errors.begin()),
                  std::make_move_iterator(class_errors.end()));
  }
  find_supertype_cycles(classes, &errors);
  if (errors.empty()) {
    return std::nullopt;
  }

  std::ostringstream oss;
  oss << "Classes the runtime cannot link (inconsistent input, e.g. a library "
         "jar older than the code compiled against it):\n";
  for (size_t i = 0; i < errors.size() && i < MAX_ITEMS_TO_PRINT; ++i) {
    oss << errors[i] << '\n';
  }
  if (errors.size() > MAX_ITEMS_TO_PRINT) {
    oss << "...truncated (" << errors.size() << " in total)...\n";
  }
  return oss.str();
}

ClassChecker::ClassChecker() : m_good(true) {}

void ClassChecker::init_setting(
    bool definition_check,
    const UnorderedSet<std::string>& definition_check_allowlist,
    const UnorderedSet<std::string>& definition_check_allowlist_prefixes,
    bool external_check,
    const UnorderedSet<std::string>& external_check_allowlist,
    const UnorderedSet<std::string>& external_check_allowlist_prefixes) {
  m_external_check = external_check;
  m_external_check_allowlist_prefixes = external_check_allowlist_prefixes;
  m_definition_check = definition_check;
  m_definition_check_allowlist_prefixes = definition_check_allowlist_prefixes;
  for (const auto& cls_string : UnorderedIterable(definition_check_allowlist)) {
    auto* type = DexType::get_type(cls_string);
    if (type != nullptr) {
      m_definition_check_allowlist.emplace(type);
    }
  }
  for (const auto& cls_string : UnorderedIterable(external_check_allowlist)) {
    auto* type = DexType::get_type(cls_string);
    if (type != nullptr) {
      m_external_check_allowlist.emplace(type);
    }
  }
}

void ClassChecker::run(const Scope& scope) {
  std::mutex finals_mutex;
  std::unordered_map<const DexClass*, NamedMethodMap> class_to_final_methods;
  auto hierarchy = build_type_hierarchy(scope);
  UnorderedSet<const DexType*> internal_types;
  walk::classes(scope,
                [&](DexClass* cls) { internal_types.insert(cls->get_type()); });

  auto match_allowlist_prefix =
      [&](const UnorderedSet<std::string>& allowlist_prefixes,
          const DexType* type) -> bool {
    return unordered_find_if(allowlist_prefixes,
                             [type](const std::string& name) {
                               return type->get_name()->str().starts_with(name);
                             }) != allowlist_prefixes.end();
  };

  auto check_class_defined = [&](const DexType* type) -> bool {
    if (internal_types.count(type) == 0) {
      auto* cls = type_class(type);
      if ((cls == nullptr || !cls->is_external()) &&
          m_definition_check_allowlist.find(type) ==
              m_definition_check_allowlist.end() &&
          !match_allowlist_prefix(m_definition_check_allowlist_prefixes,
                                  type)) {
        return false;
      }
    }
    return true;
  };

  Timer::scope("ClassChecker_walk", [&] {
    walk::parallel::classes(scope, [&](DexClass* cls) {
      if (!is_interface(cls) && !is_abstract(cls)) {
        for (auto* m : cls->get_all_methods()) {
          if (is_abstract(m)) {
            m_good = false;
            m_failed_classes_abstract_check.insert(cls);
            return;
          }
        }
      }
      if (!is_interface(cls)) {
        for (auto* m : cls->get_vmethods()) {
          if (is_final(m)) {
            std::lock_guard<std::mutex> lock(finals_mutex);
            NameAndProto np(m);
            class_to_final_methods[cls].emplace(np, m);
          }
        }
      }
      if (m_external_check) {
        always_assert(!cls->is_external());
        auto child_types = get_all_children(hierarchy, cls->get_type());
        for (const auto& child_type : child_types) {
          if (internal_types.count(child_type) == 0 &&
              m_external_check_allowlist.find(child_type) ==
                  m_external_check_allowlist.end() &&
              !match_allowlist_prefix(m_external_check_allowlist_prefixes,
                                      child_type)) {
            m_good = false;
            m_failed_classes_external_check.update(
                cls, [&](auto*, auto& set, bool) { set.insert(child_type); });
          }
        }
      }

      if (m_definition_check) {
        auto* super_type = cls->get_super_class();
        if (!check_class_defined(super_type)) {
          m_good = false;
          m_failed_classes_definition_check.update(
              cls, [&](auto*, auto& set, bool) { set.insert(super_type); });
        }
        for (const auto& intf : *cls->get_interfaces()) {
          if (!check_class_defined(intf)) {
            m_good = false;
            m_failed_classes_definition_check.update(
                cls, [&](auto*, auto& set, bool) { set.insert(intf); });
          }
        }
      }
    });
  });
  Timer::scope("ClassChecker_hierarchy_traverse", [&] {
    for (auto&& [cls, final_methods] : class_to_final_methods) {
      auto child_types = get_all_children(hierarchy, cls->get_type());
      for (const auto& child_type : child_types) {
        auto* child_cls = type_class(child_type);
        always_assert(child_cls != nullptr);
        if (has_colliding_methods(cls, final_methods, child_cls,
                                  &m_failed_methods)) {
          m_good = false;
        }
      }
    }
  });
}

std::ostringstream ClassChecker::print_failed_classes() {
  std::ostringstream oss;
  if (!m_failed_classes_external_check.empty()) {
    oss << "External classes with internal class hierarchy (likely dependency "
           "setting issue if fail at input):"
        << '\n';
    print_failed_external_check(m_failed_classes_external_check, &oss);
    oss << '\n';
  }
  if (!m_failed_classes_definition_check.empty()) {
    oss << "Class reference type not defined (likely dependency setting issue "
           "if fail at input):"
        << '\n';
    print_failed_definition_check(m_failed_classes_definition_check, &oss);
    oss << '\n';
  }
  if (!m_failed_classes_abstract_check.empty()) {
    oss << "Nonabstract classes with abstract methods:" << '\n';
    print_failed_things(m_failed_classes_abstract_check, &oss);
    oss << '\n';
  }
  if (!m_failed_methods.empty()) {
    oss << "Methods incorrectly overriding super class final method:" << '\n';
    print_failed_things(m_failed_methods, &oss);
    oss << '\n';
  }
  return oss;
}
