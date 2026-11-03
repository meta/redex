/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Native.h"

#include <fstream>
#include <json/reader.h>
#include <json/value.h>
#include <string_view>

#include "Debug.h"
#include "Show.h"
#include "Trace.h"

namespace fs = boost::filesystem;

namespace {

std::optional<Json::Value> read_json_from_file(const std::string& filename) {
  std::ifstream file_stream(filename);
  if (!file_stream) {
    return std::nullopt;
  }
  Json::Value json;
  file_stream >> json;
  file_stream.close();
  return json;
}

} // anonymous namespace

namespace native {

std::vector<SoLibrary> get_so_libraries(const fs::path& path) {

  constexpr static std::string_view expected_extension = ".json";

  std::vector<SoLibrary> ret;

  for (const auto& item : fs::directory_iterator(path)) {
    auto file_name = item.path().string();
    TRACE(NATIVE, 3, "Found file name %s", file_name.c_str());
    if (item.path().extension().string() == expected_extension) {
      auto lib_name = item.path().filename().stem().string();
      TRACE(NATIVE, 3, "Found lib name %s", lib_name.c_str());
      ret.emplace_back(lib_name, file_name);
    }
  }

  return ret;
}

void SoLibrary::populate_functions() {

  // Native methods can be registered with RegisterNatives calls. Use specific
  // analyses to extract information.

  auto registered_natives_opt = read_json_from_file(m_json_path.string());

  always_assert_log(
      registered_natives_opt, "File not opened: %s", m_json_path.c_str());

  for (Json::Value::ArrayIndex i = 0; i < registered_natives_opt->size(); i++) {
    auto klass = (*registered_natives_opt)[i];
    std::string class_name = klass["class_name"].asString();
    const auto& methods = klass["registered_functions"];
    for (Json::Value::ArrayIndex j = 0; j < methods.size(); j++) {
      const auto& method = methods[j];
      std::string method_name = method["method_name"].asString();
      std::string desc = method["desc"].asString();
      std::string function_name = method["function"].asString();

      // Avoids temporary allocations to make clang-tidy happy.
      auto get_compound = [&]() {
        std::string tmp;
        tmp.reserve(class_name.size() + method_name.size() + desc.size() + 2);
        tmp += class_name;
        tmp += ".";
        tmp += method_name;
        tmp += ":";
        tmp += desc;
        return tmp;
      };

      DexMethodRef* m = DexMethod::get_method(get_compound());
      if (m != nullptr) {
        DexMethod* decl = m->as_def();
        always_assert_log(decl,
                          "Attempting to bind non-concrete native method.");
        // When using RegisterNatives, we allow binding the same
        // implementation to multiple definitions.
        auto function_it = m_name_to_functions.find(function_name);
        if (function_it == m_name_to_functions.end()) {
          m_name_to_functions.emplace(function_name,
                                      Function{this, function_name, decl});
        } else {
          function_it->second.add_java_declaration(decl);
        }
      } else {
        TRACE(NATIVE,
              2,
              "Method %s%s%s not found in Java code.",
              class_name.c_str(),
              method_name.c_str(),
              desc.c_str());
      }
    }
  }
}

NativeContext NativeContext::build(const std::string& path_to_native_results,
                                   const Scope& /*java_scope*/) {
  NativeContext ret;
  fs::path path(path_to_native_results);

  if (!fs::exists(path)) {
    return ret;
  }

  ret.so_libraries = get_so_libraries(path);
  for (auto& so_library : ret.so_libraries) {
    so_library.populate_functions();
    for (auto& [fn_name, function] :
         UnorderedIterable(so_library.get_functions())) {
      const auto& java_declarations = function.get_java_declarations();
      for (DexMethod* java_declaration : UnorderedIterable(java_declarations)) {
        if (ret.java_declaration_to_function.count(java_declaration) == 0) {
          ret.java_declaration_to_function[java_declaration] = &function;
        }
      }
    }
  }
  return ret;
}

} // namespace native

std::unique_ptr<native::NativeContext> g_native_context;
