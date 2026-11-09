/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <filesystem>
#include <iostream>
#include <iterator>
#include <sstream>
#include <system_error>
#include <vector>

#include "Debug.h"
#include "Macros.h"
#include "ProguardLexer.h"
#include "ProguardParser.h"
#include "ProguardRegex.h"
#include "ReadMaybeMapped.h"

namespace keep_rules {
namespace proguard_parser {
namespace {

struct TokenIndex {
  const std::vector<Token>& vec;
  std::vector<Token>::const_iterator it;
  std::vector<Token>::const_iterator last_it;

  TokenIndex(const std::vector<Token>& vec,
             std::vector<Token>::const_iterator it)
      : vec(vec), it(it), last_it(it) {}

  void skip_comments() {
    while (it != vec.end() && it->type == TokenType::comment) {
      ++it;
    }
  }

  void next() {
    last_it = it;
    redex_assert(it != vec.end());
    redex_assert(type() != TokenType::eof_token);
    ++it;
    skip_comments();
  }
  void to_last() { it = last_it; }

  std::string str_next() {
    auto val = str();
    next();
    return val;
  }

  std::string_view data() const { return it->data; }
  std::string str() const { return std::string{it->data}; }
  std::string show() const { return it->show(); }

  size_t line() const { return it->line; }

  TokenType type() const { return it->type; }

  std::string show_context(size_t lines) const {
    return show_context(vec, it, lines);
  }

  std::string show_last_context(size_t lines) const {
    return show_context(vec, last_it, lines);
  }

  // A single line can hold arbitrarily many tokens, so bounding the context
  // by line count alone lets input without newlines walk the whole token
  // vector on every call, making diagnostics quadratic in the token count.
  // The bound is small because this renders a human-readable snippet; a
  // diagnostic hundreds of tokens wide is unreadable anyway, and the cost is
  // paid once per reported error.
  static constexpr size_t kMaxContextTokens = 32;

  // static so no accidental use of struct fields.
  static std::string show_context(const std::vector<Token>& v,
                                  const std::vector<Token>::const_iterator& i,
                                  size_t lines) {
    redex_assert(i != v.end());

    size_t this_line = i->line;
    // Lines are 1-based, so clamp instead of underflowing near the top of the
    // file, which would otherwise wrap around to a huge lower bound.
    size_t min_line = this_line > lines ? this_line - lines : 0;
    size_t max_line = this_line + lines;

    size_t budget = kMaxContextTokens;
    auto start_it = i;
    while (start_it != v.begin() && std::prev(start_it)->line >= min_line &&
           budget > 0) {
      --start_it;
      --budget;
    }
    bool clipped_start =
        start_it != v.begin() && std::prev(start_it)->line >= min_line;

    budget = kMaxContextTokens;
    auto end_it = i;
    while (end_it != v.end() && end_it->line <= max_line && budget > 0) {
      ++end_it;
      --budget;
    }
    bool clipped_end = end_it != v.end() && end_it->line <= max_line;

    std::string ret;
    if (clipped_start) {
      ret.append("... ");
    }
    std::optional<size_t> last_line = std::nullopt;
    bool new_line = true;
    for (auto show_it = start_it; show_it != end_it; ++show_it) {
      if (!last_line || last_line != show_it->line) {
        if (last_line) {
          ret.append("\n");
        }
        ret.append(std::to_string(show_it->line));
        ret.append(": ");
        last_line = show_it->line;
        new_line = true;
      }
      if (!new_line) {
        ret.append(" ");
      }

      if (show_it == i) {
        ret.append("!>");
      }

      ret.append(show_it->show());

      if (show_it == i) {
        ret.append("<!");
      }

      new_line = false;
    }

    if (clipped_end) {
      ret.append(" ...");
    }

    return ret;
  }
};

void skip_to_next_command(TokenIndex& idx) {
  while ((idx.type() != TokenType::eof_token) && (!idx.it->is_command())) {
    idx.next();
  }
}

using path = std::filesystem::path;

constexpr std::string_view kUserDir{"<user.dir>"};

std::string replace_user_dir(std::string&& in) {
  auto pos = in.find(kUserDir);
  if (pos == std::string::npos) {
    return in;
  }
  // Could cache this but may make tests harder.
  std::error_code ec;
  auto cwd = std::filesystem::current_path(ec);
  always_assert_log(!ec, "Failed to get cwd for <user.dir>: %s",
                    ec.message().c_str());
  return in.substr(0, pos) + cwd.string() + in.substr(pos + kUserDir.size());
}

std::string parse_single_filepath_command(TokenIndex& idx) {
  // Fail without consumption if this is an end of file token.
  if (idx.type() == TokenType::eof_token) {
    std::cerr << "Expecting at least one file as an argument but found end of "
                 "file at line "
              << idx.last_it->line << '\n'
              << idx.show_context(2) << '\n';
    return "";
  }
  // Fail without consumption if this is a command token.
  if (idx.it->is_command()) {
    std::cerr << "Expecting a file path argument but got command " << idx.show()
              << " at line " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return "";
  }
  // Parse the filename.
  if (idx.type() != TokenType::filepath) {
    std::cerr << "Expected a filepath but got " << idx.show() << " at line "
              << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return "";
  }
  return idx.str_next(); // Consume the filepath token
}

template <bool kOptional = false>
std::vector<std::string> parse_filepaths(TokenIndex& idx,
                                         const std::string& basedir) {
  if (idx.type() != TokenType::filepath) {
    if (!kOptional) {
      std::cerr << "Expected filepath but got " << idx.show() << " at line "
                << idx.line() << '\n'
                << idx.show_context(2) << '\n';
    }
    return {};
  }
  std::vector<std::string> res;
  while (idx.type() == TokenType::filepath) {
    res.emplace_back(basedir.empty()
                         ? idx.str_next()
                         : (path(basedir) / path(idx.str_next())).string());
  }
  return res;
}

std::vector<std::string> parse_filepath_command(TokenIndex& idx,
                                                const std::string& basedir) {
  // Fail without consumption if this is an end of file token.
  if (idx.type() == TokenType::eof_token) {
    std::cerr << "Expecting at least one file as an argument but found end of "
                 "file at line "
              << idx.last_it->line << '\n';
    return {};
  }
  // Fail without consumption if this is a command token.
  if (idx.it->is_command()) {
    std::cerr << "Expecting a file path argument but got command " << idx.show()
              << " at line " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return {};
  }
  // Parse the filename.
  if (idx.type() != TokenType::filepath) {
    std::cerr << "Expected a filepath but got " << idx.show() << " at line "
              << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return {};
  }
  return parse_filepaths(idx, basedir);
}

std::vector<std::string> parse_jars(TokenIndex& idx,
                                    const std::string& basedir) {
  // Fail without consumption if this is an end of file token.
  if (idx.type() == TokenType::eof_token) {
    std::cerr
        << "Expecting at least one file as an argument but found end of file "
        << idx.show_last_context(2) << '\n';
    return {};
  }
  // Parse the list of filenames.
  return parse_filepaths(idx, basedir);
}

void parse_repackageclasses(TokenIndex& idx) {
  // Ignore repackageclasses.
  if (idx.type() == TokenType::identifier) {
    std::cerr << "Ignoring -repackageclasses " << idx.data() << '\n'
              << idx.show_context(2) << '\n';
    idx.next();
  }
}

std::string parse_target(TokenIndex& idx) {
  // Check to make sure the next TokenType is a version token.
  if (idx.type() != TokenType::target_version_token) {
    std::cerr << "Expected a target version but got " << idx.show()
              << " at line " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return "";
  }
  return idx.str_next(); // Consume the version token
}

std::vector<std::string> parse_filter_list_command(TokenIndex& idx) {
  std::vector<std::string> filters;
  while (idx.type() == TokenType::filter_pattern) {
    filters.push_back(idx.str_next());
  }
  return filters;
}

bool parse_optimizationpasses_command(TokenIndex& idx) {
  // Consume the next token.
  if (idx.type() == TokenType::eof_token) {
    return false;
  }
  idx.next();
  return true;
}

bool is_modifier(TokenType tok) {
  return tok == TokenType::includedescriptorclasses_token ||
         tok == TokenType::allowshrinking_token ||
         tok == TokenType::allowoptimization_token ||
         tok == TokenType::allowobfuscation_token;
}

bool parse_modifiers(TokenIndex& idx, KeepSpec* keep) {
  while (idx.type() == TokenType::comma) {
    idx.next();
    if (!is_modifier(idx.type())) {
      std::cerr << "Expected keep option modifier but found : " << idx.show()
                << " at line number " << idx.line() << '\n'
                << idx.show_context(2) << '\n';
      return false;
    }
    switch (idx.type()) {
    case TokenType::includedescriptorclasses_token:
      keep->includedescriptorclasses = true;
      break;
    case TokenType::allowshrinking_token:
      keep->allowshrinking = true;
      break;
    case TokenType::allowoptimization_token:
      keep->allowoptimization = true;
      break;
    case TokenType::allowobfuscation_token:
      keep->allowobfuscation = true;
      break;
    default:
      break;
    }
    idx.next();
  }
  return true;
}

std::optional<DexAccessFlags> process_access_modifier(TokenType type) {
  switch (type) {
  case TokenType::publicToken:
    return ACC_PUBLIC;
  case TokenType::privateToken:
    return ACC_PRIVATE;
  case TokenType::final:
    return ACC_FINAL;
  case TokenType::abstract:
    return ACC_ABSTRACT;
  case TokenType::synthetic:
    return ACC_SYNTHETIC;
  case TokenType::staticToken:
    return ACC_STATIC;
  case TokenType::volatileToken:
    return ACC_VOLATILE;
  case TokenType::native:
    return ACC_NATIVE;
  case TokenType::protectedToken:
    return ACC_PROTECTED;
  case TokenType::transient:
    return ACC_TRANSIENT;
  default:
    return std::nullopt;
  }
}

bool is_negation_or_class_access_modifier(TokenType type) {
  switch (type) {
  case TokenType::notToken:
  case TokenType::publicToken:
  case TokenType::privateToken:
  case TokenType::protectedToken:
  case TokenType::final:
  case TokenType::abstract:
  case TokenType::synthetic:
  case TokenType::native:
  case TokenType::staticToken:
  case TokenType::volatileToken:
  case TokenType::transient:
    return true;
  default:
    return false;
  }
}

std::string parse_annotation_type(TokenIndex& idx) {
  if (idx.type() != TokenType::annotation_application) {
    return "";
  }
  idx.next();
  if (idx.type() != TokenType::identifier) {
    std::cerr << "Expecting a class identifier after @ but got " << idx.show()
              << " at line " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return "";
  }
  const auto& typ = idx.data();
  idx.next();
  return convert_wildcard_type(typ);
}

bool is_access_flag_set(const DexAccessFlags accessFlags,
                        const DexAccessFlags checkingFlag) {
  return (accessFlags & checkingFlag) != 0u;
}

void set_access_flag(DexAccessFlags& accessFlags,
                     const DexAccessFlags settingFlag) {
  accessFlags = accessFlags | settingFlag;
}

bool parse_access_flags(TokenIndex& idx,
                        DexAccessFlags& setFlags_,
                        DexAccessFlags& unsetFlags_) {
  bool negated = false;
  while (is_negation_or_class_access_modifier(idx.type())) {
    // Copy the iterator so we can peek and see if the next TokenType is an
    // access token; we don't want to modify the main iterator otherwise
    auto access_it = idx.it;
    if (idx.type() == TokenType::notToken) {
      negated = true;
      ++access_it;
    }
    if (auto access_flag = process_access_modifier(access_it->type)) {
      idx.it = ++access_it;
      if (negated) {
        if (is_access_flag_set(setFlags_, *access_flag)) {
          std::cerr << "Access flag " << idx.show()
                    << " occurs with conflicting settings at line "
                    << idx.line() << '\n'
                    << idx.show_context(2) << '\n';
          return false;
        }
        set_access_flag(unsetFlags_, *access_flag);
        negated = false;
      } else {
        if (is_access_flag_set(unsetFlags_, *access_flag)) {
          std::cerr << "Access flag " << idx.show()
                    << " occurs with conflicting settings at line "
                    << idx.line() << '\n'
                    << idx.show_context(2) << '\n';
          return false;
        }
        set_access_flag(setFlags_, *access_flag);
        negated = false;
      }
    } else {
      break;
    }
  }
  return true;
}

/*
 * Parse [!](class|interface|enum|@interface).
 */
bool parse_class_token(TokenIndex& idx,
                       DexAccessFlags& setFlags_,
                       DexAccessFlags& unsetFlags_) {
  bool negated = false;
  if (idx.type() == TokenType::notToken) {
    negated = true;
    idx.next();
  }
  // Make sure the next keyword is interface, class, enum.
  switch (idx.type()) {
  case TokenType::interface:
    set_access_flag(negated ? unsetFlags_ : setFlags_, ACC_INTERFACE);
    break;
  case TokenType::enumToken:
    set_access_flag(negated ? unsetFlags_ : setFlags_, ACC_ENUM);
    break;
  case TokenType::annotation:
    set_access_flag(negated ? unsetFlags_ : setFlags_, ACC_ANNOTATION);
    break;
  case TokenType::classToken:
    break;
  default:
    std::cerr << "Expected interface, class or enum but got " << idx.show()
              << " at line number " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return false;
  }
  idx.next();
  return true;
}

// Consume an expected token, indicating if that TokenType was found.
// If some other TokenType is found, then it is not consumed and false
// is returned.
bool consume_token(TokenIndex& idx, const TokenType& tok) {
  if (idx.type() != tok) {
    std::cerr << "Unexpected TokenType " << idx.show() << '\n'
              << idx.show_context(2) << '\n';
    return false;
  }
  idx.next();
  return true;
}

// Consume an expected semicolon, complaining if one was not found.
bool gobble_semicolon(TokenIndex& idx) {
  if (!consume_token(idx, TokenType::semiColon)) {
    std::cerr << "Expecting a semicolon but found " << idx.show() << " at line "
              << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return false;
  }
  return true;
}

void skip_to_semicolon(TokenIndex& idx) {
  while ((idx.type() != TokenType::semiColon) &&
         (idx.type() != TokenType::eof_token)) {
    idx.next();
  }
  if (idx.type() == TokenType::semiColon) {
    idx.next();
  }
}

bool parse_member_specification(TokenIndex& idx,
                                ClassSpecification* class_spec,
                                bool allow_return) {
  MemberSpecification member_specification;
  member_specification.annotationType = parse_annotation_type(idx);
  if (!parse_access_flags(idx,
                          member_specification.requiredSetAccessFlags,
                          member_specification.requiredUnsetAccessFlags)) {
    // There was a problem parsing the access flags. Return an empty class spec
    // for now.
    std::cerr << "Problem parsing access flags for member specification.\n";
    skip_to_semicolon(idx);
    return false;
  }
  // The next TokenType better be an identifier.
  if (idx.type() != TokenType::identifier) {
    std::cerr << "Expecting field or member specification but got "
              << idx.show() << " at line " << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    skip_to_semicolon(idx);
    return false;
  }
  const auto& ident = idx.data();
  // Check for "*".
  if (ident == "*") {
    member_specification.name = "";
    member_specification.descriptor = "";
    idx.next();
    if (!gobble_semicolon(idx)) {
      return false;
    }
    class_spec->methodSpecifications.push_back(member_specification);
    class_spec->fieldSpecifications.push_back(member_specification);
    return true;
  }
  // Check for <methods>
  if (ident == "<methods>") {
    member_specification.name = "";
    member_specification.descriptor = "";
    idx.next();
    if (!gobble_semicolon(idx)) {
      return false;
    }
    class_spec->methodSpecifications.push_back(member_specification);
    return true;
  }
  // Check for <fields>
  if (ident == "<fields>") {
    member_specification.name = "";
    member_specification.descriptor = "";
    idx.next();
    if (!gobble_semicolon(idx)) {
      return false;
    }
    class_spec->fieldSpecifications.push_back(member_specification);
    return true;
  }
  // Check for <init>
  if (ident == "<init>") {
    member_specification.name = "<init>";
    member_specification.descriptor = "V";
    set_access_flag(member_specification.requiredSetAccessFlags,
                    ACC_CONSTRUCTOR);
    idx.next();
  } else {
    // This TokenType is the type for the member specification.
    if (idx.type() != TokenType::identifier) {
      std::cerr << "Expecting type identifier but got " << idx.show()
                << " at line " << idx.line() << '\n'
                << idx.show_context(2) << '\n';
      skip_to_semicolon(idx);
      return false;
    }
    const auto& typ = idx.data();
    idx.next();
    member_specification.descriptor = convert_wildcard_type(typ);
    if (idx.type() != TokenType::identifier) {
      std::cerr << "Expecting identifier name for class member but got "
                << idx.show() << " at line " << idx.line() << '\n'
                << idx.show_context(2) << '\n';
      skip_to_semicolon(idx);
      return false;
    }
    member_specification.name = idx.str_next();
  }
  // Check to see if this is a method specification.
  if (idx.type() == TokenType::openBracket) {
    consume_token(idx, TokenType::openBracket);
    std::string arg = "(";
    while (true) {
      // If there is a ")" next we are done.
      if (idx.type() == TokenType::closeBracket) {
        consume_token(idx, TokenType::closeBracket);
        break;
      }
      if (idx.type() != TokenType::identifier) {
        std::cerr << "Expecting type identifier but got " << idx.show()
                  << " at line " << idx.line() << '\n'
                  << idx.show_context(2) << '\n';
        return false;
      }
      const auto& typ = idx.data();
      consume_token(idx, TokenType::identifier);
      arg += convert_wildcard_type(typ);
      // The next TokenType better be a comma or a closing bracket.
      if (idx.type() != TokenType::comma &&
          idx.type() != TokenType::closeBracket) {
        std::cerr << "Expecting comma or ) but got " << idx.show()
                  << " at line " << idx.line() << '\n'
                  << idx.show_context(2) << '\n';
        return false;
      }
      // If the next TokenType is a comma (rather than closing bracket) consume
      // it and check that it is followed by an identifier.
      if (idx.type() == TokenType::comma) {
        consume_token(idx, TokenType::comma);
        if (idx.type() != TokenType::identifier) {
          std::cerr << "Expecting type identifier after comma but got "
                    << idx.show() << " at line " << idx.line() << '\n'
                    << idx.show_context(2) << '\n';
          return false;
        }
      }
    }
    arg += ")";
    arg += member_specification.descriptor;
    member_specification.descriptor = arg;
  }
  // if with value, look for return
  if (allow_return && idx.type() == TokenType::returns) {
    idx.next();
    const auto& rident = idx.data();
    if (rident == "true") {
      member_specification.return_value.value_type =
          AssumeReturnValue::ValueType::ValueBool;
      member_specification.return_value.value.v = 1;
      idx.next();
    }
    if (rident == "false") {
      member_specification.return_value.value_type =
          AssumeReturnValue::ValueType::ValueBool;
      member_specification.return_value.value.v = 0;
      idx.next();
    }
  }
  // Make sure member specification ends with a semicolon.
  if (!gobble_semicolon(idx)) {
    return false;
  }
  if (member_specification.descriptor[0] == '(') {
    class_spec->methodSpecifications.push_back(member_specification);
  } else {
    class_spec->fieldSpecifications.push_back(member_specification);
  }
  return true;
}

bool parse_member_specifications(TokenIndex& idx,
                                 ClassSpecification* class_spec,
                                 bool allow_return) {
  bool ok = true;
  if (idx.type() == TokenType::openCurlyBracket) {
    idx.next();
    while ((idx.type() != TokenType::closeCurlyBracket) &&
           (idx.type() != TokenType::eof_token)) {
      if (!parse_member_specification(idx, class_spec, allow_return)) {
        // We failed to parse a member specification so skip to the next
        // semicolon.
        skip_to_semicolon(idx);
        ok = false;
      }
    }
    if (idx.type() == TokenType::closeCurlyBracket) {
      idx.next();
    }
  }
  return ok;
}

bool member_comparison(const MemberSpecification& m1,
                       const MemberSpecification& m2) {
  return m1.name < m2.name;
}

std::optional<std::string> parse_class_name(TokenIndex& idx) {
  if (idx.type() != TokenType::identifier) {
    std::cerr << "Expected class name but got " << idx.show() << " at line "
              << idx.line() << '\n'
              << idx.show_context(2) << '\n';
    return std::nullopt;
  }
  return idx.str_next();
}

bool parse_class_names(
    TokenIndex& idx,
    std::vector<ClassSpecification::ClassNameSpec>& class_names) {
  bool negated{false};
  auto maybe_negated = [&]() {
    if (idx.type() == TokenType::notToken) {
      negated = true;
      idx.next();
    }
  };
  auto push_to = [&](std::string&& s) {
    class_names.emplace_back(s, negated);
    negated = false;
  };

  maybe_negated();
  if (auto cn = parse_class_name(idx)) {
    push_to(std::move(*cn));
  } else {
    return false;
  }

  // Maybe consume comma delimited list
  while (idx.type() == TokenType::comma) {
    // Consume comma
    idx.next();

    maybe_negated();
    if (auto cn = parse_class_name(idx)) {
      push_to(std::move(*cn));
    } else {
      return false;
    }
  }
  return true;
}

std::optional<ClassSpecification> parse_class_specification(TokenIndex& idx,
                                                            bool allow_return) {
  ClassSpecification class_spec;
  class_spec.annotationType = parse_annotation_type(idx);
  if (!parse_access_flags(idx, class_spec.setAccessFlags,
                          class_spec.unsetAccessFlags)) {
    // There was a problem parsing the access flags. Return an empty class spec
    // for now.
    std::cerr << "Problem parsing access flags for class specification.\n";
    return std::nullopt;
  }
  if (!parse_class_token(idx, class_spec.setAccessFlags,
                         class_spec.unsetAccessFlags)) {
    return std::nullopt;
  }
  // Parse the class name(s).
  if (!parse_class_names(idx, class_spec.classNames)) {
    return std::nullopt;
  }
  bool ok = true;
  // Parse extends/implements if present, treating implements like extends.
  if ((idx.type() == TokenType::extends) ||
      (idx.type() == TokenType::implements)) {
    idx.next();
    class_spec.extendsAnnotationType = parse_annotation_type(idx);
    if (idx.type() != TokenType::identifier) {
      std::cerr << "Expecting a class name after extends/implements but got "
                << idx.show() << " at line " << idx.line() << '\n'
                << idx.show_context(2) << '\n';
      ok = false;
      class_spec.extendsClassName = "";
    } else {
      class_spec.extendsClassName = idx.str_next();
    }
  }
  // Parse the member specifications, if there are any
  const bool member_ok =
      parse_member_specifications(idx, &class_spec, allow_return);
  if (!ok || !member_ok) {
    return std::nullopt;
  }
  std::sort(class_spec.fieldSpecifications.begin(),
            class_spec.fieldSpecifications.end(),
            member_comparison);
  std::sort(class_spec.methodSpecifications.begin(),
            class_spec.methodSpecifications.end(),
            member_comparison);
  return std::move(class_spec);
}

bool parse_keep(TokenIndex& idx,
                KeepSpecSet* spec,
                bool mark_classes,
                bool mark_conditionally,
                bool allowshrinking,
                bool allow_return,
                const std::string& filename,
                uint32_t line) {
  auto keep = std::make_unique<KeepSpec>();
  keep->mark_classes = mark_classes;
  keep->mark_conditionally = mark_conditionally;
  keep->allowshrinking = allowshrinking;
  keep->source_filename = filename;
  keep->source_line = line;
  if (!parse_modifiers(idx, &*keep)) {
    skip_to_next_command(idx);
    return false;
  }
  auto class_spec = parse_class_specification(idx, allow_return);
  if (class_spec) {
    keep->class_spec = std::move(*class_spec);
  }
  spec->emplace(std::move(keep));
  return class_spec.has_value();
}

namespace keep_spec_desc {

enum class Target {
  Keep,
  AssumeNoSideEffects,
  AssumeValues,
  WhyAreYouKeeping,
};

template <TokenType kk>
struct KeepSpecDesc {
  // static TokenType token_type;
  // static Target spec_set;
  // static bool mark_classes;
  // static bool mark_conditionally;
  // static bool allowshrinking;
  // static bool allow_return;
};

KeepSpecSet* get_spec_set(Target spec_set, ProguardConfiguration* pg_config) {
  switch (spec_set) {
  case Target::Keep:
    return &pg_config->keep_rules;
  case Target::AssumeNoSideEffects:
    return &pg_config->assumenosideeffects_rules;
  case Target::AssumeValues:
    return &pg_config->assumevalues_rules;
  case Target::WhyAreYouKeeping:
    return &pg_config->whyareyoukeeping_rules;
  }
  UNREACHABLE();
}

template <>
struct KeepSpecDesc<TokenType::keep> {
  constexpr static TokenType token_type{TokenType::keep};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{true};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::keepclassmembers> {
  constexpr static TokenType token_type{TokenType::keepclassmembers};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::keepclasseswithmembers> {
  constexpr static TokenType token_type{TokenType::keepclasseswithmembers};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{true};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::keepnames> {
  constexpr static TokenType token_type{TokenType::keepnames};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{true};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{true};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::keepclassmembernames> {
  constexpr static TokenType token_type{TokenType::keepclassmembernames};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{true};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::keepclasseswithmembernames> {
  constexpr static TokenType token_type{TokenType::keepclasseswithmembernames};
  constexpr static Target spec_set{Target::Keep};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{true};
  constexpr static bool allowshrinking{true};
  constexpr static bool allow_return{false};
};

template <>
struct KeepSpecDesc<TokenType::assumenosideeffects> {
  constexpr static TokenType token_type{TokenType::assumenosideeffects};
  constexpr static Target spec_set{Target::AssumeNoSideEffects};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{true};
};

template <>
struct KeepSpecDesc<TokenType::assumevalues> {
  constexpr static TokenType token_type{TokenType::assumevalues};
  constexpr static Target spec_set{Target::AssumeValues};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{true};
};

template <>
struct KeepSpecDesc<TokenType::whyareyoukeeping> {
  constexpr static TokenType token_type{TokenType::whyareyoukeeping};
  constexpr static Target spec_set{Target::WhyAreYouKeeping};
  constexpr static bool mark_classes{false};
  constexpr static bool mark_conditionally{false};
  constexpr static bool allowshrinking{false};
  constexpr static bool allow_return{false};
};

} // namespace keep_spec_desc

template <TokenType kk>
bool parse_keep(TokenIndex& idx,
                ProguardConfiguration* pg_config,
                const std::string& filename,
                uint32_t line) {
  using namespace keep_spec_desc;
  redex_assert(kk == KeepSpecDesc<kk>::token_type);

  return parse_keep(idx, get_spec_set(KeepSpecDesc<kk>::spec_set, pg_config),
                    KeepSpecDesc<kk>::mark_classes,
                    KeepSpecDesc<kk>::mark_conditionally,
                    KeepSpecDesc<kk>::allowshrinking,
                    KeepSpecDesc<kk>::allow_return, filename, line);
}

template <typename T>
void move_vector_elements(std::vector<T>& from, std::vector<T>& to) {
  to.insert(to.end(),
            std::make_move_iterator(from.begin()),
            std::make_move_iterator(from.end()));
}

void parse(const std::vector<Token>& vec,
           ProguardConfiguration* pg_config,
           Stats& stats,
           const std::string& filename,
           Diagnostics* diagnostics) {
  TokenIndex idx{vec, vec.begin()};

  auto check_empty = [&stats](const auto& val) {
    if (val.empty()) {
      ++stats.parse_errors;
    }
  };
  auto check_keep = [&stats](const auto& opt_val) {
    if (!opt_val) {
      ++stats.parse_errors;
    }
  };

  while (idx.it != idx.vec.end()) {
    // Break out if we are at the end of the TokenType stream.
    if (idx.type() == TokenType::eof_token) {
      break;
    }
    if (idx.type() == TokenType::comment) {
      idx.next();
      continue;
    }

    uint32_t line = idx.line();
    if (!idx.it->is_command()) {
      std::cerr << "Expecting command but found " << idx.show() << " at line "
                << idx.line() << '\n'
                << idx.show_context(2) << '\n';
      if (diagnostics != nullptr) {
        diagnostics->unknown_commands.push_back(
            {idx.show(), filename, (uint32_t)idx.line(), idx.show_context(2)});
      }
      idx.next();
      skip_to_next_command(idx);
      ++stats.unknown_commands;
      continue;
    }

    auto type = idx.type();
    idx.next();

    switch (type) {
    case TokenType::include: {
      auto fp = parse_filepath_command(idx, pg_config->basedirectory);
      move_vector_elements(fp, pg_config->includes);
      check_empty(fp);
      continue;
    }
    case TokenType::basedirectory: {
      auto sfc = parse_single_filepath_command(idx);
      if (sfc.empty()) {
        ++stats.parse_errors;
      } else if (!pg_config->frozen_basedirectory) {
        if (sfc == "<user.dir>") {
          sfc = replace_user_dir(std::move(sfc));
        }
        pg_config->basedirectory = sfc;
      }
      continue;
    }
    case TokenType::injars: {
      auto jars = parse_jars(idx, pg_config->basedirectory);
      move_vector_elements(jars, pg_config->injars);
      check_empty(jars);
      continue;
    }
    case TokenType::outjars: {
      auto jars = parse_jars(idx, pg_config->basedirectory);
      move_vector_elements(jars, pg_config->outjars);
      check_empty(jars);
      continue;
    }
    case TokenType::libraryjars: {
      auto jars = parse_jars(idx, pg_config->basedirectory);
      move_vector_elements(jars, pg_config->libraryjars);
      check_empty(jars);
      continue;
    }
    case TokenType::keepdirectories: {
      auto fp = parse_filepath_command(idx, pg_config->basedirectory);
      move_vector_elements(fp, pg_config->keepdirectories);
      check_empty(fp);
      continue;
    }
    case TokenType::target: {
      auto target = parse_target(idx);
      if (!target.empty()) {
        pg_config->target_version = std::move(target);
      }
      continue;
    }
    case TokenType::dontskipnonpubliclibraryclasses: {
      // -skipnonpubliclibraryclasses not supported
      // -dontskipnonpubliclibraryclassmembers not supported
      // Silently ignore the dontskipnonpubliclibraryclasses option.
      continue;
    }
    case TokenType::keep:
      check_keep(parse_keep<TokenType::keep>(idx, pg_config, filename, line));
      continue;
    case TokenType::keepclassmembers:
      check_keep(parse_keep<TokenType::keepclassmembers>(idx, pg_config,
                                                         filename, line));
      continue;
    case TokenType::keepclasseswithmembers:
      check_keep(parse_keep<TokenType::keepclasseswithmembers>(idx, pg_config,
                                                               filename, line));
      continue;
    case TokenType::keepnames:
      check_keep(
          parse_keep<TokenType::keepnames>(idx, pg_config, filename, line));
      continue;
    case TokenType::keepclassmembernames:
      check_keep(parse_keep<TokenType::keepclassmembernames>(idx, pg_config,
                                                             filename, line));
      continue;
    case TokenType::keepclasseswithmembernames:
      check_keep(parse_keep<TokenType::keepclasseswithmembernames>(
          idx, pg_config, filename, line));
      continue;

    case TokenType::assumenosideeffects:
      check_keep(parse_keep<TokenType::assumenosideeffects>(idx, pg_config,
                                                            filename, line));
      continue;
    case TokenType::assumevalues:
      check_keep(
          parse_keep<TokenType::assumevalues>(idx, pg_config, filename, line));
      continue;
    case TokenType::whyareyoukeeping:
      check_keep(parse_keep<TokenType::whyareyoukeeping>(idx, pg_config,
                                                         filename, line));
      continue;

    case TokenType::printseeds: {
      auto ofp = parse_filepaths</*kOptional=*/true>(idx, "");
      move_vector_elements(ofp, pg_config->printseeds);
      continue;
    }

    case TokenType::dontshrink: {
      pg_config->shrink = false;
      continue;
    }
    case TokenType::printusage: {
      auto ofp = parse_filepaths</*kOptional=*/true>(idx, "");
      move_vector_elements(ofp, pg_config->printusage);
      continue;
    }

    case TokenType::dontoptimize: {
      pg_config->optimize = false;
      continue;
    }
    case TokenType::optimizations: {
      auto fl = parse_filter_list_command(idx);
      move_vector_elements(fl, pg_config->optimization_filters);
      check_empty(fl);
      continue;
    }
    case TokenType::optimizationpasses: {
      auto op = parse_optimizationpasses_command(idx);
      if (!op) {
        ++stats.parse_errors;
      }
      continue;
    }

    case TokenType::allowaccessmodification_token: {
      pg_config->allowaccessmodification = true;
      continue;
    }
    case TokenType::dontobfuscate: {
      pg_config->dontobfuscate = true;
      continue;
    }
    case TokenType::printmapping: {
      auto ofp = parse_filepaths</*kOptional=*/true>(idx, "");
      move_vector_elements(ofp, pg_config->printmapping);
      continue;
    }
    case TokenType::repackageclasses: {
      parse_repackageclasses(idx);
      continue;
    }
    case TokenType::keepattributes: {
      auto fl = parse_filter_list_command(idx);
      move_vector_elements(fl, pg_config->keepattributes);
      check_empty(fl);
      continue;
    }
    case TokenType::dontusemixedcaseclassnames_token: {
      pg_config->dontusemixedcaseclassnames = true;
      continue;
    }
    case TokenType::keeppackagenames: {
      auto fl = parse_filter_list_command(idx);
      move_vector_elements(fl, pg_config->keeppackagenames);
      check_empty(fl);
      continue;
    }
    case TokenType::dontpreverify_token: {
      pg_config->dontpreverify = true;
      continue;
    }
    case TokenType::printconfiguration: {
      auto ofp = parse_filepaths</*kOptional=*/true>(idx, "");
      move_vector_elements(ofp, pg_config->printconfiguration);
      continue;
    }
    case TokenType::dontwarn: {
      auto fl = parse_filter_list_command(idx);
      move_vector_elements(fl, pg_config->dontwarn);
      check_empty(fl);
      continue;
    }
    case TokenType::verbose_token: {
      pg_config->verbose = true;
      continue;
    }

    case TokenType::command:
    case TokenType::dump:
    case TokenType::mergeinterfacesaggressively:
    case TokenType::returns: {
      idx.to_last(); // Unwind moving forward.
      always_assert(idx.it->is_command());
      const auto& name = idx.data();
      if (name == "if") {
        ++stats.skipped_if_rules;
      }
      // It is benign to drop -dontnote
      if (name != "dontnote") {
        std::cerr << "Unimplemented command (skipping): " << idx.show()
                  << " at line " << idx.line() << '\n'
                  << idx.show_context(2) << '\n';
        if (diagnostics != nullptr) {
          diagnostics->skipped_commands.push_back({idx.show(), filename,
                                                   (uint32_t)idx.line(),
                                                   idx.show_context(2)});
        }
        ++stats.unimplemented;
      }
      idx.next();
      skip_to_next_command(idx);
      continue;
    }

    // These should not reach the switch.

    // Handled explicitly.
    case TokenType::eof_token:
    case TokenType::comment:
    // Not commands.
    case TokenType::openCurlyBracket:
    case TokenType::closeCurlyBracket:
    case TokenType::openBracket:
    case TokenType::closeBracket:
    case TokenType::semiColon:
    case TokenType::colon:
    case TokenType::notToken:
    case TokenType::comma:
    case TokenType::slash:
    case TokenType::classToken:
    case TokenType::publicToken:
    case TokenType::final:
    case TokenType::abstract:
    case TokenType::interface:
    case TokenType::enumToken:
    case TokenType::extends:
    case TokenType::implements:
    case TokenType::privateToken:
    case TokenType::protectedToken:
    case TokenType::staticToken:
    case TokenType::volatileToken:
    case TokenType::transient:
    case TokenType::annotation:
    case TokenType::annotation_application:
    case TokenType::synchronized:
    case TokenType::native:
    case TokenType::strictfp:
    case TokenType::synthetic:
    case TokenType::bridge:
    case TokenType::varargs:
    case TokenType::identifier:
    case TokenType::arrayType:
    case TokenType::filepath:
    case TokenType::target_version_token:
    case TokenType::filter_pattern:
    case TokenType::includedescriptorclasses_token:
    case TokenType::allowshrinking_token:
    case TokenType::allowoptimization_token:
    case TokenType::allowobfuscation_token:
    case TokenType::unknownToken:
      idx.to_last(); // Unwind moving forward.
      always_assert(!idx.it->is_command());
      always_assert(false);
      break;
    }
  }
}

Stats parse(const std::string_view& config,
            ProguardConfiguration* pg_config,
            const std::string& filename,
            Diagnostics* diagnostics) {
  Stats ret{};

  std::vector<Token> tokens = lex(config);
  bool ok = true;
  // Check for bad tokens.
  for (auto& tok : tokens) {
    if (tok.type == TokenType::unknownToken) {
      std::string spelling ATTRIBUTE_UNUSED = std::string(tok.data);
      ++ret.unknown_tokens;
      ok = false;
    }
    // std::cout << tok.show() << " at line " << tok.line << '\n';
  }

  if (!ok) {
    std::cerr << "Found " << ret.unknown_tokens << " unknown tokens in "
              << filename << "\n";
    pg_config->ok = false;
    return ret;
  }

  parse(tokens, pg_config, ret, filename, diagnostics);
  if (ret.parse_errors == 0) {
    pg_config->ok = ok;
  } else {
    pg_config->ok = false;
    std::cerr << "Found " << ret.parse_errors << " parse errors in " << filename
              << "\n";
  }

  return ret;
}

Stats parse(const std::string_view& config,
            ProguardConfiguration* pg_config,
            const std::string& filename) {
  return parse(config, pg_config, filename, /* diagnostics */ nullptr);
}

} // namespace

Stats parse(std::istream& config,
            ProguardConfiguration* pg_config,
            const std::string& filename) {
  return parse(config, pg_config, filename, /* diagnostics */ nullptr);
}

Stats parse(std::istream& config,
            ProguardConfiguration* pg_config,
            const std::string& filename,
            Diagnostics* diagnostics) {
  std::stringstream buffer;
  buffer << config.rdbuf();
  return parse(buffer.str(), pg_config, filename, diagnostics);
}

Stats parse_file(const std::string& filename,
                 ProguardConfiguration* pg_config) {
  return parse_file(filename, pg_config, /* diagnostics */ nullptr);
}

Stats parse_file(const std::string& filename,
                 ProguardConfiguration* pg_config,
                 Diagnostics* diagnostics) {
  Stats ret{};
  redex::read_file_with_contents(filename, [&](const char* data, size_t s) {
    std::string_view view(data, s);
    ret += parse(view, pg_config, filename, diagnostics);
    // Parse the included files.
    for (const auto& included_filename : pg_config->includes) {
      if (pg_config->already_included.find(included_filename) !=
          pg_config->already_included.end()) {
        continue;
      }
      pg_config->already_included.emplace(included_filename);
      ret += parse_file(included_filename, pg_config, diagnostics);
    }
  });
  return ret;
}

size_t remove_default_blocklisted_rules(ProguardConfiguration* pg_config) {
  // TODO: Make the set of excluded rules configurable.
  const auto* blocklisted_rules = R"(
  # The proguard-android-optimize.txt file that is bundled with the Android SDK
  # has a keep rule to prevent removal of all resource ID fields. This is likely
  # because ProGuard runs before aapt which can change the values of those
  # fields. Since this is no longer true in our case, this rule is redundant and
  # hampers our optimizations.
  #
  # I chose to exclude this rule instead of unmarking all resource IDs so that
  # if a resource ID really needs to be kept, the user can still keep it by
  # writing a keep rule that does a non-wildcard match.
  -keepclassmembers class **.R$* {
    public static <fields>;
  }

  # See keepclassnames.pro, or T1890454.
  -keepnames class *
)";
  return remove_blocklisted_rules(blocklisted_rules, pg_config);
}

size_t remove_blocklisted_rules(const std::string& rules,
                                ProguardConfiguration* pg_config) {
  ProguardConfiguration pg_config_blocklist;
  parse(rules, &pg_config_blocklist, "<internal blocklist>");
  size_t removed{0};
  pg_config->keep_rules.erase_if([&](const KeepSpec& ks) {
    for (const auto& blocklisted_ks : pg_config_blocklist.keep_rules) {
      if (ks == *blocklisted_ks) {
        removed++;
        return true;
      }
    }
    return false;
  });
  return removed;
}

size_t identify_blanket_native_rules(ProguardConfiguration* pg_config) {
  // A "blanket native rule" is a rule which keeps all native methods and their
  // parent classes.  We identify them and move them to a logically* separate
  // list of keep rules so that we determine their effects on reachability in
  // isolation.
  // *Physically, we move their pointers to the end of the
  // KeepSpecSet's ordered vector and store the iterator pointing at the
  // beginning.
  const auto* blanket_native_rules = R"(
  -keep class * { native <methods>; }
  -keepclassmembers class * { native <methods>; }
  -keepclasseswithmembers class * { native <methods>; }
  -keepclasseswithmembernames class * { native <methods>; }
  -keep,includedescriptorclasses class ** { native <methods>; }
  -keepclassmembers,includedescriptorclasses class ** { native <methods>; }
  -keepclasseswithmembers,includedescriptorclasses class ** { native <methods>; }
  -keepclasseswithmembernames,includedescriptorclasses class ** { native <methods>; }
)";

  ProguardConfiguration tmp_config;
  parse(blanket_native_rules, &tmp_config, "<blanket native rules>");

  // Partition the keep rules so that blanket native rules are at the end of
  // the list. (Order is otherwise preserved.)
  pg_config->keep_rules_native_begin =
      pg_config->keep_rules.stable_partition([&tmp_config](const auto* ks_ptr) {
        auto it = std::find_if(
            tmp_config.keep_rules.begin(),
            tmp_config.keep_rules.end(),
            [ks_ptr](auto* ks2_ptr) { return *ks_ptr == *ks2_ptr; });
        return it == tmp_config.keep_rules.end();
      });

  return static_cast<size_t>(std::distance(*pg_config->keep_rules_native_begin,
                                           pg_config->keep_rules.end()));
}

} // namespace proguard_parser
} // namespace keep_rules
