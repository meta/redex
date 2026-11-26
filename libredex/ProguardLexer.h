/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/**

 This ProGuard lexer is designed to lex only the output of
 running -printconfiguration from ProGuard which produces a single
 ProGuard configuration file which has the total merged configuration
 for the application. This will not contain any Ant directives like
 <java.home> which are expanded and it will not contain directives
 like -include since all the included files will have been inlined
 and merged.

 **/

#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace keep_rules {
namespace proguard_parser {

enum class TokenType {
  openCurlyBracket,
  closeCurlyBracket,
  openBracket,
  closeBracket,
  semiColon,
  colon,
  notToken,
  comma,
  slash,
  classToken,
  publicToken,
  final,
  abstract,
  interface,
  enumToken,
  extends,
  implements,
  privateToken,
  protectedToken,
  staticToken,
  volatileToken,
  transient,
  annotation,
  annotation_application,
  synchronized,
  native,
  strictfp,
  synthetic,
  bridge,
  varargs,
  command,
  identifier,
  arrayType,
  filepath,
  target_version_token,
  filter_pattern,
  eof_token,
  comment,

  // Input/Output Options
  include,
  basedirectory,
  dump,
  injars,
  outjars,
  libraryjars,
  keepdirectories,
  target,
  dontskipnonpubliclibraryclasses,

  // Keep Options
  keep,
  keepclassmembers,
  keepclasseswithmembers,
  keepnames,
  keepclassmembernames,
  keepclasseswithmembernames,
  printseeds,

  // Keep Option Modifiers
  includedescriptorclasses_token,
  allowshrinking_token,
  allowoptimization_token,
  allowobfuscation_token,

  // Shrinking Options
  dontshrink,
  printusage,
  whyareyoukeeping,

  // Optimization Options
  dontoptimize,
  optimizations,
  optimizationpasses,
  assumenosideeffects,
  assumevalues,
  mergeinterfacesaggressively,
  allowaccessmodification_token,
  returns,

  // Obfuscation Options
  dontobfuscate,
  printmapping,
  repackageclasses,
  keepattributes,
  dontusemixedcaseclassnames_token,
  keeppackagenames,

  // Preverification Options
  dontpreverify_token,

  // General Options
  printconfiguration,
  dontwarn,
  verbose_token,

  unknownToken
};

struct Token {
  TokenType type;
  uint32_t line;
  std::string_view data;

  Token(TokenType type, uint32_t line_number) : type{type}, line{line_number} {}
  Token(TokenType type, uint32_t line_number, const std::string_view& data_in)
      : type{type}, line{line_number}, data(data_in) {}

  Token(Token&&) noexcept = default;
  Token& operator=(Token&&) noexcept = default;

  std::string show() const;
  bool is_command() const;
};

std::vector<Token> lex(const std::string_view& in);

} // namespace proguard_parser
} // namespace keep_rules
