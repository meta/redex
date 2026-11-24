/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <memory>
#include <string>
#include <vector>

#include <json/value.h>

#include "ConfigFiles.h"
#include "DexStore.h"
#include "Pass.h"

/*
 * A pass sees its input only after earlier passes have rewritten it, so a shape
 * that no compiler emits is still a shape the pass must handle: transform it
 * correctly or leave it alone, and never abort. This harness checks that
 * contract by applying, one at a time, the semantics-preserving edits that
 * earlier Redex passes make to the pass's test input:
 *
 * - DeleteUnreferencedMethod deletes a non-virtual method that nothing refers
 *   to, other than a no-argument constructor, as RemoveUnreachablePass does,
 *   and then every non-virtual method and field that becomes unreferenced.
 *   (RemoveUnreachablePass may delete more, such as virtual methods and whole
 *   classes.)
 * - RemoveUnreadFieldWrites runs RemoveUnusedFieldsPass on one class, which
 *   deletes the writes of its fields that nothing reads; the fields stay
 *   declared.
 * - DeleteUnreadFields does the same and then deletes those of the class's
 *   fields that nothing refers to any more, as a later RemoveUnreachablePass
 *   does.
 * - InlineCall inlines one call of a static or direct method other than a
 *   constructor that the method inliner may inline, then deletes every
 *   non-virtual method and field that becomes unreferenced, such as the callee
 *   after its last call. (Inlining a constructor needs the inliner's
 *   whole-program step that makes fields non-final; a pipeline that should see
 *   inlined constructors runs MethodInlinePass before the edits.)
 *
 * No edit deletes a member that reflection reaches or a volatile instance
 * field, which RemoveUnreachablePass keeps too.
 *
 * Each edit applies at "sites" (a method, a class, a call), which are numbered
 * in a deterministic order, so the same input always yields the same sites.
 */
namespace pass_input_edits {

enum class Edit {
  DeleteUnreferencedMethod,
  RemoveUnreadFieldWrites,
  DeleteUnreadFields,
  InlineCall,
};

const std::vector<Edit>& all_edits();

const char* edit_name(Edit edit);

// Describes the sites in `stores` where `edit` applies, in their order. The
// code of every method must have its CFG built.
std::vector<std::string> describe_sites(Edit edit,
                                        DexStoresVector& stores,
                                        ConfigFiles& conf);

// Applies `edit` at the site numbered `site` and describes what it did.
std::string apply(Edit edit,
                  size_t site,
                  DexStoresVector& stores,
                  ConfigFiles& conf);

using LoadInput = std::function<DexStoresVector()>;
using MakePasses = std::function<std::vector<std::unique_ptr<Pass>>()>;

struct Passes {
  // Earlier passes, run before the edit to bring the input into the shape the
  // passes under test see in a pipeline. May be empty.
  MakePasses before_edits;
  // The passes under test, run after the edit.
  MakePasses after_edits;
};

struct Checks {
  // Sees each edited input before the passes under test run, to record what
  // `after` needs to know about it.
  std::function<void(const Scope& input)> before;
  // Checks the result of each run in which no pass aborted. `description`
  // describes the edit, for failure messages. The code of every method has its
  // CFG built.
  std::function<void(DexStoresVector& stores,
                     ConfigFiles& conf,
                     const std::string& description)>
      after;
};

/*
 * Runs the passes on the input as `load_input` builds it and the earlier passes
 * leave it, and then once for each site of each of `edits`, each time on a
 * newly built input with that one edit applied. Every run checks the edited
 * input the way PassManager checks its input, and type-checks all code after
 * each pass, which is stricter than app builds. An assertion or exception is a
 * test failure that names the edit and its site; every other run is handed to
 * `checks`.
 *
 * Each run replaces `g_redex` with a new RedexContext, so the caller must be a
 * test whose fixture owns `g_redex` (a RedexTest), `load_input` must build the
 * whole input, and nothing from an earlier run may be used. The earlier passes
 * must prepare the same input in every run, the passes under test must give the
 * same output for the unedited input twice, and every run must find the same
 * sites; otherwise the test fails, which catches code that keeps types or
 * methods of an earlier RedexContext. A crash
 * that kills the test binary is not caught; the run being made is printed
 * before it starts.
 */
void check_passes_never_abort(const LoadInput& load_input,
                              const Passes& passes,
                              const Json::Value& config,
                              const Checks& checks,
                              const std::vector<Edit>& edits = all_edits());

} // namespace pass_input_edits
