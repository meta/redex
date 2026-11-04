/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>

namespace cfg {
class ControlFlowGraph;
} // namespace cfg

namespace constant_propagation {

namespace intraprocedural {
class FixpointIterator;
} // namespace intraprocedural

namespace stringbuilder_append_chain {

/**
 * For every two-append `new StringBuilder().append(a).append(b).toString()`
 * sequence in `cfg` where a and b are provably non-null Strings, rewrite the
 * toString() into `a.concat(b)`. Both appends must be the String overload,
 * `append:(Ljava/lang/String;)Ljava/lang/StringBuilder;`; the other overloads
 * take a value that `concat:(Ljava/lang/String;)Ljava/lang/String;` cannot
 * accept. Non-nullness is what keeps the contents identical: `concat` throws
 * on a null receiver or argument, where `append` writes the text "null".
 *
 * `a + b` on Strings arrives as this shape from both Java and Kotlin, whose
 * `invokedynamic` to StringConcatFactory (since JVM target 9) D8 desugars into
 * the said pattern. Before:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   invoke-virtual {v0, v2} StringBuilder.append:(String)StringBuilder
 *   invoke-virtual {v0} StringBuilder.toString:()String
 *   move-result-object v5
 *
 * After:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   move-object v3, v1
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   move-object v4, v2
 *   invoke-virtual {v0, v2} StringBuilder.append:(String)StringBuilder
 *   invoke-virtual {v3, v4} String.concat:(String)String
 *   move-result-object v5
 *
 * Non-nullness is read from `fp_iter`, an already-solved intraprocedural
 * constant-propagation fixpoint. When that fixpoint was seeded with an
 * interprocedural WholeProgramState (as inside IPConstantPropagation), operands
 * that are non-null across all callers -- e.g. a method parameter -- are proven
 * non-null too, which a purely intraprocedural run cannot see.
 *
 * The rewrite introduces a semantic change; see
 * `InterproceduralConstantPropagationPass::get_config_doc`.
 */
size_t reduce_two_append_concats(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg);

/*
 * Merge consecutive `append(String)` calls whose operands are all
 * compile-time constant Strings into a single `append` of the concatenation:
 * `...append("a").append("b")...` becomes `...append("ab")...`, saving one
 * invocation per merged append. It targets mixed builders (constant appends
 * interspersed with non-constant ones), since the source compilers already
 * fold a fully-constant concatenation into a single constant. Constant values
 * are read from `fp_iter`. Returns the number of appends eliminated. Before:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   invoke-virtual {v0, v3} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "a"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "b"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *
 * After:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   invoke-virtual {v0, v3} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "a"
 *   const-string v4, "ab"
 *   invoke-virtual {v0, v4} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "b"
 *
 * A fresh register holds the concatenation, since an operand load may have
 * consumers elsewhere and so cannot be overwritten in place. The original
 * loads stay behind; where nothing else reads them, a later LocalDce run
 * removes them.
 *
 * Only appends threading a single builder register via the self-loop pattern
 * (R = R.append(...)) are merged, so dropping all but the first leaves that
 * register holding the builder for the following code.
 *
 * All merged appends must be in one basic block and use the same builder
 * register. Each merged append must either discard its return value or write
 * it back to that register. Between merged appends, allow only string constant
 * loads that leave the builder register unchanged and instructions that write
 * an append's return value back to it. These restrictions prevent intervening
 * instructions from observing the builder's contents before all the strings
 * are appended.
 * Before:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   const-string v1, "a"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "b"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   if-eqz v5, :long
 *   invoke-virtual {v0} StringBuilder.toString:()String     ; "ab"
 *   move-result-object v2
 *   return-object v2
 *   :long
 *   const-string v1, "c"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "d"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   invoke-virtual {v0} StringBuilder.toString:()String     ; "abcd"
 *   move-result-object v3
 *   return-object v3
 *
 * After:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   const-string v1, "a"
 *   const-string v6, "ab"
 *   invoke-virtual {v0, v6} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "b"
 *   if-eqz v5, :long
 *   invoke-virtual {v0} StringBuilder.toString:()String     ; "ab"
 *   move-result-object v2
 *   return-object v2
 *   :long
 *   const-string v1, "c"
 *   const-string v7, "cd"
 *   invoke-virtual {v0, v7} StringBuilder.append:(String)StringBuilder
 *   const-string v1, "d"
 *   invoke-virtual {v0} StringBuilder.toString:()String     ; "abcd"
 *   move-result-object v3
 *   return-object v3
 *
 * "a" and "b" sit in one block and "c" and "d" in another, so each pair
 * merges on its own.
 */
size_t merge_adjacent_constant_appends(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg);

/*
 * Replace a builder holding one compile-time constant String with the string
 * it would have produced: the `toString()` becomes a `const-string` of that
 * constant, and nothing reads the builder. Its single operation must be an
 * `append(String)` whose operand `fp_iter` proves constant. A
 * `StringBuilder(String)` constructor contributes contents of its own, so a
 * builder built from one is left alone.
 *
 * A builder with several operations is left alone as well.
 * `merge_adjacent_constant_appends` collapses a run of constant appends within
 * one block to one append ahead of this. Returns the number of toString() calls
 * replaced, which exceeds the number of builders when several of them read one
 * builder. Before:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   const-string v1, "ab"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   invoke-virtual {v0} StringBuilder.toString:()String
 *   move-result-object v2
 *
 * After:
 *
 *   new-instance v0, StringBuilder
 *   invoke-direct {v0} StringBuilder.<init>:()V
 *   const-string v1, "ab"
 *   invoke-virtual {v0, v1} StringBuilder.append:(String)StringBuilder
 *   const-string v2, "ab"
 *
 * The allocation, the constructor and the appends are left in place: proving
 * the builder unreachable is an escape analysis, which a later
 * ObjectSensitiveDce run performs. Removing them is what makes this profitable
 * -- the chain costs an allocation, a backing array and two invocations,
 * where the result costs a resolved string reference.
 *
 * The other reductions in this file preserve the identity of the produced
 * String; this one does not. `toString()` returns a fresh String, whereas a
 * `const-string` of a literal resolves to the interned instance, so a `==`
 * comparison against an equal literal changes from false to true, as does
 * anything else keyed on object identity, such as `IdentityHashMap` or
 * `synchronized`. Content-wise the two are always equal.
 *
 * Only a `toString()` whose result is captured by a `move-result-object` is
 * replaced; one whose result is discarded leaves the builder for a dead-code
 * pass.
 */
size_t replace_constant_tostring_with_const_string(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg);

} // namespace stringbuilder_append_chain

} // namespace constant_propagation
