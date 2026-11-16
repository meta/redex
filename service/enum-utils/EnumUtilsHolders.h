/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

class DexField;
class DexType;

/*
 * OptimizeEnumsPass boxes each enum ordinal N it needs once, into a
 * `public static final Integer fN` field initialized with Integer.valueOf(N),
 * in classes it generates. This component owns the names of those holder
 * classes, so that the pass that creates them and the analyses that read their
 * fields agree on which classes they are.
 *
 * The holders form a family: chunk 0 is `<family>;` and chunk n >= 1, when the
 * pass splits the values into chunks, is `<family>$<n>;`. The family is
 * `Lredex/$EnumUtils`, with `$u` appended as often as needed for the names of
 * all its chunks to be unused.
 */
namespace enum_utils {

// The first family whose names for chunks [0, num_chunks) are all unused.
std::string unused_family(uint32_t num_chunks);

std::string holder_name(std::string_view family, uint32_t chunk);

// The name of the field that holds the boxed `value`; boxed_value parses it.
std::string field_name(uint32_t value);

// Whether `type` names a holder class that OptimizeEnumsPass generated. A
// class that merely has a holder-shaped name, such as an inner class of an
// input class named `redex.$EnumUtils`, is not one.
bool is_holder(const DexType* type);

// The value whose boxed object `field` holds, if it is a holder's fN field.
std::optional<int32_t> boxed_value(const DexField* field);

} // namespace enum_utils
