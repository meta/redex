/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <algorithm>
#include <ostream>
#include <set>
#include <vector>

namespace optimize_enums {

enum class UnsafeType {
  kNotFinal,
  kCannotDelete,
  kHasInterfaces,
  kMoreThanOneSynthField,
  kUnexpectedSynthFields,
  kMultipleCtors,
  kComplexCtor,
  kUnrenamableDmethod,
  kUnrenamableVmethod,
  kComplexField,
  kUsage,
  kUsageUnrenamableFieldType,
  kUsageUnrenamableMethodRef,
  kUsageAnnotationMethodRef,
  // Previously called Reason
  kUsageCastWhenReturn,
  kUsageCastThisPointer,
  kUsageCastParameter,
  kUsageUsedAsClassObject,
  kUsageCastCheckCast,
  kUsageCastISPutObject,
  kUsageCastAputObject,
  kUsageMultiEnumTypes,
  kUsageUnsafeInvocationOnCandidateEnum,
  kUsageIFieldSetOutsideInit,
  kUsageCastEnumArrayToObject,
  kUsageUsedInInstanceOf,
  kUsageUsedEnumEntries,
  kUsageNoOptimizationsMethod,
  kUsageUsedValuesField,
  kUsageConstantSetOutsideClinit,
};

inline std::ostream& operator<<(std::ostream& os, const UnsafeType& u) {
  switch (u) {
  case UnsafeType::kNotFinal:
    os << "NotFinal";
    break;
  case UnsafeType::kCannotDelete:
    os << "CannotDelete";
    break;
  case UnsafeType::kHasInterfaces:
    os << "HasInterfaces";
    break;
  case UnsafeType::kMoreThanOneSynthField:
    os << "MoreThanOneSynthField";
    break;
  case UnsafeType::kUnexpectedSynthFields:
    os << "UnexpectedSynthFields";
    break;
  case UnsafeType::kMultipleCtors:
    os << "MultipleCtors";
    break;
  case UnsafeType::kComplexCtor:
    os << "ComplexCtor";
    break;
  case UnsafeType::kUnrenamableDmethod:
    os << "UnrenamableDmethod";
    break;
  case UnsafeType::kUnrenamableVmethod:
    os << "UnrenamableVmethod";
    break;
  case UnsafeType::kComplexField:
    os << "ComplexField";
    break;
  case UnsafeType::kUsage:
    os << "Usage";
    break;
  case UnsafeType::kUsageUnrenamableFieldType:
    os << "UsageUnrenamableFieldType";
    break;
  case UnsafeType::kUsageUnrenamableMethodRef:
    os << "UsageUnrenamableMethodRef";
    break;
  case UnsafeType::kUsageAnnotationMethodRef:
    os << "UsageAnnotationMethodRef";
    break;
  case UnsafeType::kUsageCastWhenReturn:
    os << "UsageCastWhenReturn";
    break;
  case UnsafeType::kUsageCastThisPointer:
    os << "UsageCastThisPointer";
    break;
  case UnsafeType::kUsageCastParameter:
    os << "UsageCastParameter";
    break;
  case UnsafeType::kUsageUsedAsClassObject:
    os << "UsageUsedAsClassObject";
    break;
  case UnsafeType::kUsageCastCheckCast:
    os << "UsageCastCheckCast";
    break;
  case UnsafeType::kUsageCastISPutObject:
    os << "UsageCastISPutObject";
    break;
  case UnsafeType::kUsageCastAputObject:
    os << "UsageCastAputObject";
    break;
  case UnsafeType::kUsageMultiEnumTypes:
    os << "UsageMultiEnumTypes";
    break;
  case UnsafeType::kUsageUnsafeInvocationOnCandidateEnum:
    os << "UsageUnsafeInvocationOnCandidateEnum";
    break;
  case UnsafeType::kUsageIFieldSetOutsideInit:
    os << "UsageIFieldSetOutsideInit";
    break;
  case UnsafeType::kUsageCastEnumArrayToObject:
    os << "UsageCastEnumArrayToObject";
    break;
  case UnsafeType::kUsageUsedInInstanceOf:
    os << "UsageUsedInInstanceOf";
    break;
  case UnsafeType::kUsageUsedEnumEntries:
    os << "UsageUsedEnumEntries";
    break;
  case UnsafeType::kUsageNoOptimizationsMethod:
    os << "UsageNoOptimizationsMethod";
    break;
  case UnsafeType::kUsageUsedValuesField:
    os << "UsageUsedValuesField";
    break;
  case UnsafeType::kUsageConstantSetOutsideClinit:
    os << "UsageConstantSetOutsideClinit";
    break;
  }
  return os;
}

using UnsafeTypes = std::set<UnsafeType>;

inline std::ostream& operator<<(std::ostream& os, const UnsafeTypes& u) {
  std::vector<UnsafeType> vec(u.begin(), u.end());
  std::sort(vec.begin(), vec.end());
  for (auto t : vec) {
    os << " ";
    os << t;
  }
  return os;
}

} // namespace optimize_enums
