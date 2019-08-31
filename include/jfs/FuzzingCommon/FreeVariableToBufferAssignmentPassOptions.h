//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_OPTIONS_H
#define JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_OPTIONS_H
#include <cstddef>

namespace jfs {
namespace fuzzingCommon {
class FreeVariableToBufferAssignmentPassOptions {
public:
  enum class FreeVariableSortStrategyTy {
    ALPHABETICAL,
    FIRST_OBSERVED,
    NONE, // Warning: Will likely be non-deterministic
  };
  size_t bufferElementBitAlignment = 1;
  FreeVariableSortStrategyTy sortStrategy =
      FreeVariableSortStrategyTy::FIRST_OBSERVED;
  FreeVariableToBufferAssignmentPassOptions();
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
