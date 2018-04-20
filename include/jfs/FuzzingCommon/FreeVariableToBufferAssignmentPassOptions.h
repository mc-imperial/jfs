//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
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
  size_t bufferElementBitAlignment = 1;
  FreeVariableToBufferAssignmentPassOptions();
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
