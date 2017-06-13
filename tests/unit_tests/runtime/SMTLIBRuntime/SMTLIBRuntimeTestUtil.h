//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_SMTLIB_RUNTIME_TEST_UTIL_H
#define JFS_SMTLIB_RUNTIME_TEST_UTIL_H
#include <stdint.h>
namespace jfs {
namespace smtlib_runtime_test_util {
int64_t to_signed_value(uint64_t bits, uint64_t N);
}
}
#endif
