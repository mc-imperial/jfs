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
#include <assert.h>
#include <stdint.h>

namespace jfs {
namespace smtlib_runtime_test_util {
int64_t to_signed_value(uint64_t bits, uint64_t N) {
  assert(N < 64);
  uint64_t mask = (UINT64_C(1) << N) - 1;
  int64_t negativeMSB = ((int64_t)(UINT64_C(1) << (N - 1))) * -1;
  uint64_t maskOnlyPositiveBits = mask >> 1;
  int64_t valueAsSigned =
      (bits & (UINT64_C(1) << (N - 1)))
          ? (((int64_t)(bits & maskOnlyPositiveBits)) + negativeMSB)
          : ((int64_t)bits);
  return valueAsSigned;
}
}
}
