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
#include "SMTLIBRuntimeTestUtil.h"
#include <assert.h>

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

uint64_t get_neg_bits(uint64_t v, uint64_t N) {
  assert(N < 64);
  uint64_t mask = (UINT64_C(1) << N) - 1;
  return ((~v) + 1) & mask;
}

uint64_t to_expected_bits_from_signed_value(int64_t bits, uint64_t N) {
  assert(N < 64);
  uint64_t mask = (UINT64_C(1) << N) - 1;
  uint64_t expectedBits = *(reinterpret_cast<uint64_t *>(&bits));
  expectedBits &= mask;
  return expectedBits;
}
}
}
