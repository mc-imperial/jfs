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
#ifndef JFS_SMTLIB_RUNTIME_TEST_UTIL_H
#define JFS_SMTLIB_RUNTIME_TEST_UTIL_H
#include <stdint.h>
namespace jfs {
namespace smtlib_runtime_test_util {

int64_t to_signed_value(uint64_t bits, uint64_t N);

uint64_t get_neg_bits(uint64_t v, uint64_t N);

uint64_t to_expected_bits_from_signed_value(int64_t bits, uint64_t N);
}
}
#endif
