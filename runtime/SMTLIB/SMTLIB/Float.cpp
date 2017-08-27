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
#include "SMTLIB/Float.h"

template <>
Float32 makeFloatFrom(BufferRef<const uint8_t> buffer, uint64_t lowBit,
                      uint64_t highBit) {
  jassert((lowBit + 31) == highBit);
  return jfs_nr_make_float32_from_buffer(buffer.get(), buffer.getSize(),
                                         lowBit);
}

template <>
Float64 makeFloatFrom(BufferRef<const uint8_t> buffer, uint64_t lowBit,
                      uint64_t highBit) {
  jassert((lowBit + 63) == highBit);
  return jfs_nr_make_float64_from_buffer(buffer.get(), buffer.getSize(),
                                         lowBit);
}
