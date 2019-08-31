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

template <> Float64 Float32::convertToFloat<11, 53>(JFS_NR_RM rm) const {
  // No rounding mode needed
  return jfs_nr_convert_float32_to_float64(data);
}

template <> Float32 Float32::convertToFloat<8, 24>(JFS_NR_RM rm) const {
  // No-op
  return data;
}

template <> Float32 Float64::convertToFloat<8, 24>(JFS_NR_RM rm) const {
  return jfs_nr_convert_float64_to_float32(rm, data);
}

template <> Float64 Float64::convertToFloat<11, 53>(JFS_NR_RM rm) const {
  // No-op
  return data;
}
