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
#ifndef JFS_RUNTIME_SMTLIB_CORE_H
#define JFS_RUNTIME_SMTLIB_CORE_H
#include "BufferRef.h"
#include <assert.h>
#include <stdint.h>
#include <type_traits>

// We just use the `bool` type to model SMTLIB semantics
// The mapping is trivial so we don't provide many runtime
// functions.

template <
    uint64_t LOWBIT, uint64_t HIGHBIT,
    typename std::enable_if<(((HIGHBIT - LOWBIT) + 1) <= 8)>::type* = nullptr>
bool makeBoolFrom(BufferRef<uint8_t> buffer) {
  static_assert(HIGHBIT >= LOWBIT, "invalid LOWBIT and HIGHBIT");
  constexpr size_t bitWidth = (HIGHBIT - LOWBIT) + 1;
  static_assert(bitWidth <= 8, "Too many bits");
  constexpr size_t lowBitByte = LOWBIT / 8;
  constexpr size_t highBitByte = HIGHBIT / 8;
  assert(lowBitByte < buffer.getSize());
  assert(highBitByte < buffer.getSize());
  uint8_t data = 0;
  constexpr size_t shiftOffset = LOWBIT % 8;
  uint8_t dataMask = 0;
  if (bitWidth < 8) {
    dataMask = (UINT8_C(1) << bitWidth) - 1;
  } else {
    dataMask = UINT8_MAX;
  }
  // Read from firstByte
  uint8_t bufferByte = buffer.get()[lowBitByte];
  data = (bufferByte >> shiftOffset);
  // If necessary read bits from the subsequent byte if we
  // are stradling bytes
  if (highBitByte > lowBitByte) {
    assert(shiftOffset > 0);
    uint8_t nextBufferByte = buffer.get()[highBitByte];
    data |= (nextBufferByte << (8 - shiftOffset));
  }
  data &= dataMask;
  if (data == 0)
    return false;
  return true;
}
#endif
