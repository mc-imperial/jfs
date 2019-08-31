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
// FIXME: Make the layout consistent between srcdir and build directory
#include "SMTLIB/Core.h"
#include "jassert.h"

// FIXME: Should we specialise for byte aligned access?
bool makeBoolFrom(BufferRef<const uint8_t> buffer, const uint64_t lowBit,
                  const uint64_t highBit) {
  jassert(highBit >= lowBit && "invalid lowBit and highBit");
  const size_t bitWidth = (highBit - lowBit) + 1;
  jassert(bitWidth <= 8 && "Too many bits");
  const size_t lowBitByte = lowBit / 8;
  const size_t highBitByte = highBit / 8;
  jassert(lowBitByte < buffer.getSize());
  jassert(highBitByte < buffer.getSize());
  uint8_t data = 0;
  const size_t shiftOffset = lowBit % 8;
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
    jassert(shiftOffset > 0);
    jassert(highBitByte < buffer.getSize());
    uint8_t nextBufferByte = buffer.get()[highBitByte];
    data |= (nextBufferByte << (8 - shiftOffset));
  }
  data &= dataMask;
  if (data == 0)
    return false;
  return true;
}
