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
#ifndef JFS_RUNTIME_SMTLIB_BITVECTOR_H
#define JFS_RUNTIME_SMTLIB_BITVECTOR_H
#include "BufferRef.h"
#include "NativeBitVector.h"
#include "jassert.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <type_traits>


// Arbitary precision bitvector of width N
// that mimics the semantics of SMT-LIBv2
template <uint64_t N, typename = void> class BitVector {};

// Foward declaration
template <uint64_t EB, uint64_t SB> class Float;

// Use template magic to specialize BitVector for widths
// <= 64 bits. This implementation uses native machine operations
// for speed.
template <uint64_t N>
class BitVector<
    N, typename std::enable_if<(N <= JFS_NR_BITVECTOR_TY_BITWIDTH)>::type> {
private:
  typedef jfs_nr_bitvector_ty dataTy;
  dataTy data;
  constexpr dataTy mask() const {
    return (N >= 64) ? UINT64_MAX : ((UINT64_C(1) << N) - 1);
  }
  dataTy doMod(dataTy value) const {
    if (N >= 64)
      return value;
    else
      return value % (UINT64_C(1) << N);
  }
  constexpr dataTy mostSignificantBitMask() const {
    return (UINT64_C(1) << (N - 1));
  }

  constexpr dataTy computeSignExtendMask(uint64_t bits) const {
    return ((N + bits) >= 64) ? UINT64_MAX : ((UINT64_C(1) << (N + bits)) - 1);
  }

public:
  BitVector(uint64_t value) {
    static_assert(N > 0 && N <= JFS_NR_BITVECTOR_TY_BITWIDTH,
                  "Invalid value for N");
    data = doMod(value);
    jassert(data == value);
  }

  BitVector() : BitVector(0) {
    static_assert(N > 0 && N <= JFS_NR_BITVECTOR_TY_BITWIDTH,
                  "Invalid value for N");
  }
  BitVector(const BitVector<N>& other) : data(other.data) {
    static_assert(N > 0 && N <= JFS_NR_BITVECTOR_TY_BITWIDTH,
                  "Invalid value for N");
  }
  BufferRef<uint8_t> getBuffer() const {
    return BufferRef<uint8_t>(
        reinterpret_cast<uint8_t*>(const_cast<dataTy*>(&data)), sizeof(dataTy));
  }
  // Operators producing values of width != N

  // Repeat operation producing a width that is native
  template <
      uint64_t M,
      typename std::enable_if<(((N * M) <= JFS_NR_BITVECTOR_TY_BITWIDTH) &&
                               (N * M) > 0)>::type* = nullptr>
  BitVector<(N * M)> repeat() const {
    // TODO:
    JFS_RUNTIME_FAIL();
    return BitVector<N * M>(0);
  }

  // Repeat operation producing a width that is not native
  template <uint64_t M,
            typename std::enable_if<
                ((N * M) > JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<(N * M)> repeat() const {
    // TODO:
    JFS_RUNTIME_FAIL();
    return BitVector<N * M>(0);
  }

  // Concat [this][rhs]
  // this is conceptually in MSB.
  // rhs is in conceptually in LSB.
  //
  // Implementation for where result is a native BitVector
  template <uint64_t M,
            typename std::enable_if<
                ((N + M) <= JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + M> concat(const BitVector<M>& rhs) const {
    // Concatentation produces native BitVector.
    static_assert((N + M) <= 64, "Too many bits");
    return BitVector<N + M>(jfs_nr_concat(data, N, rhs.data, M));
  }

  // Implementation for where result is not a native BitVector
  template <uint64_t M,
            typename std::enable_if<
                ((N + M) > JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + M> concat(const BitVector<M>& rhs) const {
    // Concat produces bitvector that we can't represent natively.
    constexpr size_t bufferSize = (N + M + 7) / 8;
    uint8_t rawData[bufferSize];

    // Copy across rhs
    memcpy(rawData, rhs.getBuffer().get(), rhs.getBuffer().getSize());

    const size_t lhsByteStart = M / 8;
    const size_t shiftOffset = M % 8;
    const size_t lookBackShiftOffset = 8 - shiftOffset;
    if (shiftOffset == 0) {
      // On byte boundary
      for (unsigned int index = lhsByteStart; index < bufferSize; ++index) {
        if ((index * 8) < (N + M)) {
          const uint8_t* lhsByte =
              reinterpret_cast<const uint8_t*>(&data) + (index - lhsByteStart);
          // We are writing a byte from lhs
          rawData[index] = *lhsByte;
          continue;
        }
        // Zero the data
        rawData[index] = 0;
      }
    } else {
      // Not on byte boundary. More complicated
      for (unsigned int index = lhsByteStart; index < bufferSize; ++index) {
        if ((index * 8) < (N + M)) {
          // We are writing at least 1 bit for lhs
          const uint8_t* lhsByte =
              reinterpret_cast<const uint8_t*>(&data) + (index - lhsByteStart);
          if (index == lhsByteStart) {
            // First byte has to be done specially because we writing
            // to a byte that contains bits from rhs (hence `|=`).
            rawData[index] |= ((*lhsByte) << shiftOffset);
            continue;
          }
          // Not doing the first byte. This means we need to also grab the bits
          // from the previous iteration that we shifted out.
          const uint8_t* lhsBytePrevIter = lhsByte - 1;
          uint8_t lhsByteValue = 0;
          if ((index - lhsByteStart) < sizeof(dataTy)) {
            // Guard accessing this byte. On the last iteration
            // we may need to still copy bits from the previous iteration
            // but reading `*lhsByte` would be an out of bounds access.
            lhsByteValue = *lhsByte;
          }
          rawData[index] = (lhsByteValue << shiftOffset) |
                           ((*lhsBytePrevIter) >> lookBackShiftOffset);
          continue;
        }
        // Not writing any bits from lhs so just zero the data
        rawData[index] = 0;
      }
    }
    BufferRef<uint8_t> rawDataRef(reinterpret_cast<uint8_t*>(rawData),
                                  bufferSize);
    return BitVector<N + M>(rawDataRef);
  }

  template <uint64_t BITS>
  BitVector<BITS> extract(uint64_t highBit, uint64_t lowBit) const {
    return BitVector<BITS>(jfs_nr_extract(data, N, highBit, lowBit));
  }

  // Implementation for where result is a native BitVector
  template <uint64_t BITS,
            typename std::enable_if<
                ((N + BITS) <= JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + BITS> zeroExtend() const {
    static_assert((N + BITS) <= JFS_NR_BITVECTOR_TY_BITWIDTH, "too many bits");
    return BitVector<N + BITS>(jfs_nr_zero_extend(data, N, BITS));
  }

  // Implementation for where result is not a native BitVector
  template <uint64_t BITS,
            typename std::enable_if<
                ((N + BITS) > JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + BITS> zeroExtend() const {
    constexpr size_t bufferSize = (N + BITS + 7) / 8;
    uint8_t rawData[bufferSize];
    // Zero the buffer
    memset(rawData, 0, bufferSize);
    // Copy in this bits
    memcpy(rawData, &data, sizeof(dataTy));
    BufferRef<uint8_t> bufferRef(rawData, bufferSize);
    return BitVector<N + BITS>(bufferRef);
  }

  // Implementation for where result is a native BitVector
  template <uint64_t BITS,
            typename std::enable_if<
                ((N + BITS) <= JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + BITS> signExtend() const {
    static_assert((N + BITS) <= JFS_NR_BITVECTOR_TY_BITWIDTH, "too many bits");
    return BitVector<N + BITS>(jfs_nr_sign_extend(data, N, BITS));
  }

  // Implementation for where result is not a native BitVector
  template <uint64_t BITS,
            typename std::enable_if<
                ((N + BITS) > JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
  BitVector<N + BITS> signExtend() const {
    static_assert((N + BITS) > JFS_NR_BITVECTOR_TY_BITWIDTH, "too few bits");
    if ((data & mostSignificantBitMask()) == 0) {
      // Can just zero extend
      return zeroExtend<BITS>();
    }
    // Have to sign extend
    constexpr size_t bufferSize = (N + BITS + 7) / 8;
    uint8_t rawData[bufferSize];
    uint64_t resultMask = computeSignExtendMask(BITS);
    uint64_t signExtendedOriginal = (data | (~mask())) & resultMask;
    // Copy in signExtended
    memcpy(rawData, &signExtendedOriginal, sizeof(dataTy));
    // Now set remaining bytes to all ones.
    memset(rawData + sizeof(dataTy), 0xff, bufferSize - sizeof(dataTy));
    // Modify last byte if necessary. We need to maintain invariant
    // that bits in the buffer outside of the bitvector we want to represent
    // are zero.
    if (((N + BITS) % 8) != 0) {
      uint8_t lastByteMask = 0xff;
      lastByteMask >>= (8 - ((N + BITS) % 8));
      rawData[bufferSize - 1] &= lastByteMask;
    }
    BufferRef<uint8_t> buffer(rawData, bufferSize);
    return BitVector<N + BITS>(buffer);
  }

  // Arithmetic operators
  BitVector<N> bvneg() const { return BitVector<N>(jfs_nr_bvneg(data, N)); }

  BitVector<N> bvadd(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvadd(data, other.data, N));
  }

  BitVector<N> bvsub(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvsub(data, other.data, N));
  }

  BitVector<N> bvmul(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvmul(data, other.data, N));
  }

  BitVector<N> bvudiv(const BitVector<N>& divisor) const {
    return BitVector<N>(jfs_nr_bvudiv(data, divisor.data, N));
  }

  BitVector<N> bvurem(const BitVector<N>& divisor) const {
    return BitVector<N>(jfs_nr_bvurem(data, divisor.data, N));
  }

  BitVector<N> bvsdiv(const BitVector<N>& divisor) const {
    return BitVector<N>(jfs_nr_bvsdiv(data, divisor.data, N));
  }

  BitVector<N> bvsrem(const BitVector<N>& divisor) const {
    return BitVector<N>(jfs_nr_bvsrem(data, divisor.data, N));
  }

  BitVector<N> bvsmod(const BitVector<N>& divisor) const {
    return BitVector<N>(jfs_nr_bvsmod(data, divisor.data, N));
  }

  // Shift operators

  BitVector<N> bvshl(const BitVector<N>& shift) const {
    return BitVector<N>(jfs_nr_bvshl(data, shift.data, N));
  }

  BitVector<N> bvlshr(const BitVector<N>& shift) const {
    return BitVector<N>(jfs_nr_bvlshr(data, shift.data, N));
  }

  BitVector<N> bvashr(const BitVector<N>& shift) const {
    return BitVector<N>(jfs_nr_bvashr(data, shift.data, N));
  }

  BitVector<N> rotate_left(uint64_t shift) const {
    return BitVector<N>(jfs_nr_rotate_left(data, shift, N));
  }

  BitVector<N> rotate_right(uint64_t shift) const {
    return BitVector<N>(jfs_nr_rotate_right(data, shift, N));
  }

  // Bitwise operators
  BitVector<N> bvand(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvand(data, other.data, N));
  }

  BitVector<N> bvor(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvor(data, other.data, N));
  }

  BitVector<N> bvnot() const { return BitVector<N>(jfs_nr_bvnot(data, N)); }

  BitVector<N> bvnand(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvnand(data, other.data, N));
  }

  BitVector<N> bvnor(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvnor(data, other.data, N));
  }

  BitVector<N> bvxor(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvxor(data, other.data, N));
  }

  BitVector<N> bvxnor(const BitVector<N>& other) const {
    return BitVector<N>(jfs_nr_bvxnor(data, other.data, N));
  }

  // Comparison operators
  bool operator==(const BitVector<N>& rhs) const { return data == rhs.data; }
  bool operator!=(const BitVector<N>& rhs) const { return data != rhs.data; }

  bool bvult(const BitVector<N>& rhs) const {
    return jfs_nr_bvult(data, rhs.data, N);
  }
  bool bvule(const BitVector<N>& rhs) const {
    return jfs_nr_bvule(data, rhs.data, N);
  }
  bool bvugt(const BitVector<N>& rhs) const {
    return jfs_nr_bvugt(data, rhs.data, N);
  }
  bool bvuge(const BitVector<N>& rhs) const {
    return jfs_nr_bvuge(data, rhs.data, N);
  }

  bool bvslt(const BitVector<N>& rhs) const {
    return jfs_nr_bvslt(data, rhs.data, N);
  }

  bool bvsle(const BitVector<N>& rhs) const {
    return jfs_nr_bvsle(data, rhs.data, N);
  }

  bool bvsgt(const BitVector<N>& rhs) const {
    return jfs_nr_bvsgt(data, rhs.data, N);
  }

  bool bvsge(const BitVector<N>& rhs) const {
    return jfs_nr_bvsge(data, rhs.data, N);
  }

  BitVector<1> bvcomp(const BitVector<N>& rhs) const {
    // SMTLIB gives this recursive definition:
    // (bvcomp s t) abbreviates (bvxnor s t) if m = 1, and
    //   (bvand (bvxnor ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
    //          (bvcomp ((_ extract |m-2| 0) s) ((_ extract |m-2| 0) t)))
    //          otherwise
    //
    // But we can just do this.
    if (data == rhs.data) {
      return BitVector<1>(1);
    }
    return BitVector<1>(0);
  }
  // This template is friends with all other instantiations
  // FIXME: It would be better if we were only friends where
  // N <= 64.
  template <uint64_t W, typename T> friend class BitVector;
  // Float needs raw access
  template <uint64_t EB, uint64_t SB> friend class Float;
};

template <uint64_t N>
class BitVector<
    N, typename std::enable_if<(N > JFS_NR_BITVECTOR_TY_BITWIDTH)>::type> {
private:
  uint8_t* data;
  constexpr size_t numBytesRequired(size_t bits) const {
    return (bits + 7) / 8;
  }

public:
  // FIXME: We make this more efficient by lazily allocating memory.
  // Initialize from array
  BitVector(uint8_t* bytesToCopy, size_t numBytes) : data(nullptr) {
    data = reinterpret_cast<uint8_t*>(malloc(numBytesRequired(N)));
    jassert(data);
    jassert(bytesToCopy);
    jassert(numBytes <= numBytesRequired(N));
    memcpy(data, bytesToCopy, numBytesRequired(N));
  }
  BitVector(BufferRef<uint8_t> bufferRef)
      : BitVector(bufferRef.get(), bufferRef.getSize()) {}
  // Initialize to zero
  BitVector() {
    data = reinterpret_cast<uint8_t*>(malloc(numBytesRequired(N)));
    jassert(data);
    memset(data, 0, numBytesRequired(N));
  }
  BitVector(uint64_t value) : BitVector() {
    memcpy(data, &value, sizeof(uint64_t));
  }
  ~BitVector() {
    if (data)
      free(data);
  }
  BufferRef<uint8_t> getBuffer() const {
    return BufferRef<uint8_t>(data, numBytesRequired(N));
  }
  // TODO:
};

// Convenience function for creating a BitVector
// from any arbitrary bit offset in a buffer. Offset
// is [lowbit, highbit].
// Implementation for native BitVector
template <uint64_t BITWIDTH,
          typename std::enable_if<
              (BITWIDTH <= JFS_NR_BITVECTOR_TY_BITWIDTH)>::type* = nullptr>
BitVector<BITWIDTH> makeBitVectorFrom(BufferRef<const uint8_t> buffer,
                                      uint64_t lowBit, uint64_t highBit) {
  jassert(highBit >= lowBit && "invalid lowBit and highBit");
  jassert(((highBit - lowBit) + 1) == BITWIDTH);
  jassert(highBit < (buffer.getSize() * 8));
  jfs_nr_bitvector_ty data =
      jfs_nr_make_bitvector(buffer.get(), buffer.getSize(), lowBit, highBit);
  return BitVector<BITWIDTH>(data);
}

#endif
