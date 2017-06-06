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
#ifndef JFS_RUNTIME_SMTLIB_BITVECTOR_H
#define JFS_RUNTIME_SMTLIB_BITVECTOR_H
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <type_traits>

// Arbitary precision bitvector of width N
// that mimics the semantics of SMT-LIBv2
template <uint64_t N, typename = void> class BitVector {};

// Use template magic to specialize BitVector for widths
// <= 64 bits. This implementation uses native machine operations
// for speed.
template <uint64_t N>
class BitVector<N, typename std::enable_if<(N <= 64)>::type> {
private:
  typedef uint64_t dataTy;
  dataTy data;
  constexpr dataTy mask() const {
    if (N >= 64)
      return UINT64_MAX;

    // FIXME: gcc fails this assert
    // static_assert(N < 64, "Invalid N value");
    // FIXME: gcc incorrect warns about overshift here
    return (1 << N) - 1;
  }
  dataTy doMod(dataTy value) const {
    if (N == 64)
      return value;
    else
      return value % (1 << N);
  }

public:
  BitVector(uint64_t value) {
    static_assert(N > 0 && N <= 64, "Invalid value for N");
    data = doMod(value);
    assert(data == value);
  }

  BitVector() : BitVector(0) {
    static_assert(N > 0 && N <= 64, "Invalid value for N");
  }
  // Operators producing values of width != N
  // TODO
  template <uint64_t M> BitVector<N + M> concat(BitVector<M> &other) const {
    // TODO
    return BitVector<N + M>(0);
  }

  template <uint64_t HIGH, uint64_t LOW>
  BitVector<(HIGH - LOW) + 1> extract() const {
    static_assert(HIGH >= LOW, "Invalid HIGH and/or LOW value");
    // TODO
    return BitVector<(HIGH - LOW) + 1>(0);
  }

  template <uint64_t BITS> BitVector<N + BITS> zeroExtend() const {
    // TODO
    return BitVector<N + BITS>(0);
  }

  template <uint64_t BITS> BitVector<N + BITS> signExtend() const {
    // TODO
    return BitVector<N + BITS>(0);
  }

  // Arithmetic operators
  BitVector<N> bvadd(BitVector<N> &other) const {
    return BitVector<N>(doMod(data + other.data));
  }
  BitVector<N> bvsub(BitVector<N> &other) const {
    return BitVector<N>(doMod(data - other.data));
  }
  BitVector<N> bvmul(BitVector<N> &other) const {
    return BitVector<N>(doMod(data * other.data));
  }
  BitVector<N> bvudiv(BitVector<N> &divisor) const {
    //   [[(bvudiv s t)]] := if bv2nat([[t]]) = 0
    //                       then λx:[0, m). 1
    //                      else nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))
    if (divisor == 0) {
      return BitVector<N>(mask());
    }
    return data / divisor.data;
  }
  // TODO

  // Bitwise operators
  // TODO

  // Logical operators
  // TODO

  // Comparison operators
  bool operator==(const BitVector &rhs) const { return data == rhs.data; }
  bool operator==(uint64_t &rhs) const { return data == rhs; }
  bool operator!=(const BitVector &rhs) const { return !(*this == rhs); }
};

// Use template magic to specialize BitVector for widths
// > 64 bits.
template <uint64_t N>
class BitVector<N, typename std::enable_if<(N > 64)>::type> {
private:
  uint8_t *data;
  constexpr size_t numBytesRequired(size_t bits) const {
    return (bits + 7) / 8;
  }

public:
  // FIXME: We make this more efficient by lazily allocating memory.
  // Initialize from array
  BitVector(uint8_t *bytesToCopy, size_t numBytes) : data(nullptr) {
    data = reinterpret_cast<uint8_t *>(malloc(numBytesRequired(N)));
    assert(data);
    assert(bytesToCopy);
    assert(numBytes <= numBytesRequired(N));
    memcpy(data, bytesToCopy, numBytesRequired(N));
  }
  // Initialize to zero
  BitVector() {
    data = reinterpret_cast<uint8_t *>(malloc(numBytesRequired(N)));
    assert(data);
    memset(data, 0, numBytesRequired(N));
  }
  ~BitVector() {
    if (data)
      free(data);
  }
  // TODO:
};
#endif
