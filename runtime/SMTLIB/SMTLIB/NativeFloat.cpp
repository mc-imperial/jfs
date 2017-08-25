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
// This is the implemenation of the runtime for SMTLIB Floats that
// uses native machine operations. It is written with a C compatible interface
// so that in the future we can easily use LLVM's JIT.
#include "SMTLIB/NativeFloat.h"
#include "SMTLIB/NativeBitVector.h"
#include "SMTLIB/jassert.h"
#include <math.h>
#include <string.h>

namespace {

// Generic version
template <typename T>
T jfs_nr_internal_make_float_from_buffer(const uint8_t* bufferData,
                                         const uint64_t bufferSize,
                                         const uint64_t lowBit) {
  // Just re-use bitvector method for now.
  // This assume little-endian which might things on other architectures.
  uint64_t highBit = lowBit + (sizeof(T) * 8) - 1;
  jassert((((highBit - lowBit) + 1) % 8) == 0 &&
          "Width requested should be whole bytes");
  jfs_nr_bitvector_ty rawBits =
      jfs_nr_make_bitvector(bufferData, bufferSize, lowBit, highBit);
  T result;
  // Copy into result
  memcpy(&result, &rawBits, sizeof(T));
  return result;
}

// Generic version
template <typename RetTy, typename ArgTy>
RetTy jfs_nr_internal_float_get_raw_bits(const ArgTy value) {
  static_assert(sizeof(RetTy) == sizeof(ArgTy), "Size mismatch");
  RetTy data = 0;
  memcpy(&data, &value, sizeof(RetTy));
  return data;
}
}

#ifdef __cplusplus
extern "C" {
#endif

uint32_t jfs_nr_float32_get_raw_bits(const jfs_nr_float32 value) {
  return jfs_nr_internal_float_get_raw_bits<uint32_t, jfs_nr_float32>(value);
}

uint64_t jfs_nr_float64_get_raw_bits(const jfs_nr_float64 value) {
  return jfs_nr_internal_float_get_raw_bits<uint64_t, jfs_nr_float64>(value);
}

bool jfs_nr_float32_smtlib_equals(const jfs_nr_float32 lhs,
                                  const jfs_nr_float32 rhs) {
  // In SMT-LIBv2 no distinction is made between the different types of NaN
  /*
   *  (set-logic QF_FPBV)
      (declare-const x (_ BitVec 32))
      (declare-const y (_ BitVec 32))
      (assert (not (= x y)))
      (assert (fp.isNaN ((_ to_fp 8 24) x)))
      (assert (fp.isNaN ((_ to_fp 8 24) y)))
      (assert
        (not
          (=
            ((_ to_fp 8 24) x)
            ((_ to_fp 8 24) y)
          )
        )
      )
      (check-sat)
      unsat
  */
  bool lhsIsNaN = isnanf(lhs);
  bool rhsIsNaN = isnanf(rhs);
  if (lhsIsNaN && rhsIsNaN) {
    return true;
  }
  // Positive and negative 0 are distinct but C's `==` operator considers them
  // equal so just do bit comparison.
  return jfs_nr_float32_get_raw_bits(lhs) == jfs_nr_float32_get_raw_bits(rhs);
}

jfs_nr_float32 jfs_nr_make_float32_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit) {
  return jfs_nr_internal_make_float_from_buffer<jfs_nr_float32>(
      bufferData, bufferSize, lowBit);
}

jfs_nr_float64 jfs_nr_make_float64_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit) {
  return jfs_nr_internal_make_float_from_buffer<jfs_nr_float64>(
      bufferData, bufferSize, lowBit);
}

#ifdef __cplusplus
}
#endif
