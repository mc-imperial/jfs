//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_RUNTIME_SMTLIB_NATIVE_BITVECTOR_H
#define JFS_RUNTIME_SMTLIB_NATIVE_BITVECTOR_H
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint64_t jfs_nr_bitvector_ty;
typedef uint64_t jfs_nr_width_ty;

#define JFS_NR_BITVECTOR_TY_BITWIDTH (sizeof(jfs_nr_bitvector_ty) * 8)

bool jfs_nr_is_valid(const jfs_nr_bitvector_ty value,
                     const jfs_nr_width_ty width);

// FIXME: This should not be public but NativeFloat needs this.
jfs_nr_bitvector_ty jfs_nr_get_bitvector_mod(const jfs_nr_bitvector_ty value,
                                             const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_concat(const jfs_nr_bitvector_ty lhs,
                                  const jfs_nr_width_ty lhsBitWidth,
                                  const jfs_nr_bitvector_ty rhs,
                                  const jfs_nr_width_ty rhsBitWidth);

jfs_nr_bitvector_ty jfs_nr_extract(const jfs_nr_bitvector_ty value,
                                   const jfs_nr_width_ty bitWidth,
                                   const jfs_nr_width_ty highBit,
                                   const jfs_nr_width_ty lowBit);

jfs_nr_bitvector_ty jfs_nr_zero_extend(const jfs_nr_bitvector_ty value,
                                       const jfs_nr_width_ty bitWidth,
                                       const jfs_nr_width_ty extraBits);

jfs_nr_bitvector_ty jfs_nr_sign_extend(const jfs_nr_bitvector_ty value,
                                       const jfs_nr_width_ty bitWidth,
                                       const jfs_nr_width_ty extraBits);

jfs_nr_bitvector_ty jfs_nr_bvneg(const jfs_nr_bitvector_ty value,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvadd(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvsub(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvmul(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvudiv(const jfs_nr_bitvector_ty dividend,
                                  const jfs_nr_bitvector_ty divisor,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvurem(const jfs_nr_bitvector_ty dividend,
                                  const jfs_nr_bitvector_ty divisor,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvsdiv(const jfs_nr_bitvector_ty dividend,
                                  const jfs_nr_bitvector_ty divisor,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvsrem(const jfs_nr_bitvector_ty dividend,
                                  const jfs_nr_bitvector_ty divisor,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvsmod(const jfs_nr_bitvector_ty dividend,
                                  const jfs_nr_bitvector_ty divisor,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvshl(const jfs_nr_bitvector_ty value,
                                 const jfs_nr_bitvector_ty shift,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvlshr(const jfs_nr_bitvector_ty value,
                                  const jfs_nr_bitvector_ty shift,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvashr(const jfs_nr_bitvector_ty value,
                                  const jfs_nr_bitvector_ty shift,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_rotate_left(const jfs_nr_bitvector_ty value,
                                       const jfs_nr_bitvector_ty shift,
                                       const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_rotate_right(const jfs_nr_bitvector_ty value,
                                        const jfs_nr_bitvector_ty shift,
                                        const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvand(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvor(const jfs_nr_bitvector_ty lhs,
                                const jfs_nr_bitvector_ty rhs,
                                const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvnand(const jfs_nr_bitvector_ty lhs,
                                  const jfs_nr_bitvector_ty rhs,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvnor(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvxor(const jfs_nr_bitvector_ty lhs,
                                 const jfs_nr_bitvector_ty rhs,
                                 const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvxnor(const jfs_nr_bitvector_ty lhs,
                                  const jfs_nr_bitvector_ty rhs,
                                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_bvnot(const jfs_nr_bitvector_ty value,
                                 const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvult(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvule(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvugt(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvuge(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvslt(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvsle(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvsgt(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

bool jfs_nr_bvsge(const jfs_nr_bitvector_ty lhs, const jfs_nr_bitvector_ty rhs,
                  const jfs_nr_width_ty bitWidth);

jfs_nr_bitvector_ty jfs_nr_make_bitvector(const uint8_t* bufferData,
                                          const uint64_t bufferSize,
                                          const uint64_t lowBit,
                                          const uint64_t highBit);

#ifdef __cplusplus
}
#endif

#endif
