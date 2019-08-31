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
#include "jfs/Core/Z3ASTVisitor.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Compiler.h"

namespace jfs {
namespace core {

Z3ASTVisitor::Z3ASTVisitor() {}

Z3ASTVisitor::~Z3ASTVisitor() {}

// Macro to avoid accidental drop through and typos
#define ACTION(X)                                                              \
  {                                                                            \
    X;                                                                         \
    return;                                                                    \
  }
// Dispatch to appropriate visitor method
void Z3ASTVisitor::visit(Z3ASTHandle e) {
  assert(e.isApp() && "expr should be an application");
  Z3AppHandle asApp = e.asApp();
  switch (asApp.getKind()) {
  case Z3_OP_TRUE:
    ACTION(visitBoolConstant(asApp))
  case Z3_OP_FALSE:
    ACTION(visitBoolConstant(asApp))
  case Z3_OP_BNUM:
    ACTION(visitBitVector(asApp))
  case Z3_OP_FPA_NUM:
    ACTION(visitFloatingPointConstant(asApp))
  // Overloaded operations
  case Z3_OP_EQ:
    ACTION(visitEqual(asApp))
  case Z3_OP_DISTINCT:
    ACTION(visitDistinct(asApp))
  case Z3_OP_ITE:
    ACTION(visitIfThenElse(asApp))
  // Boolean operations
  case Z3_OP_AND:
    ACTION(visitAnd(asApp))
  case Z3_OP_OR:
    ACTION(visitOr(asApp))
  case Z3_OP_XOR:
    ACTION(visitXor(asApp))
  case Z3_OP_NOT:
    ACTION(visitNot(asApp))
  case Z3_OP_IMPLIES:
    ACTION(visitImplies(asApp))
  case Z3_OP_IFF:
    ACTION(visitIff(asApp))
  // Arithmetic BitVector operations
  case Z3_OP_BNEG:
    ACTION(visitBvNeg(asApp))
  case Z3_OP_BADD:
    ACTION(visitBvAdd(asApp))
  case Z3_OP_BSUB:
    ACTION(visitBvSub(asApp))
  case Z3_OP_BMUL:
    ACTION(visitBvMul(asApp))
  case Z3_OP_BSDIV_I:
    LLVM_FALLTHROUGH;
  case Z3_OP_BSDIV:
    ACTION(visitBvSDiv(asApp))
  case Z3_OP_BUDIV:
    LLVM_FALLTHROUGH;
  case Z3_OP_BUDIV_I:
    ACTION(visitBvUDiv(asApp))
  case Z3_OP_BSREM_I:
    LLVM_FALLTHROUGH;
  case Z3_OP_BSREM:
    ACTION(visitBvSRem(asApp))
  case Z3_OP_BUREM_I:
    LLVM_FALLTHROUGH;
  case Z3_OP_BUREM:
    ACTION(visitBvURem(asApp))
  case Z3_OP_BSMOD_I:
    LLVM_FALLTHROUGH;
  case Z3_OP_BSMOD:
    ACTION(visitBvSMod(asApp))
  // Comparison BitVector operations
  case Z3_OP_ULEQ:
    ACTION(visitBvULE(asApp))
  case Z3_OP_SLEQ:
    ACTION(visitBvSLE(asApp))
  case Z3_OP_UGEQ:
    ACTION(visitBvUGE(asApp))
  case Z3_OP_SGEQ:
    ACTION(visitBvSGE(asApp))
  case Z3_OP_ULT:
    ACTION(visitBvULT(asApp))
  case Z3_OP_SLT:
    ACTION(visitBvSLT(asApp))
  case Z3_OP_UGT:
    ACTION(visitBvUGT(asApp))
  case Z3_OP_SGT:
    ACTION(visitBvSGT(asApp))
  case Z3_OP_BCOMP:
    ACTION(visitBvComp(asApp))
  // Bitwise BitVector operations
  case Z3_OP_BAND:
    ACTION(visitBvAnd(asApp))
  case Z3_OP_BOR:
    ACTION(visitBvOr(asApp))
  case Z3_OP_BNOT:
    ACTION(visitBvNot(asApp))
  case Z3_OP_BXOR:
    ACTION(visitBvXor(asApp))
  case Z3_OP_BNAND:
    ACTION(visitBvNand(asApp))
  case Z3_OP_BNOR:
    ACTION(visitBvNor(asApp))
  case Z3_OP_BXNOR:
    ACTION(visitBvXnor(asApp))
  // Shift and rotation BitVector operations
  case Z3_OP_BSHL:
    ACTION(visitBvShl(asApp))
  case Z3_OP_BLSHR:
    ACTION(visitBvLShr(asApp))
  case Z3_OP_BASHR:
    ACTION(visitBvAShr(asApp))
  case Z3_OP_ROTATE_LEFT:
    ACTION(visitBvRotateLeft(asApp))
  case Z3_OP_ROTATE_RIGHT:
    ACTION(visitBvRotateRight(asApp))
  // Sort changing BitVector operations
  case Z3_OP_CONCAT:
    ACTION(visitBvConcat(asApp))
  case Z3_OP_SIGN_EXT:
    ACTION(visitBvSignExtend(asApp))
  case Z3_OP_ZERO_EXT:
    ACTION(visitBvZeroExtend(asApp))
  case Z3_OP_EXTRACT:
    ACTION(visitBvExtract(asApp))
  // TODO: Add more application kinds
  // Floating point operations
  case Z3_OP_FPA_FP:
    ACTION(visitFloatingPointFromTriple(asApp));
  case Z3_OP_FPA_TO_FP: {
    if (asApp.getNumKids() == 1) {
      assert(asApp.getKid(0).getSort().isBitVectorTy());
      visitFloatingPointFromIEEEBitVector(asApp);
      return;
    }
    assert(asApp.getNumKids() == 2);
    assert(asApp.getKid(0).getSort().getKind() == Z3_ROUNDING_MODE_SORT);
    auto argSort = asApp.getKid(1).getSort();
    if (argSort.isFloatingPointTy()) {
      visitConvertToFloatFromFloat(asApp);
    } else {
      assert(argSort.isBitVectorTy());
      visitConvertToFloatFromSignedBitVector(asApp);
    }
    return;
  }
  case Z3_OP_FPA_TO_FP_UNSIGNED:
    ACTION(visitConvertToFloatFromUnsignedBitVector(asApp))
  case Z3_OP_FPA_IS_NAN:
    ACTION(visitFloatIsNaN(asApp))
  case Z3_OP_FPA_IS_NORMAL:
    ACTION(visitFloatIsNormal(asApp))
  case Z3_OP_FPA_IS_SUBNORMAL:
    ACTION(visitFloatIsSubnormal(asApp))
  case Z3_OP_FPA_IS_ZERO:
    ACTION(visitFloatIsZero(asApp))
  case Z3_OP_FPA_IS_POSITIVE:
    ACTION(visitFloatIsPositive(asApp))
  case Z3_OP_FPA_IS_NEGATIVE:
    ACTION(visitFloatIsNegative(asApp))
  case Z3_OP_FPA_IS_INF:
    ACTION(visitFloatIsInfinite(asApp))
  case Z3_OP_FPA_EQ:
    ACTION(visitFloatIEEEEquals(asApp))
  case Z3_OP_FPA_LT:
    ACTION(visitFloatLessThan(asApp))
  case Z3_OP_FPA_LE:
    ACTION(visitFloatLessThanOrEqual(asApp))
  case Z3_OP_FPA_GT:
    ACTION(visitFloatGreaterThan(asApp))
  case Z3_OP_FPA_GE:
    ACTION(visitFloatGreaterThanOrEqual(asApp))
  case Z3_OP_FPA_PLUS_ZERO:
    ACTION(visitFloatPositiveZero(asApp))
  case Z3_OP_FPA_MINUS_ZERO:
    ACTION(visitFloatNegativeZero(asApp))
  case Z3_OP_FPA_PLUS_INF:
    ACTION(visitFloatPositiveInfinity(asApp))
  case Z3_OP_FPA_MINUS_INF:
    ACTION(visitFloatNegativeInfinity(asApp))
  case Z3_OP_FPA_NAN:
    ACTION(visitFloatNaN(asApp))
  case Z3_OP_FPA_ABS:
    ACTION(visitFloatAbs(asApp))
  case Z3_OP_FPA_NEG:
    ACTION(visitFloatNeg(asApp))
  case Z3_OP_FPA_MIN:
    ACTION(visitFloatMin(asApp))
  case Z3_OP_FPA_MAX:
    ACTION(visitFloatMax(asApp))
  case Z3_OP_FPA_ADD:
    ACTION(visitFloatAdd(asApp))
  case Z3_OP_FPA_SUB:
    ACTION(visitFloatSub(asApp))
  case Z3_OP_FPA_MUL:
    ACTION(visitFloatMul(asApp))
  case Z3_OP_FPA_DIV:
    ACTION(visitFloatDiv(asApp))
  case Z3_OP_FPA_FMA:
    ACTION(visitFloatFMA(asApp))
  case Z3_OP_FPA_SQRT:
    ACTION(visitFloatSqrt(asApp))
  case Z3_OP_FPA_REM:
    ACTION(visitFloatRem(asApp))
  case Z3_OP_FPA_ROUND_TO_INTEGRAL:
    ACTION(visitFloatRoundToIntegral(asApp))
  case Z3_OP_FPA_TO_UBV:
    ACTION(visitConvertToUnsignedBitVectorFromFloat(asApp))
  case Z3_OP_FPA_TO_SBV:
    ACTION(visitConvertToSignedBitVectorFromFloat(asApp))
  case Z3_OP_UNINTERPRETED:
    ACTION(visitUninterpretedFunc(asApp))
  case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
  case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
  case Z3_OP_FPA_RM_TOWARD_POSITIVE:
  case Z3_OP_FPA_RM_TOWARD_NEGATIVE:
  case Z3_OP_FPA_RM_TOWARD_ZERO:
  default:
    llvm_unreachable("unsupported kind");
  }
#undef ACTION
}
}
}
