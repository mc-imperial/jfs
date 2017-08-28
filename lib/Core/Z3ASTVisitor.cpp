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
  // FIXME: Add handler for this.
  // case Z3_OP_FPA_NUM:
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
    assert(asApp.getNumKids() == 1);
    assert(asApp.getKid(0).getSort().isBitVectorTy());
    visitFloatingPointFromIEEEBitVector(asApp);
    return;
  }
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
  default:
    llvm_unreachable("unsupported kind");
  }
#undef ACTION
}
}
}
