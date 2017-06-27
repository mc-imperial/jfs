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
  case Z3_OP_BSDIV:
    ACTION(visitBvSDiv(asApp))
  case Z3_OP_BUDIV:
    ACTION(visitBvUDiv(asApp))
  case Z3_OP_BSREM:
    ACTION(visitBvSRem(asApp))
  case Z3_OP_BUREM:
    ACTION(visitBvURem(asApp))
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
  // Bitwise BitVector operations
  case Z3_OP_BAND:
    ACTION(visitBvAnd(asApp))
  case Z3_OP_BOR:
    ACTION(visitBvOr(asApp))
  // TODO: Add more application kinds
  default:
    llvm_unreachable("unsupported kind");
  }
#undef ACTION
}
}
}
