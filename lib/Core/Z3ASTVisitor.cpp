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

// Dispatch to appropriate visitor method
void Z3ASTVisitor::visit(Z3ASTHandle e) {
  assert(e.isApp() && "expr should be an application");
  Z3AppHandle asApp = e.asApp();
  switch (asApp.getKind()) {
  case Z3_OP_TRUE:
  case Z3_OP_FALSE:
    visitBoolConstant(asApp);
    return;
  case Z3_OP_BNUM:
    visitBitVector(asApp);
    return;
  // TODO: Add more application kinds
  default:
    llvm_unreachable("unsupported kind");
  }
}
}
}
