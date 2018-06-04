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
#include "jfs/Core/Model.h"

namespace jfs {
namespace core {

Model::Model(JFSContext& ctx) : ctx(ctx) {}
Model::~Model() {}

Z3ASTHandle Model::getAssignmentFor(Z3FuncDeclHandle funcDecl) {
  return getRepr().getAssignmentFor(funcDecl);
}

bool Model::hasAssignmentFor(Z3FuncDeclHandle decl) {
  return getRepr().hasAssignmentFor(decl);
}

bool Model::addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                             bool allowOverwrite) {
  return getRepr().addAssignmentFor(decl, e, allowOverwrite);
}

std::string Model::getSMTLIBString() {
  // FIXME: This isn't actually SMTLIB syntax.  Z3 doesn't seem to have a C
  // API for this.  We either need to get them to implement one or we need to
  // implement it by hand.
  return getRepr().toStr();
}

} // namespace core
} // namespace jfs
