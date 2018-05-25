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
  auto model = getRepr();
  if (model.isNull()) {
    // No model available.
    // FIXME: Report this error to the JFSContext
    assert(false && "no model available");
    return Z3ASTHandle();
  }
  assert(funcDecl.getContext() == model.getContext() && "mismatched contexts");
  Z3_ast rawPointer = nullptr;
  Z3_bool success =
      ::Z3_model_eval(model.getContext(), model,
                      ::Z3_func_decl_to_ast(model.getContext(), funcDecl),
                      /*model_completion=*/true, &rawPointer);
  assert(success && "Failed to get assignment from Z3 model");
  return Z3ASTHandle(rawPointer, model.getContext());
}

bool Model::hasAssignmentFor(Z3FuncDeclHandle decl) {
  auto model = getRepr();
  return model.hasAssignmentFor(decl);
}

bool Model::addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                             bool allowOverwrite) {
  Z3ModelHandle model = getRepr();
  assert(decl.getContext() == model.getContext() &&
         "mistached decl and model context");
  assert(e.getContext() == model.getContext() &&
         "mismatched assignment and model context");
  if (!allowOverwrite) {
    // Check if an assignment already exists
    if (model.hasAssignmentFor(decl)) {
      return false;
    }
  }
  if (!e.isConstant()) {
    // We only support constant assignments right now.
    // Z3's API allows giving assignments to arrays and
    // uninterpreted functions but let's not worry about that
    // right now.
    return false;
  }
  Z3_add_const_interp(model.getContext(), model, decl, e);
  return true;
}

std::string Model::getSMTLIBString() {
  // FIXME: This isn't actually SMTLIB syntax.  Z3 doesn't seem to have a C
  // API for this.  We either need to get them to implement one or we need to
  // implement it by hand.
  return getRepr().toStr();
}

} // namespace core
} // namespace jfs
