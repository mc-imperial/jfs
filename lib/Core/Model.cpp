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

Z3ASTHandle Model::getAssignment(Z3FuncDeclHandle funcDecl) {
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

std::string Model::getSMTLIBString() {
  // FIXME: This isn't actually SMTLIB syntax.  Z3 doesn't seem to have a C
  // API for this.  We either need to get them to implement one or we need to
  // implement it by hand.
  return model.toStr();
}

} // namespace core
} // namespace jfs
