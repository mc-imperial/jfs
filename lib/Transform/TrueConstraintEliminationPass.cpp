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
#include "jfs/Transform/TrueConstraintEliminationPass.h"
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool TrueConstraintEliminationPass::run(Query &q) {
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  const JFSContext &ctx = q.getContext();
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle e = *ci;
    if (!Z3_is_app(ctx.z3Ctx, e)) {
      // Not an application. Just add as a constraint
      newConstraints.push_back(e);
      continue;
    }
    Z3AppHandle topLevelApp = Z3AppHandle(::Z3_to_app(ctx.z3Ctx, e), ctx.z3Ctx);
    Z3FuncDeclHandle topLevelFunc =
        Z3FuncDeclHandle(::Z3_get_app_decl(ctx.z3Ctx, topLevelApp), ctx.z3Ctx);
    Z3_decl_kind kind = Z3_get_decl_kind(ctx.z3Ctx, topLevelFunc);
    if (kind == Z3_OP_TRUE) {
      // Is the "true" constrant. Ignore it
      changed = true;
      continue;
    }
    newConstraints.push_back(e);
  }

  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
};

llvm::StringRef TrueConstraintEliminationPass::getName() {
  return "TrueConstraintElimination";
}
}
}
