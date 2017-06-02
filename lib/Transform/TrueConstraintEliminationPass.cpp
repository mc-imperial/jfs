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
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle e = *ci;
    if (e.isTrue()) {
      // Don't add "true" to constraint set.
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
