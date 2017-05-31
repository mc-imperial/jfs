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
#include "jfs/Transform/DuplicateConstraintEliminationPass.h"
#include "jfs/Core/Z3NodeSet.h"
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool DuplicateConstraintEliminationPass::run(Query &q) {
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());
  Z3ASTSet seenConstraints;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    if (seenConstraints.count(*ci) > 0) {
      changed = true;
      continue;
    }
    // Not seen before
    seenConstraints.insert(*ci);
    newConstraints.push_back(*ci);
  }

  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef DuplicateConstraintEliminationPass::getName() {
  return "DuplicateConstraintElimination";
}
}
}
