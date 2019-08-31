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
#include "jfs/Transform/DuplicateConstraintEliminationPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3NodeSet.h"
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool DuplicateConstraintEliminationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());
  Z3ASTSet seenConstraints;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    if (seenConstraints.count(*ci) > 0) {
      changed = true;
      continue;
    }
    // Not seen before
    seenConstraints.insert(*ci);
    newConstraints.push_back(*ci);
  }

  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }

  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef DuplicateConstraintEliminationPass::getName() {
  return "DuplicateConstraintElimination";
}

bool DuplicateConstraintEliminationPass::convertModel(jfs::core::Model* m) {
  // This pass preserves equivalence so the model does not need to be
  // converted.
  return true;
}
}
}
