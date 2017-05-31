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
#include "jfs/Transform/StandardPasses.h"
#include "jfs/Transform/AndHoistingPass.h"
#include "jfs/Transform/DuplicateConstraintEliminationPass.h"
#include "jfs/Transform/SimpleContradictionsToFalsePass.h"
#include "jfs/Transform/SimplificationPass.h"
#include "jfs/Transform/TrueConstraintEliminationPass.h"

namespace jfs {
namespace transform {
void AddStandardPasses(QueryPassManager &pm) {
  // TODO: We should implement a wrapper pass that executes until
  // a fixed point is reached. We should then use it with some of
  // these passes.

  // Seperate out into as many constraints as possible.
  pm.add(std::make_shared<AndHoistingPass>());
  // Simplify constraints.
  pm.add(std::make_shared<SimplificationPass>());
  // Remove duplicate constraints
  pm.add(std::make_shared<DuplicateConstraintEliminationPass>());
  // Remove any "true" constraints that were in the original constraints
  // or come from simplification.
  pm.add(std::make_shared<TrueConstraintEliminationPass>());

  // TODO: We should do expression canonicalization so we can do a better job
  // of spotting patterns.

  // Try to replace some simple contradictions that we know
  // how to recognise with false.
  pm.add(std::make_shared<SimpleContradictionsToFalsePass>());

  // Remove any duplicate "false" expressions that were introduced
  pm.add(std::make_shared<DuplicateConstraintEliminationPass>());
}
}
}
