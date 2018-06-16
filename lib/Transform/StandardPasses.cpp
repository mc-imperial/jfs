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
#include "jfs/Transform/StandardPasses.h"
#include "jfs/Transform/Passes.h"

namespace jfs {
namespace transform {
void AddStandardPasses(QueryPassManager &pm) {

  // Seperate out into as many constraints as possible.
  pm.add(std::make_shared<AndHoistingPass>());

  // TODO: This should probably be iterated to a fixed point. This just became
  // much harder because now we have to support model generation. The current
  // implementation can only have convertModel() called on a pass once (i.e.
  // we can't reuse a pass because it stores the model conversion information
  // for that step).

  // FIXME: BvBoundPropagationPass shouldn't be here. There seems to be some
  // issues when combining simplifier and propagate-bv-bounds
  // https://github.com/Z3Prover/z3/issues/1054
  // FIXME: BvBoundPropagationPass is broken. On some benchmarks it gets stuck
  // see https://github.com/Z3Prover/z3/issues/1078
  // Simplify bounds
  //pm.add(std::make_shared<BvBoundPropagationPass>());
  // Simplify constraints.
  pm.add(std::make_shared<SimplificationPass>());
  // Hoist any ands introduced
  pm.add(std::make_shared<AndHoistingPass>());
  // Simplify bounds
  // FIXME: BvBoundPropagationPass is broken. On some benchmarks it gets stuck
  // see https://github.com/Z3Prover/z3/issues/1078
  //pm.add(std::make_shared<BvBoundPropagationPass>());
  // Simplify again
  pm.add(std::make_shared<SimplificationPass>());
  // Propagate constants
  pm.add(std::make_shared<ConstantPropagationPass>());
  // Hoist any ands introduced
  pm.add(std::make_shared<AndHoistingPass>());
  // Simplify again
  pm.add(std::make_shared<SimplificationPass>());
  // Propagate constants
  pm.add(std::make_shared<ConstantPropagationPass>());
  // Simplify again
  pm.add(std::make_shared<SimplificationPass>());
  // Hoist any ands introduced
  pm.add(std::make_shared<AndHoistingPass>());

  // Remove duplicate constraints
  pm.add(std::make_shared<DuplicateConstraintEliminationPass>());

  // FIXME: The `ConstantPropagationPass` actually removes
  // `true` constraints too. Is `TrueConstraintEliminationPass` now redundant?
  //
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
