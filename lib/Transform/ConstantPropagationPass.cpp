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
#include "jfs/Transform/ConstantPropagationPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool ConstantPropagationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::vector<Z3ASTHandle> newConstraints;
  z3Ctx = q.getContext().z3Ctx;
  Z3TacticHandle propagateValuesTactic(
      ::Z3_mk_tactic(z3Ctx, "propagate-values"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  // Add the constraints to the goal
// FIXME: I wish Z3's Goal API didn't do this. I'd like the simplifications
// to come from the tactics I apply and not happen implicitly.
#ifndef NDEBUG
  bool falseAdded = false;
#endif
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
#ifndef NDEBUG
    unsigned expectedIncrement = 0;
    if (ci->isTrue()) {
      // `true` gets ignored when inserted into a goal so don't count it for the
      // assert.
    } else if (ci->isFalse()) {
      // Adding false seems to make Z3 reduce goal to just contain false.
      falseAdded = true;
    } else if (ci->isAppOf(Z3_OP_AND)) {
      // Z3's API seems to hoist ands so count these.
      expectedIncrement += ci->asApp().getNumKids();
    } else if (ci->isAppOf(Z3_OP_NOT) && ci->asApp().getKid(0).isAppOf(Z3_OP_OR)) {
      // Z3's API seems to apply de-morgan
      // (not (or a b)) === (not a) , (not b)
      expectedIncrement += ci->asApp().getKid(0).asApp().getNumKids();
    } else {
      // Otherwise assume that adding the formula will add one formula
      // to the formula count
      ++expectedIncrement;
    }
    unsigned countBefore = initialGoal.getNumFormulas();
#endif
    initialGoal.addFormula(*ci);
#ifndef NDEBUG
    unsigned countAfter = initialGoal.getNumFormulas();
    if (falseAdded) {
      assert(countAfter == 1 &&
             "Expected adding false to reduce goal to false");
    } else {
      assert(((countAfter - countBefore) == expectedIncrement) &&
             "unexpected gain/loss of formulas");
    }
#endif
  }

  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }

  // Apply the tactic
  Z3ApplyResultHandle result = propagateValuesTactic.apply(initialGoal);

  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }

  // Collect all the resulting formulas
  result.collectAllFormulas(newConstraints);

  if (Query::areSame(q.constraints, newConstraints, /*ignoreOrder=*/true))
    return false;

  // Something changed
  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef ConstantPropagationPass::getName() {
  return "ConstantPropagation";
}
}
}
