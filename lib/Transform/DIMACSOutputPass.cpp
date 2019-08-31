//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Transform/DIMACSOutputPass.h"
#include "jfs/Core/IfVerbose.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool DIMACSOutputPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::vector<Z3ASTHandle> newConstraints;
  z3Ctx = ctx.getZ3Ctx();

  Z3TacticHandle tactic(::Z3_mk_tactic(z3Ctx, "sat"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    initialGoal.addFormula(*ci);
  }

#define CHECK_CANCELED()                                                       \
  if (cancelled) {                                                             \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return false;                                                              \
  }

  CHECK_CANCELED();

  // Enable `dimacs.display` which writes CNF in DIMACS format to stdout without
  // solving satisfiability.
  // FIXME: This option has been removed in newer versions of Z3, so some care
  // is needed when upgrading Z3 here. Newer Z3 offers a
  // `Z3_goal_to_dimacs_string` API which should work as a replacement.  It may
  // require an additional `tseitin-cnf` pass for valid results.
  // NOTE: Z3's DIMACS output includes comment lines that map constraints to CNF
  // variables, but it has an off-by-one error in this output. Since they are
  // comment lines, there is no functional impact on consumers that read this
  // format.
  Z3ParamsHandle params(::Z3_mk_params(z3Ctx), z3Ctx);
  Z3_symbol dimacs_display = ::Z3_mk_string_symbol(z3Ctx, "dimacs.display");
  Z3_params_set_bool(z3Ctx, params, dimacs_display, true);

  // Apply the tactic and store it for use in convertModel()
  result = tactic.applyWithParams(initialGoal, params);

  CHECK_CANCELED();

  // This is an output pass only, so we skip updating the constraints
  return false;
}

llvm::StringRef DIMACSOutputPass::getName() { return "DIMACSOutput"; }
}
}
