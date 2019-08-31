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
#include "jfs/Z3Backend/Z3Solver.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Model.h"

using namespace jfs::core;

namespace jfs {
  namespace z3Backend {

  Z3Solver::Z3Solver(std::unique_ptr<SolverOptions> options, JFSContext& ctx)
      : jfs::core::Solver(std::move(options), ctx), z3Ctx(ctx.getZ3Ctx()),
        cancelled(false) {}
  Z3Solver::~Z3Solver() {}

  llvm::StringRef Z3Solver::getName() const { return "Z3Solver"; }

  class Z3Model : public jfs::core::Model {
  public:
    Z3Model(JFSContext& ctx, Z3ModelHandle m) : Model(ctx) { z3Model = m; }
    ~Z3Model() {}
  };

  class Z3SolverResponse : public SolverResponse {
    private:
      std::unique_ptr<Model> model;

    public:
    Z3SolverResponse(SolverSatisfiability sat) : SolverResponse(sat), model(nullptr) {}
    ~Z3SolverResponse() {}
    Model* getModel() override { return model.get(); }
    friend class Z3Solver;
    // To be used by Z3Solver only
    void setModel(JFSContext& ctx, Z3ModelHandle m) {
      model.reset(new Z3Model(ctx, m));
    }
  };

  void Z3Solver::cancel() {
    cancelled = true;
    if (z3Ctx) {
      ::Z3_interrupt(z3Ctx);
    }
  }

  std::unique_ptr<SolverResponse> Z3Solver::solve(const Query& q,
                                                  bool getModel) {
    assert(&ctx == &(q.getContext()));
    assert(z3Ctx == q.getContext().getZ3Ctx());
    // Use default solver behaviour
    Z3SolverHandle solver = Z3SolverHandle(::Z3_mk_solver(z3Ctx), z3Ctx);

    for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
         ++ci) {
      ::Z3_solver_assert(z3Ctx, solver, *ci);
    }
    Z3_lbool satisfiable = Z3_L_UNDEF;
    if (!cancelled) {
      satisfiable = Z3_solver_check(z3Ctx, solver);
    }

    SolverResponse::SolverSatisfiability sat = SolverResponse::UNKNOWN;
    switch (satisfiable) {
      case Z3_L_TRUE:
        sat = SolverResponse::SAT;
        break;
      case Z3_L_FALSE:
        sat = SolverResponse::UNSAT;
        break;
      default:
        sat = SolverResponse::UNKNOWN;
    }

    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    }

    std::unique_ptr<SolverResponse> resp(new Z3SolverResponse(sat));
    if (getModel && sat == SolverResponse::SAT) {
      // Add the model
      Z3ModelHandle model = Z3ModelHandle(::Z3_solver_get_model(z3Ctx, solver), z3Ctx);
      static_cast<Z3SolverResponse*>(resp.get())->setModel(ctx, model);
    }
    return resp;
  }
}
}
