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
#include "jfs/Z3Backend/Z3Solver.h"
#include "jfs/Core/IfVerbose.h"

using namespace jfs::core;

namespace jfs {
  namespace z3Backend {

  Z3Solver::Z3Solver(std::unique_ptr<SolverOptions> options)
      : jfs::core::Solver(std::move(options)), z3Ctx(nullptr),
        cancelled(false) {}
  Z3Solver::~Z3Solver() {}

  llvm::StringRef Z3Solver::getName() const { return "Z3Solver"; }

  class Z3Model : public jfs::core::Model {
    private:
      Z3ModelHandle model;
    public:
      Z3Model(Z3ModelHandle m) : model(m) {}
      Z3ASTHandle getAssignment(Z3FuncDeclHandle funcDecl) override {
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
  };

  class Z3SolverResponse : public SolverResponse {
    private:
      std::shared_ptr<Model> model;
    public:
    Z3SolverResponse(SolverSatisfiability sat) : SolverResponse(sat), model(nullptr) {}
    ~Z3SolverResponse() {}
    std::shared_ptr<Model> getModel() override {
      return model;
    }
    friend class Z3Solver;
    // To be used by Z3Solver only
    void setModel(Z3ModelHandle m) {
      model.reset(new Z3Model(m));
    }
  };

  void Z3Solver::cancel() {
    cancelled = true;
    if (z3Ctx) {
      ::Z3_interrupt(z3Ctx);
    }
  }

  std::unique_ptr<SolverResponse> Z3Solver::solve(const Query &q, bool getModel) {
    JFSContext& ctx = q.getContext();
    z3Ctx = q.getContext().z3Ctx;
    // Use default solver behaviour
    Z3SolverHandle solver = Z3SolverHandle(::Z3_mk_solver(z3Ctx), z3Ctx);

    // Set solver timeout. Assume default is no timeout.
    if (options->maxTime > 0) {
      Z3ParamsHandle params = Z3ParamsHandle(::Z3_mk_params(z3Ctx), z3Ctx);
      Z3_symbol timeoutSymbol = ::Z3_mk_string_symbol(z3Ctx, "timeout");
      // Z3's timeout is in milliseconds.
      ::Z3_params_set_uint(z3Ctx, params, timeoutSymbol,
                           options->maxTime * 1000);
      ::Z3_solver_set_params(z3Ctx, solver, params);
    }
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
      static_cast<Z3SolverResponse*>(resp.get())->setModel(model);
    }
    return resp;
  }
}
}
