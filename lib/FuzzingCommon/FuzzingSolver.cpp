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
#include "jfs/FuzzingCommon/FuzzingSolver.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/Transform/QueryPassManager.h"
#include <atomic>
#include <mutex>

using namespace jfs::core;
using namespace jfs::transform;

namespace jfs {
namespace fuzzingCommon {


// This response type is used for the trivial queries
// that we can solve without fuzzing
class TrivialFuzzingSolverResponse : public jfs::core::SolverResponse {
public:
  TrivialFuzzingSolverResponse(SolverResponse::SolverSatisfiability sat)
      : SolverResponse(sat) {}
  std::shared_ptr<Model> getModel() override {
    // TODO: Figure out how to support Model generation.
    // Can we have common code for all fuzzing backends or
    // will they need their own?
    return nullptr;
  }
};

// FIXME: This complication exists because I don't want to expose the
// implementation details to the client. This might be too complicated.
class FuzzingSolverImpl {
  std::atomic<bool> cancelled;
  FuzzingSolver* interF;
  std::mutex cancellablePassManagerMutex;
  QueryPassManager* cancellablePassManager;
  llvm::StringRef getName() const { return "FuzzingSolver"; }

public:
  FuzzingSolverImpl(FuzzingSolver* interF)
      : cancelled(false), interF(interF), cancellablePassManager(nullptr) {}
  void cancel() {
    cancelled = true;
    std::lock_guard<std::mutex> lock(cancellablePassManagerMutex);
    if (cancellablePassManager) {
      cancellablePassManager->cancel();
    }
  }
  std::unique_ptr<SolverResponse> solve(const jfs::core::Query& q,
                                        bool produceModel) {
#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    JFSContext& ctx = q.getContext();                                          \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return std::unique_ptr<SolverResponse>(                                    \
        new TrivialFuzzingSolverResponse(SolverResponse::UNKNOWN));            \
  }

    // Check for trivial SAT
    if (q.constraints.size() == 0) {
      // Empty constraint set is trivially satisifiable
      assert(!produceModel && "producing models not implemented");
      return std::unique_ptr<SolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::SAT));
    }

    CHECK_CANCELLED()

    // Check for trivial UNSAT
    bool isUnsat = false;
    for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
         ++ci) {
      Z3ASTHandle e = *ci;
      if (e.isFalse()) {
        isUnsat = true;
        break;
      }
    }
    if (isUnsat) {
      return std::unique_ptr<SolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::UNSAT));
    }

    CHECK_CANCELLED()

    // FIXME: Not sure we need to modify the query yet. If not we should
    // change the pass hierarchy so we can have analysis only passes that
    // work on `const Query`.
    // Make a copy of the query to work on. This is so that the client's
    // copy of the query doesn't unexpectedly change.
    Query qCopy(q);

    // Can't trivially prove sat/unsat, so we have to fuzz.
    // Collect the information we need to fuzz and start fuzz
    auto fai = std::make_shared<FuzzingAnalysisInfo>();
    QueryPassManager preprocessingPassses;
    {
      // Make the pass manager cancellable
      std::lock_guard<std::mutex> lock(cancellablePassManagerMutex);
      cancellablePassManager = &preprocessingPassses;
    }

    fai->addTo(preprocessingPassses);
    if (!cancelled) {
      preprocessingPassses.run(qCopy);
    }

    {
      // Make the pass manager uncancellable
      std::lock_guard<std::mutex> lock(cancellablePassManagerMutex);
      cancellablePassManager = nullptr;
    }

    // Check for trivial SAT. This can happen if the query only consists
    // of equalities.
    if (qCopy.constraints.size() == 0) {
      // Empty constraint set is trivially satisifiable
      assert(!produceModel && "producing models not implemented");
      return std::unique_ptr<SolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::SAT));
    }

    // Check if equalities simplified to false
    if (qCopy.constraints.size() == 1 && qCopy.constraints[0].isFalse()) {
      return std::unique_ptr<SolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::UNSAT));
    }

    CHECK_CANCELLED()
    return interF->fuzz(qCopy, produceModel, fai);
  }
#undef CHECK_CANCELLED
};

FuzzingSolver::FuzzingSolver(std::unique_ptr<SolverOptions> options)
    : Solver(std::move(options)), impl(new FuzzingSolverImpl(this)) {}
FuzzingSolver::~FuzzingSolver() {}
std::unique_ptr<jfs::core::SolverResponse>
FuzzingSolver::solve(const jfs::core::Query& q, bool produceModel) {
  return impl->solve(q, produceModel);
}
void FuzzingSolver::cancel() { impl->cancel(); }
}
}
