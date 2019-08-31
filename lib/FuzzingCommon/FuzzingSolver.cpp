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
#include "jfs/FuzzingCommon/FuzzingSolver.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/SimpleModel.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/FuzzingCommon/FuzzingSolverOptions.h"
#include "jfs/Transform/QueryPassManager.h"
#include "llvm/Support/Casting.h"
#include <atomic>
#include <mutex>

using namespace jfs::core;
using namespace jfs::transform;

namespace jfs {
namespace fuzzingCommon {

class FuzzingSolverImpl;

// This response type is used for the trivial queries
// that we can solve without fuzzing
class TrivialFuzzingSolverResponse : public jfs::core::SolverResponse {
private:
  friend class FuzzingSolverImpl;
  std::unique_ptr<jfs::core::Model> model;
  void setModel(std::unique_ptr<jfs::core::Model> m) { model = std::move(m); }

public:
  TrivialFuzzingSolverResponse(SolverResponse::SolverSatisfiability sat)
      : SolverResponse(sat) {}
  Model* getModel() override {
    if (sat != SolverSatisfiability::SAT)
      return nullptr;
    return model.get();
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
    assert(q.getContext() == interF->ctx);
#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    JFSContext& ctx = q.getContext();                                          \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return std::unique_ptr<SolverResponse>(                                    \
        new TrivialFuzzingSolverResponse(SolverResponse::UNKNOWN));            \
  }
    // Use dyn_cast because the options provided aren't neccessarily
    // an instance of `FuzzingSolverOptions`.
    const FuzzingSolverOptions* fuzzingOptions =
        llvm::dyn_cast<FuzzingSolverOptions>(interF->options.get());

    // Check for trivial SAT
    if (q.constraints.size() == 0) {
      // Empty constraint set is trivially satisifiable

      auto resp = std::unique_ptr<TrivialFuzzingSolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::SAT));
      if (produceModel) {
        // Make empty model
        auto model =
            std::unique_ptr<SimpleModel>(new SimpleModel(q.getContext()));
        resp->setModel(std::move(model));
      }
      if (fuzzingOptions && fuzzingOptions->debugSaveModel) {
        JFSContext& ctx = q.getContext();
        IF_VERB(ctx, ctx.getDebugStream()
            << "(model save request ignored, not serializable");
      }
      return resp;
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
    FuzzingSolverOptions* fsOpts =
        llvm::dyn_cast<FuzzingSolverOptions>(interF->options.get());
    auto fai = std::make_shared<FuzzingAnalysisInfo>(
        (fsOpts != nullptr) ? fsOpts->getFreeVariableToBufferAssignmentOptions()
                            : nullptr);
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
      auto resp = std::unique_ptr<TrivialFuzzingSolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::SAT));
      if (produceModel) {
        // Make empty model
        auto model = std::unique_ptr<Model>(new SimpleModel(q.getContext()));
        // Now convert model so that it satisfies the query given to the
        // preprocessing passes.
        bool convertModelSuccess =
            preprocessingPassses.convertModel(model.get());
        if (!convertModelSuccess) {
          // FIXME: Should we try to recover instead?
          q.getContext().raiseFatalError("Failed to convert model");
        }
        resp->setModel(std::move(model));
      }
      if (fuzzingOptions && fuzzingOptions->debugSaveModel) {
        JFSContext& ctx = q.getContext();
        IF_VERB(ctx, ctx.getDebugStream()
            << "(model save request ignored, not serializable");

      }
      return resp;
    }

    // Check if equalities simplified to false
    if (qCopy.constraints.size() == 1 && qCopy.constraints[0].isFalse()) {
      return std::unique_ptr<SolverResponse>(
          new TrivialFuzzingSolverResponse(SolverResponse::UNSAT));
    }

    CHECK_CANCELLED()
    // Have to performing fuzzing
    auto resp = interF->fuzz(qCopy, produceModel, fai);
    if (resp->sat == SolverResponse::SAT) {
      if (produceModel) {
        // Now convert model so that it satisfies the query given to the
        // preprocessing passes.
        bool convertModelSuccess =
            preprocessingPassses.convertModel(resp->getModel());
        if (!convertModelSuccess) {
          // FIXME: Should we try to recover instead?
          q.getContext().raiseFatalError("Failed to convert model");
        }
      }
    }
    return resp;
  }
#undef CHECK_CANCELLED
};

FuzzingSolver::FuzzingSolver(std::unique_ptr<SolverOptions> options,
                             std::unique_ptr<WorkingDirectoryManager> wdm,
                             JFSContext& ctx)
    : Solver(std::move(options), ctx), impl(new FuzzingSolverImpl(this)),
      wdm(std::move(wdm)) {}
FuzzingSolver::~FuzzingSolver() {}
std::unique_ptr<jfs::core::SolverResponse>
FuzzingSolver::solve(const jfs::core::Query& q, bool produceModel) {
  return impl->solve(q, produceModel);
}
void FuzzingSolver::cancel() { impl->cancel(); }
}
}
