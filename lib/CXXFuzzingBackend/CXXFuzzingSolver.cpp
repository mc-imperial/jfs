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
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolver.h"
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolverOptions.h"
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/FuzzingCommon/SortConformanceCheckPass.h"
#include "jfs/Transform/QueryPass.h"
#include "jfs/Transform/QueryPassManager.h"
#include <atomic>
#include <mutex>
#include <unordered_set>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;
using namespace jfs::transform;

namespace jfs {
namespace cxxfb {

class CXXFuzzingSolverResponse : public SolverResponse {
public:
  CXXFuzzingSolverResponse(SolverResponse::SolverSatisfiability sat)
      : SolverResponse(sat) {}
  std::shared_ptr<Model> getModel() override {
    // TODO: Figure out how to do model generation
    return nullptr;
  }
};

class CXXFuzzingSolverImpl {
  std::mutex cancellablePassesMutex; // protects `cancellablePasses`
  std::unordered_set<jfs::transform::QueryPass*> cancellablePasses;
  std::atomic<bool> cancelled;
  JFSContext& ctx;
  // Raw pointer because we don't own the storage.
  CXXFuzzingSolverOptions* options;

public:
  friend class CXXFuzzingSolver;
  CXXFuzzingSolverImpl(JFSContext& ctx, CXXFuzzingSolverOptions* options)
      : cancelled(false), ctx(ctx), options(options) {
    // Check paths
    bool clangPathsOkay = options->getClangOptions()->checkPaths(ctx);
    if (!clangPathsOkay) {
      ctx.raiseFatalError("One or more Clang paths do not exist");
    }
  }
  llvm::StringRef getName() { return "CXXFuzzingSolver"; }
  void cancel() {
    cancelled = true;
    // Cancel any active passes
    {
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      for (const auto& pass : cancellablePasses) {
        pass->cancel();
      }
    }
  }
  // FIXME: Should be const Query.
  bool sortsAreSupported(Query& q) {
    JFSContext &ctx = q.getContext();
    auto p = std::make_shared<SortConformanceCheckPass>([&ctx](Z3SortHandle s) {
      switch (s.getKind()) {
      case Z3_BOOL_SORT: {
        return true;
      }
      case Z3_BV_SORT: {
        unsigned width = s.getBitVectorWidth();
        if (width <= 64) {
          return true;
        }
        // Too wide
        IF_VERB(ctx,
                ctx.getWarningStream()
                    << "(BitVector width " << width << " not supported)\n");
        return false;
      }
      // TODO: Add support for floating point
      default: {
        // Sort not supported
        IF_VERB(ctx,
                ctx.getWarningStream()
                    << "(Sort \"" << s.toStr() << "\" not supported)\n");
        return false;
      }
      }
    });

    QueryPassManager pm;
    {
      // Make the pass cancellable
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(p.get());
      pm.add(p);
    }

    pm.run(q);

    {
      // The pass is done remove it from set of cancellable passes
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.erase(p.get());
    }
    return p->predicateAlwaysHeld();
  }

  std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query &q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) {
    assert(ctx == q.getContext());
    if (produceModel) {
      ctx.getErrorStream() << "(error model generation not supported)\n";
      return nullptr;
    }
#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return std::unique_ptr<SolverResponse>(                                    \
        new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));                \
  }

    // Check types are supported
    if (!sortsAreSupported(q)) {
      IF_VERB(ctx, ctx.getDebugStream() << "(unsupported sorts)\n");
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
    }

    // Cancellation point
    CHECK_CANCELLED();

    // TODO: Do fuzzing
    QueryPassManager pm;
    auto pbp = std::make_shared<CXXProgramBuilderPass>(info, ctx);

    {
      // Make the pass cancellable
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(pbp.get());
      pm.add(pbp);
    }
    pm.run(q);
    {
      // Pass is done. Remove from the set of cancellable passes
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(pbp.get());
    }

    // Cancellation point
    CHECK_CANCELLED();

    return std::unique_ptr<SolverResponse>(
        new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
  }
};

CXXFuzzingSolver::CXXFuzzingSolver(
    std::unique_ptr<CXXFuzzingSolverOptions> options,
    std::unique_ptr<WorkingDirectoryManager> wdm, JFSContext& ctx)
    : jfs::fuzzingCommon::FuzzingSolver(std::move(options), std::move(wdm),
                                        ctx),
      impl(new CXXFuzzingSolverImpl(
          ctx, static_cast<CXXFuzzingSolverOptions*>(this->options.get()))) {}

CXXFuzzingSolver::~CXXFuzzingSolver() {}

std::unique_ptr<jfs::core::SolverResponse>
CXXFuzzingSolver::fuzz(jfs::core::Query &q, bool produceModel,
                       std::shared_ptr<FuzzingAnalysisInfo> info) {
  return impl->fuzz(q, produceModel, info);
}

llvm::StringRef CXXFuzzingSolver::getName() const { return "CXXFuzzingSolver"; }

void CXXFuzzingSolver::cancel() {
  // Call parent
  FuzzingSolver::cancel();
  // Notify implementation
  impl->cancel();
}
}
}
