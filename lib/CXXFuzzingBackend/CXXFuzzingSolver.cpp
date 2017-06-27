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
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/FuzzingCommon/SortConformanceCheckPass.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

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
public:
  // FIXME: Should be const Query.
  bool sortsAreSupported(Query &q) const {
    JFSContext &ctx = q.getContext();
    SortConformanceCheckPass p([&ctx](Z3SortHandle s) {
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
    p.run(q);
    return p.predicateAlwaysHeld();
  }

  std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query &q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) {
    JFSContext &ctx = q.getContext();
    if (produceModel) {
      ctx.getErrorStream() << "(error model generation not supported)\n";
      return nullptr;
    }

    // Check types are supported
    if (!sortsAreSupported(q)) {
      IF_VERB(ctx, ctx.getDebugStream() << "(unsupported sorts)\n");
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
    }

    // TODO: Do fuzzing
    CXXProgramBuilderPass pbp(info, ctx);
    pbp.run(q);
    return std::unique_ptr<SolverResponse>(
        new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
  }
};

CXXFuzzingSolver::CXXFuzzingSolver(const jfs::core::SolverOptions &options)
    : jfs::fuzzingCommon::FuzzingSolver(options),
      impl(new CXXFuzzingSolverImpl()) {}

CXXFuzzingSolver::~CXXFuzzingSolver() {}

std::unique_ptr<jfs::core::SolverResponse>
CXXFuzzingSolver::fuzz(jfs::core::Query &q, bool produceModel,
                       std::shared_ptr<FuzzingAnalysisInfo> info) {
  return impl->fuzz(q, produceModel, info);
}

llvm::StringRef CXXFuzzingSolver::getName() const { return "CXXFuzzingSolver"; }
}
}
