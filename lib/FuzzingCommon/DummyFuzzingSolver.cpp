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
#include "jfs/FuzzingCommon/DummyFuzzingSolver.h"

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {
DummyFuzzingSolver::DummyFuzzingSolver(
    std::unique_ptr<SolverOptions> options,
    std::unique_ptr<WorkingDirectoryManager> wdm, JFSContext& ctx)
    : FuzzingSolver(std::move(options), std::move(wdm), ctx) {}

DummyFuzzingSolver::~DummyFuzzingSolver() {}

llvm::StringRef DummyFuzzingSolver::getName() const {
  return "DummyFuzzingSolver";
}

void DummyFuzzingSolver::cancel() {
  // Dummy solver, so nothing to cancel
}

class DummyFuzzingSolverResponse : public SolverResponse {
public:
  DummyFuzzingSolverResponse() : SolverResponse(SolverResponse::UNKNOWN) {}
  Model* getModel() override {
    // There is no model
    return nullptr;
  }
};

std::unique_ptr<jfs::core::SolverResponse>
DummyFuzzingSolver::fuzz(jfs::core::Query& q, bool produceModel,
                         std::shared_ptr<FuzzingAnalysisInfo> info) {
  // Don't try to fuzz. Just give up immediately
  return std::unique_ptr<SolverResponse>(new DummyFuzzingSolverResponse());
}
}
}
