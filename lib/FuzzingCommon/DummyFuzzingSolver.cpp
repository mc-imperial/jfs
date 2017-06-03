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
#include "jfs/FuzzingCommon/DummyFuzzingSolver.h"

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {
DummyFuzzingSolver::DummyFuzzingSolver(const SolverOptions &opts)
    : FuzzingSolver(opts) {}

DummyFuzzingSolver::~DummyFuzzingSolver() {}

llvm::StringRef DummyFuzzingSolver::getName() const {
  return "DummyFuzzingSolver";
}

class DummyFuzzingSolverResponse : public SolverResponse {
public:
  DummyFuzzingSolverResponse() : SolverResponse(SolverResponse::UNKNOWN) {}
  std::shared_ptr<Model> getModel() override {
    // There is no model
    return nullptr;
  }
};

std::unique_ptr<jfs::core::SolverResponse>
DummyFuzzingSolver::fuzz(jfs::core::Query &q, bool produceModel,
                         std::shared_ptr<FuzzingAnalysisInfo> info) {
  // Don't try to fuzz. Just give up immediately
  return std::unique_ptr<SolverResponse>(new DummyFuzzingSolverResponse());
}
}
}
