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
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

CXXProgramBuilderPass::CXXProgramBuilderPass(
    std::shared_ptr<FuzzingAnalysisInfo> info)
    : info(info) {}

CXXProgramBuilderPass::~CXXProgramBuilderPass() {}

llvm::StringRef CXXProgramBuilderPass::getName() { return "CXXProgramBuilder"; }

bool CXXProgramBuilderPass::run(Query& q) {
  // TODO:
  return false;
}
}
}
