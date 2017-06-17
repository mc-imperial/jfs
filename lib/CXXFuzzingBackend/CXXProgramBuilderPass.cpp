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
#include "jfs/CXXFuzzingBackend/CXXProgram.h"

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
  JFSContext& ctx = q.getContext();
  program = std::make_shared<CXXProgram>();
  // Runtime header include
  CXXDeclRef include =
      std::make_shared<CXXIncludeDecl>(program, "SMTLIB/BitVector.h", false);
  program->appendDecl(include);

  if (ctx.getVerbosity() >= 2) {
    ctx.getDebugStream() << "(" << getName() << "\n\n";
    program->print(ctx.getDebugStream());
    ctx.getDebugStream() << "\n)\n";
  }
  return false;
}
}
}
