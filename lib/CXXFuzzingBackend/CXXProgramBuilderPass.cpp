//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "CXXProgramBuilderPassImpl.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

CXXProgramBuilderPass::CXXProgramBuilderPass(
    std::shared_ptr<FuzzingAnalysisInfo> info, JFSContext& ctx)
    : impl(new CXXProgramBuilderPassImpl(info, ctx)) {}

std::shared_ptr<CXXProgram> CXXProgramBuilderPass::getProgram() {
  return impl->program;
}

CXXProgramBuilderPass::~CXXProgramBuilderPass() {}

llvm::StringRef CXXProgramBuilderPass::getName() { return "CXXProgramBuilder"; }

bool CXXProgramBuilderPass::run(Query& q) {
  JFSContext& ctx = q.getContext();
  impl->build(q);

  // Print final result
  if (ctx.getVerbosity() >= 2) {
    ctx.getDebugStream() << "(" << getName() << "\n\n";
    impl->program->print(ctx.getDebugStream());
    ctx.getDebugStream() << "\n)\n";
  }
  return false;
}
}
}
