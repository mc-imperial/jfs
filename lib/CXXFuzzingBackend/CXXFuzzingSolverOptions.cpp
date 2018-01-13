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
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolverOptions.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/IfVerbose.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
namespace jfs {
namespace cxxfb {

CXXFuzzingSolverOptions::CXXFuzzingSolverOptions(
    std::unique_ptr<ClangOptions> clangOpt,
    std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOpt,
    std::unique_ptr<CXXProgramBuilderOptions> cxxProgramBuilderOpt)
    : jfs::core::SolverOptions(CXX_FUZZING_SOLVER_KIND),
      clangOpt(std::move(clangOpt)), libFuzzerOpt(std::move(libFuzzerOpt)),
      cxxProgramBuilderOpt(std::move(cxxProgramBuilderOpt)),
      redirectClangOutput(false), redirectLibFuzzerOutput(false) {}
}
}
