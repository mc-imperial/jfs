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
#include "jfs/CXXFuzzingBackend/CmdLine/CXXProgramBuilderOptionsBuilder.h"
#include "jfs/CXXFuzzingBackend/CmdLine/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"
#include <string>

using namespace jfs::cxxfb;
using namespace jfs::core;

namespace {

llvm::cl::opt<bool> RecordMaxNumSatisfiedConstraints(
    "record-max-num-satisfied-constraints",
    llvm::cl::desc(
        "Record the maximum number of satisfied constraints (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));
}

namespace jfs {
namespace cxxfb {
namespace cl {

std::unique_ptr<CXXProgramBuilderOptions>
buildCXXProgramBuilderOptionsFromCmdLine() {
  std::unique_ptr<CXXProgramBuilderOptions> opts(
      new CXXProgramBuilderOptions());

  opts->setRecordMaxNumSatisfiedConstraints(RecordMaxNumSatisfiedConstraints);

  return opts;
}
} // namespace cl
} // namespace cxxfb
} // namespace jfs
