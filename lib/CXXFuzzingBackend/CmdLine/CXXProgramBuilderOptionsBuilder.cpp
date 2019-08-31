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

llvm::cl::opt<bool> RecordNumberOfInputs(
    "record-num-inputs",
    llvm::cl::desc("Record the number of inputs tried (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> RecordNumberOfWrongSizedInputs(
    "record-num-wrong-sized-inputs",
    llvm::cl::desc(
        "Record the number of wrong sized inputs tried (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<CXXProgramBuilderOptions::BranchEncodingTy> BranchEncoding(
    "branch-encoding", llvm::cl::desc("Encoding used for constraint branches"),
    llvm::cl::values(
        clEnumValN(CXXProgramBuilderOptions::BranchEncodingTy::FAIL_FAST,
                   "fail-fast",
                   "Stop trying input at first unsat branch (default)"),
        clEnumValN(CXXProgramBuilderOptions::BranchEncodingTy::TRY_ALL,
                   "try-all", "Serebrayany encoding. Evaluate all branches")
#ifdef __linux__
            ,
        clEnumValN(CXXProgramBuilderOptions::BranchEncodingTy::TRY_ALL_IMNCSF,
                   "try-all-imncsf",
                   "Cadar encoding. Like `try-all` except increases in the "
                   "maximum number of "
                   "constraints solved are treated as increase in coverage "
                   "(linux only)")
#endif
            ),
    llvm::cl::init(CXXProgramBuilderOptions::BranchEncodingTy::FAIL_FAST),
    llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> TraceIncreaseMaxNumSatisfiedConstraints(
    "trace-max-num-satisfied-constraints",
    llvm::cl::desc("Report when the maximum number of satisfied constraints "
                   "increases (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> TraceWrongSizedInputs(
    "trace-wrong-sized-inputs",
    llvm::cl::desc("Report when the fuzzer tries an input of the wrong size "
                   "increases (default: true)"),
    llvm::cl::init(true), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));
}

namespace jfs {
namespace cxxfb {
namespace cl {

std::unique_ptr<CXXProgramBuilderOptions>
buildCXXProgramBuilderOptionsFromCmdLine() {
  std::unique_ptr<CXXProgramBuilderOptions> opts(
      new CXXProgramBuilderOptions());

  opts->setRecordMaxNumSatisfiedConstraints(RecordMaxNumSatisfiedConstraints);
  opts->setRecordNumberOfInputs(RecordNumberOfInputs);
  opts->setRecordNumberOfWrongSizedInputs(RecordNumberOfWrongSizedInputs);
  opts->setBranchEncoding(BranchEncoding);
  opts->setTraceIncreaseMaxNumSatisfiedConstraints(
      TraceIncreaseMaxNumSatisfiedConstraints);
  opts->setTraceWrongSizedInputs(TraceWrongSizedInputs);

  return opts;
}
} // namespace cl
} // namespace cxxfb
} // namespace jfs
