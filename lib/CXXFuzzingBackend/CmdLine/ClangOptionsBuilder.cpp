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
#include "jfs/CXXFuzzingBackend/CmdLine/ClangOptionsBuilder.h"
#include "jfs/CXXFuzzingBackend/CmdLine/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"
#include <string>

using namespace jfs::cxxfb;
using namespace jfs::core;

namespace {
llvm::cl::opt<ClangOptions::LibFuzzerBuildType> LibFuzzerBuildTypeToLinkAgainst(
    "libfuzzer-build-type",
    llvm::cl::desc("The build type of LibFuzzer to link against"),
    llvm::cl::values(
        clEnumValN(ClangOptions::LibFuzzerBuildType::REL_WITH_DEB_INFO,
                   "RELWITHDEBINFO", "Release with debug symbols (default)")),
    llvm::cl::init(ClangOptions::LibFuzzerBuildType::REL_WITH_DEB_INFO),
    llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<ClangOptions::OptimizationLevel> OptimizationLevel(
    llvm::cl::desc("Optimization level"),
    llvm::cl::values(clEnumValN(ClangOptions::OptimizationLevel::O0, "O0",
                                "No optimization (default)"),
                     clEnumValN(ClangOptions::OptimizationLevel::O1, "O1", ""),
                     clEnumValN(ClangOptions::OptimizationLevel::O2, "O2", ""),
                     clEnumValN(ClangOptions::OptimizationLevel::O3, "O3", "")),
    llvm::cl::init(ClangOptions::OptimizationLevel::O0),
    llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> DebugSymbols(
    "g", llvm::cl::desc("Build with debug symbols (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> UseAsan(
    "asan", llvm::cl::desc("Build with AddressSanitizer (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> UseUBSan(
    "ubsan",
    llvm::cl::desc("Build with Undefined Behavior Sanitizer (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::list<ClangOptions::SanitizerCoverageTy> SanitizerCoverageOptions(
    "sanitizer-coverage",
    llvm::cl::desc("Sanitizer Coverage flags. Comma separated"),
    llvm::cl::CommaSeparated,
    llvm::cl::values(
        clEnumValN(ClangOptions::SanitizerCoverageTy::TRACE_PC_GUARD,
                   "trace-pc-guard", "Trace PC Guard (default)"),
        clEnumValN(ClangOptions::SanitizerCoverageTy::TRACE_CMP, "trace-cmp",
                   "Trace Comparisions. Must be used in conjuction with "
                   "another coverage type.")),
    llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> UseJFSRuntimeAsserts(
    "runtime-asserts",
    llvm::cl::desc("Build JFS runtime asserts enabled (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));

llvm::cl::opt<bool> PureRandomFuzzer(
    "libfuzzer-pure-random",
    llvm::cl::desc("Replace LibFuzzer with LibPureRandomFuzzer for use as a "
                   "control group (default: false)"),
    llvm::cl::init(false), llvm::cl::cat(jfs::cxxfb::cl::CommandLineCategory));
}

namespace jfs {
namespace cxxfb {
namespace cl {

std::unique_ptr<ClangOptions>
buildClangOptionsFromCmdLine(llvm::StringRef pathToExecutable) {
  // Tell ClangOptions to try and infer all paths
  std::unique_ptr<ClangOptions> clangOptions(
      new ClangOptions(pathToExecutable, LibFuzzerBuildTypeToLinkAgainst,
                       PureRandomFuzzer));

  // Sanitizer coverage options
  if (SanitizerCoverageOptions.size() == 0) {
    // Default (depends on fuzzer library)
    if (!PureRandomFuzzer) {
      clangOptions->appendSanitizerCoverageOption(
          ClangOptions::SanitizerCoverageTy::TRACE_PC_GUARD);
    }
  } else {
    for (const auto& flag : SanitizerCoverageOptions) {
      clangOptions->appendSanitizerCoverageOption(flag);
    }
  }

  // Debug symbols
  clangOptions->debugSymbols = DebugSymbols;
  // Optimization level
  clangOptions->optimizationLevel = OptimizationLevel;
  // ASan
  clangOptions->useASan = UseAsan;
  // UBSan
  clangOptions->useUBSan = UseUBSan;
  // JFS runtime asserts
  clangOptions->useJFSRuntimeAsserts = UseJFSRuntimeAsserts;

  return clangOptions;
}
}
}
}
