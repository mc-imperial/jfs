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
#ifndef JFS_CXX_FUZZING_BACKEND_CLANG_OPTIONS_H
#define JFS_CXX_FUZZING_BACKEND_CLANG_OPTIONS_H
#include "jfs/Core/JFSContext.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <vector>

namespace jfs {
namespace cxxfb {

struct ClangOptions {
  // Paths should be absolute
  std::string pathToBinary;
  std::string pathToRuntimeDir;
  std::string pathToRuntimeIncludeDir;
  std::string pathToLibFuzzerLib;
  std::string pathToStatLogLib;
  enum class OptimizationLevel { O0, O1, O2, O3 };
  OptimizationLevel optimizationLevel;
  bool debugSymbols;
  bool useASan;
  bool useUBSan;
  bool useJFSRuntimeAsserts;
  enum class SanitizerCoverageTy {
    TRACE_PC_GUARD,
    TRACE_CMP,
    // TODO: Add more
  };
  std::vector<SanitizerCoverageTy> sanitizerCoverageOptions;
  // FIXME: We should populate this enum from the CMake
  // runtime declarations.
  enum class LibFuzzerBuildType {
    REL_WITH_DEB_INFO,
  };
  enum class StatLogBuildType {
    REL_WITH_DEB_INFO,
  };
  // If `pathToExecutable` is not empty then paths will be
  // inferred assuming that `pathToExecutable` is the absolute
  // path to the `jfs` binary.
  ClangOptions(llvm::StringRef pathToExecutable, LibFuzzerBuildType lfbt,
               StatLogBuildType slbt);
  ClangOptions();
  void appendSanitizerCoverageOption(SanitizerCoverageTy opt);
  void dump() const;
  void print(llvm::raw_ostream& os) const;
  bool checkPaths(jfs::core::JFSContext& ctx) const;
};
}
}
#endif
