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
#ifndef JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#define JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/SolverOptions.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

namespace jfs {
namespace cxxfb {

struct ClangOptions {
  // Paths should be absolute
  std::string pathToBinary;
  std::string pathToRuntimeIncludeDir;
  std::string pathToLibFuzzerLib;
  std::string optimizationLevel;
  bool useASan;
  bool useUBSan;
  enum class SanitizerCoverageTy {
    TRACE_PC_GUARD,
    TRACE_CMP,
    // TODO: Add more
  };
  std::vector<SanitizerCoverageTy> sanitizerCoverageOptions;
  // If `pathToExecutable` is not empty then paths will be
  // inferred assuming that `pathToExecutable` is the absolute
  // path to the `jfs` binary.
  enum class LibFuzzerBuildType {
    REL_WITH_DEB_INFO,
  };
  ClangOptions(llvm::StringRef pathToExecutable, LibFuzzerBuildType lfbt,
               jfs::core::JFSContext& ctx);
  ClangOptions();
  void appendSanitizerCoverageOption(SanitizerCoverageTy opt);
  void dump() const;
  void print(llvm::raw_ostream& os) const;
  bool checkPaths(jfs::core::JFSContext& ctx) const;
};

class CXXFuzzingSolverOptions : public jfs::core::SolverOptions {
private:
  // Options
  std::unique_ptr<ClangOptions> clangOpt;

public:
  CXXFuzzingSolverOptions(std::unique_ptr<ClangOptions> clangOpt);
  static bool classof(const SolverOptions* so) {
    return so->getKind() == CXX_FUZZING_SOLVER_KIND;
  }
  const ClangOptions* getClangOptions() const { return clangOpt.get(); }
};
}
}

#endif
