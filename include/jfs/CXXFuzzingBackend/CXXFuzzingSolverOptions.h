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
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/SolverOptions.h"
#include "jfs/FuzzingCommon/LibFuzzerOptions.h"
#include <memory>

namespace jfs {
namespace cxxfb {

class CXXFuzzingSolverOptions : public jfs::core::SolverOptions {
private:
  // Options
  std::unique_ptr<ClangOptions> clangOpt;
  std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOpt;

public:
  CXXFuzzingSolverOptions(
      std::unique_ptr<ClangOptions> clangOpt,
      std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOpt);
  static bool classof(const SolverOptions* so) {
    return so->getKind() == CXX_FUZZING_SOLVER_KIND;
  }
  const ClangOptions* getClangOptions() const { return clangOpt.get(); }
  // FIXME: This needs rethinking. This isn't const because the options
  // need to be populated with internal implementation details before being
  // used.
  jfs::fuzzingCommon::LibFuzzerOptions* getLibFuzzerOptions() {
    return libFuzzerOpt.get();
  }

  // public for convenience.
  bool redirectClangOutput;
  bool redirectLibFuzzerOutput;
};
}
}

#endif
