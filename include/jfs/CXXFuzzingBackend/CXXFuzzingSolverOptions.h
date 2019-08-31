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
#ifndef JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#define JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderOptions.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/SolverOptions.h"
#include "jfs/FuzzingCommon/FuzzingSolverOptions.h"
#include "jfs/FuzzingCommon/LibFuzzerOptions.h"
#include "jfs/FuzzingCommon/SeedManagerOptions.h"
#include <memory>

namespace jfs {
namespace cxxfb {

class CXXFuzzingSolver;
class CXXFuzzingSolverImpl;

class CXXFuzzingSolverOptions
    : public jfs::fuzzingCommon::FuzzingSolverOptions {
private:
  // Options
  std::unique_ptr<ClangOptions> clangOpt;
  std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOpt;
  std::unique_ptr<CXXProgramBuilderOptions> cxxProgramBuilderOpt;
  std::unique_ptr<jfs::fuzzingCommon::SeedManagerOptions> seedManagerOpt;

public:
  CXXFuzzingSolverOptions(
      std::unique_ptr<
          jfs::fuzzingCommon::FreeVariableToBufferAssignmentPassOptions>
          fvtbapOptions,
      std::unique_ptr<ClangOptions> clangOpt,
      std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOpt,
      std::unique_ptr<CXXProgramBuilderOptions> cxxProgramBuilderOpt,
      std::unique_ptr<jfs::fuzzingCommon::SeedManagerOptions> seedManagerOpt,
      bool debugSaveModel);
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
  const CXXProgramBuilderOptions* getCXXProgramBuilderOptions() const {
    return cxxProgramBuilderOpt.get();
  }
  friend class CXXFuzzingSolver;
  friend class CXXFuzzingSolverImpl;

  // public for convenience.
  bool redirectClangOutput;
  bool redirectLibFuzzerOutput;
};
}
}

#endif
