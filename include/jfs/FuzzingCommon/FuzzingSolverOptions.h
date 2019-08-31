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
#ifndef JFS_FUZZING_COMMON_FUZZING_SOLVER_OPTIONS_H
#define JFS_FUZZING_COMMON_FUZZING_SOLVER_OPTIONS_H
#include "jfs/Core/SolverOptions.h"
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPassOptions.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {
class FuzzingSolverOptions : public jfs::core::SolverOptions {
private:
  std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> fvtbapOptions;

protected:
  // For subclasses
  FuzzingSolverOptions(
      std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> fvtbapOptions,
      bool debugSaveModel,
      jfs::core::SolverOptions::SolverOptionKind thisKind);

public:
  bool debugSaveModel;
  FuzzingSolverOptions(
      std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> fvtbapOptions,
      bool debugSaveModel);
  static bool classof(const SolverOptions* so) {
    return so->getKind() >= jfs::core::SolverOptions::FUZZING_SOLVER_KIND &&
           so->getKind() < jfs::core::SolverOptions::LAST_FUZZING_SOLVER_KIND;
  }
  FreeVariableToBufferAssignmentPassOptions*
  getFreeVariableToBufferAssignmentOptions() const;
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
