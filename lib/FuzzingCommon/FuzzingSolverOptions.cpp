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
#include "jfs/FuzzingCommon/FuzzingSolverOptions.h"

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

FuzzingSolverOptions::FuzzingSolverOptions(
    std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> fvtbapOptions,
    SolverOptions::SolverOptionKind thisKind)
    : SolverOptions(thisKind), fvtbapOptions(std::move(fvtbapOptions)) {}
FuzzingSolverOptions::FuzzingSolverOptions(
    std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> fvtbapOptions)
    : FuzzingSolverOptions(std::move(fvtbapOptions),
                           SolverOptions::FUZZING_SOLVER_KIND) {}

FreeVariableToBufferAssignmentPassOptions*
FuzzingSolverOptions::getFreeVariableToBufferAssignmentOptions() const {
  return fvtbapOptions.get();
}

} // namespace fuzzingCommon
} // namespace jfs
