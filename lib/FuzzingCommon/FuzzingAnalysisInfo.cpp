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
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPassOptions.h"
#include "llvm/Support/CommandLine.h"

namespace {

llvm::cl::opt<bool> DisableEqualityExtraction(
    "disable-equality-extraction", llvm::cl::init(false),
    llvm::cl::desc("Do not run equality extraction (default false)"));
}

namespace jfs {
namespace fuzzingCommon {

FuzzingAnalysisInfo::FuzzingAnalysisInfo(
    FreeVariableToBufferAssignmentPassOptions* fvtbapOptions)
    : equalityExtraction(std::make_shared<EqualityExtractionPass>()) {
  freeVariableAssignment = std::make_shared<FreeVariableToBufferAssignmentPass>(
      *equalityExtraction, fvtbapOptions);
}

FuzzingAnalysisInfo::~FuzzingAnalysisInfo() {}

void FuzzingAnalysisInfo::addTo(jfs::transform::QueryPassManager &pm) {
  // TODO: Enforce that this can only be called once

  // Look for equalities, extract them and remove them from the constraints
  if (!DisableEqualityExtraction) {
    pm.add(equalityExtraction);
  }
  pm.add(freeVariableAssignment);
}
}
}
