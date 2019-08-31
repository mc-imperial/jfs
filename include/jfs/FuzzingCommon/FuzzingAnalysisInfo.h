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
#ifndef JFS_FUZZING_COMMON_FUZZING_ANALYSIS_INFO_H
#define JFS_FUZZING_COMMON_FUZZING_ANALYSIS_INFO_H
#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPass.h"
#include "jfs/Transform/QueryPassManager.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {

// This contains the necessary analysis info
// that a fuzzing solver needs.
class FuzzingAnalysisInfo {
public:
  std::shared_ptr<EqualityExtractionPass> equalityExtraction;
  std::shared_ptr<FreeVariableToBufferAssignmentPass> freeVariableAssignment;
  void addTo(jfs::transform::QueryPassManager& pm);
  FuzzingAnalysisInfo(FreeVariableToBufferAssignmentPassOptions* fvtbapOptions);
  ~FuzzingAnalysisInfo();
};
} // namespace fuzzingCommon
} // namespace jfs

#endif
