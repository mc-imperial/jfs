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
#ifndef JFS_FUZZING_COMMON_FUZZING_ANALYSIS_INFO_H
#define JFS_FUZZING_COMMON_FUZZING_ANALYSIS_INFO_H
#include "jfs/Transform/QueryPassManager.h"

namespace jfs {
namespace fuzzingCommon {

// This contains the necessary analysis info
// that a fuzzing solver needs.
class FuzzingAnalysisInfo {
public:
  // TODO figure out what analysis passes belong here.
  void addTo(jfs::transform::QueryPassManager &pm) {
    // TODO
  }
};
}
}

#endif
