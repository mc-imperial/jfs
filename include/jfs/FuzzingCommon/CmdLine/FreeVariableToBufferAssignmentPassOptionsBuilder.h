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
#ifndef JFS_FUZZING_COMMON_CMDLINE_FVTBAPOB_H
#define JFS_FUZZING_COMMON_CMDLINE_FVTBAPOB_H
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPassOptions.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {
namespace cl {

std::unique_ptr<jfs::fuzzingCommon::FreeVariableToBufferAssignmentPassOptions>
buildFVTBAPOptionsFromCmdLine();
}
} // namespace fuzzingCommon
} // namespace jfs

#endif
