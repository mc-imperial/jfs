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
#ifndef JFS_CXX_FUZZING_BACKEND_CMDLINE_CXX_PROGRAM_BUILDER_OPTIONS_BUILDER
#define JFS_CXX_FUZZING_BACKEND_CMDLINE_CXX_PROGRAM_BUILDER_OPTIONS_BUILDER
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderOptions.h"
#include "jfs/Core/JFSContext.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace cxxfb {
namespace cl {

std::unique_ptr<jfs::cxxfb::CXXProgramBuilderOptions>
buildCXXProgramBuilderOptionsFromCmdLine();
}
} // namespace cxxfb
} // namespace jfs

#endif
