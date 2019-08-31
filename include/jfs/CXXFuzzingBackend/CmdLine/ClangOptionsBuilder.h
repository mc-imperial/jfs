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
#ifndef JFS_CXX_FUZZING_BACKEND_CMDLINE_CLANG_OPTIONS_BUILDER_H
#define JFS_CXX_FUZZING_BACKEND_CMDLINE_CLANG_OPTIONS_BUILDER_H
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/JFSContext.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace cxxfb {
namespace cl {

std::unique_ptr<jfs::cxxfb::ClangOptions>
buildClangOptionsFromCmdLine(llvm::StringRef pathToExecutable);
}
}
}

#endif
