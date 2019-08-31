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
#ifndef JFS_CXX_FUZZING_BACKEND_CLANG_INVOCATION_MANAGER_H
#define JFS_CXX_FUZZING_BACKEND_CLANG_INVOCATION_MANAGER_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Support/ICancellable.h"
#include <memory>

namespace jfs {
namespace cxxfb {

// Forward declarations
struct ClangOptions;
class ClangInvocationManagerImpl;
class CXXProgram;

class ClangInvocationManager : public jfs::support::ICancellable {
private:
  std::unique_ptr<ClangInvocationManagerImpl> impl;

public:
  ClangInvocationManager(jfs::core::JFSContext& ctx);
  virtual ~ClangInvocationManager();
  // Compile `program`. If `sourceFile` is non-empty the source file
  // will be written to disk before being read by Clang. If `sourceFile`
  // is empty the implementation is allowed to pipe the program directly
  // to Clang.
  bool compile(const CXXProgram* program, llvm::StringRef sourceFile,
               llvm::StringRef outputFile, const ClangOptions* options,
               llvm::StringRef stdOutFile, llvm::StringRef stdErrFile);
  void cancel() override;
};
}
}
#endif
