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
#ifndef JFS_SUPPORT_CANCELLABLE_PROCESS_H
#define JFS_SUPPORT_CANCELLABLE_PROCESS_H
#include "jfs/Support/ICancellable.h"
#include "llvm/ADT/StringRef.h"
#include <memory>
#include <string>
#include <vector>

namespace jfs {

namespace support {

class CancellableProcessImpl;

// This is a thin wrapper around LLVM's
// `llvm::sys::ExecuteAndWait()` that supports
// cancellation.
class CancellableProcess : public ICancellable {
private:
  const std::unique_ptr<CancellableProcessImpl> impl;

public:
  CancellableProcess();
  ~CancellableProcess();
  void cancel() override;
  // Return values >= 0 is program exit code.
  // Negative value indicates failure.
  int execute(llvm::StringRef program, std::vector<const char*>& args,
              std::vector<llvm::StringRef>& redirects,
              const char** envp = nullptr);
};
} // namespace support
} // namespace jfs
#endif
