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
#ifndef JFS_FUZZING_COMMON_LIBFUZZER_INVOCATION_MANAGER_H
#define JFS_FUZZING_COMMON_LIBFUZZER_INVOCATION_MANAGER_H
#include "jfs/Core/JFSContext.h"
#include "jfs/FuzzingCommon/LibFuzzerOptions.h"
#include "jfs/Support/ICancellable.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {

struct LibFuzzerResponse {
  enum class ResponseTy {
    TARGET_FOUND,
    SINGLE_RUN_TARGET_NOT_FOUND,
    RUN_BOUND_REACHED,
    CANCELLED,
    UNKNOWN,
  };
  ResponseTy outcome;
  LibFuzzerResponse();
  ~LibFuzzerResponse();
  // TODO: Add stuff here to gain access to the
  // input that hit the target if relevant.
};

class LibFuzzerInvocationManagerImpl;

class LibFuzzerInvocationManager : public jfs::support::ICancellable {
private:
  const std::unique_ptr<LibFuzzerInvocationManagerImpl> impl;

public:
  LibFuzzerInvocationManager(jfs::core::JFSContext& ctx);
  ~LibFuzzerInvocationManager();
  void cancel();
  std::unique_ptr<LibFuzzerResponse> fuzz(const LibFuzzerOptions* options,
                                          llvm::StringRef stdOutFile,
                                          llvm::StringRef stdErrFile);
};
}
}

#endif
