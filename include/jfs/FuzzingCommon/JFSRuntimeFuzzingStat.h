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
#ifndef JFS_FUZZING_COMMON_JFS_RUNTIME_FUZZING_STAT
#define JFS_FUZZING_COMMON_JFS_RUNTIME_FUZZING_STAT
#include "jfs/Core/JFSContext.h"
#include "jfs/FuzzingCommon/FuzzingSolver.h"
#include "jfs/Support/JFSStat.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {
struct JFSRuntimeFuzzingStat : public jfs::support::JFSStat {

  uint64_t maxNumConstraintsSatisfied;
  static const char* maxNumConstraintsSatisfiedKeyName;

  uint64_t numberOfInputsTried;
  static const char* numberOfInputsTriedKeyName;

  uint64_t numberOfWrongSizedInputsTried;
  static const char* numberOfWrongSizedInputsTriedKeyName;

  JFSRuntimeFuzzingStat(llvm::StringRef name);
  virtual ~JFSRuntimeFuzzingStat();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) { return s->getKind() == RUNTIME; }
  static std::unique_ptr<JFSRuntimeFuzzingStat>
  LoadFromYAML(llvm::StringRef filePath, llvm::StringRef name,
               jfs::core::JFSContext& ctx);
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
