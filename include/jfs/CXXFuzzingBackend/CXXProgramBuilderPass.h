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
#ifndef JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_PASS_H
#define JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_PASS_H
#include "jfs/Core/JFSContext.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/Transform/QueryPass.h"

namespace jfs {
namespace cxxfb {

class CXXProgram;
class CXXProgramBuilderPassImpl;
class CXXProgramBuilderOptions;

class CXXProgramBuilderPass : public jfs::transform::QueryPass {
private:
  std::unique_ptr<CXXProgramBuilderPassImpl> impl;

public:
  CXXProgramBuilderPass(
      std::shared_ptr<jfs::fuzzingCommon::FuzzingAnalysisInfo> info,
      const CXXProgramBuilderOptions* options, jfs::core::JFSContext& ctx);
  ~CXXProgramBuilderPass();
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  // FIXME: Should be a const CXXProgram
  std::shared_ptr<CXXProgram> getProgram();
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}
#endif
