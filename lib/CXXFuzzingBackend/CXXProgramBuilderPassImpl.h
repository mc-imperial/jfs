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
#ifndef JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_PASS_IMPL_H
#define JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_PASS_IMPL_H
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
namespace jfs {
namespace cxxfb {

class CXXProgramBuilderPassImpl {
private:
  std::shared_ptr<CXXProgram> program;
  std::shared_ptr<jfs::fuzzingCommon::FuzzingAnalysisInfo> info;
  CXXCodeBlockRef earlyExitBlock;
  jfs::core::Z3SortMap<CXXTypeRef> sortToCXXTypeCache;

  jfs::core::Z3ASTMap<llvm::StringRef>
      exprToSymbolName; // References strings in `usedSymbols`.
  std::unordered_set<std::string> usedSymbols;
  llvm::StringRef entryPointFirstArgName;
  llvm::StringRef entryPointSecondArgName;

  CXXProgramBuilderPassImpl(
      std::shared_ptr<jfs::fuzzingCommon::FuzzingAnalysisInfo> info);

  void build(const jfs::core::Query& q);

  // Helpers for inserting SSA variables and types
  CXXTypeRef getOrInsertTy(jfs::core::Z3SortHandle sort);
  std::string getSanitizedVariableName(const std::string& name);
  llvm::StringRef insertSymbol(const std::string& symbolName);
  llvm::StringRef insertSSASymbolForExpr(jfs::core::Z3ASTHandle e,
                                         const std::string& symbolName);

  // Function for building various parts of the CXXProgram
  CXXFunctionDeclRef buildEntryPoint();
  void insertBufferSizeGuard(CXXCodeBlockRef cb);
  void insertFreeVariableConstruction(CXXCodeBlockRef cb);
  void insertConstantAssignments(CXXCodeBlockRef cb);
  void insertBranchForConstraint(jfs::core::Z3ASTHandle constraint);
  void insertFuzzingTarget(CXXCodeBlockRef cb);
  // Only let CXXProgramBuilderPass use the implementation.
  friend class CXXProgramBuilderPass;
};
}
}
#endif
