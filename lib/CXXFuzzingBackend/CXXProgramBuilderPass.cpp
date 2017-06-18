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
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/Core/Z3Node.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

class CXXProgramBuilderPassImpl {
public:
  std::shared_ptr<CXXProgram> program;
  std::shared_ptr<jfs::fuzzingCommon::FuzzingAnalysisInfo> info;
  CXXCodeBlockRef earlyExitBlock;
  CXXProgramBuilderPassImpl(std::shared_ptr<FuzzingAnalysisInfo> info)
      : info(info) {
    program = std::make_shared<CXXProgram>();

    // Setup early exit code block
    earlyExitBlock = std::make_shared<CXXCodeBlock>(program);
    auto returnStmt =
        std::make_shared<CXXReturnIntStatement>(earlyExitBlock, 0);
    earlyExitBlock->statements.push_front(returnStmt);
  }

  CXXFunctionDeclRef buildEntryPoint() {
    program = std::make_shared<CXXProgram>();
    // Runtime header include
    program->appendDecl(
        std::make_shared<CXXIncludeDecl>(program, "SMTLIB/BitVector.h", false));
    // Int types header
    program->appendDecl(
        std::make_shared<CXXIncludeDecl>(program, "stdint.h", true));

    // Build entry point for LibFuzzer
    auto retTy = std::make_shared<CXXType>(program, "int");
    auto firstArgTy = std::make_shared<CXXType>(program, "const uint8_t*");
    auto secondArgTy = std::make_shared<CXXType>(program, "size_t");
    auto firstArg =
        std::make_shared<CXXFunctionArgument>(program, "data", firstArgTy);
    auto secondArg =
        std::make_shared<CXXFunctionArgument>(program, "size", secondArgTy);
    auto funcArguments = std::vector<CXXFunctionArgumentRef>();
    funcArguments.push_back(firstArg);
    funcArguments.push_back(secondArg);
    auto funcDefn = std::make_shared<CXXFunctionDecl>(
        program, "LLVMFuzzerTestOneInput", retTy, funcArguments,
        /*hasCVisibility=*/true);
    auto funcBody = std::make_shared<CXXCodeBlock>(funcDefn);
    funcDefn->defn = funcBody; // FIXME: shouldn't be done like this
    program->appendDecl(funcDefn);
    return funcDefn;
  }

  void insertBufferSizeGuard(CXXFunctionDeclRef fuzzFn) {
    std::string underlyingString;
    llvm::raw_string_ostream condition(underlyingString);
    unsigned bufferWidth =
        info->freeVariableAssignment->bufferAssignment->computeWidth();
    condition << "size < " << bufferWidth;
    condition.flush();
    auto ifStatement =
        std::make_shared<CXXIfStatement>(fuzzFn->defn, underlyingString);
    ifStatement->trueBlock = earlyExitBlock;
    fuzzFn->defn->statements.push_back(ifStatement);
  }

  void insertFreeVariableConstruction() {
    // TODO:
  }

  void insertBranchForConstraint(Z3ASTHandle constraint) {
    // TODO:
  }

  void insertFuzzingTarget() {
    // TODO:
  }

  void build(const Query& q) {
    JFSContext& ctx = q.getContext();
    auto fuzzFn = buildEntryPoint();

    insertBufferSizeGuard(fuzzFn);
    insertFreeVariableConstruction();

    // Generate constraint branches
    for (const auto& constraint : q.constraints) {
      insertBranchForConstraint(constraint);
    }
    insertFuzzingTarget();
  }
};

CXXProgramBuilderPass::CXXProgramBuilderPass(
    std::shared_ptr<FuzzingAnalysisInfo> info)
    : impl(new CXXProgramBuilderPassImpl(info)) {}

std::shared_ptr<CXXProgram> CXXProgramBuilderPass::getProgram() {
  return impl->program;
}

CXXProgramBuilderPass::~CXXProgramBuilderPass() {}

llvm::StringRef CXXProgramBuilderPass::getName() { return "CXXProgramBuilder"; }

bool CXXProgramBuilderPass::run(Query& q) {
  JFSContext& ctx = q.getContext();
  impl->build(q);

  // Print final result
  if (ctx.getVerbosity() >= 2) {
    ctx.getDebugStream() << "(" << getName() << "\n\n";
    impl->program->print(ctx.getDebugStream());
    ctx.getDebugStream() << "\n)\n";
  }
  return false;
}
}
}
