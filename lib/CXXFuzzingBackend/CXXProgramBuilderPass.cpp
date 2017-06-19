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
#include "jfs/Core/Z3NodeMap.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

class CXXProgramBuilderPassImpl {
public:
  std::shared_ptr<CXXProgram> program;
  std::shared_ptr<jfs::fuzzingCommon::FuzzingAnalysisInfo> info;
  CXXCodeBlockRef earlyExitBlock;
  Z3SortMap<CXXTypeRef> sortToCXXTypeCache;

  Z3ASTMap<llvm::StringRef>
      exprToSymbolName; // References strings in `usedSymbols`.
  std::unordered_set<std::string> usedSymbols;
  llvm::StringRef entryPointFirstArgName;
  llvm::StringRef entryPointSecondArgName;

  CXXProgramBuilderPassImpl(std::shared_ptr<FuzzingAnalysisInfo> info)
      : info(info) {
    program = std::make_shared<CXXProgram>();

    // Setup early exit code block
    earlyExitBlock = std::make_shared<CXXCodeBlock>(program);
    auto returnStmt =
        std::make_shared<CXXReturnIntStatement>(earlyExitBlock, 0);
    earlyExitBlock->statements.push_front(returnStmt);
  }

  CXXTypeRef getOrInsertTy(Z3SortHandle sort) {
    auto cachedIt = sortToCXXTypeCache.find(sort);
    if (cachedIt != sortToCXXTypeCache.end()) {
      return cachedIt->second;
    }
    // Don't have the sort cached. Construct the matching CXXType.
    switch (sort.getKind()) {
    case Z3_BOOL_SORT: {
      auto ty = std::make_shared<CXXType>(program, "bool");
      sortToCXXTypeCache.insert(std::make_pair(sort, ty));
      return ty;
    }
    case Z3_BV_SORT: {
      unsigned width = sort.getBitVectorWidth();
      std::string underlyingString;
      llvm::raw_string_ostream ss(underlyingString);
      ss << "BitVector<" << width << ">";
      ss.flush();
      auto ty = std::make_shared<CXXType>(program, underlyingString);
      sortToCXXTypeCache.insert(std::make_pair(sort, ty));
      return ty;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }
  }

  CXXFunctionDeclRef buildEntryPoint() {
    program = std::make_shared<CXXProgram>();
    // Runtime header includes
    // FIXME: We should probe the query and only emit these header includes
    // if we actually need them.
    program->appendDecl(std::make_shared<CXXIncludeDecl>(
        program, "SMTLIB/Core.h", /*systemHeader=*/false));
    program->appendDecl(std::make_shared<CXXIncludeDecl>(
        program, "SMTLIB/BitVector.h", /*systemHeader=*/false));
    // Int types header for LibFuzzer entry point definition.
    program->appendDecl(std::make_shared<CXXIncludeDecl>(
        program, "stdint.h", /*systemHeader=*/true));

    // Build entry point for LibFuzzer
    auto retTy = std::make_shared<CXXType>(program, "int");
    auto firstArgTy = std::make_shared<CXXType>(program, "const uint8_t*");
    auto secondArgTy = std::make_shared<CXXType>(program, "size_t");
    entryPointFirstArgName = insertSymbol("data");
    auto firstArg = std::make_shared<CXXFunctionArgument>(
        program, entryPointFirstArgName, firstArgTy);
    entryPointSecondArgName = insertSymbol("size");
    auto secondArg = std::make_shared<CXXFunctionArgument>(
        program, entryPointSecondArgName, secondArgTy);
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

  void insertBufferSizeGuard(CXXCodeBlockRef cb) {
    std::string underlyingString;
    llvm::raw_string_ostream condition(underlyingString);
    unsigned bufferWidthInBits =
        info->freeVariableAssignment->bufferAssignment->computeWidth();
    // Round up to the number of bytes needed
    unsigned bufferWidthInBytes = (bufferWidthInBits + 7) / 8;
    condition << "size < " << bufferWidthInBytes;
    condition.flush();
    auto ifStatement = std::make_shared<CXXIfStatement>(cb, underlyingString);
    ifStatement->trueBlock = earlyExitBlock;
    cb->statements.push_back(ifStatement);
  }

  std::string getSanitizedVariableName(const std::string& name) {
    // TODO:
    // TODO: don't allow the bufferRef
    // TODO: don't allow `size`
    // TODO: don't allow `data`.
    return name;
  }

  llvm::StringRef insertSymbol(const std::string& symbolName) {
    std::string sanitizedName = getSanitizedVariableName(symbolName);
    auto statusPair = usedSymbols.insert(sanitizedName);
    assert(statusPair.second && "cannot insert already used symbolName");
    return llvm::StringRef(*(statusPair.first));
  }

  llvm::StringRef insertSSASymbolForExpr(Z3ASTHandle e,
                                         const std::string& symbolName) {
    llvm::StringRef symbolNameRef = insertSymbol(symbolName);
    assert(!(e.isNull()));
    auto statusPair = exprToSymbolName.insert(std::make_pair(e, symbolNameRef));
    assert(statusPair.second && "expr already has symbol");
    return symbolNameRef;
  }

  void insertFreeVariableConstruction(CXXCodeBlockRef cb) {
    llvm::StringRef bufferRefName = insertSymbol("jfs_buffer_ref");
    const BufferAssignment& ba =
        *(info->freeVariableAssignment->bufferAssignment.get());

    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    // Insert bufferRef.
    // FIXME: We should probably just use C++'s constructor syntax
    // BufferRef<const uint8_t> jfs_buffer_ref<const uint8_t>(data, size)
    auto bufferRefTy =
        std::make_shared<CXXType>(program, "BufferRef<const uint8_t>");
    // Build `BufferRef<uint8_t>(data, size)` string.
    ss << bufferRefTy->getName() << "(" << entryPointFirstArgName << ", "
       << entryPointSecondArgName << ")";
    ss.flush();
    auto bufferRefAssignment = std::make_shared<CXXDeclAndDefnVarStatement>(
        cb, bufferRefTy, bufferRefName, underlyingString);
    cb->statements.push_back(bufferRefAssignment);
    unsigned currentBufferBit = 0;

    // Walk through free variables and construct CXX code to initialize them
    // from the buffer.
    for (const auto& be : ba) {
      // Add assignment
      auto assignmentTy = getOrInsertTy(be.getSort());
      llvm::StringRef sanitizedSymbolName =
          insertSSASymbolForExpr(be.declApp, be.getName());
      unsigned endBufferBit = (currentBufferBit + be.getBitWidth()) - 1;

      // Build string `makeBitVectorFrom<a,b>(jfs_buffer_ref)`
      // where a is min bit and b is max bit from `jfs_buffer_ref`.
      underlyingString.clear();
      switch (be.getSort().getKind()) {
      case Z3_BOOL_SORT: {
        ss << "makeBoolFrom";
        break;
      }
      case Z3_BV_SORT: {
        ss << "makeBitVectorFrom";
        break;
      }
      default:
        llvm_unreachable("Unhandled sort");
      }
      ss << "<" << currentBufferBit << "," << endBufferBit << ">("
         << bufferRefName << ")";
      ss.flush();
      auto assignmentStmt = std::make_shared<CXXDeclAndDefnVarStatement>(
          cb, assignmentTy, sanitizedSymbolName, underlyingString);
      cb->statements.push_back(assignmentStmt);

      currentBufferBit += be.getBitWidth();
      // Add equalities
      // FIXME: When we support casts this code will need to be fixed
      for (const auto& e: be.equalities) {
        assert(e.isFreeVariable() && "should be free variable");

        llvm::StringRef otherVarName =
            insertSSASymbolForExpr(e, e.asApp().getFuncDecl().getName());
        assert(e.getSort() == be.getSort() && "sorts don't match");
        auto equalityAssignmentStmt = std::make_shared<CXXDeclAndDefnVarStatement>(
            cb, assignmentTy, otherVarName, sanitizedSymbolName);
        cb->statements.push_back(equalityAssignmentStmt);
      }
    }

    // FIXME: Due to constant propagation constant assignments should not be
    // present. We probably should just remove this entirely. For now just
    // assert that they aren't present.
    assert(
        info->freeVariableAssignment->constantAssignments->assignments.size() ==
            0 &&
        "not supported");
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

    insertBufferSizeGuard(fuzzFn->defn);
    insertFreeVariableConstruction(fuzzFn->defn);

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
