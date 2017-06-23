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
#include "CXXProgramBuilderPassImpl.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

CXXProgramBuilderPassImpl::CXXProgramBuilderPassImpl(
    std::shared_ptr<FuzzingAnalysisInfo> info)
    : info(info) {
  program = std::make_shared<CXXProgram>();

  // Setup early exit code block
  earlyExitBlock = std::make_shared<CXXCodeBlock>(program);
  auto returnStmt = std::make_shared<CXXReturnIntStatement>(earlyExitBlock, 0);
  earlyExitBlock->statements.push_front(returnStmt);
  entryPointMainBlock = nullptr;
}

CXXTypeRef CXXProgramBuilderPassImpl::getOrInsertTy(Z3SortHandle sort) {
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

CXXFunctionDeclRef CXXProgramBuilderPassImpl::buildEntryPoint() {
  program = std::make_shared<CXXProgram>();
  // Runtime header includes
  // FIXME: We should probe the query and only emit these header includes
  // if we actually need them.
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program, "SMTLIB/Core.h",
                                                       /*systemHeader=*/false));
  program->appendDecl(std::make_shared<CXXIncludeDecl>(
      program, "SMTLIB/BitVector.h", /*systemHeader=*/false));
  // Int types header for LibFuzzer entry point definition.
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program, "stdint.h",
                                                       /*systemHeader=*/true));
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program, "stdlib.h",
                                                       /*systemHeader=*/true));

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

void CXXProgramBuilderPassImpl::insertBufferSizeGuard(CXXCodeBlockRef cb) {
  unsigned bufferWidthInBits =
      info->freeVariableAssignment->bufferAssignment->computeWidth();
  if (bufferWidthInBits == 0) {
    // Don't add guard to avoid Clang warning about
    // checking `size < 0`
    return;
  }
  std::string underlyingString;
  llvm::raw_string_ostream condition(underlyingString);
  // Round up to the number of bytes needed
  unsigned bufferWidthInBytes = (bufferWidthInBits + 7) / 8;
  condition << "size < " << bufferWidthInBytes;
  condition.flush();
  auto ifStatement = std::make_shared<CXXIfStatement>(cb, underlyingString);
  ifStatement->trueBlock = earlyExitBlock;
  cb->statements.push_back(ifStatement);
}

std::string
CXXProgramBuilderPassImpl::getSanitizedVariableName(const std::string& name) {
  // TODO:
  // TODO: don't allow the bufferRef
  // TODO: don't allow `size`
  // TODO: don't allow `data`.
  return name;
}

llvm::StringRef
CXXProgramBuilderPassImpl::insertSymbol(const std::string& symbolName) {
  std::string sanitizedName = getSanitizedVariableName(symbolName);
  auto statusPair = usedSymbols.insert(sanitizedName);
  assert(statusPair.second && "cannot insert already used symbolName");
  return llvm::StringRef(*(statusPair.first));
}

llvm::StringRef CXXProgramBuilderPassImpl::insertSSASymbolForExpr(
    Z3ASTHandle e, const std::string& symbolName) {
  llvm::StringRef symbolNameRef = insertSymbol(symbolName);
  assert(!(e.isNull()));
  auto statusPair = exprToSymbolName.insert(std::make_pair(e, symbolNameRef));
  assert(statusPair.second && "expr already has symbol");
  return symbolNameRef;
}

void CXXProgramBuilderPassImpl::insertFreeVariableConstruction(
    CXXCodeBlockRef cb) {
  llvm::StringRef bufferRefName = insertSymbol("jfs_buffer_ref");
  const BufferAssignment& ba =
      *(info->freeVariableAssignment->bufferAssignment.get());
  if (ba.size() == 0) {
    // Don't emit anything if the buffer is empty to avoid
    // clang warnings about unused variables.
    return;
  }

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
    for (const auto& e : be.equalities) {
      assert(e.isFreeVariable() && "should be free variable");

      llvm::StringRef otherVarName =
          insertSSASymbolForExpr(e, e.asApp().getFuncDecl().getName());
      assert(e.getSort() == be.getSort() && "sorts don't match");
      auto equalityAssignmentStmt =
          std::make_shared<CXXDeclAndDefnVarStatement>(
              cb, assignmentTy, otherVarName, sanitizedSymbolName);
      cb->statements.push_back(equalityAssignmentStmt);
    }
  }
}

void CXXProgramBuilderPassImpl::insertConstantAssignments(CXXCodeBlockRef cb) {
  // FIXME: Due to constant propagation constant assignments should not be
  // present. We probably should just remove this entirely.
  const ConstantAssignment& ca =
      *(info->freeVariableAssignment->constantAssignments);
  for (const auto& keyPair : ca.assignments) {
    Z3ASTHandle key = keyPair.first;
    Z3ASTHandle constantExpr = keyPair.second;
    assert(key.isFreeVariable());
    assert(constantExpr.isConstant());
    llvm::StringRef symbolName = key.asApp().getFuncDecl().getName();
    std::string exprAsStr;
    Z3AppHandle constantExprAsApp = constantExpr.asApp();
    switch (constantExprAsApp.getSort().getKind()) {
    case Z3_BOOL_SORT:
      exprAsStr = getboolConstantStr(constantExprAsApp);
      break;
    case Z3_BV_SORT:
      exprAsStr = getBitVectorConstantStr(constantExprAsApp);
      break;
    default:
      llvm_unreachable("Unhandled sort");
    }
    insertSSAStmt(key, exprAsStr, symbolName);
  }
}

void CXXProgramBuilderPassImpl::insertBranchForConstraint(
    Z3ASTHandle constraint) {
  // TODO:
}

void CXXProgramBuilderPassImpl::insertFuzzingTarget(CXXCodeBlockRef cb) {
  // FIXME: Replace this with something that we can use to
  // communicate LibFuzzer's outcome
  cb->statements.push_back(
      std::make_shared<CXXCommentBlock>(cb, "Fuzzing target"));
  cb->statements.push_back(
      std::make_shared<CXXGenericStatement>(cb, "abort()"));
}

void CXXProgramBuilderPassImpl::build(const Query& q) {
  JFSContext& ctx = q.getContext();
  auto fuzzFn = buildEntryPoint();
  entryPointMainBlock = fuzzFn->defn;

  insertBufferSizeGuard(fuzzFn->defn);
  insertFreeVariableConstruction(fuzzFn->defn);
  insertConstantAssignments(fuzzFn->defn);

  // Generate constraint branches
  for (const auto& constraint : q.constraints) {
    insertBranchForConstraint(constraint);
  }
  insertFuzzingTarget(fuzzFn->defn);
}

const char* CXXProgramBuilderPassImpl::getboolConstantStr(Z3AppHandle e) const {
  switch (e.getKind()) {
  case Z3_OP_TRUE:
    return "true";
  case Z3_OP_FALSE:
    return "false";
  default:
    llvm_unreachable("Unexpected expr");
  }
}

std::string
CXXProgramBuilderPassImpl::getBitVectorConstantStr(Z3AppHandle e) const {
  assert(e.isConstant());
  Z3SortHandle sort = e.getSort();
  assert(sort.isBitVectorTy());
  unsigned bitWidth = sort.getBitVectorWidth();
  assert(bitWidth <= 64 && "Support for wide bitvectors not implemented");
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);

  ss << "BitVector<" << bitWidth << ">(UINT64_C(";
  // Get constant
  __uint64 value = 0; // Eurgh: Z3's API, can't use uint64_t
  static_assert(sizeof(__uint64) == sizeof(uint64_t), "size mismatch");
  bool success = Z3_get_numeral_uint64(e.getContext(), e.asAST(), &value);
  assert(success && "Failed to get numeral value");
  ss << value;
  ss << "))";
  ss.flush();
  return underlyingString;
}

std::string CXXProgramBuilderPassImpl::getFreshSymbol() {
  // TODO: Do something more sophisticatd
  static uint64_t counter = 0;
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  ss << "jfs_ssa_" << counter;
  ss.flush();
  ++counter;
  assert(getSanitizedVariableName(underlyingString) == underlyingString);
  assert(usedSymbols.count(underlyingString) == 0);
  return underlyingString;
}

void CXXProgramBuilderPassImpl::insertSSAStmt(
    jfs::core::Z3ASTHandle e, llvm::StringRef expr,
    llvm::StringRef preferredSymbolName) {
  auto assignmentTy = getOrInsertTy(e.getSort());
  std::string requestedSymbolName;
  if (preferredSymbolName.data() == nullptr) {
    requestedSymbolName = getFreshSymbol();
  } else {
    requestedSymbolName = preferredSymbolName;
    if (usedSymbols.count(requestedSymbolName) > 0) {
      requestedSymbolName = getFreshSymbol();
    }
  }
  llvm::StringRef usedSymbol = insertSSASymbolForExpr(e, requestedSymbolName);
  auto assignmentStmt = std::make_shared<CXXDeclAndDefnVarStatement>(
      getCurrentBlock(), assignmentTy, usedSymbol, expr);
  getCurrentBlock()->statements.push_back(assignmentStmt);
}

// Visitor methods
void CXXProgramBuilderPassImpl::visitBoolConstant(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getboolConstantStr(e));
}

void CXXProgramBuilderPassImpl::visitBitVector(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getBitVectorConstantStr(e));
}
}
}
