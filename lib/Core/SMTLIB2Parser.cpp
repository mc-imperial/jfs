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
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/Z3Node.h"
#include "z3.h"
#include <assert.h>

using namespace jfs::core;

namespace {
void addConstraints(std::shared_ptr<Query> q, Z3ASTHandle constraint) {
  if (!constraint.isAppOf(Z3_OP_AND)) {
    // Not a top-level and
    q->constraints.push_back(constraint);
    return;
  }
  assert(constraint.isApp());
  Z3AppHandle app = constraint.asApp();
  unsigned numArgs = app.getNumKids();
  assert(numArgs >= 2 && "Unexpected number of args");
  for (unsigned index = 0; index < numArgs; ++index) {
    q->constraints.push_back(app.getKid(index));
  }
}
}

namespace jfs {
namespace core {
SMTLIB2Parser::SMTLIB2Parser(JFSContext &ctx) : ctx(ctx), errorCount(0) {}
SMTLIB2Parser::~SMTLIB2Parser() {}

std::shared_ptr<Query> SMTLIB2Parser::parseFile(llvm::StringRef fileName) {
  Z3ASTHandle constraint;
  ScopedJFSContextErrorHandler errorHandler(ctx, this);
  constraint =
      Z3ASTHandle(Z3_parse_smtlib2_file(ctx.z3Ctx, fileName.str().c_str(),
                                        /*num_sorts=*/0,
                                        /*sort_names=*/0,
                                        /*sorts=*/0,
                                        /*num_decls=*/0,
                                        /*decl_names=*/0,
                                        /*decls=*/0),
                  ctx.z3Ctx);
  if (errorCount > 0) {
    return nullptr;
  }

  // FIXME: We have no way of parsing solver options
  // and SMT-LIB commands.
  std::shared_ptr<Query> query(new Query(ctx));
  addConstraints(query, constraint);
  return query;
}

std::shared_ptr<Query> SMTLIB2Parser::parseStr(llvm::StringRef str) {
  Z3ASTHandle constraint;
  ScopedJFSContextErrorHandler errorHandler(ctx, this);
  constraint = Z3ASTHandle(Z3_parse_smtlib2_string(ctx.z3Ctx, str.data(),
                                                   /*num_sorts=*/0,
                                                   /*sort_names=*/0,
                                                   /*sorts=*/0,
                                                   /*num_decls=*/0,
                                                   /*decl_names=*/0,
                                                   /*decls=*/0),
                           ctx.z3Ctx);
  if (errorCount > 0) {
    return nullptr;
  }

  // FIXME: We have no way of parsing solver options
  // and SMT-LIB commands.
  std::shared_ptr<Query> query(new Query(ctx));
  addConstraints(query, constraint);
  return query;
}

JFSContextErrorHandler::ErrorAction
SMTLIB2Parser::handleZ3error(JFSContext &ctx, Z3_error_code ec) {
  ++errorCount;
  return JFSContextErrorHandler::CONTINUE;
}

unsigned SMTLIB2Parser::getErrorCount() const { return errorCount; }

void SMTLIB2Parser::resetErrorCount() { errorCount = 0; }
}
}
