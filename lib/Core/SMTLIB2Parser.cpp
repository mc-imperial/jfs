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
  std::shared_ptr<Query> query(new Query(ctx));

  // FIXME: Refactor this into a query pass
  if (!Z3_is_app(ctx.z3Ctx, constraint)) {
    // Not a top-level and
    query->constraints.push_back(constraint);
    return query;
  }
  Z3AppHandle topLevelApp =
      Z3AppHandle(::Z3_to_app(ctx.z3Ctx, constraint), ctx.z3Ctx);
  Z3FuncDeclHandle topLevelFunc =
      Z3FuncDeclHandle(::Z3_get_app_decl(ctx.z3Ctx, topLevelApp), ctx.z3Ctx);
  Z3_decl_kind kind = Z3_get_decl_kind(ctx.z3Ctx, topLevelFunc);
  if (kind != Z3_OP_AND) {
    // Not a top-level and
    query->constraints.push_back(constraint);
    return query;
  }
  unsigned numArgs = Z3_get_app_num_args(ctx.z3Ctx, topLevelApp);
  assert(numArgs >= 2 && "Unexpected number of args");
  for (unsigned index = 0; index < numArgs; ++index) {
    query->constraints.push_back(Z3ASTHandle(
        ::Z3_get_app_arg(ctx.z3Ctx, topLevelApp, index), ctx.z3Ctx));
  }
  return query;
}

JFSContextErrorHandler::ErrorAction
SMTLIB2Parser::handleZ3error(JFSContext &ctx, Z3_error_code ec) {
  ++errorCount;
  return JFSContextErrorHandler::CONTINUE;
}
}
}
