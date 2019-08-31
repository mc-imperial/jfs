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
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/Core/IfVerbose.h"

namespace jfs {
namespace core {

JFSContextErrorHandler::ErrorAction
ToolErrorHandler::handleZ3error(JFSContext& ctx, Z3_error_code ec) {
  auto msg = Z3_get_error_msg(ctx.getZ3Ctx(), ec);
  if (strcmp(msg, "canceled") == 0 && ignoreCanceled) {
    // Ignore
    IF_VERB(ctx, ctx.getDebugStream() << "(ignore \"Z3 canceled event\")\n");
    return JFSContextErrorHandler::STOP;
  }

  ctx.getErrorStream() << "(error \"" << msg << "\")\n";
  exit(1);
  return JFSContextErrorHandler::STOP; // Unreachable.
}

JFSContextErrorHandler::ErrorAction
ToolErrorHandler::handleFatalError(JFSContext& ctx, llvm::StringRef msg) {
  ctx.getErrorStream() << "(error \"" << msg << "\")\n";
  exit(1);
  return JFSContextErrorHandler::STOP; // Unreachable.
}

JFSContextErrorHandler::ErrorAction
ToolErrorHandler::handleGenericError(JFSContext& ctx, llvm::StringRef msg) {
  // Just treat as a fatal error
  return handleFatalError(ctx, msg);
}
}
}
