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
#ifndef JFS_CORE_TOOL_ERROR_HANDLER_H
#define JFS_CORE_TOOL_ERROR_HANDLER_H
#include "jfs/Core/JFSContext.h"

namespace jfs {
namespace core {

class ToolErrorHandler : public JFSContextErrorHandler {
private:
  bool ignoreCanceled;

public:
  ToolErrorHandler(bool ignoreCanceled) : ignoreCanceled(ignoreCanceled) {}

  JFSContextErrorHandler::ErrorAction handleZ3error(JFSContext& ctx,
                                                    Z3_error_code ec) override;
  ErrorAction handleFatalError(JFSContext& ctx, llvm::StringRef msg) override;
  ErrorAction handleGenericError(JFSContext& ctx, llvm::StringRef msg) override;
};
}
}
#endif
