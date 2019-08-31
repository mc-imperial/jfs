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
#ifndef JFS_CORE_SCOPED_JFS_CONTEXT_ERROR_HANDLER_H
#define JFS_CORE_SCOPED_JFS_CONTEXT_ERROR_HANDLER_H
#include "jfs/Core/JFSContext.h"
namespace jfs {
namespace core {
class ScopedJFSContextErrorHandler {
private:
  JFSContext& ctx;
  JFSContextErrorHandler* handler;

public:
  ScopedJFSContextErrorHandler(JFSContext& ctx, JFSContextErrorHandler* h)
      : ctx(ctx), handler(h) {
    ctx.registerErrorHandler(handler);
  }
  ~ScopedJFSContextErrorHandler() { ctx.unRegisterErrorHandler(handler); }
};
}
}
#endif
