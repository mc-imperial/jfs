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
#include "Messages.h"
#include <stdarg.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

// Right now these are just a thin wrappers around fprintf.  In the future
// though we could log the messages to a file.

void jfs_info(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "JFS INFO: ");
  vfprintf(stderr, fmt, args);
  va_end(args);
}

void jfs_warning(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "JFS WARNING: ");
  vfprintf(stderr, fmt, args);
  va_end(args);
}

#ifdef __cplusplus
}
#endif
