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
#ifndef JFS_RUNTIME_MESSAGES_H
#define JFS_RUNTIME_MESSAGES_H

#ifdef __cplusplus
extern "C" {
#endif

#define JFS_PRINTF_ATRRIBUTE __attribute__((format(printf, 1, 2)))

void jfs_info(const char* fmt, ...) JFS_PRINTF_ATRRIBUTE;
void jfs_warning(const char* fmt, ...) JFS_PRINTF_ATRRIBUTE;

#undef JFS_PRINTF_ATRRIBUTE

#ifdef __cplusplus
}
#endif

#endif
