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
#ifndef JFS_RUNTIME_STAT_LOG_LOGGER_H
#define JFS_RUNTIME_STAT_LOG_LOGGER_H
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void* jfs_nr_logger_ty;

jfs_nr_logger_ty jfs_nr_mk_logger(const char* path);
jfs_nr_logger_ty jfs_nr_mk_logger_from_env();

// NOTE: `name` is not stored so this memory must remained unmodified.
void jfs_nr_log_uint64(jfs_nr_logger_ty logger, const char* name,
                       uint64_t value);

void jfs_nr_del_logger(jfs_nr_logger_ty logger);

#ifdef __cplusplus
}
#endif

#endif
