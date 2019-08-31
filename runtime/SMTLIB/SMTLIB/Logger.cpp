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
#include "Logger.h"
#include "jassert.h"
#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include <string>
#include <unordered_map>

namespace {

class LoggerImpl {
private:
  std::string logPath;
  std::unordered_map<const char*, uint64_t> stats;

public:
  LoggerImpl(const char* path) : logPath(path) {}
  ~LoggerImpl() {
    // Log stats to file.
    // TODO: Rewrite using std classes
    FILE* f = fopen(logPath.c_str(), /*mode=*/"w");
    if (f == NULL) {
      JFS_RUNTIME_FAIL_WITH_REASON("Failed to open log file");
    }
    for (const auto& pair : stats) {
      fprintf(f, "%s: %" PRIu64 "\n", pair.first, pair.second);
    }
    fclose(f);
  }
  void log_uint64(const char* name, uint64_t value) {
    jassert(name != nullptr);
    stats[name] = value;
  }
};

} // namespace

extern "C" {
jfs_nr_logger_ty jfs_nr_mk_logger(const char* path) {
  LoggerImpl* l = new LoggerImpl(path);
  return reinterpret_cast<jfs_nr_logger_ty>(l);
}

jfs_nr_logger_ty jfs_nr_mk_logger_from_env() {
  const char* path = getenv("JFS_RUNTIME_LOG_PATH");
  if (path == nullptr) {
    JFS_RUNTIME_FAIL_WITH_REASON(
        "Failed to get log file path from JFS_RUNTIME_LOG_PATH "
        "environment variable\n");
  }
  return jfs_nr_mk_logger(path);
}

void jfs_nr_log_uint64(jfs_nr_logger_ty logger, const char* name,
                       uint64_t value) {
  LoggerImpl* l = (LoggerImpl*)logger;
  l->log_uint64(name, value);
}

void jfs_nr_del_logger(jfs_nr_logger_ty logger) {
  LoggerImpl* l = (LoggerImpl*)logger;
  delete l;
}
}
