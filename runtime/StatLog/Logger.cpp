//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "Logger.h"
#include <string>
// FIXME: Yuck, relative include
#include "../SMTLIB/SMTLIB/jassert.h"

namespace {

// TODO: Add implementation
class LoggerImpl {
private:
public:
  LoggerImpl(const char* path) {
    jassert("Not implemented" && false);
  }
  ~LoggerImpl() {
    jassert("Not implemented" && false);
  }
  void log_uint64(const char* name, uint64_t value) {
    jassert("Not implemented" && false);
  }
};

std::string getLogPath() { return ""; }
} // namespace

extern "C" {
jfs_nr_logger_ty jfs_nr_mk_logger() {
  std::string path = getLogPath();
  LoggerImpl* l = new LoggerImpl(path.c_str());
  return reinterpret_cast<jfs_nr_logger_ty>(l);
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
