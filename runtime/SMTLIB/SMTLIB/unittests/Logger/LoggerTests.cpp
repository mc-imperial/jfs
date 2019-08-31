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
#include "SMTLIB/Logger.h"
#include "gtest/gtest.h"
#include <cstdio>
#include <fstream>
#include <iostream>
#include <string.h>
#include <unistd.h>

#define STRINGIFY_(X) #X
#define STRINGIFY(X) STRINGIFY_(X)

// TODO: Write more tests

TEST(Logger, createLog) {
  const char* logFilePath = STRINGIFY(PATH_TO_LOG_FILE);
  // Remove old log file
  int removeLogFileResult = unlink(logFilePath);
  if (removeLogFileResult == -1) {
    printf("Removal %s failed\n", logFilePath);
  }

  // Do logging
  setenv("JFS_RUNTIME_LOG_PATH", logFilePath, /*overwrite=*/1);
  auto logger = jfs_nr_mk_logger_from_env();
  jfs_nr_log_uint64(logger, "foo", 1);
  jfs_nr_del_logger(logger);

  // Now read file back
  std::ifstream lfs(logFilePath);
  ASSERT_TRUE(lfs.good());
  char data[100];
  const uint64_t dataLength = sizeof(data) / sizeof(char);
  memset(data, 0, dataLength);
  lfs.getline(data, dataLength);
  ASSERT_STREQ(data, "foo: 1");
}
