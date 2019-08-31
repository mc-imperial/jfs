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
#ifndef JFS_SUPPORT_ERROR_MESSAGES_H
#define JFS_SUPPORT_ERROR_MESSAGES_H
#include "llvm/ADT/StringRef.h"
#include <string>
#include <system_error>

namespace jfs {

namespace support {
std::string getMessageForFailedOpenFileOrSTDIN(llvm::StringRef inputFileName,
                                               std::error_code ec);

std::string
getMessageForFailedOpenFileForWriting(llvm::StringRef outputFileName,
                                      std::error_code ec);
}
}
#endif
