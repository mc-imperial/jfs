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
std::error_code recursive_remove(llvm::StringRef path, bool IgnoreNonExisting);
}
}
#endif
