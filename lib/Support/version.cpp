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
#include "jfs/Support/version.h"
#include "jfs/Config/version.h"

#define STR_TOKENIZE(X) STR_TOKENIZER(X)
#define STR_TOKENIZER(X) #X

namespace jfs {
namespace support {
const char *getVersionString() {
  return "JFS "
    STR_TOKENIZE(JFS_VERSION_MAJOR) "."
    STR_TOKENIZE(JFS_VERSION_MINOR) "."
    STR_TOKENIZE(JFS_VERSION_PATCH) "."
    STR_TOKENIZE(JFS_VERSION_TWEAK)
#ifdef JFS_GIT_HASH
      " (" STR_TOKENIZE(JFS_GIT_HASH) ")"
#endif
#ifdef JFS_GIT_DESCRIPTION
      " (" STR_TOKENIZE(JFS_GIT_DESCRIPTION) ")"
#endif
      ;
}
}
}
