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
#ifndef JFS_CORE_IF_VERBOSE_H
#define JFS_CORE_IF_VERBOSE_H

#define IF_VERB_GT(CTX, VALUE, ACTION)                                         \
  do {                                                                         \
    if (CTX.getVerbosity() > VALUE) {                                          \
      ACTION;                                                                  \
    }                                                                          \
  } while (0)

#define IF_VERB(CTX, ACTION) IF_VERB_GT(CTX, 0, ACTION)

#endif
