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
#ifndef JFS_RUNTIME_SMTLIB_JFS_ASSERTS_H
#define JFS_RUNTIME_SMTLIB_JFS_ASSERTS_H
#include <stdio.h>
#include <stdlib.h>

// This is a hack. We use `abort()` as the fuzzing target so we can't have
// anything else in generated programs call it. C's `assert()` macro calls it
// so we use our own macro that will cause LibFuzzer to terminate abnormally in
// a way we can distinguish from the fuzzing target being found.
#ifdef JFS_RUNTIME_FAILURE_CALLS_ABORT
#define JFS_RUNTIME_FAIL() abort();
#else
#define JFS_RUNTIME_FAIL() exit(99);
#endif

#define JFS_RUNTIME_FAIL_WITH_REASON(R)                                        \
  do {                                                                         \
    fprintf(stderr, "Error: %s\n", R);                                         \
    JFS_RUNTIME_FAIL();                                                        \
  } while (0);

#ifdef ENABLE_JFS_RUNTIME_ASSERTS
#define jassert(X)                                                             \
  do {                                                                         \
    if (!(X)) {                                                                \
      fprintf(stderr, "JFS runtime assertion failure `%s` at %s:%d\n", #X,     \
              __FILE__, __LINE__);                                             \
      JFS_RUNTIME_FAIL();                                                      \
    }                                                                          \
  } while (0)
#else
// No-op
#define jassert(X)
#endif

#endif
