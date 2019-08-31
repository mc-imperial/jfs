//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#ifndef PRF_DRIVER_H
#define PRF_DRIVER_H

#include "Types.h"
#include <cstddef>
#include <string>

namespace prf {

struct Options {
#define PRF_OPTION_SIZE_T(_, name, value)                                      \
  size_t name = value;
#define PRF_OPTION_UINT(_, name, value)                                        \
  uint name = value;
#define PRF_OPTION_INT(_, name, value)                                         \
  int name = value;
#define PRF_OPTION_BOOL(_, name, value)                                        \
  bool name = value;
#define PRF_OPTION_STRING(_, name, value)                                      \
  std::string name = value;
#include "Options.def"
#undef PRF_OPTION_SIZE_T
#undef PRF_OPTION_UINT
#undef PRF_OPTION_INT
#undef PRF_OPTION_BOOL
#undef PRF_OPTION_STRING
};

int Driver(int& argc, char**& argv);

void PrintFinalStats();

Options BuildOptions(int& argc, char**& argv);

void WriteArtifact(const char* artifactType);

void AbortHandler(int sig);
void TimeoutHandler(int sig);

} // prf

#endif // PRF_DRIVER_H
