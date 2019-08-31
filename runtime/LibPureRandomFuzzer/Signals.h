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

#ifndef PRF_SIGNALS_H
#define PRF_SIGNALS_H

#include "Driver.h"
#include "Types.h"

namespace prf {

typedef void SignalHandler(int);

class Signals {
private:
  void SetSignalHandler(uint sig, SignalHandler* handler);
public:
  Signals(const Options& opts);
};

} // prf

#endif // PRF_SIGNALS_H