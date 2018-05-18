//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "Signals.h"

#include "Log.h"
#include <sys/time.h>
#include <signal.h>

namespace prf {

Signals::Signals(const Options& opts) {
  if (opts.timeout > 0) {
    SetSignalHandler(SIGALRM, &TimeoutHandler);
    // LibFuzzer transforms the timeout option in this way for some reason, so
    // we'll apply the same to match.
    int timeout = opts.timeout / 2 + 1;
    itimerval timer = {{}, {timeout, 0}};
    if (setitimer(ITIMER_REAL, &timer, nullptr)) {
      Debug("Unable to set timeout handler");
      exit(1);
    }
  }
}

void Signals::SetSignalHandler(uint sig, SignalHandler* handler) {
  const struct sigaction action = {handler, sig, 0};
  if (sigaction(sig, &action, nullptr)) {
    Debug("Unable to set handler for signal: ", sig);
    exit(1);
  }
}

} // prf