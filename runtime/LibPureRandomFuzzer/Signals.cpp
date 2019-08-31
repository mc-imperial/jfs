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

#include "Signals.h"

#include "Log.h"
#include <sys/time.h>
#include <signal.h>

namespace prf {

Signals::Signals(const Options& opts) {
  if (opts.timeout > 0) {
    SetSignalHandler(SIGALRM, &TimeoutHandler);
    // Just like LibFuzzer, we set a repeating OS level timer to just over half
    // the requested timeout value.  When the timer callback fires, we'll
    // compare time spent on the current run with the requested timeout, so in
    // the worst case, a run might continue for `~1.5 * timeout` before
    // aborting.
    int timeout = opts.timeout / 2 + 1;
    itimerval timer = {{timeout, 0}, {timeout, 0}};
    if (setitimer(ITIMER_REAL, &timer, nullptr)) {
      Debug("Unable to set timeout handler");
      exit(1);
    }
  }
  if (opts.handleSIGABRT) {
    SetSignalHandler(SIGABRT, &AbortHandler);
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