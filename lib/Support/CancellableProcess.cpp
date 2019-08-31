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
#include "jfs/Support/CancellableProcess.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"
#include <atomic>
#include <mutex>
#include <signal.h>
#include <sys/types.h>
#include <unistd.h>

namespace jfs {
namespace support {

class CancellableProcessImpl {
private:
  std::atomic<bool> cancelled;
  llvm::sys::ProcessInfo processInfo;
  std::mutex processInfoMutex;

public:
  CancellableProcessImpl() : cancelled(false) {
    // HACK: This is for the implementation of `kill()`.
    setpgid(0, 0); // Try to make ourselves the process group leader.
    cleanUp();
  }
  ~CancellableProcessImpl() {}

  void cleanUp() { processInfo.Pid = llvm::sys::ProcessInfo::InvalidPid; }

  void cancel() {
    cancelled = true;
    // Kill the process if necessary.
    kill();
  }

  void kill() {
    {
      // Only read the PID when we hold the mutex
      std::lock_guard<std::mutex> lock(processInfoMutex);
      auto pid = processInfo.Pid;
      if (pid == llvm::sys::ProcessInfo::InvalidPid)
        return;
      // FIXME: This is POSIX specific

      // HACK: Processes like Clang fork and so just doing `kill(pid, SIGTERM)`
      // won't kill the child processes. To workaround this we temporarily
      // ignore SIGTERM ourselves and then send SIGTERM to our process group
      // and then set the handler for SIGTERM to whatever it was before.
      // This sucks because this is only really safe if JFS is launched as
      // the leader of the process group. This is the case when jfs is launched
      // from a shell but probably not in other cases (e.g. Python script using
      // subprocess). Therefore the constructor of this class enforces that
      // we are the group leader.

      struct sigaction oldHandler;
      // Get the current
      int result = ::sigaction(SIGTERM, nullptr, &oldHandler);
      assert((result == 0) && "Failed to get current signal handler");
      // Set the new handler to ignore SIGTERM
      struct sigaction newHandler = oldHandler;
      newHandler.sa_handler = SIG_IGN;
      result = ::sigaction(SIGTERM, &newHandler, nullptr);
      assert((result == 0) && "Failed to change signal handler");

      // Send SIGTERM to the process group
      pid_t processGroupID = getpgrp();
      // llvm::errs() << "Sending SIGTERM to process group " << processGroupID
      // << "\n";
      result = ::kill(-processGroupID, SIGTERM);
      // llvm::errs() << "kill result: " << result << "\n";
      // Set the handler back
      result = ::sigaction(SIGTERM, &oldHandler, nullptr);
      assert((result == 0) && "Failed to change signal handler back");
    }
  }

  int execute(llvm::StringRef program, std::vector<const char*>& args,
              std::vector<llvm::StringRef>& redirects, const char** envp) {
    if (cancelled) {
      return -1;
    }
    assert(args[args.size() - 1] == nullptr && "args must be null termianted");

    // FIXME: This awkwardness is due to r313155 in LLVM. We should just fix
    // our function signature to use LLVM's use of
    // ArrayRef<Optional<StringRef>> to simplify things.
    llvm::Optional<llvm::StringRef> redirectOptionals[3] = {
        llvm::None, llvm::None, llvm::None};
    if (redirects.size() > 0) {
      assert(redirects.size() == 3);
      unsigned optionalIndex = 0;
      for (const auto& sf : redirects) {
        assert(optionalIndex < 3);
        redirectOptionals[optionalIndex] = llvm::Optional<llvm::StringRef>(sf);
        ++optionalIndex;
      }
    }

    std::string errorMsg;
    bool executionFailed = false;
    {
      // Only write when the mutex is held.
      std::lock_guard<std::mutex> lock(processInfoMutex);
      // Execute without waiting so that the `ProcessInfo`
      // is stored so we can kill it from `cancel()`.
      processInfo = llvm::sys::ExecuteNoWait(
          /*Program=*/program,
          /*args=*/args.data(),
          /*env=*/envp,
          /*redirects=*/
          ((redirects.size() == 0)
               ? (llvm::ArrayRef<llvm::Optional<llvm::StringRef>>())
               : redirectOptionals),
          /*memoryLimit=*/0,
          /*ErrMsg=*/&errorMsg,
          /*ExecutionFailed=*/&executionFailed);
    }

    if (executionFailed) {
      // FIXME: emit to an interface
      // llvm::errs() << "Execution failed: " << errorMsg << "\n";
      cleanUp(); // FIXME: Should use RAII style clean up.
      return -1;
    }

    llvm::sys::ProcessInfo tempProcessInfo =
        llvm::sys::Wait(processInfo,
                        /*secondsToWait=*/0,
                        /*WaitUntilTerminates=*/true,
                        /*ErrMsg=*/
                        &errorMsg);
    {
      // Only write when the mutex is held.
      std::lock_guard<std::mutex> lock(processInfoMutex);
      processInfo = tempProcessInfo;
    }

    if (errorMsg.size() != 0 && !cancelled) {
      cleanUp();
      // llvm::errs() << "Execution failed: " << errorMsg << "\n";
      return -1;
    }

    if (cancelled) {
      cleanUp();
      return -2;
    }
    cleanUp();
    return processInfo.ReturnCode;
  }
};

CancellableProcess::CancellableProcess() : impl(new CancellableProcessImpl()) {}
CancellableProcess::~CancellableProcess() {}

void CancellableProcess::cancel() { impl->cancel(); }
int CancellableProcess::execute(llvm::StringRef program,
                                std::vector<const char*>& args,
                                std::vector<llvm::StringRef>& redirects,
                                const char** envp) {
  return impl->execute(program, args, redirects, envp);
}
}
}
