add_library(LLVMFuzzer STATIC
  FuzzerClangCounters.cpp
  FuzzerCrossOver.cpp
  FuzzerDriver.cpp
  FuzzerExtFunctionsDlsym.cpp
  FuzzerExtFunctionsDlsymWin.cpp
  FuzzerExtFunctionsWeakAlias.cpp
  FuzzerExtFunctionsWeak.cpp
  FuzzerExtraCounters.cpp
  FuzzerIO.cpp
  FuzzerIOPosix.cpp
  FuzzerIOWindows.cpp
  FuzzerLoop.cpp
  FuzzerMain.cpp
  FuzzerMerge.cpp
  FuzzerMutate.cpp
  FuzzerSHA1.cpp
  FuzzerShmemFuchsia.cpp
  FuzzerShmemPosix.cpp
  FuzzerShmemWindows.cpp
  FuzzerTracePC.cpp
  FuzzerUtil.cpp
  FuzzerUtilDarwin.cpp
  FuzzerUtilFuchsia.cpp
  FuzzerUtilLinux.cpp
  FuzzerUtilPosix.cpp
  FuzzerUtilWindows.cpp
)

CHECK_CXX_SOURCE_COMPILES("
  static thread_local int blah;
  int main() {
  return 0;
  }
  " HAS_THREAD_LOCAL)

if(NOT HAS_THREAD_LOCAL)
  target_compile_definitions(LLVMFuzzer PRIVATE -Dthread_local=__thread)
endif()

target_link_libraries(LLVMFuzzer PRIVATE ${PTHREAD_LIB})
