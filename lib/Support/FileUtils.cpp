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
#include "jfs/Support/FileUtils.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <system_error>

namespace {
std::error_code recursive_remove_impl(llvm::StringRef path,
                                      llvm::sys::fs::file_type ft) {
  if (ft == llvm::sys::fs::file_type::directory_file) {
    std::error_code ec;
    llvm::sys::fs::directory_iterator i(path, ec);
    if (ec)
      return ec;
    for (llvm::sys::fs::directory_iterator endIt; i != endIt; i.increment(ec)) {
      if (ec)
        return ec;
      llvm::ErrorOr<llvm::sys::fs::basic_file_status> st = i->status();
      if (auto ec = st.getError()) {
        return ec;
      }
      // Remove contents of this directory first
      if (auto ec = recursive_remove_impl(i->path(), st->type())) {
        return ec;
      }
    }
    // Directory should now be empty. We can remove it now.
    return llvm::sys::fs::remove(path, /*IgnoreNonExisting=*/false);
  } else {
    return llvm::sys::fs::remove(path, /*IgnoreNonExisting=*/false);
  }
  return std::error_code();
}
}

namespace jfs {
namespace support {

// This based on code that was removed from LLVM in
// r198955 ( 217c714a6779841ae06f420f384b87e12454b1a1 ).
std::error_code recursive_remove(llvm::StringRef path, bool IgnoreNonExisting) {
  llvm::sys::fs::file_status status;
  if (auto error = llvm::sys::fs::status(path, status)) {
    if (IgnoreNonExisting && error == std::errc::no_such_file_or_directory) {
      return std::error_code();
    }
    return error;
  }
  return recursive_remove_impl(path, status.type());
}
}
}
