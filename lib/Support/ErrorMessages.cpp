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
#include "jfs/Support/ErrorMessages.h"
#include "llvm/Support/raw_ostream.h"

namespace jfs {
namespace support {

std::string getMessageForFailedOpenFileOrSTDIN(llvm::StringRef inputFileName,
                                               std::error_code ec) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << "(error \"Could not open " << inputFileName << " because "
     << ec.message() << "\")\n";
  return ss.str();
}

std::string
getMessageForFailedOpenFileForWriting(llvm::StringRef outputFileName,
                                      std::error_code ec) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << "(error \"Could not open " << outputFileName << " for writing because "
     << ec.message() << "\")\n";
  return ss.str();
}
}
}
