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
#ifndef JFS_SUPPORT_ICANCELLABLE_H
#define JFS_SUPPORT_ICANCELLABLE_H

namespace jfs {

namespace support {
// This is a simple interface that classes can implement to cancel their
// currently assigned work. It is not defined what the state of the instance
// will be after making this call.
class ICancellable {
public:
  virtual void cancel() = 0;
  virtual ~ICancellable();
};
}
}
#endif
