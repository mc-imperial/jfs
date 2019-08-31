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
#ifndef JFS_RUNTIME_SMTLIB_BUFFER_REF_H
#define JFS_RUNTIME_SMTLIB_BUFFER_REF_H
#include <stdlib.h>

template <typename T> class BufferRef {
private:
  T* data;
  size_t size;

public:
  BufferRef(T* data, size_t size) : data(data), size(size) {}
  T* get() const { return data; }
  operator T*() const { return get(); }
  size_t getSize() const { return size; }
};

#endif
