ARG BASE_IMAGE
FROM ${BASE_IMAGE}
LABEL maintainer "dan@su-root.co.uk"

# Install lit
RUN curl "https://bootstrap.pypa.io/get-pip.py" -o "get-pip.py" && \
  sudo python3 get-pip.py && \
  sudo pip install lit==0.5.0

# NOTE: We stagger copying across files (i.e. don't do `ADD / ${JFS_SRC_DIR}`
# first) to avoid triggering a rebuild of CMake/Z3/LLVM unnecessarily.

# This is unlikely to change (i.e. doing so would trigger rebuilds)
# so its okay to have this declared early.
ENV \
  JFS_SRC_DIR=/home/user/jfs/src

# Make directory for JFS source tree
RUN mkdir -p "${JFS_SRC_DIR}"

# Build Z3
ENV \
  Z3_SRC_DIR=/home/user/z3/src \
  Z3_BUILD_DIR=/home/user/z3/build \
  Z3_BUILD_TYPE=Release \
  Z3_STATIC_BUILD=1 \
  Z3_CMAKE_GENERATOR="Ninja"
ADD /scripts/dist/build_z3.sh ${JFS_SRC_DIR}/scripts/dist/
RUN ${JFS_SRC_DIR}/scripts/dist/build_z3.sh

# Build LLVM
ENV \
  LLVM_SRC_DIR=/home/user/llvm/src \
  LLVM_BUILD_DIR=/home/user/llvm/build \
  LLVM_BUILD_TYPE=Release \
  LLVM_CMAKE_GENERATOR="Ninja"
ADD /scripts/dist/build_llvm.sh ${JFS_SRC_DIR}/scripts/dist/
RUN ${JFS_SRC_DIR}/scripts/dist/build_llvm.sh

# Build JFS
# Now finally copy across all the other sources
# FIXME: For final solver build we should disable assertions
ADD / ${JFS_SRC_DIR}
ENV \
  JFS_BUILD_DIR=/home/user/jfs/build \
  JFS_BUILD_TYPE=Release \
  JFS_CMAKE_GENERATOR="Ninja" \
  JFS_ENABLE_ASSERTIONS=ON
RUN ${JFS_SRC_DIR}/scripts/dist/build_jfs.sh
