# FIXME: This isn't quite the version that's used on StarExec but
# it's damn close. Hopefully this will be ABI compatible
FROM centos:centos7.2.1511
LABEL maintainer "dan@su-root.co.uk"


# Woraround stupid issue
# https://github.com/CentOS/sig-cloud-instance-images/issues/15
RUN yum install -y yum-plugin-ovl && yum clean all

# Make the user and install sudo
RUN yum install -y sudo && \
  useradd -m user && \
  echo user:user | chpasswd && \
  echo 'user ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

USER user
WORKDIR /home/user

# In container development packages (not essential and can be commented out)
RUN sudo yum install -y vim less

# Install the dependencies for CentOS repos that we can use
RUN sudo yum install -y \
  coreutils \
  gcc \
  gcc-c++ \
  git \
  make \
  && sudo yum clean all

# Install lit
RUN curl "https://bootstrap.pypa.io/get-pip.py" -o "get-pip.py" && \
  sudo python get-pip.py && \
  sudo pip install lit==0.5.0

# Make directory for JFS source tree
RUN mkdir -p "${JFS_SRC_DIR}"

# NOTE: We stagger copying across files (i.e. don't do `ADD / ${JFS_SRC_DIR}`
# first) to avoid triggering a rebuild of CMake/Z3/LLVM unnecessarily.

# Build and install CMake
ENV \
  CMAKE_SRC_DIR=/home/user/cmake/src_build \
  CMAKE_INSTALL=1
ADD /scripts/dist/build_and_install_cmake.sh ${JFS_SRC_DIR}/scripts/dist/
RUN ${JFS_SRC_DIR}/scripts/dist/build_and_install_cmake.sh

# Build Z3
ENV \
  Z3_SRC_DIR=/home/user/z3/src \
  Z3_BUILD_DIR=/home/user/z3/build \
  Z3_BUILD_TYPE=Release \
  Z3_STATIC_BUILD=1 \
  Z3_CMAKE_GENERATOR="Unix Makefiles"
ADD /scripts/dist/build_z3.sh ${JFS_SRC_DIR}/scripts/dist/
RUN ${JFS_SRC_DIR}/scripts/dist/build_z3.sh

# Build LLVM
ENV \
  LLVM_SRC_DIR=/home/user/llvm/src \
  LLVM_BUILD_DIR=/home/user/llvm/build \
  LLVM_BUILD_TYPE=Release \
  LLVM_CMAKE_GENERATOR="Unix Makefiles"
ADD /scripts/dist/build_llvm.sh ${JFS_SRC_DIR}/scripts/dist/
RUN ${JFS_SRC_DIR}/scripts/dist/build_llvm.sh

# Build JFS
# Now finally copy across all the other sources
ADD / ${JFS_SRC_DIR}
ENV \
  JFS_SRC_DIR=/home/user/jfs/src \
  JFS_BUILD_DIR=/home/user/jfs/build \
  JFS_BUILD_TYPE=Release \
  JFS_CMAKE_GENERATOR="Unix Makefiles"
RUN ${JFS_SRC_DIR}/scripts/dist/build_jfs.sh
