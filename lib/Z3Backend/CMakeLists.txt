#===------------------------------------------------------------------------===#
#
#                                      JFS
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
jfs_add_component(JFSZ3Backend
  Z3Solver.cpp
)
target_link_libraries(JFSZ3Backend PUBLIC JFSTransform JFSCore)
