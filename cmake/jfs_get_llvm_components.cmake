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

function(jfs_get_llvm_components DESTVAR)
  if (${ARGC} LESS 2)
    message(FATAL_ERROR "Insufficent number of argument")
  endif()
  llvm_map_components_to_libnames(llvm_components ${ARGN})
  set(${DESTVAR} ${llvm_components} PARENT_SCOPE)
endfunction()
