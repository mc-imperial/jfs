set(GCC_AND_CLANG_WARNINGS
    "-Wall"
)
set(GCC_ONLY_WARNINGS "")
set(CLANG_ONLY_WARNINGS "")
set(MSVC_WARNINGS "/W3")

set(WARNING_FLAGS_TO_CHECK "")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_ONLY_WARNINGS})
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${CLANG_ONLY_WARNINGS})
  # FIXME: Remove "x.." when CMP0054 is set to NEW
elseif ("x${CMAKE_CXX_COMPILER_ID}" STREQUAL "xMSVC")
  list(APPEND WARNING_FLAGS_TO_CHECK ${MSVC_WARNINGS})

  # CMake's default flags include /W3 already so remove them if
  # they already exist.
  if ("${CMAKE_CXX_FLAGS}" MATCHES "/W3")
    string(REPLACE "/W3" "" _cmake_cxx_flags_remove_w3 "${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS "${_cmake_cxx_flags_remove_w3}" CACHE STRING "" FORCE)
  endif()
else()
  message(AUTHOR_WARNING "Unknown compiler")
endif()

# Loop through flags and use the ones which the compiler supports
foreach (flag ${WARNING_FLAGS_TO_CHECK})
  jfs_component_add_cxx_flag("${flag}")
endforeach()
