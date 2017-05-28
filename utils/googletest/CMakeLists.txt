# HACK: Make sure gtest is built with our flags
add_definitions(${JFS_COMPONENT_CXX_DEFINES})
add_compile_options(${JFS_COMPONENT_CXX_FLAGS})
add_subdirectory(googletest)
