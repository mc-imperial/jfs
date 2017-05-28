add_executable("not"
  not.cpp
)
jfs_get_llvm_components(NOT_NEEDED_LIBS Support)
target_include_directories("not" PRIVATE ${JFS_COMPONENT_EXTRA_INCLUDE_DIRS})
target_compile_options("not" PRIVATE ${JFS_COMPONENT_CXX_FLAGS})
target_compile_definitions("not" PRIVATE ${JFS_COMPONENT_CXX_DEFINES})
target_link_libraries("not" PRIVATE ${NOT_NEEDED_LIBS})
