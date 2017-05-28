add_executable(FileCheck
  FileCheck.cpp
)
jfs_get_llvm_components(FILECHECK_NEEDED_LIBS Support)
target_include_directories(FileCheck PRIVATE ${JFS_COMPONENT_EXTRA_INCLUDE_DIRS})
target_compile_options(FileCheck PRIVATE ${JFS_COMPONENT_CXX_FLAGS})
target_compile_definitions(FileCheck PRIVATE ${JFS_COMPONENT_CXX_DEFINES})
target_link_libraries(FileCheck PRIVATE ${FILECHECK_NEEDED_LIBS})
