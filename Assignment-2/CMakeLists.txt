file(GLOB SRC1 test-exes/Test.cpp *.cpp)
add_executable(ass2 ${SRC1})
target_link_libraries(ass2 ${SVF_LIB} ${llvm_libs})

set_target_properties(ass2 PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

foreach(i 1 2 3)
    add_test(NAME ass2-test${i} COMMAND ass2 ${CMAKE_SOURCE_DIR}/Assignment-2/testcase/bc/test${i}.ll)
endforeach()