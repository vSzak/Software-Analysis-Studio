cmake_minimum_required(VERSION 3.23)
PROJECT(UTS-Software-Engineer-Studio-Marking)

file(GLOB SRC1 test-exes/Test.cpp *.cpp)
add_executable(ass1 ${SRC1})

set_target_properties(ass1 PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# ctest ./ass1 ${CMAKE_SOURCE_DIR}/Assignment-1/test-exes/test${1-3}.graph.txt 
foreach(i 1 2 3)
    add_test(NAME ass1-test${i} COMMAND ass1 ${CMAKE_SOURCE_DIR}/Assignment-1/test-exes/test${i}.graph.txt)
endforeach()

