######################################################################################
### 0) Activate tests
######################################################################################

set(${CMAKE_BINARY_DIR} tests)

if(ZS_GENERATE_TESTS)
enable_testing()
include(CTest REQUIRED)

include_directories(${CMAKE_SOURCE_DIR}/include)
include_directories(${CMAKE_SOURCE_DIR}/tests)

set(TEST_LIST 
    ut-combiGenerator
    ut-cartesianProduct
    ut-simpleUpperBound
    ut-computeBetaMax
    ut-powerSetGenerator
)

foreach(test ${TEST_LIST})
    set("T_${test}_SOURCES" "${CMAKE_SOURCE_DIR}/tests/${test}.cpp")
    add_executable(${test} ${T_${test}_SOURCES} ${FILES})
    add_test(${test} ${test}) 
endforeach()

# Performance test: unbounded runtime and always returns 1, so it is built
# but not registered with CTest.
add_executable(pt-powerSetGenerator ${CMAKE_SOURCE_DIR}/tests/pt-powerSetGenerator.cpp ${FILES})

######################################################################################
### 1) Brute-force oracle and golden Pareto fronts
######################################################################################

# The oracle uses C++17; the last -std flag wins over the global -std=c++14.
add_executable(zenoOracle ${CMAKE_SOURCE_DIR}/tests/oracle/main.cpp ${FILES})
target_compile_options(zenoOracle PRIVATE -std=c++17)

add_executable(ut-oracle ${CMAKE_SOURCE_DIR}/tests/ut-oracle.cpp)
target_compile_options(ut-oracle PRIVATE -std=c++17)
add_test(ut-oracle ut-oracle)

include(${CMAKE_SOURCE_DIR}/cmake/Golden.cmake)

endif()
