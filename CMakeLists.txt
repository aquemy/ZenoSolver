cmake_minimum_required(VERSION 3.21)

project(ZenoSolver
    VERSION 0.9
    DESCRIPTION "Exact Pareto fronts for MultiZenoTravel instances"
    LANGUAGES CXX)

######################################################################################
### Options
######################################################################################

# project() creates an empty CMAKE_BUILD_TYPE cache entry, so the default has
# to be forced. Multi-configuration generators choose at build time instead.
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type." FORCE)
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS Debug Release RelWithDebInfo MinSizeRel)
endif()

option(ZS_BUILD_TESTS "Build the tests, the brute-force oracle and the golden suite." ON)
option(ZS_BUILD_BENCHMARKS "Build the component benchmarks (fetches Google Benchmark)." OFF)
option(ZS_BUILD_DOC "Add the 'doc' target (requires Doxygen)." OFF)
option(ZS_WARNINGS_AS_ERRORS "Treat compiler warnings as errors." OFF)
option(ZS_ENABLE_IPO "Link-time optimisation in Release builds, when supported." ON)
option(ZS_NATIVE "Tune for the build machine (-march=native). Binaries are not portable." OFF)
set(ZS_SANITIZERS "" CACHE STRING "Sanitizers to enable, e.g. \"address;undefined\".")

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# All binaries at the root of the build tree: build/<preset>/zeno, ...
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})

######################################################################################
### Build settings shared by every target
######################################################################################

add_library(zeno_build_settings INTERFACE)

if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    target_compile_options(zeno_build_settings INTERFACE -Wall -Wextra -Wpedantic)
    if(ZS_WARNINGS_AS_ERRORS)
        target_compile_options(zeno_build_settings INTERFACE -Werror)
    endif()
    if(ZS_NATIVE)
        target_compile_options(zeno_build_settings INTERFACE -march=native)
    endif()
    if(ZS_SANITIZERS)
        list(JOIN ZS_SANITIZERS "," zs_sanitizers)
        # Make undefined behaviour fail the tests instead of only printing.
        target_compile_options(zeno_build_settings INTERFACE
            -fsanitize=${zs_sanitizers} -fno-sanitize-recover=all -fno-omit-frame-pointer)
        target_link_options(zeno_build_settings INTERFACE -fsanitize=${zs_sanitizers})
    endif()
endif()

if(ZS_ENABLE_IPO)
    include(CheckIPOSupported)
    check_ipo_supported(RESULT zs_ipo_supported OUTPUT zs_ipo_output LANGUAGES CXX)
    if(zs_ipo_supported)
        set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_RELEASE ON)
    else()
        message(STATUS "Link-time optimisation is not supported: ${zs_ipo_output}")
    endif()
endif()

######################################################################################
### Library and solvers
######################################################################################

# The exact solver: library zeno_core (namespace zeno, include/zeno) and the
# zeno command-line tool.
add_library(zeno_core STATIC
    src/zeno/certificate.cpp
    src/zeno/forest.cpp
    src/zeno/instance.cpp
    src/zeno/io.cpp
    src/zeno/legacy_input.cpp
    src/zeno/one_plane.cpp
    src/zeno/plan.cpp
    src/zeno/reduce.cpp
    src/zeno/solve.cpp)
add_library(zeno::core ALIAS zeno_core)
target_include_directories(zeno_core PUBLIC ${PROJECT_SOURCE_DIR}/include)
find_package(Threads REQUIRED)
target_link_libraries(zeno_core PUBLIC Threads::Threads PRIVATE zeno_build_settings)

add_executable(zeno src/zeno/main.cpp)
target_link_libraries(zeno PRIVATE zeno::core zeno_build_settings)

######################################################################################
### Tests and documentation
######################################################################################

if(ZS_BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()

if(ZS_BUILD_BENCHMARKS)
    include(FetchContent)
    set(BENCHMARK_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_GTEST_TESTS OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_INSTALL OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_WERROR OFF CACHE BOOL "" FORCE)
    FetchContent_Declare(benchmark
        GIT_REPOSITORY https://github.com/google/benchmark.git
        GIT_TAG v1.9.1
        GIT_SHALLOW TRUE
        SYSTEM)
    FetchContent_MakeAvailable(benchmark)
    add_subdirectory(bench)
endif()

if(ZS_BUILD_DOC)
    find_package(Doxygen REQUIRED)
    add_subdirectory(doc)
endif()
