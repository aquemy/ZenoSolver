# ZenoSolver

######################################################################################
### 0) Check the CMake version
######################################################################################

cmake_minimum_required(VERSION 2.8 FATAL_ERROR)

######################################################################################
### 1) Define the project
######################################################################################

## Name
project("ZenoSolver")

## Language
enable_language(CXX)

######################################################################################
### 2) Include CMake files
######################################################################################

## Configuration file
include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/Config.cmake)

## Build type and flags
include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/BuildType.cmake)

## Dependencies
include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/Dependencies.cmake)

## Custom Targets file
include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/Target.cmake)

add_subdirectory(doc)

######################################################################################
### 3) Define and add module paths
######################################################################################

## Paths
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/src)

set(FILES
    src/algorithm.cpp
    src/genFunctions.cpp
    src/combiGenerator.cpp
    src/utils.cpp
    src/powerSetGenerator.cpp
    src/paretoExtraction.cpp
    )

add_executable(zenoSolver src/solver.cpp ${FILES})
#add_executable(random src/random.cpp)

######################################################################################
### 3) Include Tests
######################################################################################

include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/Tests.cmake)
