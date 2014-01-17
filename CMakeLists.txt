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

## Tests
include(${CMAKE_CURRENT_SOURCE_DIR}/cmake/Tests.cmake)

######################################################################################
### 3) Define and add module paths
######################################################################################

## Paths
set(SOURCE_DIR "${CMAKE_SOURCE_DIR}/include" CACHE INTERNAL "Sources directory" FORCE)
set(BINARY_DIR "${CMAKE_BINARY_DIR}" CACHE INTERNAL "Binaries directory" FORCE)

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/src)

add_subdirectory(src)
