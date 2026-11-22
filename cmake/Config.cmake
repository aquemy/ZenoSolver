######################################################################################
### 1) Build type
######################################################################################

# project() creates an empty CMAKE_BUILD_TYPE cache entry, so a plain
# set(... CACHE ...) never applied and default builds had no optimisation.
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Build type." FORCE)
endif()

set(ZS_GENERATE_TESTS TRUE CACHE STRING "Generate tests (activated in debug and profiling).")
set(ZS_GENERATE_DOC TRUE CACHE STRING "Generate documention.")
set(ZS_GENERATE_APP TRUE CACHE STRING "Generate an application for all activated flags (PARALLEL + STATS + ITER).")
set(ZS_PARALLEL FALSE CACHE STRING "Parallel mode using OpenMP and parallel STL")
