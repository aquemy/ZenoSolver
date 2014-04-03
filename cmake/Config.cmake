######################################################################################
### 1) Build type
######################################################################################

set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Build type.")

set(ZS_GENERATE_TESTS TRUE CACHE STRING "Generate tests (activated in debug and profiling).")
set(ZS_GENERATE_DOC TRUE CACHE STRING "Generate documention.")
set(ZS_GENERATE_APP TRUE CACHE STRING "Generate an application for all activated flags (PARALLEL + STATS + ITER).")
set(ZS_PARALLEL FALSE CACHE STRING "Parallel mode using OpenMP and parallel STL")
