######################################################################################
### 1) Build type
######################################################################################

set(ZS_BUILD_TYPE "Standard" CACHE STRING "Build type.")

set(ZS_GENERATE_TESTS TRUE CACHE STRING "Generate tests (activated in debug and profiling).")
set(ZS_GENERATE_DOC TRUE CACHE STRING "Generate documention.")
set(ZS_GENERATE_APP TRUE CACHE STRING "Generate an application for all activated flags (PARALLEL + STATS + ITER).")

set(ZS_PARETO_ONLY TRUE CACHE STRING "Printing only the Pareto front")
set(ZS_OPTIMIZED_MEMORY FALSE CACHE STRING "Optimized the size of the memory")
set(ZS_PARALLEL FALSE CACHE STRING "Parallel mode using OpenMP and parallel STL")
set(ZS_STATS FALSE CACHE STRING "Compute statistics during the process")
set(ZS_ITERATIVE FALSE CACHE STRING "Iterative mode : compute the front for each value of Beta")
set(ZS_PLOT FALSE CACHE STRING "Print statistics during the process")
set(ZS_PDDL_GENERATE FALSE CACHE STRING "Generate PDDL file for the given problem")
set(ZS_CONSTRUCT_PLAN FALSE CACHE STRING "Construct plans for Pareto-optimal points")
set(ZS_PRUNING TRUE CACHE STRING "Pruning admissible-PPP during the search process")
