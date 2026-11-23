######################################################################################
### Benchmarks (ZS_BUILD_BENCHMARKS=ON)
######################################################################################
#
# One Google Benchmark executable per component, under bench/components. End-to-end
# runs of the solver executables over the instance suites in bench/instances are
# driven by bench/tools/run_suite.py, which writes the same JSON schema.

add_library(zeno_bench_support INTERFACE)
target_include_directories(zeno_bench_support INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/support)

# zs_add_benchmark(<name> <source>... [LIBS <target>...])
function(zs_add_benchmark name)
    cmake_parse_arguments(ARG "" "" "LIBS" ${ARGN})
    add_executable(${name} ${ARG_UNPARSED_ARGUMENTS})
    target_link_libraries(${name} PRIVATE ${ARG_LIBS} zeno_bench_support zeno_build_settings benchmark::benchmark_main)
    set_property(GLOBAL APPEND PROPERTY ZS_BENCHMARK_TARGETS ${name})
endfunction()

# The exact solver.
zs_add_benchmark(bm-core components/core.cpp LIBS zeno::core)

# Components of the 2016 solver, kept as the reference until it is removed.
zs_add_benchmark(bm-legacy components/legacy.cpp LIBS zeno_legacy)

# 'cmake --build <dir> --target benchmarks' builds every benchmark.
get_property(zs_benchmarks GLOBAL PROPERTY ZS_BENCHMARK_TARGETS)
add_custom_target(benchmarks DEPENDS ${zs_benchmarks})
