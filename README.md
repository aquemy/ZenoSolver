ZenoSolver
==========

Optimal solver for multiobjectives ZenoTransportation problem.

# Requirements

- CMake >= 3.21
- A C++23 compiler: GCC >= 13, Clang >= 16 or Apple Clang >= 15
- (optional) Doxygen for the documentation

# How to compile

    cmake --preset release
    cmake --build --preset release
    ctest --preset release

The binaries are written to `build/release`. Without presets:

    cmake -S . -B build/default && cmake --build build/default -j

# Build & Compilation Options

Presets (`CMakePresets.json`):

| Preset | Purpose |
| --- | --- |
| `release` | Optimised build with link-time optimisation (the default build type). |
| `dev` | Debug build, exports `compile_commands.json`. |
| `asan` | AddressSanitizer and UndefinedBehaviorSanitizer. Any report fails the test. |

Options (`-D<option>=<value>`):

| Option | Default | Meaning |
| --- | --- | --- |
| `ZS_BUILD_TESTS` | `ON` | Build the tests, the brute-force oracle and the golden suite. |
| `ZS_BUILD_DOC` | `OFF` | Add the `doc` target (requires Doxygen). |
| `ZS_ENABLE_IPO` | `ON` | Link-time optimisation in Release builds, when supported. |
| `ZS_NATIVE` | `OFF` | Tune for the build machine (`-march=native`). Binaries are not portable. |
| `ZS_SANITIZERS` | empty | Sanitizers to enable, e.g. `address;undefined`. |
| `ZS_WARNINGS_AS_ERRORS` | `OFF` | Treat compiler warnings as errors. |

# Testing

    ctest --preset release

The golden tests compare the Pareto front of every solver variant (printed with `-F`) to fronts computed by a brute-force oracle (`tests/oracle`). The oracle enumerates every PPP, every beta set, and every assignment and order of flights to planes, and simulates the waiting in pattern P3 exactly. It is exponential, so the golden instances (`tests/golden/instances.txt`) are tiny. Regenerate the fronts with `tests/golden/regenerate.sh build/release/zenoOracle`.

Pairs that currently fail are listed in `tests/golden/known-bugs.txt`. They are expected to fail, and they must be removed from that list when fixed.

`bench/run.sh build/release` times the three variants on a few larger instances.

Every pull request is built and tested on Linux (GCC, Clang) and macOS, and once more under the sanitizers.

# RunTime Options

As ZenoSolver handles only integers for cost and durations, it will cast generated vectors (or provided data) to integers. The adjustement factor (option -r) is a multiplicative constant in order to avoid some errors (for instance, obtaining more than once the value 0 because log(i) and log(i+1) have same floor value.

By default it is set to 1 but a better value for most of functions could be 100.

More information using ./zenoSolver -h.

# References

- **True Pareto Fronts for Multi-Objective AI Planning Instances**. *Alexandre Quemy, Marc Schoenauer.* Francesco Chicano and Gabriela Ochoa. European Conference on Combinatorial Optimization - EvoCOP, Apr 2015, Copenhague, Denmark. LNCS 9026, Springer Verlag, pp.197-208, 2015. <hal-01109777>
- **Solving Large MultiZenoTravel Benchmarks with Divide-and-Evolve.** *Alexandre Quemy, Marc Schoenauer, Vincent Vidal, Johann Dréo, Pierre Savéant.* Learning and Intelligent OptimizatioN - LION 9, Jan 2015, Lille, France. LNCS 8994, Springer Verlag, pp.262-267, 2015. <hal-01109776>
