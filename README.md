ZenoSolver
==========

Exact Pareto fronts (total cost, makespan) of MultiZenoTravel planning instances.

    zeno -n 50 -t 30 -p 5            # 50 central cities, 30 passengers, 5 planes
    zeno -n 10 -t 8 -p 3 -C 2 -D 2 -r 100 --stats
    zeno -n 2 -t 5 -p 2 -d durations-and-costs.dat

`zeno` prints the front as `cost makespan` lines by increasing cost. It takes the instance options of the 2016 solvers (`zeno --help`) and builds the same instances, so their fronts can be compared. It currently handles instances with symmetric durations, which includes every instance the generator emits.

How it works (`doc/theory/exact-front.md`): the front is the set of breakpoints of E(T), the cheapest admissible partition of the 2t − p landings into p groups whose durations each sum to at most T. `zeno` brackets E between a relaxation L and the pairs and chains bounds U and U3 on every level, and runs the exact link-forest dynamic program only on the levels that the bracket and the monotonicity of E leave open. The 2016 solvers (`zenoSolver`, `zenoSolver_naive`, `zenoSolver_noDuplicate`) use a greedy schedule that is not optimal (`tests/golden/known-bugs.txt`); they are kept until the new solver covers the non-symmetric case.

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
| `bench` | Release build of the benchmarks and the solvers, without the tests. |

Options (`-D<option>=<value>`):

| Option | Default | Meaning |
| --- | --- | --- |
| `ZS_BUILD_TESTS` | `ON` | Build the tests, the brute-force oracle and the golden suite. |
| `ZS_BUILD_BENCHMARKS` | `OFF` | Build the component benchmarks; fetches Google Benchmark v1.9.1 (`bench` preset). |
| `ZS_BUILD_DOC` | `OFF` | Add the `doc` target (requires Doxygen). |
| `ZS_ENABLE_IPO` | `ON` | Link-time optimisation in Release builds, when supported. |
| `ZS_NATIVE` | `OFF` | Tune for the build machine (`-march=native`). Binaries are not portable. |
| `ZS_SANITIZERS` | empty | Sanitizers to enable, e.g. `address;undefined`. |
| `ZS_WARNINGS_AS_ERRORS` | `OFF` | Treat compiler warnings as errors. |

# Testing

    ctest --preset release

The golden tests compare the Pareto front of every solver variant (printed with `-F`) to fronts computed by a brute-force oracle (`tests/oracle`). The oracle enumerates every PPP, every beta set, and every assignment and order of flights to planes, and simulates the waiting in pattern P3 exactly. It is exponential, so the golden instances (`tests/golden/instances.txt`) are tiny. Regenerate the fronts with `tests/golden/regenerate.sh build/release/zenoOracle`.

Pairs that currently fail are listed in `tests/golden/known-bugs.txt`. They are expected to fail, and they must be removed from that list when fixed.

`ut-zeno-core` checks the exact solver against a second, independent oracle (`tests/oracle/partitionEnum.hpp`), which enumerates every landing multiset and every admissible partition: the value of every level, the bracket order L ≤ E ≤ U3 ≤ U, and the front, on random instances. `ut-zeno-core <trials> <maxN> <maxT> <maxP> <maxS>` runs a larger sweep.

Benchmarks: `cmake --preset bench && cmake --build --preset bench` builds the component benchmarks (Google Benchmark) and the solvers; `bench/tools/run_suite.py` times a solver over the instance suites in `bench/instances`. See `bench/README.md`.

Every pull request is built and tested on Linux (GCC, Clang) and macOS, and once more under the sanitizers.

# RunTime Options

As ZenoSolver handles only integers for cost and durations, it will cast generated vectors (or provided data) to integers. The adjustement factor (option -r) is a multiplicative constant in order to avoid some errors (for instance, obtaining more than once the value 0 because log(i) and log(i+1) have same floor value.

By default it is set to 1 but a better value for most of functions could be 100.

More information using ./zenoSolver -h.

# PDDL

`-G` writes the instance as a PDDL problem (`-O` sets the path) for the domain in `pddl/multi-zeno-travel.pddl`.

- `city0` is the initial city C_I, `city1`…`cityN` are the central cities, `city(N+1)` is the goal city C_G.
- Every person and every plane starts in C_I, and must end in C_G.
- `fly` takes `timeTerre` time units; landing in a city adds its `citythreat` to the total cost (0 for C_I and C_G).
- A flight between two central cities i and j lasts d_i + d_j + 100, so it is never faster than going through C_I or C_G.
- A plane carries one person at a time. `board` and `debark` are instantaneous: with the ε-separation of PDDL 2.1 a planner's makespan exceeds ZenoSolver's by at most ε per action on the critical path.
- The trailing comments list the durations, the costs and the Pareto front (makespan, cost).

# References

- **True Pareto Fronts for Multi-Objective AI Planning Instances**. *Alexandre Quemy, Marc Schoenauer.* Francesco Chicano and Gabriela Ochoa. European Conference on Combinatorial Optimization - EvoCOP, Apr 2015, Copenhague, Denmark. LNCS 9026, Springer Verlag, pp.197-208, 2015. <hal-01109777>
- **Solving Large MultiZenoTravel Benchmarks with Divide-and-Evolve.** *Alexandre Quemy, Marc Schoenauer, Vincent Vidal, Johann Dréo, Pierre Savéant.* Learning and Intelligent OptimizatioN - LION 9, Jan 2015, Lille, France. LNCS 8994, Springer Verlag, pp.262-267, 2015. <hal-01109776>
