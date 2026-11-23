ZenoSolver
==========

Exact Pareto fronts (total cost, makespan) of MultiZenoTravel planning instances.

    zeno -n 50 -t 30 -p 5            # 50 central cities, 30 passengers, 5 planes
    zeno -n 10 -t 8 -p 3 -C 2 -D 2 -r 100 --stats
    zeno -n 2 -t 5 -p 2 -d durations-and-costs.dat

`zeno` prints the front as `cost makespan` lines by increasing cost. It takes the instance options of the 2016 solvers (`zeno --help`) and builds the same instances, so their fronts can be compared. For instances with symmetric durations, which includes every instance the generator emits, the front is exact. For non-symmetric instances (`-E`/`-W`, or 3-line data files) `zeno` prints points achieved by simulated plans and reports on stderr which gaps between them a lower bound certifies, and whether the whole front is therefore exact.

How it works (`doc/theory/exact-front.md`): the front is the set of breakpoints of E(T), the cheapest admissible partition of the 2t − p landings into p groups whose durations each sum to at most T. `zeno` brackets E between a relaxation L and the pairs and chains bounds U and U3 on every level, and runs the exact link-forest dynamic program only on the levels that the bracket and the monotonicity of E leave open. The 2016 solvers (`zenoSolver`, `zenoSolver_naive`, `zenoSolver_noDuplicate`) scheduled each PPP greedily, which is not optimal; they were removed (last in commit 84ca92a), and their timings are kept in `bench/baselines/legacy` for comparison.

# Results

**Correctness.**

- `zeno` reproduces all 27 golden fronts of the brute-force oracle, including the five on which the 2016 solvers were still wrong after their bookkeeping fixes (their greedy schedule is not optimal: `doc/theory/exact-front.md` §5).
- Every level of thousands of random instances matches an independent enumeration oracle.
- On 1,800 tiny non-symmetric instances, every bracket closes and equals the oracle's front.

**Speed** (`bench/README.md`; Apple M4 Max):

| Suite instance | 2016 `zenoSolver` | `zeno` |
|---|---|---|
| EvoCOP Table 1, n = t = 8, p = 2 | 17.8 s | 3 ms |
| n = 50, t = 30, p = 5 | > 30 s | 8 ms |
| n = 100, t = 60, p = 10 | > 30 s | 61 ms |
| sqrt family with durations × 10⁴ (10⁵ levels) | > 30 s | 9 ms |

The 2016 solvers finish 21 of the 66 suite instances within 30 s; `zeno` finishes all 66. Time grows with the logarithm of the level range: 10⁸ levels take about 4 ms.

**Proofs and certificates.**

- The theory note gives a complete written proof of every statement the symmetric solver relies on.
- Each front can come with a certificate (`doc/certificate-format.md`), checked by `zeno check` and, for version 1, by the Lean-verified checker in `lean/`. Its soundness theorem holds for any central-flight durations whenever every gap is closed by the relaxation L (386 of 400 random fronts, and every front of the default generator). Fronts with `forest` gaps need the converse theorem, which is being formalised.

**Non-symmetric instances.**

- Fronts are exact wherever the certified bracket closes. The lower bounds rest on Theorem 6.1, which needs central flights to be useless (A1-NS).
- Waiting can be genuinely harmful (Proposition 6.5 refutes the papers' no-waiting assumption). On such instances `zeno` reports the open gaps and their lower bounds instead of a front it cannot prove.

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
| `ZS_BUILD_FUZZERS` | `OFF` | Build the libFuzzer targets (clang only; combine with `ZS_SANITIZERS`). |
| `ZS_BUILD_BENCHMARKS` | `OFF` | Build the component benchmarks; fetches Google Benchmark v1.9.1 (`bench` preset). |
| `ZS_BUILD_DOC` | `OFF` | Add the `doc` target (requires Doxygen). |
| `ZS_ENABLE_IPO` | `ON` | Link-time optimisation in Release builds, when supported. |
| `ZS_NATIVE` | `OFF` | Tune for the build machine (`-march=native`). Binaries are not portable. |
| `ZS_SANITIZERS` | empty | Sanitizers to enable, e.g. `address;undefined`. |
| `ZS_WARNINGS_AS_ERRORS` | `OFF` | Treat compiler warnings as errors. |

# Testing

    ctest --preset release

The golden tests compare the front of `zeno` to fronts computed by a brute-force oracle (`tests/oracle/bruteForce.hpp`), and check that `zeno check` accepts the certificate of each. The oracle enumerates every PPP, every beta set, and every assignment and order of flights to planes, and simulates the waiting in pattern P3 exactly. It is exponential, so the golden instances (`tests/golden/instances.txt`) are tiny. Regenerate the fronts with `tests/golden/regenerate.sh build/release/zenoOracle`.

Pairs that are known to fail go in `tests/golden/known-bugs.txt` (currently none). They are expected to fail, and they must be removed from that list when fixed.

`ut-zeno-core` checks the exact solver against a second, independent oracle (`tests/oracle/partitionEnum.hpp`), which enumerates every landing multiset and every admissible partition: the value of every level, the bracket order L ≤ E ≤ U3 ≤ U, and the front, on random instances. `ut-zeno-core <trials> <maxN> <maxT> <maxP> <maxS>` runs a larger sweep. It also checks metamorphic properties: permuting cities, adding dominated or duplicate cities change nothing; scaling durations or costs scales the front; adding a to every cost adds s·a to every front cost.

The certificate reader and checker are fuzzed (`tests/fuzz/fuzz_certificate.cpp`): CTest replays the seed corpus on every platform, and CI runs libFuzzer with ASan and UBSan for two minutes on every pull request (`-DZS_BUILD_FUZZERS=ON`, clang). The reader refuses values above 2^36, n, t or p above 10^5 and more than 10^7 legs, so no sum in the checker can overflow.

Benchmarks: `cmake --preset bench && cmake --build --preset bench` builds the component benchmarks (Google Benchmark) and `zeno`; `bench/tools/run_suite.py` times a solver over the instance suites in `bench/instances`. See `bench/README.md`.

Every pull request is built and tested on Linux (GCC, Clang) and macOS, and once more under the sanitizers.

# Commands

    zeno [front] [instance options] [--threads N] [--plans] [--certificate FILE] [--stats]
    zeno check CERTIFICATE
    zeno pddl [instance options] [-O FILE] [--no-front]
    zeno generate [instance options] [-O FILE]

- `front` (the default) prints the front; `--plans` adds a plan for every point, checked by simulation; `--certificate` writes a certificate (`doc/certificate-format.md`): version 1 for symmetric instances, version 2 for exact non-symmetric brackets.
- Non-symmetric instances get a certified bracket (`zeno/ns.hpp`). Upper points come from link forests in which every plane picks up at most once, or drops off at most once, and from the cheapest balanced role configurations found in the gaps, all scheduled and simulated with their waiting. Lower bounds: lemma R (no assumption), then, under assumption A1-NS (Theorem 6.1), a role relaxation, a Lagrangian relaxation of the per-city balance, and the exact balanced role program (`zeno/roles.hpp`, exponential in t − p, with state, work and time limits in `SolveOptions`). On 1,800 random tiny instances checked against the brute-force oracle every bracket is exact; on larger ones the open gaps are listed with their lower bounds and the reason they stay open.
- `check` verifies a certificate and prints the assumptions it relied on (`S`: symmetric durations; `A1`: central flights no faster than through a hub).
- `pddl` writes a PDDL problem (below); `generate` writes the instance as a data file for `-d`.

Costs and durations are integers. Generated values are multiplied by `-r` and truncated, as in 2016: `-r 100` avoids equal values for slowly growing functions such as log.

# PDDL

`zeno pddl` writes the instance as a PDDL problem (`-O` sets the path) for the domain in `pddl/multi-zeno-travel.pddl`.

- `city0` is the initial city C_I, `city1`…`cityN` are the central cities, `city(N+1)` is the goal city C_G.
- Every person and every plane starts in C_I, and must end in C_G.
- `fly` takes `timeTerre` time units; landing in a city adds its `citythreat` to the total cost (0 for C_I and C_G).
- C_I–i flights last d_i, i–C_G flights last dbar_i (equal to d_i for symmetric instances). A flight between two central cities i and j lasts max(d_i, dbar_i) + max(d_j, dbar_j) + 100, so it is never faster than going through C_I or C_G.
- A plane carries one person at a time. `board` and `debark` are instantaneous: with the ε-separation of PDDL 2.1 a planner's makespan exceeds ZenoSolver's by at most ε per action on the critical path.
- The trailing comments list the durations, the costs and, for symmetric instances, the Pareto front (makespan, cost).

# References

- **True Pareto Fronts for Multi-Objective AI Planning Instances**. *Alexandre Quemy, Marc Schoenauer.* Francesco Chicano and Gabriela Ochoa. European Conference on Combinatorial Optimization - EvoCOP, Apr 2015, Copenhague, Denmark. LNCS 9026, Springer Verlag, pp.197-208, 2015. <hal-01109777>
- **Solving Large MultiZenoTravel Benchmarks with Divide-and-Evolve.** *Alexandre Quemy, Marc Schoenauer, Vincent Vidal, Johann Dréo, Pierre Savéant.* Learning and Intelligent OptimizatioN - LION 9, Jan 2015, Lille, France. LNCS 8994, Springer Verlag, pp.262-267, 2015. <hal-01109776>
