# Benchmarks

Every algorithm component has its own benchmark, and every solver is timed end to end on fixed instance suites. A component is not done until its benchmark exists, its baseline is committed, and its measured scaling matches the complexity stated in `doc/theory/exact-front.md`.

## Build and run

```sh
cmake --preset bench                     # Release + Google Benchmark (fetched, v1.9.1)
cmake --build --preset bench --parallel  # all benchmarks and the solvers

build/bench/bm-core                                          # one component benchmark
build/bench/bm-core --benchmark_filter=Forest --benchmark_out=out.json --benchmark_out_format=json
```

End to end, over suites:

```sh
bench/tools/run_suite.py --exe build/bench/zeno \
    --suite bench/instances/regimes.txt --suite bench/instances/families.txt \
    --timeout 30 --repetitions 3 --machine apple-m4-max --out zeno.json
```

Compare two result files, failing on a regression above 10% in time or memory, or on a changed front size:

```sh
bench/tools/check_regression.py baseline.json current.json [--threshold 0.10]
```

Both tools read and write the JSON schema of Google Benchmark, so `tools/compare.py` from Google Benchmark also works on them.

## Layout

| Path | Content |
|---|---|
| `components/` | One Google Benchmark executable per component (`bm-<component>`). |
| `support/zs_bench.hpp` | Shared helpers: peak RSS counter, per-iteration counters. |
| `instances/*.txt` | Suites, one `name\|arguments` line per instance (`zeno` instance options; `@DATA@` is `instances/data`). |
| `instances/data/` | Data files: line 1 durations, line 2 costs. |
| `instances/data/airports/` | A non-symmetric instance from real data, Atlanta to Beijing through 11 large airports (OpenFlights, ODbL); in no suite. Its README gives the source and the commands that regenerate it. |
| `tools/run_suite.py` | Times an executable over suites: median wall and CPU time, peak RSS of the child, front size, status (`ok`, `timeout`, `error`). |
| `tools/check_regression.py` | Regression gate between two result files. |
| `tools/time_checker.py` | Times a certificate checker (`zeno check`, or the Lean `zeno-check`) over `*.cert` files: time, peak RSS, size, verdict. |
| `baselines/<solver>/<machine>/*.json` | Committed reference results. |

## Component benchmarks

| Executable | Components | Notes |
|---|---|---|
| `bm-core` | one-plane table (dense and staircase), relaxation L, forest programs U, U3 and exact at one level, end-to-end solve (regimes, families, random, large durations) | complexity fits; states and relaxations per iteration |
| `bm-plan` | dominance reduction, plan simulation per front point, solve with and without plans, certificates (make, write, read, check), PDDL writer, instance builder | plan checking is linear in legs, the PDDL writer quadratic in n |
| `bm-ns` | non-symmetric bracket end to end, Lagrangian balance bound, exact balanced role program, role scheduling | sweeps over n and t − p (the number of links) |

The Lean checker is timed with `tools/time_checker.py` over `lean/test/certificates` (`baselines/lean/apple-m4-max/zeno-check.json`; the C++ reference checker on the same files is in `baselines/zeno/apple-m4-max/zeno-check-cpp.json`). On those 37 certificates, including 12 of format v2, the compiled Lean checker takes 24 ms at the median and 2.4 s at most (`v2-balanced-e1w2`, 19 `balanced` gaps). `baselines/lean/apple-m4-max/zeno-check-v2.json` times it on 152 version 2 certificates of small random non-symmetric instances (3-line data files, `n ≤ 4`, `t ≤ 6`, written by `zeno -d FILE --certificate`): 23 ms at the median, 0.2 s at most apart from `e1w2`, all accepted but the Proposition 6.5 instance, which needs `search`.

`baselines/lean/apple-m4-max/zeno-check-suite.json` times it on the certificates the C++ solver writes for every suite instance (`zeno <args> --certificate FILE` over `instances/*.txt`; 66 certificates, up to 3.9 MB and 240,000 legs for `regimes/r5-n100t60p10`). Every certificate is accepted, at 33 ms at the median and 2.3 s at most (`r5`, 135 MiB peak RSS). Before the checker hoisted the gcd scaling, the one-plane table and the plan's leg list out of its inner loops, and before it restricted the forest bound's state space with Claim B′, the same certificates took 478 s in total: 295 s for `r5` and 48 s for `families/sqrt`. They now take 5.8 s in total.

`baselines/lean/apple-m4-max/zeno-check-many-cities.json` times it on certificates whose cities all survive the dominance merge, written by `zeno -n N -t T -p P -C 2 -D 2 -r 100 --certificate FILE` (the names encode the arguments). There the σ-DP is exponential, and the checker switches to the tree DP. `n20t12p6` (6 forest gaps), `n20t16p4` (5) and `n40t20p8` (2) took more than 120 s with the σ-DP alone. They now take 4.9 s, 6.8 s and 12.5 s; the C++ checker takes 0.04 s at most.

## Counters

Each component benchmark reports what explains its time, as Google Benchmark counters:

- `peak_rss_mib`: peak resident set size of the process;
- states visited and pruned, gap levels, Pareto-set sizes, certificate bytes, where they apply;
- a `Complexity()` fit over the swept parameter, to compare with the stated bound.

The suite runner reports `peak_rss_mib` and `front_size` per instance.

## Suites

| Suite | Content |
|---|---|
| `quick` | Five small instances for pull-request CI. |
| `regimes` | The five regimes of the plan: n=200 t=3 p=2; n=20 t=6 p=2; n=8 t=26 p=25; n=50 t=30 p=5; n=100 t=60 p=10. |
| `paper-table1` | Table 1 of the EvoCOP 2015 paper: n = t = 3…10, p = 2. |
| `families` | The generator families (log, sqrt, identity, power of two, staircase, mixed) on n=10 t=8 p=3. |
| `adversarial` | The LPT counterexample, clustered, near-equal and multiple durations, a 3-Partition gadget. |
| `scaling-n`, `-t`, `-p`, `-D`, `-distinct` | One parameter swept at a time: cities, passengers, planes, duration magnitude, number of distinct durations. |

## Baselines

`baselines/legacy/apple-m4-max/` holds the three 2016 solver variants (`zenoSolver`, `zenoSolver_naive`, `zenoSolver_noDuplicate`) on every suite: Apple M4 Max, 16 cores, macOS, Release build, 30 s timeout per run, median of 3 runs. These are the reference for the speed-up claims of the new solver. The 2016 solvers have since been removed from the code; to rerun them, build commit 84ca92a. Their fronts are those of the legacy solvers, which are wrong on some instances (`tests/golden/known-bugs.txt`), so `front_size` there is not a correctness reference.

`baselines/zeno/apple-m4-max/bm-*.json` are the component benchmarks (median of 3 repetitions; recorded while other builds ran, so treat differences below 20% as noise). `baselines/zeno/apple-m4-max/zeno.json` holds the exact solver (`zeno`, all cores) under the same conditions. It solves all 66 instances, the slowest in 61 ms (`regimes/r5-n100t60p10`); on the 21 that the 2016 solvers also finish it is up to 5,600 times faster. Its front sizes match the 2016 ones except on the LPT counterexample, where the 2016 solvers miss a point. Process start-up is about 3 ms, the floor of every timing. `BM_SolveLargeDurations` in `bm-core` shows the time growing with the logarithm of the level range (3.9 ms for 10^8 levels).

## CI

`.github/workflows/bench.yml`:

- **Pull requests**: builds the `bench` preset, runs every component benchmark and the `quick` suite, and writes the comparison with `baselines/*/ci-ubuntu-24.04/` to the job summary. It never blocks: shared runners are noisy.
- **Nightly**: runs everything on the runner named by the repository variable `ZS_BENCH_RUNNER` (default `ubuntu-24.04`; set it to a self-hosted machine for stable numbers) and fails on a regression above `ZS_BENCH_THRESHOLD` (default 25%, with a 5 ms noise floor `ZS_BENCH_MIN_DELTA_MS`; use 10% on a dedicated runner). `ZS_BENCH_MACHINE` names the baseline directory to compare with; `baselines/zeno/ci-ubuntu-24.04` holds the baselines of GitHub's runner.

To create or refresh the CI baselines, download the `benchmarks` artifact of a run on `master` and commit its files under `baselines/<solver>/<machine>/`.

## Profiling

For a hot component, record a profile and keep the conclusion here, per release:

```sh
# macOS
xcrun xctrace record --template 'Time Profiler' --launch -- build/bench/bm-<component> --benchmark_filter=<name>
# Linux
perf record -g build/bench/bm-<component> --benchmark_filter=<name> && perf report
```
