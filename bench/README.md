# Benchmarks

Every algorithm component has its own benchmark, and every solver is timed end to end on fixed instance suites. A component is not done until its benchmark exists, its baseline is committed, and its measured scaling matches the complexity stated in `doc/theory/exact-front.md`.

## Build and run

```sh
cmake --preset bench                     # Release + Google Benchmark (fetched, v1.9.1)
cmake --build --preset bench --parallel  # all benchmarks and the solvers

build/bench/bm-legacy                                        # one component benchmark
build/bench/bm-legacy --benchmark_out=out.json --benchmark_out_format=json
```

End to end, over suites:

```sh
bench/tools/run_suite.py --exe build/bench/zenoSolver --args=-F \
    --suite bench/instances/regimes.txt --suite bench/instances/families.txt \
    --timeout 30 --repetitions 3 --machine apple-m4-max --out zenoSolver.json
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
| `instances/*.txt` | Suites, one `name\|arguments` line per instance (legacy solver syntax; `@DATA@` is `instances/data`). |
| `instances/data/` | Data files: line 1 durations, line 2 costs. |
| `tools/run_suite.py` | Times an executable over suites: median wall and CPU time, peak RSS of the child, front size, status (`ok`, `timeout`, `error`). |
| `tools/check_regression.py` | Regression gate between two result files. |
| `baselines/<solver>/<machine>/*.json` | Committed reference results. |

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

`baselines/legacy/apple-m4-max/` holds the three 2016 solver variants (`zenoSolver`, `zenoSolver_naive`, `zenoSolver_noDuplicate`) on every suite: Apple M4 Max, 16 cores, macOS, Release build, 30 s timeout per run, median of 3 runs. These are the reference for the speed-up claims of the new solver, and they stay after the legacy solvers are removed. Their fronts are those of the legacy solvers, which are wrong on some instances (`tests/golden/known-bugs.txt`), so `front_size` there is not a correctness reference.

`baselines/zeno/apple-m4-max/zeno.json` holds the exact solver (`zeno`, all cores) under the same conditions. It solves 65 of the 66 instances; on the 21 that the 2016 solvers also finish it is 2 to 5,600 times faster, its slowest run is 2.5 s (`regimes/r5-n100t60p10`), and it times out only on `scaling-D/r10000` (durations near 10^4 with gcd 1: the dense one-plane table spans ~10^5 levels). Its front sizes match the 2016 ones except on the LPT counterexample, where the 2016 solvers miss a point. Process start-up is about 3 ms, the floor of every timing.

## CI

`.github/workflows/bench.yml`:

- **Pull requests**: builds the `bench` preset, runs every component benchmark and the `quick` suite, and writes the comparison with `baselines/*/ci-ubuntu-24.04/` to the job summary. It never blocks: shared runners are noisy.
- **Nightly**: runs everything on the runner named by the repository variable `ZS_BENCH_RUNNER` (default `ubuntu-24.04`; set it to a self-hosted machine for stable numbers) and fails on a regression above 10%. `ZS_BENCH_MACHINE` names the baseline directory to compare with.

To create or refresh the CI baselines, download the `benchmarks` artifact of a run on `master` and commit its files under `baselines/<solver>/<machine>/`.

## Profiling

For a hot component, record a profile and keep the conclusion here, per release:

```sh
# macOS
xcrun xctrace record --template 'Time Profiler' --launch -- build/bench/bm-<component> --benchmark_filter=<name>
# Linux
perf record -g build/bench/bm-<component> --benchmark_filter=<name> && perf report
```
