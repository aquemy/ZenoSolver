# Seeded validation campaign

Ten experiments that test the statements of `doc/theory/exact-front.md` against references written independently of the solver. Each `EN_name/run.py` is deterministic (`SEED = 0`), calls the repository's binaries and the research programs of `doc/theory/checks` (read-only), and writes to `results/EN_name/`:

- `summary.json`: the verdict (`passed`, `criterion`, `metrics`, `sizes`, `hypothesis`, `explanation`), the claim slugs it `tests` and `refutes`, and the figures;
- `manifest.json`: provenance (git sha, time, runtime, host, versions, sha256 of every binary used);
- `*.png`, `*.svg`: the figures.

Shared code is in `common.py`: instances and data files, running `zeno`, `zenoOracle`, `truth`, an independent plan simulator, Wilson intervals, the figure style and the verdict writer.

## Running

```sh
cmake --preset release && cmake --build --preset release -j   # zeno, zenoOracle (built on demand if missing)
(cd lean && lake build zeno-check zeno-front)                  # Lean checker and solver (E3, E8)
cd experiments
uv sync
uv run python E1_achievability/run.py                          # any experiment; exit code 0 = pass
```

The programs of `doc/theory/checks` are compiled into `build/checks/bin`, and E10's greedy into `build/experiments/bin`. `ZS_EXPERIMENT_WORKERS` sets the parallelism (default: cores - 2). E7 times single runs that use all cores, so run it alone.

## Experiments

| Experiment | Tests | Reference | Pass criterion |
|---|---|---|---|
| E1 achievability | `thm-4-1` | independent simulator of `zeno --plans` | every plan reaches exactly its front point |
| E2 symmetric front | `thm-4-7`, `cor-4-8` | `truth` (all plans; central flights none or useless), `zenoOracle` | equal fronts wherever the reference finishes |
| E3 forest DP | `thm-7-5` | CP-SAT model of E(T) (`checks/cpsat_check.py`); Lean `zeno-front` | E(T) equal at every front level and the level below the next point; same Lean front |
| E4 non-symmetric front | `thm-6-1`, `thm-6-9`, `cor-6-10` | `truth`, `simple_plans` (all simple plans, s+1 landings), `config_front` | role-configuration front = all-plans front; zeno equal whenever it closes its bracket |
| E5 harmful waiting | `prop-6-5`; refutes `paper-no-harmful-waiting` | `simple_plans ... nowait`, `config_front`, `zenoOracle`, `waiting_search` | on Prop 6.5's instance: 14 within makespan 73 when waiting is ignored, 18 with waiting |
| E6 converse without (A1), search | `thm-4-10` (formerly `conj-4-10`) | `truth ... tight` on instances whose certificate has a `forest` gap | 0 plans cheaper than E inside a forest gap (a targeted search, not a proof) |
| E7 scaling | `cor-8-3` | wall time, `--stats` | sweeps finish; time grows at most as levels^2 with the duration scale; frontier of (n, t, p) with timeouts |
| E8 certificates | `thm-9-1` | corpus, fresh certificates, 7 kinds of mutants; `zeno check` and Lean `zeno-check` | no checker accepts a false front, a plan the simulator rejects, or a missing assumption |
| E9 linear family | `thm-10-1` | closed form of Theorem 10.1 | zeno's front = the closed form; no certificate needs the forest bound |
| E10 greedy density | `paper-greedy-optimal` (refuted), `conj-10-2` | EvoCOP 2015 Algorithm 1 reimplemented (`E10_greedy_density/greedy.cpp`), validated on the golden instances | the reimplementation fails exactly on `lpt-counterexample` and `n3t5p2-C1D4r10`; reports the share of exact fronts by n, t, p, and the linear family separately |

A pass on a search (E6, and E10 on the linear family) is evidence on the sampled instances, not a proof.
