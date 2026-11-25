# Numerical checks of the theory note

Research programs and scripts that checked the statements of `doc/theory/exact-front.md` numerically, before and alongside their Lean proofs. Revision 3 of the note proves every result in Lean and quotes no numerical evidence; the experiments (`experiments/`) still use some of these programs, and the solver's own tests (`tests/`) do not depend on them. Labels below are those of revision 3; the scripts that served only results revision 3 removed were deleted (the git history keeps them).

```sh
doc/theory/checks/build.sh          # compiles the C++ programs into doc/theory/checks/bin
python3 doc/theory/checks/treedp_sweep.py doc/theory/checks 600
```

Every script that runs a program takes this directory as its first argument (it looks for `<dir>/bin/<program>`).

| File | Checks | Statements |
|---|---|---|
| `treedp.cpp`, `treedp_sweep.py` | the link-forest tree DP against enumeration of every multiset and admissible partition, at every level | Thm 6.7, Lemma 2.7 |
| `theorychecks.cpp`, `theorychecks_sweep.py`, `theorychecks_anti.py` | tree DP (all tree sizes and q ≤ q_max), σ-DP, U, U3, the bracket order, closed-form ends, dominance, Pareto variant, each against enumeration; `_anti` uses anti-correlated costs | §6 (Thms 6.7, 6.8, Props 6.4, 6.5; U3 and the Pareto variant of revision 2), Lemmas 2.3, 2.7 |
| `truth.cpp`, `truth_checks.py` | exhaustive search over plans (planes end in C_G; `ANYWHERE=1` lifts it), against the partition front, lemma R and the bridge | Thm 4.5 (both variants), Lemma 3.5, Thm 4.1 |
| `ns_sched_check.py` | the template schedule's closed form and its optimality over interleavings; W1 | Lemma 5.5 (and revision 2's Cor 6.4) |
| `achievability_check.py` | the construction of Theorem 4.1, simulated | Thm 4.1 |
| `linear_closed_form.py` | the closed form of the front of the linear family (Theorem 10.1 of revision 2), used by experiment E9 | — |
| `waiting_search.cpp` | harmful waiting: random balanced role configurations with a plane picking up twice and one dropping off twice, every order and matching, makespan against the largest load (`bin/waiting_search <trials> <seed> [maxPlanes maxLinks maxDuration tight]`) | Prop 5.7 (refutes the papers' no-harmful-waiting assumption) |
| `cpsat_check.py` | `zeno`'s fronts against an independent CP-SAT model of E(T) (admissibility by a parity matrix), at sizes enumeration cannot reach (`python3 cpsat_check.py <zeno> <trials> <seed> [maxN maxT maxP maxD]`, needs `ortools`) | Thm 4.5 via §6 |
| `conj410_search.py` | the converse without A1, first search (before the proof): on random tiny instances whose certificate has a `forest` gap (L < E), the all-plans front with the shortest central flights the triangle inequality allows, looking for a plan inside the gap cheaper than E (`python3 conj410_search.py <dir> <zeno> <trials> <seed> [maxT]`) | Thm 4.4 (then Conj 4.10 of revision 2) |
| `flowplan.py` | exact least cost of a plan with makespan at most M, for any central-flight table: integer plane and passenger flows in the time-expanded network (HiGHS, or CP-SAT), decomposed into routes and journeys and re-simulated. `xval` compares its fronts with `truth` (`python3 flowplan.py xval <dir> <trials> <seed>`). `ex413 [highs\|cpsat]` reproduces Example 4.7 | Thm 4.4, Ex 4.7 |
| `config_front.cpp`, `simple_plans.cpp`, `sd_checks.py` | schedulable domination at the front level: the front of role-configuration schedules (exact waiting, best orders and matching; built on `tests/oracle/bruteForce.hpp`) against the front of all simple plans with clean journeys, any hand-offs and up to `extra` more landings (`simple_plans`), or of all plans (`truth`); `simple_plans ... 0 nowait` gives the same plans' front with waiting ignored (`python3 sd_checks.py <dir> simple\|truth <count> <seed> [uniform\|waiting] [extra]`) | Thm 5.3, Cor 5.6 |
| `sd_full_check.py` | the whole proof of Theorem 5.3 on general plans (central flights under (A1-NS), journeys of several legs, zero durations), every step re-validated and the template simulated as a plan; modes `eo`, `noneo`, `noneo_noZ` for Lemma 6.8 of revision 2 (`python3 sd_full_check.py <trials> <seed> <zero probability> [mode]`) | Thm 5.3 |
| `sd_zero_check.py` | Theorem 5.3 without an event order: random simple plans with clean journeys on instances with cities of d = dbar = 0, a generator biased towards zero-time hand-offs between planes and injected cycles (about 37% of the plans in `strict` mode and 43% in `loose` mode are not event-ordered); the exchanges, cuts and splices of step 2, then steps 3–6, every step re-validated and the template simulated (`python3 sd_zero_check.py <trials> <seed> [strict\|loose] [maxPlanes maxSegments]`) | Thm 5.3, Cor 5.6 |
| `sd_construct_check.py` | the construction in the proof of Theorem 5.3 on random simple plans: exchanges of futures, chains, selection and the template bound | Thm 5.3 |
| `segclass_truth.cpp`, `segclass_search.py` | the exhaustive search of `truth.cpp` with an explicit central table and plans restricted to a class of segments (by start hub, end hub and number of central landings; `IG2` = crossings with one central flight, `GI2` = shuttles, `IG2e` = split crossings, `none` = simple plans), against all plans, on random tiny instances whose (AΔ) table violates (A1-NS) (`bin/segclass_truth <west> <east> <cost> <t> <p> <table> <class> [extra [maxMakespan]]`; `python3 segclass_search.py <bin dir> <trials> <seed> [tight\|random\|mixed\|sparse] [maxT maxP maxN maxD workers classes]`) | Ex 5.10; the class bound and Prop 6.18 of revision 2 |

The exhaustive search (`truth.cpp`) needs durations of at least 1 and caps costs (as revision 2 of the note described).

`flowplan.py` needs `highspy` (`pip install highspy`); the CP-SAT backend of `flowplan.py` and `cpsat_check.py` need `ortools`. Use one of the two solvers per process: HiGHS 1.16 crashed (segmentation fault) after OR-Tools 9.15 had run in the same process.
