# Numerical checks of the theory note

The programs and scripts behind the evidence table of `doc/theory/exact-front.md` (§11). They are research code, kept so that every number in the note can be reproduced; the solver's own tests (`tests/`) do not depend on them.

```sh
doc/theory/checks/build.sh          # compiles the C++ programs into doc/theory/checks/bin
python3 doc/theory/checks/treedp_sweep.py doc/theory/checks 600
```

Every script that runs a program takes this directory as its first argument (it looks for `<dir>/bin/<program>`).

| File | Checks | Statements |
|---|---|---|
| `treedp.cpp`, `treedp_sweep.py` | the link-forest tree DP against enumeration of every multiset and admissible partition, at every level | Thm 7.5, Lemma 2.7 |
| `theorychecks.cpp`, `theorychecks_sweep.py`, `theorychecks_anti.py` | tree DP (all tree sizes and q ≤ q_max), σ-DP, U, U3, the bracket order, closed-form ends, dominance, Pareto variant, each against enumeration; `_anti` uses anti-correlated costs | §7 (Thm 7.5–7.6, Props 7.3–7.10), Lemmas 2.4, 2.8 |
| `truth.cpp`, `truth_checks.py` | exhaustive search over plans (planes end in C_G; `ANYWHERE=1` lifts it), against the partition front, lemma R and the bridge | Cor 4.8, Thm 4.9, Lemma 3.4, Thm 4.1 |
| `ds_check.py` | direct selection, shrink and PAR on random simple configurations | Lemmas 4.3–4.5 |
| `ns_sched_check.py` | the template schedule's closed form and its optimality over interleavings; W1 | Lemma 6.3, Cor 6.4 |
| `achievability_check.py` | the construction of Theorem 4.1, simulated | Thm 4.1 |
| `linear_sweep.py`, `linear_closed_form.py` | the linear family: L = E, and the closed form of the front; offset progressions | Thm 10.1 |
| `waiting_search.cpp` | harmful waiting: random balanced role configurations with a plane picking up twice and one dropping off twice, every order and matching, makespan against the largest load (`bin/waiting_search <trials> <seed> [maxPlanes maxLinks maxDuration tight]`) | Prop 6.5 (refutes Conj 6.5) |
| `cpsat_check.py` | `zeno`'s fronts against an independent CP-SAT model of E(T) (admissibility by a parity matrix), at sizes enumeration cannot reach (`python3 cpsat_check.py <zeno> <trials> <seed> [maxN maxT maxP maxD]`, needs `ortools`) | Cor 4.8 via §7 |
| `scale_g.cpp`, `linear_greedy.py` | the papers' greedy on the linear family | Conj 10.2 |

The exhaustive search (`truth.cpp`) needs durations of at least 1 and caps costs as described in the note.
