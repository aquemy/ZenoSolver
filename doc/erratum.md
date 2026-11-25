# Erratum: exact Pareto fronts of MultiZenoTravel

*Draft, not published.* This note corrects two papers:

- A. Quemy, M. Schoenauer. *True Pareto Fronts for Multi-Objective AI Planning Instances.* EvoCOP 2015, LNCS 9026, pp. 197–208 (hal-01109777).
- A. Quemy, M. Schoenauer, J. Dréo. arXiv:2304.14659 (2023), which extends the approach to non-symmetric durations.

Both papers present ZenoSolver as computing the *true* Pareto front (total cost, makespan) of MultiZenoTravel instances. Every error of §1 that concerns mathematics is a numbered result of revision 3 of `doc/theory/exact-front.md` (the note), with its proof, and is machine-checked in Lean 4 (`lean/`); the numbers below are those of revision 3.

## 1. What is wrong

**The per-PPP greedy is not exact** (note, Proposition 4.8).

- Both papers fix a multiset of landings (a PPP) and schedule it greedily, the longest flights first to the least-loaded plane: EvoCOP 2015 Algorithm 1 (the greedy G_E, with its P3 patterns) and arXiv §3.2 (the greedy G_A). The papers state the greedy in these two forms, and do not say how ties between equally loaded planes are broken; the results below hold for every tie-breaking.
- Both greedies miss the point (cost 260, makespan 60) of durations d = (6, 10), costs c = (40, 20), t = 5 passengers, p = 2 planes, with any central flights (`tests/golden/data/lpt-counterexample.dat`).
  - (260, 60) is on the true front. It lands five times in city 1 and three times in city 2: one plane takes the five city-1 landings (loads 5 × 6 = 30), the other the three city-2 landings (3 × 10 = 30). The makespan is 2 × 30 = 60.
  - For every PPP of cost at most 260, G_E, for every set of P3 patterns, and G_A give a makespan above 60. On the landings of (260, 60), G_E without P3 patterns ends with the loads 52 and 68, and every set of P3 patterns gives at least 64.
  - ZenoSolver 2016 prints five of the six points of the front: it misses (260, 60).
- The two greedies differ: only the arXiv greedy misses the point (42, 12) of d = (1, 3), c = (9, 5), t = 4, p = 2, with any central flights (`tests/golden/data/p3-first-counterexample.dat`). For every PPP of cost at most 42, G_A gives a makespan above 12; G_E reaches (42, 12) with one P3 pattern in city 2.
- Other golden instances where the 2016 variants differ from the exhaustive oracle are listed in the git history of `tests/golden/known-bugs.txt`, for example `-n 3 -t 5 -p 2 -C 1 -D 4 -r 10`.

**No polynomial schedule of a fixed PPP can be exact, unless P = NP.**

- Deciding whether a fixed multiset of landings can be flown within a given makespan is as hard as 3-Partition (note, Theorem 7.1, proved in Lean): with 3m cities of durations a_i, B/4 < a_i < B/2 and Σ a_i = mB, p = m planes and t = 2m passengers, the multiset that lands once in every city can be flown within makespan 2B iff the a_i split into m triples of sum B.
- 3-Partition is strongly NP-complete (Garey & Johnson, *Computers and Intractability*, 1979; cited, not formalised), and the reduction writes its instance in polynomial time. So, unless P = NP, no polynomial rule that schedules each PPP on its own can be exact.

**Non-symmetric durations: waiting can be harmful** (note, Proposition 5.7).

- arXiv:2304.14659 reads the front off the role loads, which rules out harmful waiting: a pick-up that must wait for the passenger it collects. This is false, for every table of central flights no faster than a detour through a hub (the paper's assumption for this case).
- Example: d = (3, 19) on the C_I side, d̄ = (3, 11) on the C_G side, c = (5, 1), t = 7, p = 4.
  - The cheapest role configuration (drop-offs, pick-ups and crossings per plane) with every plane's load at most 73 costs 14.
  - Every plan of makespan at most 73 costs at least 18.
  - Cause: in the configuration of cost 14, a plane that must pick up three passengers in city 2 reaches it at time 17, but the first passenger is only dropped there at time 19. The wait shifts all three pick-ups.
- The front computed from role loads is therefore only a lower bound.

**The reduction of general flight graphs does not keep the front** (note, Example 5.9).

- arXiv:2304.14659 §2.4 reduces an arbitrary flight graph to the clique model, with one virtual city for each central vertex i and pair of simple paths I → i and i → G. It claims that the two instances have the same front.
- They do not. Take the path I – a – b – G with durations 1, 2, 1, landing costs 1 and 1, t = 3 passengers and p = 2 planes.
  - The reduced instance has two cities and the front {(8, 10)}, also with any central flights no faster than a detour through a hub. The graph has a plan of cost 8 and makespan 8, so (8, 10) is not on its front.
  - In the plan of makespan 8, one plane flies I → a → b → a → b → G. In this single trip between hubs it drops a passenger at b, flies back to a and picks up another passenger there.
  - The reduced instance has no flights between its virtual cities (the paper sets their durations to infinity), and going through a hub instead takes twice as long, so it cannot express that trip. Relaying passengers is not the issue: in the plan of makespan 8, every passenger changes planes at most once.

**Non-symmetric durations: the shuttle construction misses the front** (note, Example 5.10).

- For central flights faster than any detour through a hub, arXiv:2304.14659 (§2.3 and §3.3) adds a virtual city for each "B Ā B̄" situation: a drop-off at one city, a shuttle C_G → i → j → C_I carrying the passenger to a second city, and a pick-up there. The augmented instance has no central flights, and the paper reads the front off it.
- Example: d = (1, 3), d̄ = (3, 1), c = (6, 1), central flights of duration 2 between the two cities, t = 3, p = 2; the triangle inequality holds.
  - A plan of cost 15 and makespan 8 flies C_I → 2 → 1 → C_G on one plane: it leaves a passenger in city 2 and takes another from city 1.
  - In the augmented instance as printed (equations (3)–(6) and Figure 10), under both readings of its "Ā with a null multiplicity", every configuration has a plane whose patterns last at least 10. So every point of the construction has makespan at least 10, and its front is not the front of the instance.

**Pareto-optimal plans need not land exactly 2t − p times** (note, Example 4.6).

- Both papers' Proposition I says that Pareto-optimal plans land exactly 2t − p times in central cities.
- Example: one city with d = d̄ = 1 and cost 0, t = 5, p = 3, so 2t − p = 7, with any central flight. The front is {(0, 6)}, and a feasible plan with 9 central landings attains (0, 6): every plane flies C_I → 1 → C_G → 1 → C_I → 1 → C_G from time 0.
- Proposition I holds for the front only: under the assumptions of §2, every point of the front is attained by a plan with exactly 2t − p central landings (note, Theorems 4.1 and 4.5).

**Bookkeeping errors in the 2016 code** (fixed in 2026, PRs #3 and #4 of the repository):

- the extraction of the Pareto front;
- the update of the front;
- the beta sets for p = 1;
- undefined behaviour on some paths.

## 2. What still holds

- The model, the patterns and the lower bound of 2t − p patterns in every feasible plan hold (note, Lemma 3.3), and Proposition I in the sense of the front (§1).
- For symmetric durations whose central flights satisfy the hub triangles, d_j ≤ d_i + d_ij and d_i ≤ d_ij + d_j, the front is the Pareto set of (c(X), M(X)) over landing multisets X of size 2t − p (note, Theorems 4.4 and 4.5). The hub triangles follow from the EvoCOP 2015 assumption, central flights no faster than through a hub, and from the triangle inequality (note, Lemma 1.5). M(X) is the smallest makespan of an *admissible* partition of X among the planes: one with a parity matrix, a set of cities for each plane, among those it lands in, whose size has the parity opposite to that of its group, every city lying in an even number of the sets (note, Definition 2.1).

## 3. Replacement

The repository's solver `zeno` (2026) computes the exact front.

**Symmetric instances.**

- A pseudo-polynomial dynamic program over "link forests" (note §6, Theorem 6.7; its step count is Theorem 7.3).
- It reproduces all 27 golden fronts of an exhaustive oracle, including the five on which ZenoSolver 2016 was still wrong after its bookkeeping fixes.
- It solves every instance of the benchmark suites within 61 ms. ZenoSolver 2016 finishes 21 of the 66 within 30 s.
- A second solver, written in Lean, is proved to return the front under symmetric durations and the hub triangles (note, Theorem 6.9).

**Certificates.**

- Each front can be written with a certificate: one simulated plan per point, plus a lower bound for every gap between consecutive points.
- A checker formally verified in Lean 4 accepts certificates whose gaps are closed by a relaxation that needs no assumption on central flights, or by the exact bound under the hub triangles (note, Theorem 8.2). The relaxation alone closes 386 of 400 random fronts. Its soundness theorem is kernel-checked.

**Non-symmetric instances.**

- `zeno` reports a certified bracket: achieved plans above, proved lower bounds below. Its certificates have a second format, with a checker also verified in Lean (note, Theorem 8.7).
- The front is exact wherever the two meet. On 3,700 small random instances checked against the oracle, the bracket closed on all but 3, and it never claimed an inexact front.
- Elsewhere it lists the open gaps and their bounds.

## 4. Not checked

- Fronts that third-party papers report as computed by ZenoSolver.

The arXiv paper's reduction of general flight graphs to the clique model, listed here before, has been checked since. It does not keep the front (§1; note, Example 5.9).
