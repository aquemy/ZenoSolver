# Erratum: exact Pareto fronts of MultiZenoTravel

*Draft, not published.* This note corrects two papers:

- A. Quemy, M. Schoenauer. *True Pareto Fronts for Multi-Objective AI Planning Instances.* EvoCOP 2015, LNCS 9026, pp. 197–208 (hal-01109777).
- A. Quemy, M. Schoenauer, J. Dréo. arXiv:2304.14659 (2023), which extends the approach to non-symmetric durations.

Both papers present ZenoSolver as computing the *true* Pareto front (total cost, makespan) of MultiZenoTravel instances. Proofs, algorithms and evidence for every statement below are in `doc/theory/exact-front.md`; the numbers can be reproduced with the tests and scripts it cites.

## 1. What is wrong

**The per-PPP schedule is not optimal.**

- Both papers fix a multiset of landings (a PPP) and schedule it greedily: EvoCOP 2015 Algorithm 1, arXiv §3.2. The greedy assigns the longest flights first to the least-loaded plane.
- This schedule can be slower than the best schedule of the same landings, so the front that ZenoSolver reports can miss Pareto points.
- Smallest example: durations d = (6, 10), costs c = (40, 20), t = 5 passengers, p = 2 planes (`tests/golden/data/lpt-counterexample.dat`).
  - The true front has six points.
  - ZenoSolver 2016 prints five: it misses (cost 260, makespan 60).
  - That point lands five times in city 1 and three times in city 2. One plane takes the five city-1 landings (loads 5 × 6 = 30), the other the three city-2 landings (3 × 10 = 30). The makespan is 2 × 30 = 60.
- Other golden instances where the 2016 variants differ from the exhaustive oracle are listed in the git history of `tests/golden/known-bugs.txt`, for example `-n 3 -t 5 -p 2 -C 1 -D 4 -r 10`.

**No fast greedy can fix this in general.**

- Deciding whether a fixed multiset of landings can be flown within a given makespan is strongly NP-complete (note §8, reduction from 3-Partition with p part of the input).
- Unless P = NP, no polynomial rule that schedules each PPP on its own can be exact.

**Non-symmetric durations: waiting can be harmful.**

- arXiv:2304.14659 assumes that no plane needs to wait harmfully for a passenger (in the note's numbering, Conjecture 6.5). This is false, even under the triangle inequality on the flights that exist and with no central flights.
- Example: d = (3, 19) on the C_I side, d̄ = (3, 11) on the C_G side, c = (5, 1), t = 7, p = 4 (note, Proposition 6.5).
  - The cheapest role configuration (drop-offs, pick-ups and crossings per plane) with every plane's load at most 73 costs 14.
  - Every plan of makespan at most 73 costs at least 18.
  - Cause: a plane that must pick up three passengers in city 2 reaches it at time 17, but the first passenger is only dropped there at time 19. The wait shifts all three pick-ups.
- The front computed from role loads is therefore only a lower bound. The exhaustive oracle confirms the true front.

**Bookkeeping errors in the 2016 code** (fixed in 2026, PRs #3 and #4 of the repository):

- the extraction of the Pareto front;
- the update of the front;
- the beta sets for p = 1;
- undefined behaviour on some paths.

## 2. What still holds

- The model, the patterns and the lower bound of 2t − p landings (EvoCOP 2015, Proposition I) hold, the latter in the sense of the front.
- For symmetric durations, with central flights no faster than through a hub (the EvoCOP 2015 assumption, which every generated instance satisfies), the front is the Pareto set of (c(X), M(X)) over landing multisets X of size 2t − p (note, Theorem 4.7 and Corollary 4.8). M(X) is the smallest makespan of an *admissible* partition of X among the planes: in every connected component of the planes-and-cities graph, an even number of planes land an even number of times.

**The default benchmarks are probably unaffected.**

- The generator's default (`-C 3 -D 3`) gives costs affine in durations, c_i + d_i constant. For this family the note proves a closed form of the front (Theorem 10.1).
- The papers' greedy reproduces that front on all 115 small instances checked (Conjecture 10.2). The published fronts of default-generator benchmarks are therefore likely correct, but this is not proved.
- Fronts for the other generator families (log, square root, 2^i, (5/2)i) and for data files can be wrong.

## 3. Replacement

The repository's solver `zeno` (2026) computes the exact front.

**Symmetric instances.**

- A pseudo-polynomial dynamic program over "link forests" (note §7).
- It reproduces all 27 golden fronts of an exhaustive oracle, including the five on which ZenoSolver 2016 was still wrong after its bookkeeping fixes.
- It solves every instance of the benchmark suites within 61 ms. ZenoSolver 2016 finishes 21 of the 66 within 30 s.

**Certificates.**

- Each front can be written with a certificate: one simulated plan per point, plus a lower bound for every gap between consecutive points.
- A checker formally verified in Lean 4 accepts certificates whose gaps are closed by a relaxation that needs no assumption on central flights. This covers every default-generator front and 386 of 400 random fronts. Its soundness theorem is kernel-checked.

**Non-symmetric instances.**

- `zeno` reports a certified bracket: achieved plans above, proved lower bounds below.
- The front is exact wherever the two meet. On 3,700 small random instances checked against the oracle, the bracket closed on all but 3, and it never claimed an inexact front.
- Elsewhere it lists the open gaps and their bounds.

## 4. Not checked

- The arXiv paper's reduction of general flight graphs to the clique model.
- Fronts that third-party papers report as computed by ZenoSolver.
