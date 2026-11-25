# Revision 3 of the theory note: the statement map

This file is the contract for revision 3 of `doc/theory/exact-front.md` (work package WP0 of the plan
"a lean theory, every result fully machine-checked"). For every numbered result of the current note
(revision 2) it says whether the result stays, in which words, under which new number, which Lean
declarations prove it and which work package supplies the Lean that is missing. WP1–WP6 deliver the
Lean, WP7 rewrites the note from Table A, WP8 updates `claims.toml`, and the renumbering script reads
Table C.

## 1. Rules

**Decisions of the user.**

1. *Complexity.* The reductions and the step count of the DP are proved in Lean. The strong
   NP-hardness of 3-Partition (Garey–Johnson) is the only cited fact. It appears in a remark, never
   inside a numbered statement.
2. *General graphs.* Example 6.11 stays and is proved, with a minimal flight-graph model.
   Propositions 6.12–6.16 go.
3. *§10 and the generators.* Removed completely: Theorem 10.1, Conjecture 10.2 and every claim about
   generator families (the scope sentence of §1.3, paper E9, the linear-family split of E10).
4. *Numbering.* Consecutive within each section, one counter shared by all kinds (definitions,
   lemmas, theorems, propositions, corollaries, examples), as the note does now.

**Keep rule.** A result stays only if it

* is on the proof path of a headline theorem: H1 the symmetric front (Theorem 4.5), H2 the verified
  solver (Theorem 6.9), H3 the sound checkers (Theorems 8.2 and 8.7), H4 the non-symmetric front
  (Corollary 5.6);
* or justifies a shipped certificate kind or a step of the verified solver;
* or refutes a claim of the 2015/2023 papers that the revised paper corrects.

§7 (complexity) is kept by decision 1, not by this rule. The C++ solver is untrusted: its
optimisations are checked per run by certificates and need no theorem.

**Strict status rule.** A result counts as machine-checked only if Lean proves every assertion of its
statement, with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. Concrete computations
are proved by kernel `decide` (`decide +kernel`), never `native_decide`, which `CheckAxioms` rejects.
Each final statement below says exactly what the most direct proof gives and nothing that is unused
downstream; for a narrowed row it is the Lean statement in mathematical words.

**Slug policy.** Slugs stay as stable IDs, so the CKC history stays valid. A new `label` field
carries the new number, and everything user-visible uses the label. A result new to the note gets a
descriptive slug `<kind>-<description>`, the kind read from its new label (`def`, `lem`, `thm`,
`prop`, `cor`), following the rule of the `claims.toml` header for statements the note does not
number (`claim-converse-s-only`). In a merge the first slug listed survives and carries the label;
the others are archived with `removed = "2026-11-25: merged into <slug>"`. Removed results are
archived with `removed = "2026-11-25: <reason>"` (Table B).

**Model.** The note's model becomes Lean's model: natural-number durations, times and costs; a
complete central table `dc(i, j)` for every ordered pair of central cities, `i = j` included, read as
directed durations; Lean's passenger condition (Definition 1.2); and a rounding lemma for rational
or real times (Lemma 1.3).

**Conventions of Table A.**

* *Action.* `keep`: the old statement stays (possibly reworded to Lean's form). `narrow`: the
  statement is cut down, to what Lean proves or to what later proofs use. `merge`: several old
  statements become this one. `wrap`: the statement stays and Lean needs a short corollary of
  existing declarations. `new`: the statement is not in the current note (the code uses it, or the
  plan adds it).
* *Lean.* Every name is in the namespace `ZenoFront`, in `lean/ZenoFront/<File>.lean`. Names
  without a mark exist today (checked against the source of `origin/master` at `89fd9fa`);
  `planned:` names are proposals for the work package, not existing declarations.
* *WP.* The work package that supplies the missing Lean. `—` means the Lean is complete; the row then
  needs only WP7 (text) and WP8 (ledger).
* *Conditional rows.* `cond. WP3`: the row stands or falls with WP3's decision on the σ-DP.
  `remove if WP4 confirms Corollary 5.4 from Theorem 5.3`: Lemmas 5.11 and 5.12. Such rows sit last in
  their section where possible, so that removing them shifts few labels; if one goes, the section is
  renumbered consecutively and Table C regenerated.
* *Notation.* `s = 2t − p`; `e_i = min(d_i, d̄_i)`; `δ(Y) = Σ_{w∈Y} d_w`, `δ̄(Y) = Σ_{w∈Y} d̄_w`,
  `e(Y)` likewise; `c(Y)` the cost of a multiset and |Y| its size; `F_k` the flight time of plane
  `k`; `(H)` the hub triangles of Definition 1.4.

## 2. New outline

Sections and subsections of §1 keep their numbers; §2–§8 have no subsections.

* **§1 Model.** Definition 1.1 (instance), Definition 1.2 (plan), Lemma 1.3 (rounding times),
  Definition 1.4 (assumptions), Lemma 1.5 (hub triangles), Definition 1.6 (fronts), Lemma 1.7
  (dominating sets), *Notation*. §1.3 (PDDL semantics) is prose that claims nothing.
* **§2 Admissible partitions.** Definition 2.1 (admissible partition), Lemma 2.2 (integer form),
  Lemma 2.3 (disjoint groups), Lemma 2.4 (row bound), Definition 2.5 (link forest), Lemma 2.6 (link
  forests), Lemma 2.7 (few touched cities, cond. WP3).
* **§3 Counting and bounds.** *Segments* (paragraph), Lemma 3.1 (crossings outnumber returns),
  Lemma 3.2 (chains), Lemma 3.3 (counting), Lemma 3.4 (segment durations), Lemma 3.5 (relaxation),
  Proposition 3.6 (makespan and cost lower bounds).
* **§4 Symmetric front.** Theorem 4.1 (achievability), Lemma 4.2 (adding a plane), Lemma 4.3
  (shrinking), Theorem 4.4 (converse under (S) and (H)), Theorem 4.5 (symmetric front, H1), Example
  4.6 (an optimal plan with extra landings), Example 4.7 ((H) cannot be dropped), Proposition 4.8 (the
  papers' greedy is not exact).
* **§5 Non-symmetric front.** Definition 5.1 (role configuration), Definition 5.2 (scheduled
  configuration, template value), Theorem 5.3 (schedulable domination), Corollary 5.4 (role-load
  bound), Lemma 5.5 (template achievability), Corollary 5.6 (non-symmetric front, H4), Proposition
  5.7 (harmful waiting), Definition 5.8 (flight graphs, the reduction), Example 5.9 (the reduction
  misses the front), Example 5.10 (the shuttle construction misses the front), Lemma 5.11 (records
  give a configuration) and Lemma 5.12 (shrinking role configurations), both to be removed if WP4
  confirms Corollary 5.4 from Theorem 5.3.
* **§6 Algorithm.** Lemma 6.1 (one-plane table), Lemma 6.2 (the function E), Proposition 6.3 (front
  = breakpoints of E), Proposition 6.4 (bracket), Proposition 6.5 (dominance, symmetric), Proposition
  6.6 (dominance, non-symmetric), Theorem 6.7 (link-forest DP), Theorem 6.8 (σ-DP, cond. WP3),
  Theorem 6.9 (verified solver, H2).
* **§7 Complexity.** Theorem 7.1 (3-Partition reduction), Proposition 7.2 (Partition reduction for
  p = 2), Theorem 7.3 (step count of the DP).
* **§8 Certificates.** Theorem 8.1 (obligations imply the front), Theorem 8.2 (v1 checker, H3),
  Propositions 8.3–8.6 (the `roles`, `lagrangian`, `balanced` and `search` bounds), Theorem 8.7 (v2
  checker, H3).

## 3. Table A: kept results

59 rows: 8 keep, 31 narrow, 4 merge, 3 wrap, 13 new. Four slugs are archived by merges: `thm-4-7`,
`conj-4-10`, `thm-4-9`, `cor-4-12`. Eighteen slugs are new.

### §1 Model

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Definition 1.1 (instance) | §1.1 | `def-instance` (new) | narrow | Central cities 1, …, n and hubs C_I, C_G; durations d_i (C_I–i) and d̄_i (i–C_G) in ℕ and a central duration dc(i, j) ∈ ℕ for every ordered pair of central cities, i = j included; no flight joins the two hubs. Landing in i costs c_i ∈ ℕ, hubs are free; p planes and t passengers start in C_I. Theorems assume 1 ≤ p ≤ t where they use it. | Plan.lean: `Network`, `Network.duration` | — |
| Definition 1.2 (plan) | Definition (plan); §1.2 | `def-plan` (new) | narrow | A plan gives each plane a list of legs (origin, destination, departure, arrival, passenger or none). It is feasible if every leg is a flight of exactly its duration, each plane's legs form a route from C_I (each leg leaves where the previous one arrived, no earlier, the first at time ≥ 0) ending in C_G, and for each passenger the legs naming it form, in some order, such a route from time 0 ending in C_G. Cost: the landing costs of all legs into central cities; makespan: the latest end of a route; in the variant with planes ending anywhere, routes need not end in C_G. | Plan.lean: `Leg`, `Plan`, `Flies`, `IsRoute`, `PlaneFeasible`, `Feasible`, `planCost`, `planMakespan`; Checker.lean: `achievable`; Bridge.lean: `PlaneFeasibleAnywhere`, `FeasibleAnywhere`, `achievableAnywhere` | — |
| Lemma 1.3 (rounding times) | — (the times in 𝕂 of §1.1) | `lem-rounding` (new) | new | Let a plan have times in ℚ or ℝ, integer durations, and satisfy Definition 1.2. Rounding every time down gives a feasible plan with natural-number times, the same cost and a makespan at most the original one; conversely an integer plan is such a plan with the same cost and makespan. | RationalPlans.lean: `QFeasible`, `QFeasible.floor`, `qPlanCost_eq`, `planMakespan_floor_le`, `Feasible.toRat` (over ℚ); planned: the same over any `FloorRing`, generalising `QFeasible.floor`, in RationalPlans.lean | WP2 |
| Definition 1.4 (assumptions) | §1.4 | `def-assumptions` (new) | narrow | (S) d̄ = d. (A1) d_i + d_j ≤ dc(i, j). (A1-NS) min(d_i + d_j, d̄_i + d̄_j) ≤ dc(i, j). (AΔ) dur(a, b) ≤ dur(a, x) + dur(x, b) whenever a ≠ b and the three flights exist. (H) d_j ≤ d_i + dc(i, j) and d_i ≤ dc(i, j) + d_j for all central i, j (the triangles through C_I, and under (S) through C_G). | hypothesis `N.dbar = N.d`; Converse.lean: `Network.A1`; NonSymmetric.lean: `Network.A1NS`; TriSegments.lean: `Network.ATri`, `Network.ATriHub` | — |
| Lemma 1.5 (hub triangles) | — | `lem-hub-triangles` (new) | new | (A1) implies (H), and (AΔ) implies (H). | TriSegments.lean: `Network.A1.hub`, `Network.ATri.hub` | — |
| Definition 1.6 (fronts) | §1.5 | `def-front` (new) | keep | Points (cost, makespan) are ordered componentwise, and y weakly dominates z when y ≤ z. Min S is the set of minimal points of S; the front is F = Min A, A (A′) the points of the feasible plans (of the plans whose planes end anywhere). A list is the Pareto front of S if its points lie in S, weakly dominate every point of S and are pairwise incomparable. | Checker.lean: `achievable`, `IsParetoFront`; Bridge.lean: `achievableAnywhere`; Mathlib `Minimal` | — |
| Lemma 1.7 (dominating sets) | Lemma 1.1 | `lem-1-1` | narrow | (a) If every point of A is weakly dominated by a point of B and every point of B by a point of A, then Min A = Min B; in particular when B ⊆ A and B dominates A. (b) A list that is the Pareto front of S lists exactly Min S. | Achievability.lean: `minimal_iff_of_dominated`; Bridge.lean: `minimal_iff_of_subset_of_dominated`; Checker.lean: `IsParetoFront.mem_iff_minimal` | — |

### §2 Admissible partitions

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Definition 2.1 (admissible partition) | Definition 2.2 | `def-2-2` | keep | A partition of a multiset X over p planes is a family of groups X_1, …, X_p with Σ_k X_k = X. A parity matrix gives each plane k a set η_k of cities of X_k with \|η_k\| ≡ \|X_k\| + 1 (mod 2), every city lying in an even number of the η_k. The partition is admissible if it has a parity matrix. | Admissible.lean: `IsParityWitness`, `Admissible` | — |
| Lemma 2.2 (integer form) | Lemma 2.3 | `lem-2-3` | wrap | A partition is admissible iff some h̃ ∈ ℕ^{p×n} has h̃_{k,i} ≤ X_k(i), Σ_i h̃_{k,i} ≡ \|X_k\| + 1 (mod 2) for every plane k, and Σ_k h̃_{k,i} even for every city i. | planned: `admissible_iff_exists_natWitness` in Admissible.lean | WP2 |
| Lemma 2.3 (disjoint groups) | Lemma 2.4 | `lem-2-4` | narrow | If no city lies in two groups, the partition is admissible iff every group has odd size. | planned: `admissible_iff_odd_of_disjoint` in Complexity.lean | WP6 |
| Lemma 2.4 (row bound) | Lemma 2.5 | `lem-2-5` | keep | For every parity matrix and plane k, \|η_k\| + 1 ≤ \|X_k\|. Hence the groups of an admissible partition are non-empty, and \|X\| ≡ p (mod 2). | Admissible.lean: `IsParityWitness.card_add_one_le`, `Admissible.card_pos`; Shrink.lean: `IsParityWitness.size_mod_two` | — |
| Definition 2.5 (link forest) | Definition (link forest) | `def-link-forest` (new) | keep | A rooted link tree is a plane with a multiset of free landings and a list of children, each hung from it by a link labelled with a city; the group of a plane is its free landings, one copy of each child's label and one copy of its parent's label, so (F1) holds by construction. (F2): every plane has an odd number of free landings. A link forest of a partition is a list of such trees satisfying (F2) whose groups are the partition's groups, up to relabelling the planes. | LinkForest.lean: `LTree`, `LKids`, `LTree.groups`, `LTree.WF`, `forestGroups` | — |
| Lemma 2.6 (link forests) | Lemma 2.6 | `lem-2-6` | narrow | A partition is admissible iff it has a link forest. | TreeExact.lean: `admissible_iff_exists_linkForest`, `admissible_forestPartition`; LinkForest.lean: `Admissible.exists_linkForest` | — |
| Lemma 2.7 (few touched cities) | Lemma 2.8 | `lem-2-8` | narrow (cond. WP3) | An admissible partition with \|X\| = s has a parity matrix whose sets η_k together contain at most min(p − 1, t − p) cities. | MinimalWitness.lean: `Admissible.exists_card_touched_le`, `IsParityWitness.card_touched_le_of_minimal`; SupportBound.lean: `IsParityWitness.card_touched_le` | WP3 |

### §3 Counting and bounds

*Segments* (unnumbered paragraph, moved from §2): the segments of a route are its parts between
consecutive hub arrivals (Lean `hubArrivals`), of types A, Ā, B, B̄ by their end hubs.

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Lemma 3.1 (crossings outnumber returns) | Lemma 2.1 | `lem-2-1` | narrow | Record every central landing of a route with whether its incoming leg leaves C_I and whether its outgoing leg arrives in C_I (a central outgoing leg counts as towards C_G). On a route from C_I to C_G, the records of type A (from C_I, not back to C_I) number one more than those of type Ā (not from C_I, back to C_I). On a route without central flights the records are its segments. | Converse.lean: `landingRecs`, `cntA`, `cntAbar`, `PlaneFeasible.cntA_eq`; visit form: Rewire.lean: `TRoute.countP_isA`; SchedBuild.lean: `VRoute.countP_isA` | — |
| Lemma 3.2 (chains) | Lemma 3.1 | `lem-3-1` | narrow | (a) In a feasible plan, and in a plan whose planes end anywhere, every passenger rides a chain: legs carrying it, the first leaving C_I, each leaving where the previous one arrived and no earlier, landing in central cities until the last, which arrives in C_G. (b) If the plan has no central flight, every passenger rides a leg C_I → x and then a leg x → C_G leaving no earlier than the first one arrives. | ConverseTri.lean: `ToGoal`, `exists_chain`, `Feasible.exists_chains`; FrontTri.lean: `FeasibleAnywhere.exists_chains`, `ToGoal.dst_ne_ci`; Domination.lean: `exists_transfer_pw` | — |
| Lemma 3.3 (counting) | Lemma 3.2 | `lem-3-2` | narrow | In a feasible plan, 2t ≤ Σ_k h_k + p, where h_k is the number of hub arrivals (segments) of plane k. | PlanBounds.lean: `ciDepartures_add_cgArrivals`, `Feasible.le_ciDepartures`, `Feasible.le_cgArrivals`, `Feasible.le_sum_hubArrivals` | — |
| Lemma 3.4 (segment durations) | Lemma 3.3 | `lem-3-3` | narrow | (a) A feasible plane has a multiset Z of central cities with \|Z\| equal to its number of hub arrivals, 2e(Z) ≤ its end time and c(Z) ≤ its landing cost. (b) Under (S) and (H) its route is the concatenation of its segments, one per hub arrival, each landing in a central city and flying at least 2d_y for every central city y it lands in; and a chain from a central city y ends at least d_y after it starts. (c) On a route without central flights the two legs of a central landing at x last its role weight, d_x + d̄_x for a crossing, 2d_x for a drop-off and 2d̄_x for a pick-up, so the role weights sum to at most the flight time. | PlanBounds.lean: `PlaneFeasible.exists_segments_emin`, `PlaneFeasible.exists_segments`; TriSegments.lean: `PlaneFeasible.exists_segments_tri`, `segment_bound`; FrontTri.lean: `ToGoal.add_d_le_endTime`, `ToGoal.arr_add_d_le`; SchedBuild.lean: `VOK.w_eq`, `VChain.sum_w_le`; NonSymmetric.lean: `roleW_landingRecs_le` | — |
| Lemma 3.5 (relaxation) | Lemma 3.4; the `relaxed` kind of format v2 | `lem-3-4` | merge | Let p ≤ t. Every feasible plan with cost C and makespan M has non-empty multisets Y_1, …, Y_p with Σ_k \|Y_k\| = s, c(Y_1 + ⋯ + Y_p) ≤ C and 2e(Y_k) ≤ M for every k; under (S), e = d. Hence C ≥ L_e(⌊M/2⌋), where L_e(T) is the least Σ_k min{c(Y) : \|Y\| = m_k, e(Y) ≤ T} over m_1, …, m_p ≥ 1 with Σ_k m_k = s (∞ if none). | PlanBounds.lean: `Network.emin`, `Network.emin_eq_of_sym`, `exists_trim`, `Feasible.exists_relaxation_emin`, `Feasible.exists_relaxation`; Relaxation.lean: `relaxCost`, `relaxCost_oneplane_le_totalCost`; planned: `Feasible.relaxCost_le_planCost` in Relaxation.lean | WP2 |
| Proposition 3.6 (lower bounds) | Proposition 7.10 (a), (b), lower halves | `prop-7-10` | narrow | Let p ≤ t. Every feasible plan costs at least s·c_min. Under (S) and 1 ≤ p, every feasible plan has makespan at least 2d_min⌈s/p⌉. | Checker.lean: `minOf`, `Feasible.minOf_le_cost_emin`, `Feasible.minOf_le_cost`, `Feasible.minOf_le_makespan` | — |

### §4 Symmetric front

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Theorem 4.1 (achievability) | Theorem 4.1 | `thm-4-1` | narrow | Assume (S) and p ≤ t. Every admissible partition X_1, …, X_p with \|X\| = 2t − p is flown by a feasible plan whose planes land exactly at the groups (up to relabelling the planes), of cost c(X) and makespan 2·max_k δ(X_k). | Achievability.lean: `Admissible.exists_plan`, `admissiblePoints_subset_achievable` | — |
| Lemma 4.2 (adding a plane) | Lemma 4.6 | `lem-4-6` | keep | An admissible partition of q planes with 2t − q landings, t ≥ q + 1, gives an admissible partition of q + 1 planes with 2t − q − 1 landings, no larger cost, and loads bounded by every bound on the old loads; repeating, one of p planes for any q ≤ p ≤ t. | AddPlane.lean: `Admissible.addPlane`, `Admissible.addPlane_of_size`, `Admissible.addPlanes`; Bridge.lean: `Admissible.addPlanes_le` | — |
| Lemma 4.3 (shrinking) | Lemma 4.11 | `lem-4-11` | keep | If X is admissible with at least s landings, p ≤ s and s ≡ p (mod 2), some admissible Y with Y_k ≤ X_k for every k has exactly s landings; in particular two landings can be removed when \|X\| ≥ p + 2. | Shrink.lean: `Admissible.exists_shrink`; TriSegments.lean: `Admissible.exists_remove_two` | — |
| Theorem 4.4 (converse under (S) and (H)) | Theorem 4.10; Theorem 4.7; Conjecture 4.10 | `thm-4-10`; `thm-4-7`, `conj-4-10` (archived: merged) | merge | Assume (S), (H) and p ≤ t. If every plane flies from C_I to C_G and every passenger rides a chain (Lemma 3.2), some admissible partition X_1, …, X_p has \|X\| = 2t − p, c(X) at most the plan's cost and 2δ(X_k) ≤ F_k for every plane. In particular this holds for every feasible plan, where F_k ≤ M. | ConverseTri.lean: `exists_merge`, `exists_admissible_of_chains`, `PlaneFeasible.durSum_le_planMakespan`, `Feasible.exists_admissible_hub`, corollaries `Feasible.exists_admissible_ATri`, `Feasible.exists_admissible_A1_flightTime`; TriCore.lean: `TriCore.exists_tjoin`, `TriCore.exists_selection`, `exists_admissible_of_blocks` | WP1 (callers, delete `Feasible.exists_admissible`) |
| Theorem 4.5 (symmetric front, H1) | Corollary 4.8; Theorem 4.9; Corollary 4.12 | `cor-4-8`; `thm-4-9`, `cor-4-12` (archived: merged) | merge | Assume (S), (H) and p ≤ t. The feasible plans, the plans whose planes end anywhere, the admissible partitions of 2t − p landings (points (c(X), 2·max_k δ(X_k))) and the multisets of 2t − p landings that have an admissible partition (points (c(X), M(X)), M(X) the least 2·max_k δ(X_k) over them) have the same minimal points: F = Min A′ = Min 𝒫 = Min 𝒳. | Achievability.lean ((A1)): `admissiblePoints`, `multisetPoints`, `minMakespan`, `minimal_admissiblePoints_iff_multisetPoints`, `minimal_achievable_iff_admissiblePoints`, `minimal_achievable_iff_multisetPoints`, `minimal_achievable_iff_anywhere_of_A1`; FrontTri.lean ((AΔ)): `FeasibleAnywhere.exists_admissible_hub`, `minimal_achievable_iff_admissiblePoints_ATri`, `minimal_achievable_iff_multisetPoints_ATri`, `minimal_achievable_iff_anywhere_of_ATri`; planned: `minimal_achievable_iff_admissiblePoints_hub`, `minimal_achievable_iff_multisetPoints_hub`, `minimal_achievable_iff_anywhere_hub` in FrontTri.lean | WP1 |
| Example 4.6 (an optimal plan with extra landings) | — (the remark after Corollary 4.8) | `claim-extra-landings` (new) | new | Take n = 1, d_1 = 1, c_1 = 0, t = 5, p = 3, symmetric durations and any central table, so (H) holds. The front is {(0, 6)}, and a feasible plan with 9 central landings, more than s = 7, attains (0, 6). So a Pareto-optimal plan need not have exactly 2t − p landings: the papers' Proposition I holds only in the sense of Theorem 4.5. | planned: `extraLandings_plan_feasible` (`planOK` by `decide +kernel`, then `planOK_feasible`) and `extraLandings_front` (`solveFront` by `decide +kernel`, then Theorem 6.9) in Counterexamples.lean | WP5 |
| Example 4.7 ((H) cannot be dropped) | Example 4.13 | `claim-4-13` | narrow | Take d = (2, 3, 9, 11), c = (50, 44, 17, 0), t = 6, p = 3 and the symmetric central table dc_12 = 1, dc_13 = 5, dc_14 = 6, dc_23 = 3, dc_24 = 6, dc_34 = 1 (dc_ii arbitrary). (S) holds and (H) fails (d_4 > d_3 + dc_34). The plan of the note is feasible, of cost 260 and makespan 39, while every admissible partition of 9 landings with every δ(X_k) ≤ 19 costs at least 264, so none has cost ≤ 260 and makespan ≤ 39: the conclusion of Theorem 4.4 fails, and no point of 𝒫 weakly dominates (260, 39). | planned: `hubCounterexample_feasible` (needs a feasibility check that accepts central legs; `planOK` accepts hub legs only), `hubCounterexample_minCost` (the bound 264 at level 19 by `decide +kernel` through `treeBoundAt_eq_minCost`) in Counterexamples.lean | WP5 |
| Proposition 4.8 (the papers' greedy is not exact) | §5 | `claim-5` | narrow | Let G be the per-PPP greedy of EvoCOP 2015 Algorithm 1 (longest durations first, to the least-loaded plane) and F_G the Pareto set of its points. (a) For d = (6, 10), c = (40, 20), t = 5, p = 2, (260, 60) ∈ F and no point of F_G weakly dominates it (on the landings of that point G ends at 68). (b) For d = (1, 3), c = (9, 5), t = 4, p = 2, (42, 12) ∈ F and no point of F_G weakly dominates it. | Examples.lean: `Examples.lptCounterexample_check`, `Examples.lptCounterexample_front`; planned: `greedy`, `greedy_misses_260_60`, `greedy_misses_42_12` and a front certificate for (b) in Counterexamples.lean | WP5 |

### §5 Non-symmetric front

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Definition 5.1 (role configuration) | Definition 4.2 | `def-4-2` | keep | A role configuration on p planes gives each plane multisets Dr_k (drop-offs), Pk_k (pick-ups) and Cr_k (crossings) of central cities, with \|Cr_k\| odd and Σ_k Dr_k = Σ_k Pk_k. Its groups are X_k = Dr_k + Pk_k + Cr_k, its cost is c(X), and the role load of plane k is λ_k = 2δ(Dr_k) + 2δ̄(Pk_k) + δ(Cr_k) + δ̄(Cr_k). The passenger count is read through the landings, \|X\| = 2t − p. | Roles.lean: `RoleConfig`, `RoleConfig.groups`; NonSymmetric.lean: `RoleConfig.roleLoad` | — |
| Definition 5.2 (scheduled configuration, template value) | — (§6.2: orders, link matching; the formula of Lemma 6.3) | `def-scheduled-config` (new) | new | A scheduled configuration gives each plane an ordered list of drop-offs, an ordered list of pick-ups and a multiset of crossings, and matches every pick-up slot to a drop-off slot; it is valid if every \|Cr_k\| is odd and the matching is a bijection between pick-up and drop-off slots of the same city. Its template value is M_tmpl = max(max_k λ_k, max over links (u, j; v, l) at x of Pre_u(j) + d_x + d̄_x + Suf_v(l)), with Pre_u(j) = 2Σ_{j′<j} d(Dr_u[j′]) and Suf_v(l) = 2Σ_{l′>l} d̄(Pk_v[l′]). | SearchGap.lean: `Sched`, `Sched.Valid`, `Sched.size`, `Sched.cost`, `Sched.load`, `Sched.pre`, `Sched.suf`, `Sched.term`, `Sched.tmpl` | — |
| Theorem 5.3 (schedulable domination) | Theorem 6.9 | `thm-6-9` | narrow | Assume (A1-NS) and p ≤ t. Every feasible plan with cost C and makespan M gives a valid scheduled configuration with 2t − p landings, cost at most C and M_tmpl ≤ M. | DominationAll.lean: `schedulableDomination_all`; NonSymmetric.lean: `Feasible.split`; Domination.lean: `exists_transfer_pw`; Rewire.lean: `exists_rewired`; LinkCount.lean: `exists_links`; SchedBuild.lean: `exists_sched_of` | — |
| Corollary 5.4 (role-load bound) | Theorem 6.1 | `thm-6-1` | narrow | Assume (A1-NS) and p ≤ t. Every feasible plan with cost C and makespan M gives a role configuration with 2t − p landings, cost at most C and every λ_k ≤ M. | NonSymmetric.lean: `Feasible.exists_roleConfig_ns`; planned: `Sched.load_le_tmpl` in SearchGap.lean and `Sched.toRoleConfig`, to derive it from Theorem 5.3 | WP4 |
| Lemma 5.5 (template achievability) | Lemma 6.3 | `lem-6-3` | narrow | Let p ≤ t. For every central table and every valid scheduled configuration S with 2t − p landings, some feasible plan has cost c(S) and makespan at most M_tmpl(S). | planned: `Sched.exists_plan` in Template.lean | WP4 |
| Corollary 5.6 (non-symmetric front, H4) | Corollary 6.10 | `cor-6-10` | narrow | Assume (A1-NS) and p ≤ t. F = Min 𝒦, where 𝒦 is the set of points (c(S), M_tmpl(S)) of the valid scheduled configurations S with 2t − p landings. | planned: `minimal_achievable_iff_schedPoints` in Template.lean (from `schedulableDomination_all`, `Sched.exists_plan`, `minimal_iff_of_dominated`) | WP4 |
| Proposition 5.7 (harmful waiting) | Proposition 6.5; Conjecture 6.5 | `prop-6-5` | narrow | Take n = 2, d = (3, 19), d̄ = (3, 11), c = (5, 1), t = 7, p = 4, with any central table satisfying (A1-NS) (the note's "no central flights", under which (A1-NS) and (AΔ) hold vacuously). The cheapest role configuration with 2t − p landings and every λ_k ≤ 73 costs 14, but every feasible plan of makespan ≤ 73 costs at least 18. So the front is not the Pareto set of (cost, max_k λ_k) over role configurations, as arXiv:2304.14659 assumes when it rules out harmful waiting. | planned: `prop65_check` (`Cert2.check` on `lean/test/certificates/accepted/v2-search-prop65.cert` by `decide +kernel`), `prop65_cost_ge` (with `Cert2.check_sound`), `prop65_roleConfig` (a configuration of cost 14) and `prop65_roleBound` (none cheaper, by `decide +kernel` on a role-configuration bound of §8, such as `BalData.value_le_totalCost`) in Counterexamples.lean | WP5 |
| Definition 5.8 (flight graphs, the reduction) | — (§6.6: Model, Reduction) | `def-flight-graph` (new) | new | A flight graph U has hubs C_I, C_G, central vertices 1, …, n, an optional duration on every pair of locations (none between the hubs) and landing costs; its plans, feasibility, cost and makespan are those of Definition 1.2 with its edges as flights. Its reduction f(U) is the clique instance with the same t and p and one city v = (w, e) for every central vertex i, simple path w from C_I to i and simple path e from i to C_G, with d_v = φ(w), d̄_v = φ(e) and c_v = ω(w) + ω(e) (φ the duration of a path, ω the landing costs of its vertices after the first). | planned: `FlightGraph`, `FlightGraph.Feasible`, `FlightGraph.reduce` in Graph.lean | WP5 |
| Example 5.9 (the reduction misses the front) | Example 6.11 | `claim-6-11` | narrow | Let U be the path C_I–a–b–C_G with durations 1, 2, 1, c_a = c_b = 1, t = 3, p = 2. f(U) has the two cities (d, d̄, c) = (1, 3, 2) and (3, 1, 2), and for every central table of f(U) satisfying (A1-NS) its front is {(8, 10)}; U has a feasible plan of cost 8 and makespan 8. So F_U ≠ F_{f(U)}, against arXiv:2304.14659 §2.4. | planned: `pathGraph_reduce`, `pathGraph_plan_feasible`, `pathGraph_reduced_front` (a v2 certificate checked by `decide +kernel` and `Cert2.check_sound`) in Counterexamples.lean | WP5 |
| Example 5.10 (the shuttle construction misses the front) | Proposition 6.7; Conjecture 6.7 | `prop-6-7` | narrow | Take n = 2, d = (1, 3), d̄ = (3, 1), c = (6, 1), t = 3, p = 2 and the central flight dc_12 = dc_21 = 2 (dc_ii arbitrary); (AΔ) holds. The clique instance that arXiv:2304.14659 (§2.3, §3.3) builds from it, with one virtual city for every "B Ā B̄" situation (a drop-off at x, a shuttle C_G → x → y → C_I carrying the passenger to y, a pick-up at y) and no central flights, has front {(4, 10)} for every central table satisfying (A1-NS); the instance has a feasible plan of cost 15 and makespan 8, which (4, 10) does not dominate. So the construction misses the front. | planned: `shuttleInstance` (the paper's construction, for every instance) in Graph.lean; `shuttle_reduced_front` (a v2 certificate checked by `decide +kernel` and `Cert2.check_sound`) and `shuttle_plan_feasible` (the plan flies the central leg, so it needs a feasibility check that accepts central legs) in Counterexamples.lean | WP5 |
| Lemma 5.11 (records give a configuration) | Lemma 4.3 | `lem-4-3` | narrow (remove if WP4 confirms Corollary 5.4 from Theorem 5.3) | Every feasible plan on p planes gives a role configuration with at least 2t − p landings whose drop-offs and pick-ups are cities of landing records (Lemma 3.1) of type B (from and back to C_I) and B̄ (neither) of their plane, and whose crossings are exactly the cities of its records of type A and Ā. | Converse.lean: `recCities`, `Feasible.exists_roleConfig_records` | WP4 |
| Lemma 5.12 (shrinking role configurations) | Lemma 4.4 | `lem-4-4` | keep (remove if WP4 confirms Corollary 5.4 from Theorem 5.3) | Let p ≤ s. A role configuration with s + 2N landings has one with exactly s landings whose drop-offs, pick-ups and crossings are sub-multisets of the old ones, so its cost, role loads and groups do not grow. | NonSymmetric.lean: `RoleConfig.exists_shrink` | WP4 |

### §6 Algorithm

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Lemma 6.1 (one-plane table) | Lemma 7.2 | `lem-7-2` | narrow | The table G[0][T] = 0, G[m + 1][T] = min over i with d_i ≤ T of c_i + G[m][T − d_i] (∞ over the empty set) gives the least cost of an m-multiset with δ ≤ T, and is ∞ iff there is none; its memoised version agrees with it. | OnePlane.lean: `oneplane`, `oneplane_le_cost`, `isLeast_oneplane`, `oneplane_eq_top_iff`, `oneplaneTable_getD` | — |
| Lemma 6.2 (the function E) | Proposition 7.10 (c), first half; §7.1 (unnumbered) | `lem-min-cost` (new) | new | Let E(T) be the least cost of an admissible partition of 2t − p landings into p groups with every δ(X_k) ≤ T (∞ if none). E is non-increasing and attained when finite; with 1 ≤ p, E(T) = ∞ for T < d_min⌈s/p⌉; and a level T at which E drops (E(T) = C < E(T′) for every T′ < T) has T ≤ (2t − p)·d_max. | MinCost.lean: `minCost`, `minCost_le`, `minCost_attained`, `minCost_antitone`; Solver.lean: `minCost_eq_top_of_lt`, `breakpoint_le` | — |
| Proposition 6.3 (front = breakpoints of E) | Proposition 7.1 | `prop-7-1` | wrap | Assume (S), (H) and p ≤ t. (C, M) ∈ F iff M = 2T for some T with E(T) = C and E(T′) > C for every T′ < T (original units). | Solver.lean: `minimal_admissiblePoints_iff`; FrontTri.lean: `minimal_achievable_iff_minCost_ATri`; planned: `minimal_achievable_iff_minCost_hub` in FrontTri.lean | WP2 |
| Proposition 6.4 (bracket) | Proposition 7.3 | `prop-7-3` | narrow | Let U₂(T) be the least cost of a partition whose link forest has trees of one or two planes (a single plane with an odd number of landings, or two planes linked at a city b, each with one copy of b and an odd number of free landings), every load ≤ T. At every level T ≤ Tmax of the table, L(T) ≤ E(T) ≤ U₂(T), with L = L_d of Lemma 3.5 computed from Lemma 6.1, and where L(T) = U₂(T), E(T) = L(T). | Relaxation.lean: `relaxedBoundAt`, `relaxRow_getD`, `relaxedBoundAt_le_totalCost`; PairBound.lean: `pairsBoundAt`, `relaxedBoundAt_le_minCost`, `minCost_le_pairsBoundAt`, `minCost_eq_of_bracket` | — |
| Proposition 6.5 (dominance, symmetric) | Proposition 7.9 | `prop-7-9` | narrow | Let rep map cities to cities with d(rep i) ≤ d_i and c(rep i) ≤ c_i (domRep, the first non-dominated representative, is one). Replacing every landing of an admissible partition by its representative gives an admissible partition with the same group sizes, no larger cost and no larger loads. | Shrink.lean: `Admissible.map`; AdmissibleBound.lean: `domRep`, `domRep_le` | — |
| Proposition 6.6 (dominance, non-symmetric) | — (the argument of Proposition 6.14) | `prop-dominance-ns` (new) | new | Let rep satisfy d(rep i) ≤ d_i, d̄(rep i) ≤ d̄_i and c(rep i) ≤ c_i (domRep3 is one). Replacing every city by its representative maps a role configuration to one with the same number of landings, no larger cost and no larger role loads, and a valid scheduled configuration to a valid one with the same number of landings, no larger cost and no larger M_tmpl. | LagrangianBound.lean: `domRep3`, `domRep3_le`, `RoleConfig.map`, `RoleConfig.size_map`, `RoleConfig.totalCost_map_le`, `RoleConfig.roleLoad_map_le`; SchedMap.lean: `Sched.map`, `Sched.Valid.map`, `Sched.size_map`, `Sched.cost_map_le`, `Sched.tmpl_map_le` | — |
| Theorem 6.7 (link-forest DP) | Theorem 7.5 | `thm-7-5` | narrow | For 1 ≤ p and T ≤ Tmax, the link-forest DP (tables Ch, Sub, Root and For over rooted link trees of up to p planes, labels among the non-dominated cities, free landings from G) equals E(T). | TreeBound.lean: `treeBoundAt`, `treeBoundAt_le_totalCost`; TreeExact.lean: `treeBoundAt_eq_minCost` | — |
| Theorem 6.8 (σ-DP) | Theorem 7.6 | `thm-7-6` | narrow (cond. WP3) | For 1 ≤ p ≤ t and T ≤ Tmax, the σ-DP, whose states are sets of at most min(p − 1, t − p) non-dominated cities, equals E(T). | AdmissibleBound.lean: `sigmaBoundAt_le_totalCost`; Solver.lean: `sigmaBoundAt_eq_minCost` | WP3 |
| Theorem 6.9 (verified solver, H2) | Verified solver (blueprint node) | `thm-verified-solver` (new) | new | Assume (S), (H) and 1 ≤ p ≤ t. The list `solveFront d c t p` is the Pareto front of the feasible plans. | Solver.lean: `solveFront`, `solveFront_eq`, `mem_solveFront_iff`, `solveFront_isParetoFront` (under (A1)); FrontTri.lean: `solveFront_isParetoFront_ATri`; planned: `solveFront_isParetoFront` under (H) | WP1 |

### §7 Complexity

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Theorem 7.1 (3-Partition reduction) | Theorem 8.1 | `thm-8-1` | narrow | Let a_1, …, a_{3m} and B be positive integers with Σ_i a_i = mB and B/4 < a_i < B/2. In the symmetric instance with cities d_i = a_i, p = m and t = 2m, the multiset X containing every city once has M(X) ≤ 2B iff the a_i split into m triples of sum B. The instance's numbers are the a_i, B and m. | planned: `threePartition_iff` in Complexity.lean (uses Lemma 2.3) | WP6 |
| Proposition 7.2 (Partition reduction, p = 2) | Proposition 8.2 (the NP-hard half) | `prop-8-2` | narrow | Let a_1, …, a_m be natural numbers with sum 2B, r ≥ m odd and K = B + 1. In the symmetric instance with 2r cities of durations a_i + K (i ≤ m) and K (the other 2r − m), p = 2 and t = r + 1, the multiset X containing every city once has M(X) ≤ 2(B + rK) iff some sub-multiset of the a_i sums to B. All durations are positive. | planned: `partition_iff` in Complexity.lean | WP6 |
| Theorem 7.3 (step count) | Corollary 8.3; Theorem 7.5 (its complexity clause) | `cor-8-3` | merge | (a) The link-forest DP instrumented with a step counter returns, at every level T ≤ Tmax, the value of Theorem 6.7 and a number of steps at most an explicit polynomial P(n, t, p, T). (b) Scanning the levels 0, …, (2t − p)·d_max with it gives the front (Proposition 6.3, Lemma 6.2) in at most ((2t − p)·d_max + 1)·P(n, t, p, (2t − p)·d_max) steps. | planned: `treeBoundSteps`, `treeBoundSteps_value`, `treeBoundSteps_le`, `scanSteps_le` in Complexity.lean | WP6 |

### §8 Certificates

| New label | Old label(s) | Slug(s) | Action | Final statement | Lean declarations | WP |
|---|---|---|---|---|---|---|
| Theorem 8.1 (obligations imply the front) | Theorem 9.1 | `thm-9-1` | wrap | Let S ⊆ ℕ² and (C_1, M_1), …, (C_r, M_r), r ≥ 1, with M_1 < ⋯ < M_r and C_1 > ⋯ > C_r. If (1) every listed point is in S, (2) every point of S has makespan ≥ M_1, (3) for i < r every point of S with makespan < M_{i+1} has cost ≥ C_i, and (4) every point of S has cost ≥ C_r, then the list is the Pareto front of S. | Checker.lean: `gapsOK`, `exists_le_of_gapsOK`; planned: `isParetoFront_of_obligations` in Checker.lean | WP2 |
| Theorem 8.2 (v1 checker, H3) | — (the Lean form of Theorem 9.1, `Cert.check_sound`) | `thm-checker-v1` (new) | new | If `Cert.check` accepts a format v1 certificate, its points are the Pareto front of the feasible plans of its instance for every central table satisfying (H), and for every central table if all its gaps are `relaxed`; the same holds for plans with rational times (Lemma 1.3) and, under (H), for planes ending anywhere. | Checker.lean: `Cert.check`, `Cert.forestGapBound_le`, `Cert.check_sound`, `Cert.check_sound_A1`, `Cert.check_sound_relaxed`; Simulate.lean: `planOK_feasible`; Relaxation.lean: `load_eq_scale_mul`; RationalPlans.lean: `Cert.check_sound_rat`; Bridge.lean: `Cert.check_sound_anywhere`; FrontTri.lean: `Cert.forestGapBound_le_ATri`, `Cert.check_sound_ATri`, `Cert.check_sound_anywhere_ATri`, `Cert.check_sound_rat_ATri`; planned: these restated under (H) | WP1 |
| Proposition 8.3 (`roles` bound) | — | `prop-roles-bound` (new) | new | The roles bound at level T, the larger of (A) the plane-by-plane relaxation in which a plane's m landings contain an odd number of crossings of weight d + d̄, the others weighing 2·min(d, d̄), all within T, and (B) the least cost of s landings of weight d + d̄ within pT, is at most the cost of every role configuration with s landings and every λ_k ≤ T. | RoleBound.lean: `rolesBoundAt`, `roleM_le`, `sum_roleLoad_eq_load_fill`, `rolesBoundAt_le_totalCost`; CheckerV2.lean: `Cert2.exists_repConfig`, `Cert2.rolesWith_le` | — |
| Proposition 8.4 (`lagrangian` bound) | — | `prop-lagrangian-bound` (new) | new | For every integer vector μ, the Lagrangian value at level T, the plane-by-plane relaxation in which a drop-off at i costs c_i + μ_i, a pick-up c_i − μ_i and every plane has an odd number of crossings within T, is at most the cost of every role configuration with S landings, all in the allowed cities, whose planes weigh at most T, a crossing at i weighing fill_i, a drop-off drop_i and a pick-up pick_i (d_i + d̄_i, 2d_i and 2d̄_i in the checker). | LagrangianBound.lean: `LagData`, `LagData.lagM_le`, `LagData.value_le_totalCost`; CheckerV2.lean: `Cert2.lagWith_le` | — |
| Proposition 8.5 (`balanced` bound) | Proposition 6.6 | `prop-6-6` | narrow | The imbalance-vector program at level T (planes in order; state: landings used and the imbalance vector Σ(Dr − Pk) so far, of ℓ¹-norm at most t − p) has value at most the cost of every role configuration with s landings and every λ_k ≤ T, for the weights and crossing table the checker builds. | BalancedBound.lean: `BalData`, `BalData.layers_dominate`, `RoleConfig.norm_prefix_le`, `BalData.value_le_totalCost`; CheckerV2.lean: `Cert2.balWith_le` | — |
| Proposition 8.6 (`search` bound) | — (the `search` kind) | `prop-search-complete` (new) | new | If the exhaustive search over scheduled configurations of cost below C reports the gap closed at level T, every valid scheduled configuration with s landings and cost below C has M_tmpl > T. | SearchGap.lean: `SearchData.closed`, `SearchData.closed_sound`; SchedMap.lean: `Sched.mul_tmpl_map_le`; CheckerV2.lean: `Cert2.searchWith_le` | — |
| Theorem 8.7 (v2 checker, H3) | Version 2 checker (blueprint node) | `thm-checker-v2` (new) | new | If `Cert2.check` accepts a format v2 certificate, its points are the Pareto front of the feasible plans of its instance for every central table that satisfies (A1-NS) if the certificate lists it, and for every central table otherwise. | CheckerV2.lean: `Cert2.check`, `Cert2.relaxedWith_le`, `Cert2.check_sound` | WP1 (delete `EO`, `Cert2.check_sound_EO`) |

### Refuted claims kept in the ledger

They stay active as `math.disproved`, each with the Lean refutation of the result named here.

| Slug | Claim | Refuted by | WP |
|---|---|---|---|
| `paper-greedy-optimal` | the per-PPP greedy of both papers is exact | Proposition 4.8 | WP5 |
| `paper-no-harmful-waiting` | arXiv:2304.14659: no harmful waiting (note's Conjecture 6.5); to be restated without (AΔ-path) | Proposition 5.7 | WP5 |
| `paper-general-graph-reduction` | arXiv:2304.14659 §2.4: F_U = F_{f(U)} | Example 5.9 | WP5 |
| `conj-6-7` | arXiv:2304.14659 §2.3, §3.3: virtual cities for the shuttle situations complete the front (note's Conjecture 6.7); to be restated as the paper's construction | Example 5.10 | WP5 |
| `claim-converse-s-only` | the converse under (S) alone; to be restated as "(S) without (H)" | Example 4.7 | WP5 |

## 4. Table B: removed results

Each removed slug is archived in `claims.toml` with `removed = "2026-11-25: <reason>"`, and
`gen_blueprint.py` and `gen_graph.py` skip it. Slugs absorbed by a merge are listed in Table A, not
here.

| Old label | Slug | Reason | Where it goes |
|---|---|---|---|
| Statement 1.2 | `claim-1-2` | argued, never proved; no headline proof, certificate kind or solver step uses it (§1.3 stays as prose) | deleted; ledger archive |
| Corollary 2.7 | `cor-2-7` | the Lean link-forest DP allows trees of up to p planes, so no kept proof needs the q_max cap | deleted; ledger archive |
| Lemma 2.9 | `lem-2-9` | used only by the attainment halves of Proposition 7.10 and by Theorem 10.1, both removed | deleted; ledger archive |
| Lemma 4.5 | `lem-4-5` | used only by the role-route proof of Theorem 4.7, replaced by Theorem 4.4 | deleted; ledger archive (WP1 deletes `RoleConfig.admissible_groups`, `RoleConfig.isParityWitness_witness`) |
| Lemma 6.2 | `lem-6-2` | L_NS is implemented nowhere (§6.5 and the paper say otherwise, wrongly); no kept proof uses it | deleted; ledger archive |
| Corollary 6.4 | `cor-6-4` | no code, certificate kind or headline proof uses it | deleted; ledger archive |
| Lemma 6.8 | `lem-6-8` | event orders leave the model: Theorem 5.3 covers every plan, and WP1 deletes the `EO` assumption | deleted; ledger archive |
| end of §6.2 | `claim-6-2-end` | superseded: Theorem 5.3 holds for every plan | deleted; ledger archive |
| Definition 6.17 | `def-6-17` | Example 5.10 defines the shuttle situation it needs, and Proposition 6.18, its other user, goes | deleted; ledger archive |
| Proposition 6.18 (a)–(c) | `prop-6-18` | computed by search only; no kept result uses it | deleted; ledger archive |
| Proposition 6.18 (d) | `claim-6-18-d` | rests on the flow model only; no kept result uses it | deleted; ledger archive |
| Lemma 6.19 | `lem-6-19` | no code, certificate kind or headline proof uses it | deleted; ledger archive |
| Proposition 6.12 | `prop-6-12` | decision 2; Example 5.9 is proved by certificate without it | deleted; ledger archive |
| Proposition 6.13 | `prop-6-13` | decision 2; only the dropped clause F_U = {(8, 8)} of Example 6.11 used it | deleted; ledger archive |
| Proposition 6.14 | `prop-6-14` | decision 2; its argument survives as Proposition 6.6 | deleted; ledger archive |
| Proposition 6.15 | `prop-6-15` | decision 2 | deleted; ledger archive |
| Proposition 6.16 | `prop-6-16` | decision 2 | deleted; ledger archive |
| Proposition 7.4 | `prop-7-4` | the U and U₃ shortcuts are untrusted C++ optimisations, checked per run; the `gadget` kind was never built | deleted; ledger archive |
| Lemma 7.7 | `lem-7-7` | only the Pareto-set variant uses it, and no certificate kind, solver step or headline proof does | deleted; ledger archive |
| Proposition 7.8 | `prop-7-8` | no certificate kind, solver step or headline proof uses it | deleted; ledger archive |
| Lemma 9.2 | `lem-9-2` | the `sigma-potential` kind was never built | deleted; ledger archive |
| Lemma 9.3 | `lem-9-3` | the `sigma-potential` kind was never built | deleted; ledger archive |
| Theorem 10.1 | `thm-10-1` | decision 3 | deleted; ledger archive |
| Conjecture 10.2 | `conj-10-2` | decision 3 | deleted; ledger archive |
| Appendix A | — | superseded proof of Theorem 4.7 | deleted |
| §4.6, remark on d′ | — | rule 3: a remark that claims an unused bound | deleted |
| §7.3, "Pairs are not enough" | — | rule 3: an unnumbered claim about U₃, which goes | deleted |

Also deleted: §0 (regenerated from Table A), §6.5 (its kinds are §8), §10, §11 (the experiments live
in the paper), §12, and the clauses dropped from narrowed results (§6 below).

## 5. Table C: renumbering

`old<TAB>new`, using the label strings of the note and of the `{{< node "…" >}}` shortcodes of
`site/`. The script must apply all pairs at once (one alternation, longest match first) and match
whole labels: the table has chains (Lemma 3.1 → 3.2, Lemma 3.2 → 3.3) and prefixes (Theorem 4.1 and
Theorem 4.10). Identity pairs are listed so that every kept label is accounted for. Abbreviated
forms (Thm, Prop, Cor, Ex, Def) in Lean docstrings and C++ messages follow the same map.
`Conjecture 4.10` is left out: the sentences that mention it are deleted. `Conjecture 6.5` and
`Conjecture 6.7` are redirected to the results that state the claims they refute. `Proposition 7.10`
maps to two results (Proposition 3.6 and Lemma 6.2); its site uses are checked by hand (review item
8).
The `§` entries of this table are blueprint node labels, as in `{{< node "§1.1" >}}`; section
references in prose ("§4.6 of the note") follow the section map after it instead.

```text
§1.1	Definition 1.1
§1.2	Definition 1.2
Definition (plan)	Definition 1.2
§1.4	Definition 1.4
§1.5	Definition 1.6
Lemma 1.1	Lemma 1.7
Notation	Notation
Definition 2.2	Definition 2.1
Lemma 2.3	Lemma 2.2
Lemma 2.4	Lemma 2.3
Lemma 2.5	Lemma 2.4
Definition (link forest)	Definition 2.5
Lemma 2.6	Lemma 2.6
Lemma 2.8	Lemma 2.7
Lemma 2.1	Lemma 3.1
Lemma 3.1	Lemma 3.2
Lemma 3.2	Lemma 3.3
Lemma 3.3	Lemma 3.4
Lemma 3.4	Lemma 3.5
Proposition 7.10	Proposition 3.6
Theorem 4.1	Theorem 4.1
Lemma 4.6	Lemma 4.2
Lemma 4.11	Lemma 4.3
Theorem 4.10	Theorem 4.4
Theorem 4.7	Theorem 4.4
Corollary 4.8	Theorem 4.5
Theorem 4.9	Theorem 4.5
Corollary 4.12	Theorem 4.5
Example 4.13	Example 4.7
§5	Proposition 4.8
Definition 4.2	Definition 5.1
Theorem 6.9	Theorem 5.3
Theorem 6.1	Corollary 5.4
Lemma 6.3	Lemma 5.5
Corollary 6.10	Corollary 5.6
Proposition 6.5	Proposition 5.7
Conjecture 6.5	Proposition 5.7
Example 6.11	Example 5.9
Proposition 6.7	Example 5.10
Conjecture 6.7	Example 5.10
Lemma 4.3	Lemma 5.11
Lemma 4.4	Lemma 5.12
Lemma 7.2	Lemma 6.1
Proposition 7.1	Proposition 6.3
Proposition 7.3	Proposition 6.4
Proposition 7.9	Proposition 6.5
Theorem 7.5	Theorem 6.7
Theorem 7.6	Theorem 6.8
Verified solver	Theorem 6.9
Theorem 8.1	Theorem 7.1
Proposition 8.2	Proposition 7.2
Corollary 8.3	Theorem 7.3
Theorem 9.1	Theorem 8.1
Proposition 6.6	Proposition 8.5
Version 2 checker	Theorem 8.7
```

Prose references to sections follow this map; §1 keeps its subsections.

```text
§0	§0
§1.1	§1.1
§1.2	§1.2
§1.3	§1.3
§1.4	§1.4
§1.5	§1.5
§2	§2
§3	§3
§4.1	§4
§4.2	§5
§4.3	§4
§4.4	§4
§4.5	§4
§4.6	§4
§5	§4
§6.1	§5
§6.2	§5
§6.3	§8
§6.6	§5
§7.1	§6
§7.2	§6
§7.3	§6
§7.4	§6
§7.5	§6
§7.6	§6
§7.7	§6
§8	§7
§9	§8
```

## 6. Narrowed statements: the dropped clauses

Line numbers are those of `doc/theory/exact-front.md` at `89fd9fa`. "Kept use" means a proof of a
result that stays.

**Narrow rows.**

* *Definition 1.1* [§1.1]: drops durations and times in an archimedean field (Lemma 1.3 covers
  rational and real times), undirected flights, the absence of a flight i–i and optional central
  flights (the table is complete and directed). Every kept theorem holds for every table, so none
  uses the absence of a flight; Proposition 5.7 and Examples 5.9 and 5.10, which had "no central
  flights", now quantify over the tables satisfying (A1-NS).
* *Definition 1.2* [Definition (plan)]: drops the condition that consecutive legs of a journey on
  one plane come later on its route, and the event-ordered plans. Kept uses: none (the route
  condition is used at 1033, Lemma 6.8(b); event orders at 155–162, 1017–1041, 1144–1159, all
  removed).
* *Definition 1.4* [§1.4]: drops (AΔ-path). Its users were Corollary 6.4 (945–958) and Conjecture
  6.5 (960), both removed, and Proposition 6.5 (966), now stated without it; 75–76 (§0), 1007 (a
  remark) and 1046 (Theorem 6.9: "not needed") go with them. The instance of Proposition 6.5 satisfied
  only the first of the two inequalities of §1.4 (for i = 2, z = 1: 19 > 11 + 3 + 3).
* *Lemma 1.7* [Lemma 1.1]: drops finiteness and "every point is weakly dominated by a point of
  Min S". Cited at 613, 630, 805, 1154, 1946 (kept proofs: only Min A = Min B is used) and at 1549,
  1569, 1786, 2046 (removed; 1786, Lemma 7.7, used the dropped clause).
* *Lemma 2.3* [Lemma 2.4]: drops (a) for general components and (b) (a parity matrix inside every
  spanning forest). Cited at 271 (text), 373 (Lemma 2.9), 2207 (Appendix A), removed; at 1899 and
  1912 (Theorems 7.1, 7.2), which use only the disjoint case; at 323 (Lemma 2.6) and 704 (Theorem
  4.10, Step 2), which used (b): both proofs are re-routed (review item 5).
* *Lemma 2.6*: drops "a link forest with at most one edge of each label at each plane". Used only
  inside its own proof (315, 323–326).
* *Lemma 2.7* [Lemma 2.8]: drops (a) and (b) as statements, and the clause h_k ≤ min(|X_k| − 1, w)
  of (c). Cited at 1768 (Theorem 7.6, which used the clause; re-routed, review item 5) and 2007
  (§9 trust list, deleted).
* *Lemma 3.1* [Lemma 2.1]: counts landing records and visits instead of segment types; on routes
  without central flights they coincide. Cited at 524 (Lemma 4.3(b): record form), 1103 (Theorem
  6.9, Step 4: visit form), 894, 1209, 1235, 2186 (removed).
* *Lemma 3.2* [Lemma 3.1]: extracts a chain instead of rewriting the journeys, and drops "a clean
  journey has no flight arriving in C_I and none departing from C_G" (implied by the chain form).
  Cited at 500 (Lemma 4.3(a), dropped), 595 and 633–637 (Theorems 4.7, 4.9, merged; Lean uses
  chains), 670 and 812 (Theorem 4.10, Corollary 4.12: the chain form, `ToGoal.dst_ne_ci`), 877
  (Theorem 6.1: `exists_transfer`), 1393, 1603 (removed).
* *Lemma 3.3* [Lemma 3.2]: drops "hence at least s landings in central cities". Cited at 428, 673
  and 690 (segment count only), 1847 (Proposition 7.10(b), which used the clause; re-routed,
  review item 5), 1955 (§9 text, deleted).
* *Lemma 3.4* [Lemma 3.3]: (a) becomes the per-plane form with weight e (the per-segment bound
  d_{x_1} + d_{x_m} is its step); (b) becomes the (S) + (H) form (2d_y per landing, and the chain
  bound); drops the non-symmetric (AΔ) bounds for the four segment types. Non-symmetric (b) was used
  at 888, 1210, 1234, 1331 (Lemmas 6.2, 6.19, Definition 6.17, Proposition 6.7, all removed); 672
  and 814 (Theorem 4.10, Corollary 4.12) use the new (b).
* *Proposition 3.6* [Proposition 7.10 (a), (b)]: drops attainment (a plan of makespan 2d_min κ, a
  plan of cost s·c_min and makespan 2d_cheap κ, the cheapest front point) and part (c) except its
  first half, which moves to Lemma 6.2. Cited at 1746, 1805, 1864, 1955, 2005, 2038: text, §7.4
  levels, Proposition 7.8 and Theorem 10.1, removed or prose; obligations 2 and 4 use only the lower
  halves.
* *Theorem 4.1*: drops "plane k flies ℓ(X_k)", "picks up at most one passenger" and "uses no central
  flight" (the statement holds for every central table). Used at 1025 and 1041 (Lemma 6.8(c)), 1844
  (Proposition 7.10(a)), 2045 (Theorem 10.1), all removed; 609 (Corollary 4.8's "exactly s central
  landings") is covered by "land exactly at the groups".
* *Example 4.7* [Example 4.13]: drops L(19) = 260, the consecutive front points and the evidence
  from other solvers; "neither (A1) nor (AΔ)" becomes "(H) fails". Not cited by kept results.
* *Proposition 4.8* [§5]: drops the explanation of the greedy's choices. Cited at 30 and 108 (status
  tables) and 2061 (§10), all deleted.
* *Theorem 5.3* [Theorem 6.9]: the template's makespan becomes the closed form M_tmpl. Used at 1154
  (Corollary 6.10, which now combines the closed form with Lemma 5.5) and 1572 (removed).
* *Corollary 5.4* [Theorem 6.1]: drops λ_k ≤ F_k. No kept proof uses it: 1003 and 1011 are text,
  1049 (Theorem 6.9) borrows only the splitting step, and 1164, 1237, 1355 are removed.
* *Lemma 5.5* [Lemma 6.3]: keeps attainment, as "a feasible plan of makespan at most M_tmpl"; drops
  the lower bound for every schedule with the same orders and matching, and "the least makespan is
  the minimum of M_tmpl". Kept uses: 1116 and 1133 (Theorem 6.9, Steps 5–6, the formula only, now
  Definition 5.2); 1423 (Example 6.11, now by certificate). Corollary 6.10 (1144–1146) used the least
  makespan of §6.2, which Corollary 5.6 replaces by M_tmpl.
* *Corollary 5.6* [Corollary 6.10]: drops F = Min A_eo (event-ordered plans) and the least makespan
  m(cfg). Cited at 1157 and 197 (Statement 1.2, removed).
* *Proposition 5.7* [Proposition 6.5]: drops (AΔ-path), the list of all front points (only "cost at
  least 18 up to makespan 73" is used) and the waiting argument, which the certificate replaces. Not
  cited by kept results.
* *Example 5.9* [Example 6.11]: drops F_U = {(8, 8)} (it needed Proposition 6.13) and the remarks on
  relays. Cited at 1252 (Proposition 6.7 text) and 1591 (Proposition 6.15), both removed.
* *Example 5.10* [Proposition 6.7]: replaces the class bound (every plan whose central flights lie in
  segments of type Ā has makespan at least 10) by the front of the paper's own construction; fixes
  c = (6, 1) instead of "any costs"; drops the full front {(4, 10), (15, 8)}, "(A1-NS) fails" and
  Definition 6.17, whose shuttle situation is defined inside the example. Cited at 1252, 1257–1264,
  1286, 1334–1340 and 1369 (text, Proposition 6.18, Lemma 6.19, §6.5), all removed.
* *Lemma 5.11* [Lemma 4.3]: drops (a), the hypotheses "simple plan" and "clean journeys" (Lean works
  on records of any feasible plan) and the cost and λ_k ≤ F_k conclusions (the role-load route takes
  them from Lemma 3.4(c)). (a) was used at 639 (Theorem 4.9, merged), 1034 (Lemma 6.8, removed), 1049
  (Theorem 6.9, Step 1; re-routed, review item 5) and 1453 (removed).
* *Lemma 6.1* [Lemma 7.2]: drops "G is non-increasing in τ". No use.
* *Proposition 6.4* [Proposition 7.3]: drops U₃. Used at 1680–1690 (Proposition 7.4), 1867 (§7.7)
  and 2007 (§9), removed or untrusted C++.
* *Proposition 6.5* [Proposition 7.9]: drops "E(T) and L(T) unchanged" and "the front unchanged
  under (S) and (A1)"; the relabelling form is what the DPs use. Cited at 808 (Corollary 4.12,
  merged), 1863 (§7.7) and 2008 (§9), not kept proofs.
* *Theorem 6.7* [Theorem 7.5]: drops the cap q_max (so Corollary 2.7) and the time and memory bounds
  (to Theorem 7.3). Cited at 1868 (§7.7), 1924 (Corollary 8.3, merged into Theorem 7.3), 1962 and
  2007 (§9).
* *Theorem 6.8* [Theorem 7.6]: runs on the non-dominated cities. Cited at 1801, 1868, 1997 and 2007
  (Proposition 7.8, §7.7, Lemma 9.3, §9), removed or prose.
* *Theorem 7.1* [Theorem 8.1]: drops membership in NP and the complexity-class conclusion, which go
  to the remark that cites Garey–Johnson. Cited at 861 (§5 text).
* *Proposition 7.2* [Proposition 8.2]: drops the algorithm for fixed p and "weakly NP-complete". No
  use.
* *Proposition 8.5* [Proposition 6.6]: drops equality with E_NS(T) and the count of states. Cited at
  1355 and 1364 (§6.5, deleted).

**Merge rows.**

* *Lemma 3.5* [Lemma 3.4 + the v2 `relaxed` kind], slug `lem-3-4`: the weight becomes e = min(d, d̄),
  with no assumption; drops ℓ(Y_k) ≤ F_k. Cited at 1842, 1848 and 1950 (which use ≤ M only) and 2044
  (removed).
* *Theorem 4.4* [Theorems 4.7, 4.10, Conjecture 4.10]: (A1) and (AΔ) become (H) (Lemma 1.5); the
  form "on any set Q of planes" is the case of any p ≤ t.
* *Theorem 4.5* [Corollaries 4.8, 4.12, Theorem 4.9]: drops "attained by a plan with exactly s
  central landings" (Theorem 4.1 gives it) and Corollary 4.12's references to Propositions 7.1
  (now 6.3), 7.8 (removed), 7.9 (now 6.5) and to `forest` gaps (now Theorem 8.2).
* *Theorem 7.3* [Corollary 8.3, Theorem 7.5's bounds]: an explicit polynomial replaces the O-bounds;
  drops "not strongly NP-hard unless P = NP" and the open question on E(T) ≤ C.

## 7. Review decisions (2026-11-25)

The open questions of the first version of this map, with the decisions taken on them. Earlier
sections cite them as review items.

1. **(AΔ-path)** is removed from the model. Its only users, Corollary 6.4 and Conjecture 6.5, are
   removed, and Proposition 5.7 is stated without it. (The instance of Proposition 6.5 satisfied only
   the first of the two inequalities of §1.4, the only one that the paper's prose and
   `checks/waiting_search.cpp` used.)
2. **Shuttles.** A refutation of arXiv §2.3 and §3.3 stays, since it refutes a paper claim: Example
   5.10, slug `prop-6-7`, through the paper's own construction; `conj-6-7` stays in the ledger as the
   refuted claim. Definition 6.17, Proposition 6.18 and `claim-6-18-d` stay removed, and the example
   defines what it needs. The sentence of `doc/erratum.md` §1 on segments with one central flight
   loses its support (WP9).
3. **Proposition I.** The remark after Corollary 4.8 becomes Example 4.6, slug
   `claim-extra-landings`, with a kernel proof (WP5).
4. **Lemma 2.3** is narrowed to disjoint groups, the only case Theorems 7.1 and 7.2 use.
5. **Proofs re-routed to Lean.** Each kept proof that used a dropped clause is written as its Lean
   proof, which does not use the clause:
   * Lemma 2.6, "only if" (Lemma 2.4(b)) → a witness with the fewest edges and removal of a leaf
     (`Admissible.exists_linkForest`, `Admissible.exists_minimal`).
   * Theorem 4.4, Step 2 (the T-join "as in Lemma 2.4(b)") → `TriCore.exists_tjoin`; and Step 4
     ("leave out a segment") → merging two segments of one plane (`exists_merge`).
   * Theorem 5.3, Step 1 (Lemma 4.3(a)) → Lemma 3.2(b) (`exists_transfer_pw`).
   * Theorem 5.3, Step 6 (Lemma 4.4) → the shrinking inside the proof (`exists_sched_of`, Step 6), so
     Theorem 5.3 does not depend on Lemma 5.12.
   * Theorem 6.8 (the bound on η_k from Lemma 2.8(c)) → Lemma 2.4 and η_k ⊆ Z(h)
     (`sigmaBoundAt_le_totalCost`).
   * Proposition 3.6, cost bound ("at least s central landings" of Lemma 3.2) → Lemma 3.5
     (`Feasible.minOf_le_cost_emin`).
6. **Lemmas 5.11 and 5.12** are removed if WP4 confirms Corollary 5.4 from Theorem 5.3
   (`Sched.load k ≤ Sched.tmpl` holds by the definition of `tmpl` as a maximum, and Theorem 5.3 needs
   neither lemma, item 5). Their Lean goes with them: `Feasible.exists_roleConfig_records`,
   `RoleConfig.exists_shrink`, and `PlaneFeasible.cntA_eq` and `roleW_landingRecs_le`, whose only
   users they are (the visit forms of Lemmas 3.1 and 3.4 stay). They are last in §5, so nothing
   shifts. If the corollary route fails, they move before Corollary 5.4 and §5 is renumbered.
7. **WP3.** Lemma 2.7 and Theorem 6.8 stand or fall with the σ-DP. If it goes, Theorem 6.9 becomes
   Theorem 6.8; nothing else shifts.
8. **Proposition 7.10** splits into Proposition 3.6 (lower bounds) and Lemma 6.2 (E = ∞ below
   d_min⌈s/p⌉). Table C sends the label to Proposition 3.6; its four site uses are checked by hand.
9. **Model definitions** are numbered: Definitions 1.1, 1.2, 1.4 and 1.6, with new `def-` slugs; the
   blueprint nodes labelled "§1.1" etc. take these labels.
10. **Surviving slugs of merges:** `lem-3-4` (the relaxation), `thm-4-10` (the converse) and
    `cor-4-8` (the front).
11. **Conjecture 6.5** has no slug of its own (it is `paper-no-harmful-waiting`); Table C redirects its
    label to Proposition 5.7, which states the claim it refutes, and Conjecture 6.7 to Example 5.10.

## 8. Notes for WP8 (ledger) and WP9

* `exp-e9-linear-family` is archived with §10 (decision 3); `exp-e10-greedy-density` drops
  `conj-10-2` from `tests`.
* `exp-e2-symmetric-front` and `exp-e6-conj410-search` test `thm-4-7` and `cor-4-8`, and `thm-4-10`:
  point them at the surviving slugs `thm-4-10` and `cor-4-8`.
* `exp-e4-nonsymmetric-front` tests `thm-6-1`, `thm-6-9`, `cor-6-10`: unchanged slugs.
* New definition claims (`def-instance`, `def-plan`, `def-assumptions`, `def-front`,
  `def-link-forest`, `def-scheduled-config`, `def-flight-graph`) are badged machine-checked by their
  Lean definitions, as `def-2-2` is.
* `lem-3-4` survives the relaxation merge and takes the statement with the weight min(d, d̄).
* `paper-no-harmful-waiting` is restated without (AΔ-path).
* `prop-6-7` takes the label Example 5.10 and its new statement; `conj-6-7` is restated as the claim of
  arXiv §2.3 and §3.3 and stays `math.disproved`, refuted by Example 5.10.
* `claim-extra-landings` (Example 4.6) is new.
* WP9: `doc/erratum.md` §1 keeps its shuttle item, now proved by Example 5.10, and drops the sentence
  on segments with one central flight (Proposition 6.18 goes).
