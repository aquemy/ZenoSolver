/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Examples
public import ZenoFront.Graph
public import ZenoFront.Solver
public import ZenoFront.TriSegments
public import ZenoFront.CheckerV2
public import ZenoFront.DominationAll
public import ZenoFront.RoleBound
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Order.WellQuasiOrder

/-!
# The counterexamples of the theory note, checked by the kernel

Concrete refutations of claims of the 2015 and 2023 papers, and of the hypotheses of the note's
own theorems. Every computation is done by the Lean **kernel** (`decide +kernel`): no compiled
code and no `native_decide`.

## The per-PPP greedy of both papers (§5 of the note)

Both papers fix a *possibly Pareto-optimal plan* (PPP), a multiset of central landings, and claim
that a greedy schedules it optimally. They state the greedy in two forms. Both are defined here for
symmetric durations:

* `Greedy.evocopLoads`: EvoCOP 2015, Algorithm 1 ("Computing the optimal makespan of PPP `(e, w)`
  when `β = 0`"), then its Step 2 (each P3, longest first, to the two planes with the smallest
  flight times). A PPP `(e, w)` has `t` eastbound and `t − p` westbound landings. Its makespan,
  `evocopMakespan`, is the least over the sub-multisets `β` of `e ∩ w` (the P3 patterns).
* `Greedy.arxivLoads`: the four steps of arXiv:2304.14659, §3.2, for a PPP `(a, ā, b)` of
  `k + p` crossings `A`, `k` crossings `Ā` and `t − p − k` drop-off/pick-up pairs `B B̄`.

The `lpt` instance is `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2`. Its exact front contains
`(260, 60)` (`Examples.lptCounterexample_front`). For every PPP of cost at most 260, every set of
P3 patterns and every way to break the ties of `ArgMin`, both greedies give a makespan above 60
(`evocop_misses_lpt`, `arxiv_misses_lpt`). On the landings of `(260, 60)`, EvoCOP's Algorithm 1
without P3 ends at `(52, 68)`, whatever the ties (`evocop_lpt_noP3`), as §4 of the note says. With
its best `β`, EvoCOP's greedy reaches 64 (`evocop_lpt_ppp`).

The `p3First` instance is `d = (1, 3)`, `c = (9, 5)`, `t = 4`, `p = 2`. Its exact front contains
`(42, 12)` (`p3First_front`). For every PPP of cost at most 42 and every tie-breaking, the arXiv
greedy gives a makespan above 12 (`arxiv_misses_p3First`). EvoCOP's greedy reaches `(42, 12)`,
with one P3 at city 2, whatever the ties (`evocop_reaches_p3First`).

The papers leave some choices open:

* the ties of `ArgMin`: every tie-breaking is covered (`minIdxs`, `evocopLoadsAll`,
  `arxivLoadsAll`). `evocopLoads` and `arxivLoads` break ties towards the first plane, as the 2016
  C++ does (EvoCOP's worked example on p. 7 agrees); they serve the cross-check below;
* the P3 patterns `β` of a PPP: every sub-multiset of `e ∩ w` is covered;
* in EvoCOP's Step 2, for `p = 1`, both halves of a P3 go to the single plane (`p = 2` in both
  instances);
* in arXiv Step 2, the `p` largest crossings go in decreasing order, each to the least-loaded plane
  that has none yet ("each plane must receive one");
* in arXiv Step 3, the plane is the least loaded among those whose next pattern (`Ā` after `A`,
  `A` after `Ā`) is still available. Read literally ("while it remains some elements in `a` and
  `ā`, select the plane with the minimal duration"), the step can stop or get stuck with crossings
  left over.

On the 27 golden instances (`tests/golden/instances.txt`), `evocopPoints` gives the front of the
2016 `zenoSolver`, and `arxivPoints` that of `zenoSolver_noDuplicate` on 25 of them.

## Example 4.7: the triangles through a hub cannot be dropped

On `d = d̄ = (2, 3, 9, 11)`, `c = (50, 44, 17, 0)`, `t = 6`, `p = 3`, with a central flight of
duration 1 between cities 3 and 4, a plan of cost 260 and makespan 39 flies that central flight
(`Ex413.plan_feasible`). The checker of format v1 accepts hub flights only, so the plan is
simulated on its duration table (`planOKDur`, `Graph.lean`). Every admissible partition of 9
landings with loads `δ(X_k) ≤ 19` costs at least 264 (`Ex413.minCost_19`), so no admissible point
weakly dominates `(260, 39)` (`Ex413.not_admissible_le`). The conclusion of Theorem 4.4 and
Theorem 4.5 fail there (`Ex413.no_admissible_partition`, `Ex413.not_isParetoFront`).

## Proposition 5.7: harmful waiting

On `d = (3, 19)`, `d̄ = (3, 11)`, `c = (5, 1)`, `t = 7`, `p = 4`, the cheapest role configuration
with every role load at most 73 costs 14 (`Prop65.cheapest_roleConfig`, through the `roles` bound).
Yet no feasible plan of makespan at most 73 costs less than 18, for every table of central flights
satisfying (A1-NS) (`Prop65.cost_ge_of_makespan_le`). The proof is Theorem 5.3 and the exhaustive
search of a `search` gap (`SearchData.closed_sound`). The kernel decides that search in eight
pieces, split by the option of the first plane, so that no declaration needs more than a few
gigabytes. The test certificate `v2-search-prop65.cert` also uses `balanced` gaps, whose bound uses
`Std.HashMap`; the kernel cannot reduce it, and with `search` gaps only the whole certificate
exhausts memory. So only the gap below makespan 74 is proved here, which is all the statement
needs.

## Example 5.9: the reduction of arXiv §2.4 misses the front

On the path `U = C_I – a – b – C_G` with durations 1, 2, 1, `c_a = c_b = 1`, `t = 3`, `p = 2`, the
reduction `f` of `Graph.lean` gives the clique instance with `d = (1, 3)`, `d̄ = (3, 1)`, `c = (2, 2)`
(`Ex611.vcities_U`, `Ex611.reduced_graph`). A kernel-checked v2 certificate proves that its front
is `{(8, 10)}` (`Ex611.reduced_front`). `U` has a plan of cost 8 and makespan 8 (`Ex611.plan`), so
the two fronts differ (`Ex611.fronts_differ`).

## Example 5.10: the shuttle construction of arXiv §3.3 misses the front

For each `B Ā B̄` situation through two central cities `i` and `j`, arXiv:2304.14659 §3.3 adds a
virtual city whose patterns have their own durations and costs (`Shuttle.shuttleCity`,
`Shuttle.augment`). The augmented instance is modelled by role configurations with per-pattern
durations (`Shuttle.TConfig`). The construction is formalised as printed: the pick-up at the new
city lasts `2 d_j` (equation (4)). The erratum's correction, `2 d̄_j`, is not formalised. The paper
says the situation becomes a `B B̄` pair "and a `Ā` with a null multiplicity". Both readings are
covered: the shuttle `Ā` is counted or not (the flag `shuttle`). One choice is left open by the
paper and taken here: every ordered pair `i ≠ j` gets a virtual city (in the Lean model every pair
of central cities is joined by a flight).

The instance is `d = (1, 3)`, `d̄ = (3, 1)`, a central flight of duration 2, `c = (6, 1)`, `t = 3`,
`p = 2`; (AΔ) holds. It has a feasible plan of cost 15 and makespan 8 (`Shuttle.plan_feasible`), so
its front has a point of makespan at most 8 (`Shuttle.front_le`). Every configuration of the
augmented instance has a plane that flies at least 10, in both readings (`Shuttle.load_ge`). So the
construction's front is not the instance's front (`Shuttle.shuttle_misses`).

## Proposition I holds only in the front sense

Both papers' Proposition I says that Pareto-optimal plans land exactly `2t − p` times. On `n = 1`,
`d₁ = 1`, `c₁ = 0`, `t = 5`, `p = 3`, the front is `{(0, 6)}` (`PropI.front`), and a feasible plan
with 9 central landings, more than `2t − p = 7`, attains it (`PropI.plan9_pareto`).

## Main results

* `ZenoFront.Greedy.evocop_misses_lpt`, `ZenoFront.Greedy.arxiv_misses_lpt`: neither greedy reaches
  the front point `(260, 60)` of the `lpt` instance.
* `ZenoFront.Greedy.arxiv_misses_p3First`: the arXiv greedy does not reach the front point
  `(42, 12)` of the `p3First` instance; `ZenoFront.Greedy.evocop_reaches_p3First`: EvoCOP's does.
* `ZenoFront.Ex413.plan_feasible`, `ZenoFront.Ex413.not_admissible_le`,
  `ZenoFront.Ex413.not_isParetoFront`: Example 4.7.
* `ZenoFront.Prop65.prop65`, `ZenoFront.Prop65.harmful_waiting`: Proposition 5.7.
* `ZenoFront.Ex611.reduced_front`, `ZenoFront.Ex611.fronts_differ`: Example 5.9.
* `ZenoFront.PropI.plan9_pareto`: a Pareto-optimal plan with more than `2t − p` landings.
* `ZenoFront.Shuttle.shuttle_misses`: Example 5.10.
-/

@[expose] public section

namespace ZenoFront

namespace Greedy

/-! ### Plane loads -/

/-- The first plane with the least load among those that `ok` accepts (`none` if there is none). -/
def argMinAmong (D : List ℕ) (ok : ℕ → Bool) : Option ℕ :=
  ((List.range D.length).filter ok).foldl
    (fun best k => match best with
      | none => some k
      | some b => if D.getD k 0 < D.getD b 0 then some k else some b) none

/-- The first plane with the least load. -/
def argMin (D : List ℕ) : ℕ := (argMinAmong D fun _ => true).getD 0

/-- Add `x` to the load of plane `k`. -/
def addAt (D : List ℕ) (k x : ℕ) : List ℕ := D.modify k (· + x)

/-- The largest load. -/
def maxLoad (D : List ℕ) : ℕ := D.foldr max 0

/-- Insert into a non-increasing list. -/
def insertDesc (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDesc x ys

/-- Sort in non-increasing order (insertion sort, so that the kernel reduces it). -/
def sortDesc : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

/-- The durations of a multiset of cities given by its counts, longest first. -/
def durs {n : ℕ} (d : Fin n → ℕ) (cnt : List ℕ) : List ℕ :=
  sortDesc (((List.finRange n).zip cnt).flatMap fun x => List.replicate x.2 (d x.1))

/-- The cost of a multiset of cities given by its counts. -/
def costOf {n : ℕ} (c : Fin n → ℕ) (cnt : List ℕ) : ℕ :=
  (((List.finRange n).zip cnt).map fun x => x.2 * c x.1).sum

/-! ### EvoCOP 2015, Algorithm 1 and Step 2 -/

/-- The first loop of Algorithm 1: while westbound landings remain, the plane with the least
load flies the longest remaining eastbound landing if it is in `C_I` (`S k = true`, EAST), and
the longest remaining westbound one otherwise. Returns the loads, the positions and the
eastbound landings left. -/
def loop1 : ℕ → List ℕ → List Bool → List ℕ → List ℕ → List ℕ × List Bool × List ℕ
  | 0, D, S, es, _ => (D, S, es)
  | _ + 1, D, S, es, [] => (D, S, es)
  | f + 1, D, S, es, w :: ws =>
    let k := argMin D
    if S.getD k true then
      match es with
      | [] => (D, S, es)
      | e :: es' => loop1 f (addAt D k (2 * e)) (S.set k false) es' (w :: ws)
    else loop1 f (addAt D k (2 * w)) (S.set k true) es ws

/-- The second loop of Algorithm 1: each remaining eastbound landing, longest first, to the plane
in `C_I` with the least load. -/
def loop2 : List ℕ → List Bool → List ℕ → List ℕ
  | D, _, [] => D
  | D, S, e :: es =>
    match argMinAmong D fun k => S.getD k false with
    | none => D
    | some k => loop2 (addAt D k (2 * e)) (S.set k false) es

/-- Step 2: each P3, longest first, adds `2 d_i` to each of the two planes with the least loads
(both halves to the single plane if `p = 1`). -/
def p3Step : List ℕ → List ℕ → List ℕ
  | D, [] => D
  | D, b :: bs =>
    let k₁ := argMin D
    match argMinAmong D fun k => k != k₁ with
    | none => p3Step (addAt D k₁ (4 * b)) bs
    | some k₂ => p3Step (addAt (addAt D k₁ (2 * b)) k₂ (2 * b)) bs

/-- The private makespans of EvoCOP 2015's two steps for `p` planes, the eastbound landings `es`
and the westbound ones `ws` without the P3 patterns, and the P3 patterns `bs` (durations, longest
first). -/
def evocopLoads (p : ℕ) (es ws bs : List ℕ) : List ℕ :=
  let r := loop1 (es.length + ws.length) (List.replicate p 0) (List.replicate p true) es ws
  p3Step (loop2 r.1 r.2.1 r.2.2) bs

/-- The makespan of EvoCOP 2015's two steps: the largest private makespan. -/
def evocopRun (p : ℕ) (es ws bs : List ℕ) : ℕ := maxLoad (evocopLoads p es ws bs)

/-! ### arXiv:2304.14659, §3.2 (symmetric durations) -/

/-- Steps 1 and 4: each pair `B B̄`, longest first, adds `2 d_i` to the least-loaded plane. -/
def pairStep : List ℕ → List ℕ → List ℕ
  | D, [] => D
  | D, b :: bs => pairStep (addAt D (argMin D) (2 * b)) bs

/-- Step 2: the `p` largest crossings `A`, longest first, each to the least-loaded plane that has
none yet. -/
def firstStep : List ℕ → List Bool → List ℕ → List ℕ
  | D, _, [] => D
  | D, got, a :: as =>
    match argMinAmong D fun k => !got.getD k true with
    | none => D
    | some k => firstStep (addAt D k (2 * a)) (got.set k true) as

/-- Step 3: while crossings remain, the least-loaded plane whose next pattern is available gets
the longest remaining crossing of that type (`Ā` after `A`, `A` after `Ā`; `next k = true` means
`Ā`). -/
def altStep : ℕ → List ℕ → List Bool → List ℕ → List ℕ → List ℕ
  | 0, D, _, _, _ => D
  | f + 1, D, next, as, abs =>
    let ok := fun k => if next.getD k true then !abs.isEmpty else !as.isEmpty
    match argMinAmong D ok with
    | none => D
    | some k =>
      if next.getD k true then
        altStep f (addAt D k (2 * abs.headD 0)) (next.set k false) as abs.tail
      else altStep f (addAt D k (2 * as.headD 0)) (next.set k true) as.tail abs

/-- The plane loads of the four steps of arXiv §3.2 for `p` planes, crossings `A` (`as`), crossings
`Ā` (`abs`) and pairs `B B̄` (`bs`), all as durations, longest first. Under symmetric durations
`2 max(d, d̄) = 2 min(d, d̄) = 2d` and a crossing lasts `d + d̄ = 2d`. -/
def arxivLoads (p : ℕ) (as abs bs : List ℕ) : List ℕ :=
  let D := pairStep (List.replicate p 0) bs
  let D := firstStep D (List.replicate p false) (as.take p)
  let D := altStep ((as.drop p).length + abs.length) D (List.replicate p true) (as.drop p) abs
  pairStep D bs

/-- The makespan of the four steps of arXiv §3.2. -/
def arxivRun (p : ℕ) (as abs bs : List ℕ) : ℕ := maxLoad (arxivLoads p as abs bs)

/-! ### The PPPs -/

/-- All count vectors over `n` cities with total `m`. -/
def vecs : ℕ → ℕ → List (List ℕ)
  | 0, m => if m = 0 then [[]] else []
  | n + 1, m => (List.range (m + 1)).flatMap fun k => (vecs n (m - k)).map (k :: ·)

/-- All count vectors below `u`, coordinatewise (the sub-multisets). -/
def subVecs : List ℕ → List (List ℕ)
  | [] => [[]]
  | u :: us => (List.range (u + 1)).flatMap fun k => (subVecs us).map (k :: ·)

/-- Coordinatewise difference of count vectors (the multiset difference). -/
def vsub (u v : List ℕ) : List ℕ := List.zipWith (· - ·) u v

/-- Coordinatewise minimum of count vectors (the multiset intersection). -/
def vmin (u v : List ℕ) : List ℕ := List.zipWith min u v

/-- The makespan EvoCOP 2015 gives the PPP `(e, w)` (counts): the least, over the sub-multisets
`β` of `e ∩ w`, of the two steps on `(e − β, w − β, β)`. -/
def evocopMakespan {n : ℕ} (d : Fin n → ℕ) (p : ℕ) (e w : List ℕ) : ℕ :=
  ((subVecs (vmin e w)).map fun β =>
    evocopRun p (durs d (vsub e β)) (durs d (vsub w β)) (durs d β)).foldr min
    (evocopRun p (durs d e) (durs d w) [])

/-- The (cost, makespan) points of EvoCOP 2015's algorithm: one per PPP `(e, w)` with `|e| = t`
and `|w| = t − p`. -/
def evocopPoints {n : ℕ} (d c : Fin n → ℕ) (t p : ℕ) : List (ℕ × ℕ) :=
  (vecs n t).flatMap fun e => (vecs n (t - p)).map fun w =>
    (costOf c e + costOf c w, evocopMakespan d p e w)

/-- The PPPs of arXiv §3.1 as count vectors `(a, ā, b)`: `|a| = k + p`, `|ā| = k`,
`|b| = t − p − k` for `k = 0, …, t − p`. -/
def triples (n t p : ℕ) : List (List ℕ × List ℕ × List ℕ) :=
  (List.range (t - p + 1)).flatMap fun k =>
    (vecs n (k + p)).flatMap fun a => (vecs n k).flatMap fun ab =>
      (vecs n (t - p - k)).map fun b => (a, ab, b)

/-- The (cost, makespan) points of arXiv §3.2: one per PPP `(a, ā, b)`, of cost
`c(a) + c(ā) + 2 c(b)`. -/
def arxivPoints {n : ℕ} (d c : Fin n → ℕ) (t p : ℕ) : List (ℕ × ℕ) :=
  (triples n t p).map fun x =>
    (costOf c x.1 + costOf c x.2.1 + 2 * costOf c x.2.2,
      arxivRun p (durs d x.1) (durs d x.2.1) (durs d x.2.2))

/-- `x ≤ y` in both coordinates, as a `Bool`. -/
def leB (x y : ℕ × ℕ) : Bool := decide (x.1 ≤ y.1) && decide (x.2 ≤ y.2)

/-- Insert a point into a list sorted by increasing cost. -/
def insertByCost (x : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertByCost x ys

/-- The Pareto-minimal points of a list, without repetitions, by increasing cost. -/
def paretoMin (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((S.filter fun x => S.all fun y => !leB y x || y == x).dedup).foldr insertByCost []

/-! ### Every way to break the ties of `ArgMin`

The papers do not say how `ArgMin` breaks ties. The functions below follow every choice: they
return the list of all the outcomes, one per sequence of tie-breaking choices. The theorems on the
two instances are stated over all of them. -/

/-- The planes that `ok` accepts and whose load is the least among them: every value `ArgMin`
can take. -/
def minIdxs (D : List ℕ) (ok : ℕ → Bool) : List ℕ :=
  let cand := (List.range D.length).filter ok
  match (cand.map fun k => D.getD k 0).min? with
  | none => []
  | some m => cand.filter fun k => D.getD k 0 = m

/-- `loop1` under every tie-breaking. -/
def loop1All : ℕ → List ℕ → List Bool → List ℕ → List ℕ → List (List ℕ × List Bool × List ℕ)
  | 0, D, S, es, _ => [(D, S, es)]
  | _ + 1, D, S, es, [] => [(D, S, es)]
  | f + 1, D, S, es, w :: ws =>
    (minIdxs D fun _ => true).flatMap fun k =>
      if S.getD k true then
        match es with
        | [] => [(D, S, es)]
        | e :: es' => loop1All f (addAt D k (2 * e)) (S.set k false) es' (w :: ws)
      else loop1All f (addAt D k (2 * w)) (S.set k true) es ws

/-- `loop2` under every tie-breaking. -/
def loop2All : List ℕ → List Bool → List ℕ → List (List ℕ)
  | D, _, [] => [D]
  | D, S, e :: es =>
    let ks := minIdxs D fun k => S.getD k false
    if ks.isEmpty then [D]
    else ks.flatMap fun k => loop2All (addAt D k (2 * e)) (S.set k false) es

/-- `p3Step` under every choice of the two least-loaded planes. -/
def p3StepAll : List ℕ → List ℕ → List (List ℕ)
  | D, [] => [D]
  | D, b :: bs =>
    (minIdxs D fun _ => true).flatMap fun k₁ =>
      let ks := minIdxs D fun k => k != k₁
      if ks.isEmpty then p3StepAll (addAt D k₁ (4 * b)) bs
      else ks.flatMap fun k₂ => p3StepAll (addAt (addAt D k₁ (2 * b)) k₂ (2 * b)) bs

/-- The private makespans of EvoCOP 2015's two steps, under every tie-breaking. -/
def evocopLoadsAll (p : ℕ) (es ws bs : List ℕ) : List (List ℕ) :=
  (loop1All (es.length + ws.length) (List.replicate p 0) (List.replicate p true) es ws).flatMap
    fun r => (loop2All r.1 r.2.1 r.2.2).flatMap fun D => p3StepAll D bs

/-- Every makespan EvoCOP 2015's two steps can give the PPP `(e, w)` (counts): for every
sub-multiset `β` of `e ∩ w` (the P3 patterns) and every tie-breaking. -/
def evocopMakespansAll {n : ℕ} (d : Fin n → ℕ) (p : ℕ) (e w : List ℕ) : List ℕ :=
  (subVecs (vmin e w)).flatMap fun β =>
    (evocopLoadsAll p (durs d (vsub e β)) (durs d (vsub w β)) (durs d β)).map maxLoad

/-- `pairStep` under every tie-breaking. -/
def pairStepAll : List ℕ → List ℕ → List (List ℕ)
  | D, [] => [D]
  | D, b :: bs => (minIdxs D fun _ => true).flatMap fun k => pairStepAll (addAt D k (2 * b)) bs

/-- `firstStep` under every tie-breaking. -/
def firstStepAll : List ℕ → List Bool → List ℕ → List (List ℕ)
  | D, _, [] => [D]
  | D, got, a :: as =>
    let ks := minIdxs D fun k => !got.getD k true
    if ks.isEmpty then [D]
    else ks.flatMap fun k => firstStepAll (addAt D k (2 * a)) (got.set k true) as

/-- `altStep` under every tie-breaking. -/
def altStepAll : ℕ → List ℕ → List Bool → List ℕ → List ℕ → List (List ℕ)
  | 0, D, _, _, _ => [D]
  | f + 1, D, next, as, abs =>
    let ks := minIdxs D fun k => if next.getD k true then !abs.isEmpty else !as.isEmpty
    if ks.isEmpty then [D]
    else ks.flatMap fun k =>
      if next.getD k true then
        altStepAll f (addAt D k (2 * abs.headD 0)) (next.set k false) as abs.tail
      else altStepAll f (addAt D k (2 * as.headD 0)) (next.set k true) as.tail abs

/-- The plane loads of the four steps of arXiv §3.2, under every tie-breaking. -/
def arxivLoadsAll (p : ℕ) (as abs bs : List ℕ) : List (List ℕ) :=
  (pairStepAll (List.replicate p 0) bs).flatMap fun D =>
    (firstStepAll D (List.replicate p false) (as.take p)).flatMap fun D =>
      (altStepAll ((as.drop p).length + abs.length) D (List.replicate p true) (as.drop p)
        abs).flatMap fun D => pairStepAll D bs

/-- Every makespan the four steps of arXiv §3.2 can give the PPP `x = (a, ā, b)` (counts), under
every tie-breaking. -/
def arxivMakespansAll {n : ℕ} (d : Fin n → ℕ) (p : ℕ) (x : List ℕ × List ℕ × List ℕ) :
    List ℕ :=
  (arxivLoadsAll p (durs d x.1) (durs d x.2.1) (durs d x.2.2)).map maxLoad

/-- The cost of the PPP `(a, ā, b)` of arXiv §3.1: `c(a) + c(ā) + 2 c(b)`. -/
def arxivCost {n : ℕ} (c : Fin n → ℕ) (x : List ℕ × List ℕ × List ℕ) : ℕ :=
  costOf c x.1 + costOf c x.2.1 + 2 * costOf c x.2.2

/-! ### The `lpt` instance: `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2` -/

/-- The landings of the front point `(260, 60)` as a PPP: eastbound `e` = three landings in city 1
(`d = 6`) and two in city 2 (`d = 10`), westbound `w` = two in city 1 and one in city 2. Its cost
is 260. -/
theorem lpt_ppp_cost : costOf ![40, 20] [3, 2] + costOf ![40, 20] [2, 1] = 260 := by decide +kernel

/-- **§4 of the note.** On the landings of `(260, 60)`, EvoCOP's Algorithm 1 without P3 gives
every plane a crossing of 20 first and ends with the private makespans `(52, 68)`, in some order,
whatever the tie-breaking. -/
theorem evocop_lpt_noP3 :
    ∀ D ∈ evocopLoadsAll 2 (durs ![6, 10] [3, 2]) (durs ![6, 10] [2, 1]) [],
      D = [52, 68] ∨ D = [68, 52] := by
  decide +kernel

/-- With ties broken towards the first plane, the private makespans are `(52, 68)`. -/
theorem evocop_lpt_noP3_first :
    evocopLoads 2 (durs ![6, 10] [3, 2]) (durs ![6, 10] [2, 1]) [] = [52, 68] := by decide +kernel

/-- With its best set of P3 patterns, EvoCOP's greedy schedules the landings of `(260, 60)` in 64,
still above 60, whatever the tie-breaking. -/
theorem evocop_lpt_ppp : ∀ m ∈ evocopMakespansAll ![6, 10] 2 [3, 2] [2, 1], 64 ≤ m := by
  decide +kernel

/-- With ties broken towards the first plane, the best set of P3 patterns gives 64. -/
theorem evocop_lpt_ppp_first : evocopMakespan ![6, 10] 2 [3, 2] [2, 1] = 64 := by decide +kernel

/-- The front EvoCOP's algorithm returns on the `lpt` instance. -/
theorem evocop_lpt_front : paretoMin (evocopPoints ![6, 10] ![40, 20] 5 2) =
    [(160, 80), (200, 72), (240, 64), (280, 56), (320, 48)] := by decide +kernel

/-- The front the four steps of arXiv §3.2 return on the `lpt` instance: the same. -/
theorem arxiv_lpt_front : paretoMin (arxivPoints ![6, 10] ![40, 20] 5 2) =
    [(160, 80), (200, 72), (240, 64), (280, 56), (320, 48)] := by decide +kernel

/-- **EvoCOP's greedy is not exact (§5).** On `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2`, the
point `(260, 60)` is Pareto-optimal among all feasible plans, whatever the central flights, but for
every PPP `(e, w)` of cost at most 260, every set `β` of P3 patterns and every tie-breaking,
EvoCOP's two steps give a makespan above 60. -/
theorem evocop_misses_lpt (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![6, 10], ![6, 10], dc⟩ ![40, 20] 5 2) (260, 60) ∧
      ∀ e ∈ vecs 2 5, ∀ w ∈ vecs 2 (5 - 2), costOf ![40, 20] e + costOf ![40, 20] w ≤ 260 →
        ∀ m ∈ evocopMakespansAll ![6, 10] 2 e w, 60 < m :=
  ⟨((Examples.lptCounterexample_front dc).mem_iff_minimal _).mp (by decide),
    by decide +kernel⟩

/-- **The greedy of arXiv §3.2 is not exact.** On the same instance, for every PPP `(a, ā, b)` of
cost at most 260 and every tie-breaking, the four steps (with Steps 2 and 3 read as in the module
documentation) give a makespan above 60. -/
theorem arxiv_misses_lpt (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![6, 10], ![6, 10], dc⟩ ![40, 20] 5 2) (260, 60) ∧
      ∀ x ∈ triples 2 5 2, arxivCost ![40, 20] x ≤ 260 →
        ∀ m ∈ arxivMakespansAll ![6, 10] 2 x, 60 < m :=
  ⟨((Examples.lptCounterexample_front dc).mem_iff_minimal _).mp (by decide),
    by decide +kernel⟩

/-! ### The `p3First` instance: `d = (1, 3)`, `c = (9, 5)`, `t = 4`, `p = 2` -/

/-- The certificate of the `p3First` instance (`golden-p3-first-counterexample.cert`). -/
def p3FirstCert : Cert where
  n := 2
  t := 4
  p := 2
  d := ![1, 3]
  dbar := ![1, 3]
  c := ![9, 5]
  assumptions := ["S"]
  front := [(54, 6), (50, 8), (46, 10), (42, 12), (38, 14), (30, 18)]
  plans := [
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .cg, 1, 2, some 0⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 0, 4, 5, some 1⟩, ⟨.city 0, .cg, 5, 6, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 2, some 2⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 0, 4, 5, some 3⟩, ⟨.city 0, .cg, 5, 6, some 3⟩]],
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .ci, 1, 2, none⟩,
         ⟨.ci, .city 1, 2, 5, some 1⟩, ⟨.city 1, .cg, 5, 8, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 2, some 2⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 0, 4, 5, some 3⟩, ⟨.city 0, .cg, 5, 6, some 3⟩,
         ⟨.cg, .city 0, 6, 7, none⟩, ⟨.city 0, .cg, 7, 8, some 0⟩]],
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .cg, 1, 2, some 0⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 1, 4, 7, some 1⟩, ⟨.city 1, .cg, 7, 10, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 2, some 2⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 1, 4, 7, some 3⟩, ⟨.city 1, .cg, 7, 10, some 3⟩]],
    ![[⟨.ci, .city 1, 0, 3, some 0⟩, ⟨.city 1, .ci, 3, 6, none⟩,
         ⟨.ci, .city 1, 6, 9, some 1⟩, ⟨.city 1, .cg, 9, 12, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 2, some 2⟩,
         ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
         ⟨.ci, .city 0, 4, 5, some 3⟩, ⟨.city 0, .cg, 5, 6, some 3⟩,
         ⟨.cg, .city 1, 6, 9, none⟩, ⟨.city 1, .cg, 9, 12, some 0⟩]],
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .cg, 1, 2, some 0⟩,
         ⟨.cg, .city 1, 2, 5, none⟩, ⟨.city 1, .ci, 5, 8, none⟩,
         ⟨.ci, .city 1, 8, 11, some 1⟩, ⟨.city 1, .cg, 11, 14, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 2, some 2⟩,
         ⟨.cg, .city 1, 2, 5, none⟩, ⟨.city 1, .ci, 5, 8, none⟩,
         ⟨.ci, .city 1, 8, 11, some 3⟩, ⟨.city 1, .cg, 11, 14, some 3⟩]],
    ![[⟨.ci, .city 1, 0, 3, some 0⟩, ⟨.city 1, .cg, 3, 6, some 0⟩,
         ⟨.cg, .city 1, 6, 9, none⟩, ⟨.city 1, .ci, 9, 12, none⟩,
         ⟨.ci, .city 1, 12, 15, some 1⟩, ⟨.city 1, .cg, 15, 18, some 1⟩],
      [⟨.ci, .city 1, 0, 3, some 2⟩, ⟨.city 1, .cg, 3, 6, some 2⟩,
         ⟨.cg, .city 1, 6, 9, none⟩, ⟨.city 1, .ci, 9, 12, none⟩,
         ⟨.ci, .city 1, 12, 15, some 3⟩, ⟨.city 1, .cg, 15, 18, some 3⟩]]]
  gaps := [.relaxed, .relaxed, .relaxed, .relaxed, .relaxed]

set_option maxRecDepth 100000 in
/-- The kernel accepts the certificate of the `p3First` instance. -/
theorem p3FirstCert_check : p3FirstCert.check = true := by decide +kernel

/-- **The exact front of the `p3First` instance**, for every table of central flight durations:
`(54, 6), (50, 8), (46, 10), (42, 12), (38, 14), (30, 18)`. -/
theorem p3First_front (dc : Fin 2 → Fin 2 → ℕ) :
    IsParetoFront (achievable ⟨![1, 3], ![1, 3], dc⟩ ![9, 5] 4 2)
      [(54, 6), (50, 8), (46, 10), (42, 12), (38, 14), (30, 18)] :=
  p3FirstCert.check_sound_relaxed p3FirstCert_check (by decide) dc

/-- **EvoCOP's greedy reaches `(42, 12)`** on the `p3First` instance: the PPP `e = (1, 1, 2, 2)`,
`w = (1, 2)` of cost 42 with one P3 at city 2 gets makespan 12 whatever the tie-breaking. -/
theorem evocop_reaches_p3First :
    costOf ![9, 5] [2, 2] + costOf ![9, 5] [1, 1] = 42 ∧
      ∀ D ∈ evocopLoadsAll 2 (durs ![1, 3] (vsub [2, 2] [0, 1])) (durs ![1, 3] (vsub [1, 1] [0, 1]))
        (durs ![1, 3] [0, 1]), maxLoad D = 12 := by
  decide +kernel

/-- EvoCOP's algorithm, with ties broken towards the first plane, finds the front of the
`p3First` instance. -/
theorem evocop_p3First_front : paretoMin (evocopPoints ![1, 3] ![9, 5] 4 2) =
    [(30, 18), (38, 14), (42, 12), (46, 10), (50, 8), (54, 6)] := by decide +kernel

/-- The four steps of arXiv §3.2 miss `(42, 12)` on the `p3First` instance. -/
theorem arxiv_p3First_front : paretoMin (arxivPoints ![1, 3] ![9, 5] 4 2) =
    [(30, 18), (38, 14), (46, 10), (50, 8), (54, 6)] := by decide +kernel

/-- **The greedy of arXiv §3.2 is not exact (§4).** On `d = (1, 3)`, `c = (9, 5)`, `t = 4`, `p = 2`,
the point `(42, 12)` is Pareto-optimal among all feasible plans, whatever the central flights, but
for every PPP `(a, ā, b)` of cost at most 42 and every tie-breaking, the four steps (with Steps 2
and 3 read as in the module documentation) give a makespan above 12. -/
theorem arxiv_misses_p3First (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![1, 3], ![1, 3], dc⟩ ![9, 5] 4 2) (42, 12) ∧
      ∀ x ∈ triples 2 4 2, arxivCost ![9, 5] x ≤ 42 →
        ∀ m ∈ arxivMakespansAll ![1, 3] 2 x, 12 < m :=
  ⟨((p3First_front dc).mem_iff_minimal _).mp (by decide), by decide +kernel⟩

end Greedy

/-! ### Example 4.7: without (A1) and (AΔ), a plan beats the admissible partitions -/

namespace Ex413

/-- The hub durations of Example 4.7, `d = d̄ = (2, 3, 9, 11)` (cities numbered from `0` here). -/
def d : Fin 4 → ℕ := ![2, 3, 9, 11]

/-- The landing costs of Example 4.7, `c = (50, 44, 17, 0)`. -/
def c : Fin 4 → ℕ := ![50, 44, 17, 0]

/-- The central flights of Example 4.7: `d₁₂ = 1`, `d₁₃ = 5`, `d₁₄ = 6`, `d₂₃ = 3`, `d₂₄ = 6`,
`d₃₄ = 1` in the note's numbering. The diagonal is never flown. -/
def dc : Fin 4 → Fin 4 → ℕ := ![![0, 1, 5, 6], ![1, 0, 3, 6], ![5, 3, 0, 1], ![6, 6, 1, 0]]

/-- The network of Example 4.7: symmetric hub durations and the central flights `dc`. -/
def net : Network 4 := ⟨d, d, dc⟩

/-- The plan of Example 4.7 (passengers numbered from `0`). Plane 1 crosses at city 1, picks up
at city 4 the passenger that plane 3 dropped there, then crosses back and forth at city 2;
plane 2 crosses at city 2 twice and at city 4; plane 3 drops a passenger at city 4, flies the
central flight `4 → 3` back towards `C_I`, and crosses at city 3. -/
def plan : Plan 4 6 3 :=
  ![[⟨.ci, .city 0, 0, 2, some 0⟩, ⟨.city 0, .cg, 2, 4, some 0⟩,
      ⟨.cg, .city 3, 4, 15, none⟩, ⟨.city 3, .cg, 15, 26, some 1⟩,
      ⟨.cg, .city 1, 26, 29, none⟩, ⟨.city 1, .ci, 29, 32, none⟩,
      ⟨.ci, .city 1, 32, 35, some 2⟩, ⟨.city 1, .cg, 35, 38, some 2⟩],
    [⟨.ci, .city 1, 0, 3, some 3⟩, ⟨.city 1, .cg, 3, 6, some 3⟩,
      ⟨.cg, .city 1, 6, 9, none⟩, ⟨.city 1, .ci, 9, 12, none⟩,
      ⟨.ci, .city 3, 12, 23, some 4⟩, ⟨.city 3, .cg, 23, 34, some 4⟩],
    [⟨.ci, .city 3, 0, 11, some 1⟩, ⟨.city 3, .city 2, 11, 12, none⟩, ⟨.city 2, .ci, 12, 21, none⟩,
      ⟨.ci, .city 2, 21, 30, some 5⟩, ⟨.city 2, .cg, 30, 39, some 5⟩]]

/-- The flights the plan uses: the hub flights, and the central flight between cities 4 and 3. -/
def usedGraph : FlightGraph 4 :=
  ⟨fun a b => match a, b with
    | .city i, .city j => if i = 3 ∧ j = 2 then some 1 else none
    | a, b => Network.duration ⟨d, d, fun _ _ => 0⟩ a b⟩

/-- The plan is feasible on the flights it uses. -/
theorem plan_feasible_used : GFeasible usedGraph plan :=
  gFeasible_of_planOKDur (by decide +kernel)

/-- **The plan is feasible** in every network with the hub durations `d` (symmetric) and a
central flight of duration 1 from city 4 to city 3, whatever the other central flights. -/
theorem plan_feasible (dc' : Fin 4 → Fin 4 → ℕ) (h : dc' 3 2 = 1) :
    Feasible ⟨d, d, dc'⟩ plan := by
  refine (feasible_iff_gFeasible _ _).mpr (plan_feasible_used.mono fun a b τ hab => ?_)
  cases a <;> cases b <;> simp only [usedGraph, Network.toGraph, Network.duration] at hab ⊢ <;>
    try exact hab
  rename_i i j
  split_ifs at hab with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [h]
    exact hab

/-- The plan is feasible in the network of Example 4.7. -/
theorem plan_feasible_net : Feasible net plan := plan_feasible dc rfl

/-- The plan costs 260. -/
theorem plan_cost : planCost c plan = 260 := by decide +kernel

/-- The plan has makespan 39. -/
theorem plan_makespan : planMakespan plan = 39 := by decide +kernel

/-- The central flights violate (A1): `d₃ + d₄ = 20 > 1 = d₃₄`. -/
theorem not_A1 : ¬ net.A1 := fun h => absurd (h 3 2) (by decide)

/-- The central flights violate (AΔ): `d₄ = 11 > 10 = d₃ + d₃₄`. -/
theorem not_ATri : ¬ net.ATri := fun h =>
  absurd (h .ci (.city 2) (.city 3) (by decide) 11 9 1 rfl rfl rfl) (by decide)

/-- They violate even the triangles through a hub (`ATriHub`), all that Theorem 4.4 uses. -/
theorem not_ATriHub : ¬ net.ATriHub := fun h => absurd (h 2 3).1 (by decide)

set_option maxRecDepth 100000 in
/-- `E(19) = 264`, by the link-forest DP in the kernel. -/
theorem minCost_19 : minCost d c 6 3 19 = 264 := by
  rw [← treeBoundAt_eq_minCost d c (p := 3) (t := 6) (Tmax := 19) (by decide) le_rfl]
  decide +kernel

/-- Every admissible partition of `2t − p = 9` landings with every `δ(X_k) ≤ 19` costs at least
264. -/
theorem admissible_cost_ge (X : Groups 4 3) (hX : Admissible X) (hsize : size X = 2 * 6 - 3)
    (hload : ∀ k, load d (X k) ≤ 19) : 264 ≤ totalCost c X := by
  have h := minCost_le d c (t := 6) hX hsize hload
  rw [minCost_19] at h
  exact_mod_cast h

set_option maxRecDepth 100000 in
/-- The relaxation `L(19)` of the checker (`relaxedBoundAt`, a lower bound on every plan of
makespan below 40 by Lemma 3.5) is 260, the plan's cost. -/
theorem relaxedBound_19 : relaxedBoundAt 3 9 19 (oneplaneTable d c 19 9) 19 = 260 := by
  decide +kernel

/-- **The conclusion of Theorem 4.4 fails for the plan**: no admissible partition of
`2t − p = 9` landings costs at most 260 with every load `ℓ(X_k) = 2δ(X_k)` at most 39. -/
theorem no_admissible_partition :
    ¬ ∃ X : Groups 4 3, Admissible X ∧ size X = 2 * 6 - 3 ∧ totalCost c X ≤ planCost c plan ∧
      ∀ k, 2 * load d (X k) ≤ planMakespan plan := by
  rintro ⟨X, hX, hsize, hcost, hload⟩
  rw [plan_cost] at hcost
  rw [plan_makespan] at hload
  have h := minCost_le d c (t := 6) hX hsize (T := 19) fun k => by have := hload k; omega
  rw [minCost_19] at h
  have h' : ((264 : ℕ) : WithTop ℕ) ≤ ((260 : ℕ) : WithTop ℕ) :=
    h.trans (WithTop.coe_le_coe.mpr hcost)
  exact absurd (WithTop.coe_le_coe.mp h') (by decide)

/-- **No admissible point weakly dominates the plan's point `(260, 39)`.** -/
theorem not_admissible_le : ∀ x ∈ admissiblePoints net c 6 3, ¬ x ≤ (260, 39) := by
  rintro x ⟨X, hX, hsize, rfl⟩ hle
  refine no_admissible_partition ⟨X, hX, hsize, ?_, fun k => ?_⟩
  · rw [plan_cost]
    exact (Prod.le_def.mp hle).1
  · rw [plan_makespan]
    exact (Nat.mul_le_mul_left 2 (load_le_maxLoad d X k)).trans (Prod.le_def.mp hle).2

set_option maxRecDepth 100000 in
/-- **The front of admissible partitions** of Example 4.7, computed by the verified solver in the
kernel. Its consecutive points `(264, 34)` and `(228, 40)` surround the plan's makespan 39. -/
theorem admissible_front : solveFront d c 6 3 =
    [(450, 12), (432, 14), (414, 16), (396, 18), (393, 20), (364, 22), (352, 24), (332, 26),
      (314, 28), (300, 30), (282, 32), (264, 34), (228, 40), (222, 42), (182, 44), (176, 46),
      (150, 48), (132, 50), (102, 58), (51, 62), (0, 66)] := by
  decide +kernel

/-- The solver's points are the minimal admissible points (`mem_solveFront_iff`); so `(264, 34)`
and `(228, 40)` are on the front of admissible partitions, and no point of it has a makespan
strictly between 34 and 40. -/
theorem admissible_front_consecutive :
    Minimal (· ∈ admissiblePoints net c 6 3) (264, 34) ∧
      Minimal (· ∈ admissiblePoints net c 6 3) (228, 40) ∧
      ∀ x, Minimal (· ∈ admissiblePoints net c 6 3) x → ¬ (34 < x.2 ∧ x.2 < 40) := by
  have h := fun x => (mem_solveFront_iff net c (p := 3) (t := 6) (by decide) (by decide) x).symm
  change ∀ x, Minimal (· ∈ admissiblePoints net c 6 3) x ↔ x ∈ solveFront d c 6 3 at h
  simp only [h, admissible_front]
  decide

/-- **Theorem 4.5 fails for Example 4.7**: the front of admissible partitions, which the solver
computes, is not the Pareto front of the feasible plans, since it does not dominate the plan's
point `(260, 39)`. -/
theorem not_isParetoFront : ¬ IsParetoFront (achievable net c 6 3) (solveFront d c 6 3) := by
  intro hF
  obtain ⟨x, hx, hle⟩ := hF.dominates (planCost c plan, planMakespan plan)
    ⟨plan, plan_feasible_net, rfl⟩
  rw [plan_cost, plan_makespan] at hle
  have hmin := (mem_solveFront_iff net c (p := 3) (t := 6) (by decide) (by decide) x).mp hx
  exact not_admissible_le x hmin.prop hle

end Ex413

/-! ### Proposition 5.7: harmful waiting -/

namespace Prop65

/-- The durations to `C_I` of Proposition 5.7, `d = (3, 19)`. -/
def d : Fin 2 → ℕ := ![3, 19]

/-- The durations to `C_G`, `d̄ = (3, 11)`. -/
def db : Fin 2 → ℕ := ![3, 11]

/-- The landing costs, `c = (5, 1)`. -/
def c : Fin 2 → ℕ := ![5, 1]

/-- Without central flights, (A1-NS) holds: in the Lean model, whose table of central flights is
complete, every central flight at least as long as the detour through a hub, for instance of
duration 100. -/
theorem a1ns_of_long : (⟨d, db, fun _ _ => 100⟩ : Network 2).A1NS := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-! #### The role-load bound at level 73 is 14 -/

/-- A role configuration of cost 14 with every role load at most 72: plane 1 crosses at city 1
and picks up three passengers at city 2 (load `6 + 3 · 22 = 72`); the three other planes cross at
city 2 and drop one passenger there (load `30 + 38 = 68`). -/
def cfg14 : RoleConfig 2 4 where
  drop := ![0, {1}, {1}, {1}]
  pick := ![{1, 1, 1}, 0, 0, 0]
  cross := ![{0}, {1}, {1}, {1}]
  odd_card_cross := by decide
  sum_drop_eq_sum_pick := by decide

theorem cfg14_size : size cfg14.groups = 10 := by decide

theorem cfg14_cost : totalCost c cfg14.groups = 14 := by decide

theorem cfg14_load (dc : Fin 2 → Fin 2 → ℕ) : ∀ k, cfg14.roleLoad ⟨d, db, dc⟩ k ≤ 72 := by
  have h : ∀ k, cfg14.roleLoad ⟨d, db, fun _ _ => 0⟩ k ≤ 72 := by decide
  exact h

set_option maxRecDepth 100000 in
/-- The `roles` bound at level 73, computed in the kernel. -/
theorem rolesBound_73 : rolesBoundAt 4 10 73 (roleLayers d db c 73 10)
    (oneplaneTable (fillW d db) c (4 * 73) 10) 73 = 14 := by
  decide +kernel

/-- **The cheapest role configuration with every role load at most 73 costs 14** (with
passenger count 7, that is `2t − p = 10` landings). -/
theorem cheapest_roleConfig (dc : Fin 2 → Fin 2 → ℕ) :
    (∃ cfg : RoleConfig 2 4, size cfg.groups = 10 ∧ totalCost c cfg.groups = 14 ∧
        ∀ k, cfg.roleLoad ⟨d, db, dc⟩ k ≤ 73) ∧
      ∀ cfg : RoleConfig 2 4, size cfg.groups = 10 → (∀ k, cfg.roleLoad ⟨d, db, dc⟩ k ≤ 73) →
        14 ≤ totalCost c cfg.groups := by
  refine ⟨⟨cfg14, cfg14_size, cfg14_cost, fun k => (cfg14_load dc k).trans (by decide)⟩,
    fun cfg hsize hload => ?_⟩
  have h := rolesBoundAt_le_totalCost d db c dc (Tmax := 73) cfg hsize hload
  rw [rolesBound_73] at h
  exact_mod_cast h

/-! #### The search below makespan 74, split for the kernel -/

/-- The exhaustive search of a `search` gap below makespan 74 (level 73), for configurations
cheaper than 18. -/
def search73 : SearchData 2 := ⟨d, db, c, 4, 10, 73, ((18 : ℕ) : WithTop ℕ)⟩

/-- The plane options of the search (`search73.opts`), as a literal. -/
def opts73 : List (POpt 2) :=
  [
    ([], [], [0]), ([], [], [0, 0, 0]), ([], [], [0, 0, 1]), ([], [], [0, 1, 1]),
    ([], [], [1]), ([], [0], [0]), ([], [0], [0, 0, 1]), ([], [0], [0, 1, 1]),
    ([], [0], [1]), ([], [0, 0], [0]), ([], [0, 0], [1]), ([], [0, 0, 0], [1]),
    ([], [0, 0, 0, 1], [1]), ([], [0, 0, 1], [0]), ([], [0, 0, 1], [1]), ([], [0, 0, 1, 0], [1]),
    ([], [0, 0, 1, 1], [0]), ([], [0, 1], [0]), ([], [0, 1], [0, 0, 1]), ([], [0, 1], [1]),
    ([], [0, 1, 0], [0]), ([], [0, 1, 0], [1]), ([], [0, 1, 0, 0], [1]), ([], [0, 1, 0, 1], [0]),
    ([], [0, 1, 1], [0]), ([], [0, 1, 1, 0], [0]), ([], [1], [0]), ([], [1], [0, 0, 0]),
    ([], [1], [0, 0, 1]), ([], [1], [1]), ([], [1, 0], [0]), ([], [1, 0], [0, 0, 1]),
    ([], [1, 0], [1]), ([], [1, 0, 0], [0]), ([], [1, 0, 0], [1]), ([], [1, 0, 0, 0], [1]),
    ([], [1, 0, 0, 1], [0]), ([], [1, 0, 1], [0]), ([], [1, 0, 1, 0], [0]), ([], [1, 1], [0]),
    ([], [1, 1], [0, 0, 0]), ([], [1, 1, 0], [0]), ([], [1, 1, 0, 0], [0]), ([], [1, 1, 1], [0]),
    ([0], [], [0]), ([0], [], [0, 0, 1]), ([0], [], [0, 1, 1]), ([0], [], [1]),
    ([0], [0], [0]), ([0], [0], [1]), ([0], [0, 0], [1]), ([0], [0, 0, 1], [1]),
    ([0], [0, 1], [0]), ([0], [0, 1], [1]), ([0], [0, 1, 0], [1]), ([0], [0, 1, 1], [0]),
    ([0], [1], [0]), ([0], [1], [0, 0, 1]), ([0], [1], [1]), ([0], [1, 0], [0]),
    ([0], [1, 0], [1]), ([0], [1, 0, 0], [1]), ([0], [1, 0, 1], [0]), ([0], [1, 1], [0]),
    ([0], [1, 1, 0], [0]), ([0, 0], [], [0]), ([0, 0], [], [1]), ([0, 0], [0], [1]),
    ([0, 0], [0, 1], [1]), ([0, 0], [1], [0]), ([0, 0], [1], [1]), ([0, 0], [1, 0], [1]),
    ([0, 0], [1, 1], [0]), ([0, 0, 0], [], [1]), ([0, 0, 0], [1], [1]), ([0, 0, 1], [], [0]),
    ([0, 1], [], [0]), ([0, 1], [0], [0]), ([0, 1], [1], [0]), ([0, 1, 0], [], [0]),
    ([1], [], [0]), ([1], [], [0, 0, 0]), ([1], [], [1]), ([1], [0], [0]),
    ([1], [0, 0], [0]), ([1], [0, 1], [0]), ([1], [1], [0]), ([1], [1, 0], [0]),
    ([1, 0], [], [0]), ([1, 0], [0], [0]), ([1, 0], [1], [0]), ([1, 0, 0], [], [0])
  ]

set_option maxRecDepth 100000 in
theorem opts73_eq : search73.opts = opts73 := by decide +kernel

/-- The test of one tuple of plane options: not a full configuration, or every assignment of its
pick-ups to drop-offs has a closed form above the level. -/
def tupleOK (D : SearchData 2) (tu : List (POpt 2)) : Bool :=
  !D.full tu || (SearchData.assignments (SearchData.pickSlots tu) (SearchData.dropSlots tu)).all
    fun asg => decide (D.T < D.tmplOf tu asg)

/-- The search restricted to the tuples whose first plane takes the option `o`. -/
def firstOK (D : SearchData 2) (os : List (POpt 2)) (o : POpt 2) : Bool :=
  if ((0 + D.optCost o : ℕ) : WithTop ℕ) < D.C ∧ SearchData.optLand (n := 2) o ≤ D.s then
    ((D.tuples os 3 (0 + D.optCost o) (D.s - SearchData.optLand (n := 2) o)).map (o :: ·)).all
      (tupleOK D)
  else true

/-- The search of `search73` splits by the option of the first plane. -/
theorem search73_closed_eq :
    search73.closed = search73.opts.all (firstOK search73 search73.opts) := by
  change (search73.tuples search73.opts 4 0 10).all (tupleOK search73) = _
  rw [SearchData.tuples, List.all_flatMap]
  congr 1
  funext o
  unfold firstOK
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem all_drop_of_take {α : Type*} (l : List α) (F : α → Bool) (a b : ℕ)
    (h₁ : ((l.drop a).take b).all F = true) (h₂ : (l.drop (a + b)).all F = true) :
    (l.drop a).all F = true := by
  rw [← List.take_append_drop b (l.drop a), List.all_append, h₁, List.drop_drop, h₂]
  rfl

set_option maxRecDepth 100000 in
theorem search73_0 : ((opts73.drop 0).take 4).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_4 : ((opts73.drop 4).take 1).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_5 : ((opts73.drop 5).take 24).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_29 : ((opts73.drop 29).take 1).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_30 : ((opts73.drop 30).take 28).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_58 : ((opts73.drop 58).take 24).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_82 : ((opts73.drop 82).take 1).all (firstOK search73 opts73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem search73_83 : (opts73.drop 83).all (firstOK search73 opts73) = true := by decide +kernel

/-- **The search is closed**: no valid scheduled configuration of cost below 18 has a closed form
(the template makespan of Lemma 5.5) at most 73. -/
theorem search73_closed : search73.closed = true := by
  rw [search73_closed_eq, opts73_eq]
  exact all_drop_of_take _ _ 0 4 search73_0 <| all_drop_of_take _ _ 4 1 search73_4 <|
    all_drop_of_take _ _ 5 24 search73_5 <| all_drop_of_take _ _ 29 1 search73_29 <|
    all_drop_of_take _ _ 30 28 search73_30 <| all_drop_of_take _ _ 58 24 search73_58 <|
    all_drop_of_take _ _ 82 1 search73_82 search73_83

/-- **Every valid scheduled configuration of cost below 18 waits harmfully**: whatever its orders
and link matching, its template makespan exceeds 73. -/
theorem tmpl_gt_of_cost_lt (S : Sched 2 4) (hS : S.Valid) (hsize : S.size = 10)
    (hcost : S.cost c < 18) : 73 < S.tmpl d db :=
  SearchData.closed_sound search73 search73_closed S hS hsize
    (show ((S.cost c : ℕ) : WithTop ℕ) < ((18 : ℕ) : WithTop ℕ) by exact_mod_cast hcost)

/-- **No plan of makespan at most 73 costs less than 18**, for every table of central flights
satisfying (A1-NS): Theorem 5.3 turns the plan into a valid scheduled configuration, of cost at
most the plan's and closed form at most its makespan. -/
theorem cost_ge_of_makespan_le (dc : Fin 2 → Fin 2 → ℕ) (hA : (⟨d, db, dc⟩ : Network 2).A1NS)
    {P : Plan 2 7 4} (hP : Feasible ⟨d, db, dc⟩ P) (hM : planMakespan P ≤ 73) :
    18 ≤ planCost c P := by
  obtain ⟨S, hS, hsize, hcost, htmpl⟩ := schedulableDomination_all c (by decide) hA hP
  by_contra hlt
  have := tmpl_gt_of_cost_lt S hS hsize (by omega)
  change S.tmpl d db ≤ planMakespan P at htmpl
  omega

/-- The same without central flights: the plans of the clique instance are plans of the network
whose central flights last 100, which satisfies (A1-NS). -/
theorem cost_ge_of_makespan_le_noCentral {P : Plan 2 7 4}
    (hP : GFeasible (cliqueGraph d db) P) (hM : planMakespan P ≤ 73) :
    18 ≤ planCost c P :=
  cost_ge_of_makespan_le _ a1ns_of_long (hP.feasible_of_clique _) hM

/-- **Proposition 5.7.** On `d = (3, 19)`, `d̄ = (3, 11)`, `c = (5, 1)`, `t = 7`, `p = 4`, with
central flights satisfying (A1-NS), the cheapest role configuration with `2t − p = 10` landings and
every role load at most 73 costs 14, and no feasible plan of makespan at most 73 costs less than
18. -/
theorem prop65 (dc : Fin 2 → Fin 2 → ℕ) (hA : (⟨d, db, dc⟩ : Network 2).A1NS) :
    (∃ cfg : RoleConfig 2 4, size cfg.groups = 10 ∧ totalCost c cfg.groups = 14 ∧
        ∀ k, cfg.roleLoad ⟨d, db, dc⟩ k ≤ 73) ∧
      (∀ cfg : RoleConfig 2 4, size cfg.groups = 10 → (∀ k, cfg.roleLoad ⟨d, db, dc⟩ k ≤ 73) →
        14 ≤ totalCost c cfg.groups) ∧
      ∀ x ∈ achievable ⟨d, db, dc⟩ c 7 4, x.2 ≤ 73 → 18 ≤ x.1 :=
  ⟨(cheapest_roleConfig dc).1, (cheapest_roleConfig dc).2,
    fun _ ⟨_, hP, hx⟩ hM => by subst hx; exact cost_ge_of_makespan_le dc hA hP hM⟩

/-- **No harmful waiting is false** (Proposition 5.7 of the note). The configuration `cfg14` has
role loads at most 72, but every valid scheduled configuration of its cost waits: whatever the
orders and the matching, its template makespan exceeds 73. In front form: some role configuration
has cost 14 and role loads at most 73, but no feasible plan has cost at most 14 and makespan at
most 73, so the front is not the Pareto set of (cost, largest role load). -/
theorem harmful_waiting (dc : Fin 2 → Fin 2 → ℕ) (hA : (⟨d, db, dc⟩ : Network 2).A1NS) :
    (∀ k, cfg14.roleLoad ⟨d, db, dc⟩ k ≤ 72) ∧
      (∀ S : Sched 2 4, S.Valid → S.size = 10 → S.cost c ≤ 14 → 73 < S.tmpl d db) ∧
      (∃ cfg : RoleConfig 2 4, size cfg.groups = 10 ∧ totalCost c cfg.groups ≤ 14 ∧
        ∀ k, cfg.roleLoad ⟨d, db, dc⟩ k ≤ 73) ∧
      ¬ ∃ x ∈ achievable ⟨d, db, dc⟩ c 7 4, x.1 ≤ 14 ∧ x.2 ≤ 73 :=
  ⟨cfg14_load dc, fun S hS hsize hcost => tmpl_gt_of_cost_lt S hS hsize (by omega),
    ⟨cfg14, cfg14_size, cfg14_cost.le, fun k => (cfg14_load dc k).trans (by decide)⟩,
    fun ⟨x, hx, h₁, h₂⟩ => absurd ((prop65 dc hA).2.2 x hx h₂) (by omega)⟩

end Prop65

/-! ### Example 5.9: the reduction of arXiv §2.4 misses the front -/

namespace Ex611

/-- The path `C_I – a – b – C_G` of Example 5.9, with durations 1, 2, 1 (`a`, `b` are the
central vertices 0 and 1). -/
def U : FlightGraph 2 :=
  ⟨fun x y =>
    if (x = .ci ∧ y = .city 0) ∨ (x = .city 0 ∧ y = .ci) then some 1
    else if (x = .city 0 ∧ y = .city 1) ∨ (x = .city 1 ∧ y = .city 0) then some 2
    else if (x = .city 1 ∧ y = .cg) ∨ (x = .cg ∧ y = .city 1) then some 1
    else none⟩

/-- The landing costs `c_a = c_b = 1`. -/
def c : Fin 2 → ℕ := ![1, 1]

/-- `U` is undirected. -/
theorem U_undirected : U.Undirected := by
  intro a b
  have : ∀ a ∈ allLocs 2, ∀ b ∈ allLocs 2, U.dur a b = U.dur b a := by decide +kernel
  exact this a (mem_allLocs a) b (mem_allLocs b)

/-- `U` has no flight between the hubs. -/
theorem U_noHubFlight : U.NoHubFlight := ⟨by decide +kernel, by decide +kernel⟩

/-- **`f(U)` has two cities**: `v_a = (C_I a, a b C_G)` and `v_b = (C_I a b, b C_G)`. -/
theorem vcities_U : vcities U =
    [⟨0, [.ci, .city 0], [.city 0, .city 1, .cg]⟩,
      ⟨1, [.ci, .city 0, .city 1], [.city 1, .cg]⟩] := by
  decide +kernel

/-- Their `(d, d̄, c)` are `(1, 3, 2)` and `(3, 1, 2)`. -/
theorem vcities_data : (vcities U).map (fun v => (pathDur U v.w, pathDur U v.e,
    pathCost c v.w + pathCost c v.e)) = [(1, 3, 2), (3, 1, 2)] := by
  decide +kernel

/-- **`f(U)` is the two-city clique instance** with `d = (1, 3)`, `d̄ = (3, 1)` and no central
flight. -/
theorem reduced_graph : (Reduced.graph U : FlightGraph 2) = cliqueGraph ![1, 3] ![3, 1] := by
  unfold Reduced.graph
  congr 1 <;> funext v <;> fin_cases v <;> decide +kernel

/-- The costs of `f(U)` are `c = (2, 2)`. -/
theorem reduced_c : (Reduced.c U c : Fin 2 → ℕ) = ![2, 2] := by
  funext v
  fin_cases v <;> decide +kernel

/-- The plan of Example 5.9 in `U` (passengers numbered from `0`). Plane 1 flies
`C_I a b a b C_G`: it drops passenger 1 at `b` at time 3, flies the central edge back to `a` and
picks passenger 2 up there at time 5. -/
def plan : Plan 2 3 2 :=
  ![[⟨.ci, .city 0, 0, 1, some 1⟩, ⟨.city 0, .city 1, 1, 3, some 1⟩, ⟨.city 1, .city 0, 3, 5, none⟩,
      ⟨.city 0, .city 1, 5, 7, some 2⟩, ⟨.city 1, .cg, 7, 8, some 2⟩],
    [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .ci, 1, 2, none⟩, ⟨.ci, .city 0, 2, 3, some 0⟩,
      ⟨.city 0, .city 1, 3, 5, some 0⟩, ⟨.city 1, .cg, 5, 6, some 0⟩, ⟨.cg, .city 1, 6, 7, none⟩,
      ⟨.city 1, .cg, 7, 8, some 1⟩]]

/-- The plan is feasible in `U`. -/
theorem plan_feasible : GFeasible U plan := gFeasible_of_planOKDur (by decide +kernel)

/-- It costs 8. -/
theorem plan_cost : planCost c plan = 8 := by decide +kernel

/-- Its makespan is 8. -/
theorem plan_makespan : planMakespan plan = 8 := by decide +kernel

/-- `(8, 8)` is a point of `U`. -/
theorem mem_gAchievable_U : ((8, 8) : ℕ × ℕ) ∈ gAchievable U c 3 2 :=
  ⟨plan, plan_feasible, by rw [plan_cost, plan_makespan]⟩

/-- The certificate of the front of `f(U)`, as written by `zeno front --certificate`, with the
fastest point closed by the `search` kind (Theorem 5.3). -/
def reducedCert : Cert2 where
  n := 2
  t := 3
  p := 2
  d := ![1, 3]
  dbar := ![3, 1]
  c := ![2, 2]
  assumptions := ["A1-NS"]
  front := [(8, 10)]
  fastest := .search
  plans := [
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .ci, 1, 2, none⟩, ⟨.ci, .city 0, 2, 3, some 1⟩,
        ⟨.city 0, .cg, 3, 6, some 1⟩],
      [⟨.ci, .city 0, 0, 1, some 2⟩, ⟨.city 0, .cg, 1, 4, some 2⟩, ⟨.cg, .city 0, 4, 7, none⟩,
        ⟨.city 0, .cg, 7, 10, some 0⟩]]]
  gaps := []

set_option maxRecDepth 100000 in
/-- The kernel accepts the certificate of `f(U)`. -/
theorem reducedCert_check : reducedCert.check = true := by decide +kernel

/-- **The front of `f(U)` is `{(8, 10)}`**: its plans, which have no central flight, are plans of
every network with its hub durations, and in such a network with (A1-NS) the certificate is
sound. -/
theorem reduced_front :
    IsParetoFront (gAchievable (Reduced.graph U) (Reduced.c U c) 3 2) [(8, 10)] := by
  rw [reduced_graph, reduced_c]
  refine ⟨fun x hx => ?_, fun y ⟨P, hP, hy⟩ => ?_, by simp⟩
  · rw [List.mem_singleton.mp hx]
    exact ⟨_, gFeasible_of_planOKDur (P := reducedCert.plans.headD fun _ => [])
      (by decide +kernel), by decide +kernel⟩
  · have hF := reducedCert.check_sound reducedCert_check (fun _ _ => 100)
      (fun _ i j => by fin_cases i <;> fin_cases j <;> decide)
    exact hF.dominates y ⟨P, hP.feasible_of_clique _, hy⟩

/-- The front of `f(U)` read in the Lean model, whose table of central flights is complete: for
every table of central flights satisfying (A1-NS), it is `{(8, 10)}`. -/
theorem reduced_front_network (dc : Fin 2 → Fin 2 → ℕ)
    (hA : (⟨![1, 3], ![3, 1], dc⟩ : Network 2).A1NS) :
    IsParetoFront (achievable ⟨![1, 3], ![3, 1], dc⟩ ![2, 2] 3 2) [(8, 10)] :=
  reducedCert.check_sound reducedCert_check dc fun _ => hA

/-- In particular, every plan of `f(U)` has makespan at least 10. -/
theorem reduced_makespan_ge : ∀ x ∈ gAchievable (Reduced.graph U) (Reduced.c U c) 3 2, 10 ≤ x.2 :=
  fun x hx => by
    obtain ⟨y, hy, hle⟩ := reduced_front.dominates x hx
    rw [List.mem_singleton.mp hy] at hle
    exact (Prod.le_def.mp hle).2

/-- **The reduction misses the front (Example 5.9).** `(8, 10)` is Pareto-optimal for `f(U)` but
not for `U`, which has the plan `(8, 8)`. So the fronts of `U` and `f(U)` differ, against the claim
of arXiv §2.4. -/
theorem fronts_differ :
    Minimal (· ∈ gAchievable (Reduced.graph U) (Reduced.c U c) 3 2) (8, 10) ∧
      ¬ Minimal (· ∈ gAchievable U c 3 2) (8, 10) ∧
      ¬ ∀ x, Minimal (· ∈ gAchievable U c 3 2) x ↔
        Minimal (· ∈ gAchievable (Reduced.graph U) (Reduced.c U c) 3 2) x := by
  have h₁ := (reduced_front.mem_iff_minimal (8, 10)).mp (List.mem_singleton_self _)
  have h₂ : ¬ Minimal (· ∈ gAchievable U c 3 2) ((8, 10) : ℕ × ℕ) := fun h =>
    absurd (h.2 mem_gAchievable_U (by decide)) (by decide)
  exact ⟨h₁, h₂, fun h => h₂ ((h _).mpr h₁)⟩

end Ex611

/-! ### Proposition I holds only in the front sense -/

namespace PropI

/-- The certificate of `n = 1`, `d₁ = 1`, `c₁ = 0`, `t = 5`, `p = 3`, as written by
`zeno front --certificate`: one point, `(0, 6)`, with groups of 1, 3 and 3 landings. -/
def cert : Cert where
  n := 1
  t := 5
  p := 3
  d := ![1]
  dbar := ![1]
  c := ![0]
  assumptions := ["S"]
  front := [(0, 6)]
  plans := [
    ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .cg, 1, 2, some 0⟩],
      [⟨.ci, .city 0, 0, 1, some 1⟩, ⟨.city 0, .cg, 1, 2, some 1⟩,
        ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
        ⟨.ci, .city 0, 4, 5, some 2⟩, ⟨.city 0, .cg, 5, 6, some 2⟩],
      [⟨.ci, .city 0, 0, 1, some 3⟩, ⟨.city 0, .cg, 1, 2, some 3⟩,
        ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
        ⟨.ci, .city 0, 4, 5, some 4⟩, ⟨.city 0, .cg, 5, 6, some 4⟩]]]
  gaps := []

set_option maxRecDepth 100000 in
/-- The kernel accepts the certificate. -/
theorem cert_check : cert.check = true := by decide +kernel

/-- **The front is `{(0, 6)}`**, for every central flight duration (here a flight from the city
to itself). -/
theorem front (dc : Fin 1 → Fin 1 → ℕ) :
    IsParetoFront (achievable ⟨![1], ![1], dc⟩ ![0] 5 3) [(0, 6)] :=
  cert.check_sound_relaxed cert_check (by decide) dc

/-- The number of central landings of a plan. -/
def centralLandings {n t p : ℕ} (P : Plan n t p) : ℕ :=
  ((allLegs P).filter fun ℓ => !ℓ.dst.isHub).length

/-- The plan of the certificate, in which the plane with one landing also flies a crossing pair
`Ā, A`, empty, within its slack. -/
def plan9 : Plan 1 5 3 :=
  ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .cg, 1, 2, some 0⟩,
      ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
      ⟨.ci, .city 0, 4, 5, none⟩, ⟨.city 0, .cg, 5, 6, none⟩],
    [⟨.ci, .city 0, 0, 1, some 1⟩, ⟨.city 0, .cg, 1, 2, some 1⟩,
      ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
      ⟨.ci, .city 0, 4, 5, some 2⟩, ⟨.city 0, .cg, 5, 6, some 2⟩],
    [⟨.ci, .city 0, 0, 1, some 3⟩, ⟨.city 0, .cg, 1, 2, some 3⟩,
      ⟨.cg, .city 0, 2, 3, none⟩, ⟨.city 0, .ci, 3, 4, none⟩,
      ⟨.ci, .city 0, 4, 5, some 4⟩, ⟨.city 0, .cg, 5, 6, some 4⟩]]

/-- **A Pareto-optimal plan with more than `2t − p` landings.** For `n = 1`, `d₁ = 1`, `c₁ = 0`,
`t = 5`, `p = 3` and every central flight duration, the plan `plan9` is feasible, lands 9 times in
central cities, more than `2t − p = 7`, and attains the point `(0, 6)`, which is Pareto-optimal.
So the papers' Proposition I (Pareto-optimal plans land exactly `2t − p` times) holds only in the
front sense: every front point is attained with `2t − p` landings, not only with them. -/
theorem plan9_pareto (dc : Fin 1 → Fin 1 → ℕ) :
    Feasible ⟨![1], ![1], dc⟩ plan9 ∧ planCost ![0] plan9 = 0 ∧ planMakespan plan9 = 6 ∧
      centralLandings plan9 = 9 ∧ 2 * 5 - 3 < centralLandings plan9 ∧
      Minimal (· ∈ achievable ⟨![1], ![1], dc⟩ ![0] 5 3) (0, 6) :=
  ⟨planOK_feasible dc (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ((front dc).mem_iff_minimal _).mp (by decide)⟩

end PropI

/-! ### Example 5.10: the shuttle construction of arXiv §3.3 misses the front -/

namespace Shuttle

open Finset

/-- A city of a pattern-typed instance (arXiv:2304.14659, §3.3): a duration and a landing cost for
each pattern, `A` (`C_I → x → C_G`), `Ā` (`C_G → x → C_I`), `B` (`C_I → x → C_I`) and `B̄`
(`C_G → x → C_G`), and whether the city is virtual. -/
structure TCity where
  dA : ℕ
  dAb : ℕ
  dB : ℕ
  dBb : ℕ
  cA : ℕ
  cAb : ℕ
  cB : ℕ
  cBb : ℕ
  virtual : Bool
  deriving DecidableEq, Repr

variable {n : ℕ}

/-- A central city `i`: its patterns last `d_i + d̄_i`, `d̄_i + d_i`, `2 d_i` and `2 d̄_i`, and each
lands once in `i`, for `c_i`. -/
def plainCity (d dbar c : Fin n → ℕ) (i : Fin n) : TCity :=
  ⟨d i + dbar i, dbar i + d i, 2 * d i, 2 * dbar i, c i, c i, c i, c i, false⟩

/-- **The virtual city of arXiv §3.3** for a `B Ā B̄` situation through `C_i` and `C_j`, as printed:
`d^A = min(d_i + d̄_i, d_j + d̄_j)`, `d^Ā = d̄_i + d_ij + d_j` (the shuttle), `d^B = 2 d_i` and
`d^B̄ = 2 d_j` (equations (3)–(6)); it costs `c_i + c_j` for `A` and `Ā`, `c_i` for `B` and `c_j` for
`B̄` (Figure 10). -/
def shuttleCity (d dbar c : Fin n → ℕ) (dc : Fin n → Fin n → ℕ) (i j : Fin n) : TCity :=
  ⟨min (d i + dbar i) (d j + dbar j), dbar i + dc i j + d j, 2 * d i, 2 * d j, c i + c j,
    c i + c j, c i, c j, true⟩

/-- **The augmented instance of arXiv §3.3**: the central cities, then one virtual city for each
ordered pair `i ≠ j` (every pair of central cities is joined by a flight in the Lean model). -/
def augment (d dbar c : Fin n → ℕ) (dc : Fin n → Fin n → ℕ) : List TCity :=
  (List.finRange n).map (plainCity d dbar c) ++
    (List.finRange n).flatMap fun i =>
      ((List.finRange n).filter (· ≠ i)).map (shuttleCity d dbar c dc i)

/-- A role configuration of a pattern-typed instance with `m` cities, by its counts: for each
plane `k` and city `x`, how many patterns `A`, `Ā`, `B` and `B̄` plane `k` flies at `x`. -/
structure TConfig (p m : ℕ) where
  a : Fin p → Fin m → ℕ
  ab : Fin p → Fin m → ℕ
  b : Fin p → Fin m → ℕ
  bb : Fin p → Fin m → ℕ

namespace TConfig

variable {p m : ℕ} (C : Fin m → TCity) (cfg : TConfig p m)

/-- The load of plane `k`: the durations of its patterns. Each plane flies its patterns one after
the other, so every schedule of the configuration has a makespan at least every load. -/
def load (k : Fin p) : ℕ :=
  ∑ x, (cfg.a k x * (C x).dA + cfg.ab k x * (C x).dAb + cfg.b k x * (C x).dB +
    cfg.bb k x * (C x).dBb)

/-- The cost: the landings of all patterns. -/
def cost : ℕ :=
  ∑ k, ∑ x, (cfg.a k x * (C x).cA + cfg.ab k x * (C x).cAb + cfg.b k x * (C x).cB +
    cfg.bb k x * (C x).cBb)

/-- The number of landings, one per pattern. -/
def size : ℕ := ∑ k, ∑ x, (cfg.a k x + cfg.ab k x + cfg.b k x + cfg.bb k x)

/-- A valid configuration for `t` passengers. Every plane flies one more `A` than `Ā` (it starts in
`C_I` and ends in `C_G`); the `B` and `B̄` balance city by city (each `B B̄` pair carries one
passenger); there are `t` passengers, one per `A` and one per pair. With `shuttle`, every pair at
a virtual city also needs its shuttle, an `Ā` at that city. -/
structure Valid (shuttle : Bool) (t : ℕ) : Prop where
  alt : ∀ k, ∑ x, cfg.a k x = ∑ x, cfg.ab k x + 1
  bal : ∀ x, ∑ k, cfg.b k x = ∑ k, cfg.bb k x
  pax : ∑ k, ∑ x, (cfg.a k x + cfg.b k x) = t
  shut : shuttle = true → ∀ x, (C x).virtual = true → ∑ k, cfg.b k x ≤ ∑ k, cfg.ab k x

end TConfig

/-- The points the construction can give: the cost of a valid configuration with `2t − p`
landings, and any makespan at least its loads. Every schedule of a configuration has such a
makespan, so this set contains every point of the construction (it over-approximates it). -/
def points {m : ℕ} (C : Fin m → TCity) (shuttle : Bool) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ cfg : TConfig p m, cfg.Valid C shuttle t ∧ cfg.size = 2 * t - p ∧
    cfg.cost C = x.1 ∧ ∀ k, cfg.load C k ≤ x.2}

/-! #### The instance of Example 5.10 -/

/-- The durations to `C_I`, `d = (1, 3)`. -/
def d : Fin 2 → ℕ := ![1, 3]

/-- The durations to `C_G`, `d̄ = (3, 1)`. -/
def db : Fin 2 → ℕ := ![3, 1]

/-- The landing costs, `c = (6, 1)`. -/
def c : Fin 2 → ℕ := ![6, 1]

/-- The central flight between cities 1 and 2 lasts 2 (the diagonal is never flown). -/
def dc : Fin 2 → Fin 2 → ℕ := ![![0, 2], ![2, 0]]

/-- The instance, with its central flight. -/
def net : Network 2 := ⟨d, db, dc⟩

/-- (AΔ) holds: the only triangles are `C_I, 1, 2` and `C_G, 1, 2`, and `d_12 = 2` is between the
difference and the sum of the two other sides. -/
theorem net_ATri : net.ATri := by
  intro a x b hab τab τax τxb h₁ h₂ h₃
  have key : ∀ a ∈ allLocs 2, ∀ x ∈ allLocs 2, ∀ b ∈ allLocs 2, a ≠ b →
      ∀ u ∈ (net.duration a b).toList, ∀ v ∈ (net.duration a x).toList,
        ∀ w ∈ (net.duration x b).toList, u ≤ v + w := by
    decide +kernel
  exact key a (mem_allLocs a) x (mem_allLocs x) b (mem_allLocs b) hab τab (by simp [h₁]) τax
    (by simp [h₂]) τxb (by simp [h₃])

/-- (A1-NS) fails: `d_12 = 2 < 4 = min(d_1 + d_2, d̄_1 + d̄_2)`. -/
theorem not_net_A1NS : ¬ net.A1NS := fun h => absurd (h 0 1) (by decide)

/-- The plan of Example 5.10 (passengers numbered from `0`). Plane 1 leaves passenger 0 in
city 1, carries passenger 1 across city 2, and picks passenger 2 up in city 2. Plane 2 flies the
split crossing `C_I → 2 → 1 → C_G`: it leaves passenger 2 in city 2, flies the central flight
empty, and carries passenger 0 from city 1. -/
def plan : Plan 2 3 2 :=
  ![[⟨.ci, .city 0, 0, 1, some 0⟩, ⟨.city 0, .ci, 1, 2, none⟩, ⟨.ci, .city 1, 2, 5, some 1⟩,
      ⟨.city 1, .cg, 5, 6, some 1⟩, ⟨.cg, .city 1, 6, 7, none⟩, ⟨.city 1, .cg, 7, 8, some 2⟩],
    [⟨.ci, .city 1, 0, 3, some 2⟩, ⟨.city 1, .city 0, 3, 5, none⟩, ⟨.city 0, .cg, 5, 8, some 0⟩]]

/-- The flights the plan uses: the hub flights and the central flight from city 2 to city 1. -/
def usedGraph : FlightGraph 2 :=
  ⟨fun a b => match a, b with
    | .city i, .city j => if i = 1 ∧ j = 0 then some 2 else none
    | a, b => Network.duration ⟨d, db, fun _ _ => 0⟩ a b⟩

/-- **The plan is feasible** in every network with these hub durations and a central flight of
duration 2 from city 2 to city 1. -/
theorem plan_feasible (dc' : Fin 2 → Fin 2 → ℕ) (h : dc' 1 0 = 2) : Feasible ⟨d, db, dc'⟩ plan := by
  refine (feasible_iff_gFeasible _ _).mpr
    ((gFeasible_of_planOKDur (U := usedGraph) (by decide +kernel)).mono fun a b τ hab => ?_)
  cases a <;> cases b <;> simp only [usedGraph, Network.toGraph, Network.duration] at hab ⊢ <;>
    try exact hab
  rename_i i j
  split_ifs at hab with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [h]
    exact hab

/-- It costs 15. -/
theorem plan_cost : planCost c plan = 15 := by decide +kernel

/-- Its makespan is 8. -/
theorem plan_makespan : planMakespan plan = 8 := by decide +kernel

/-- **The front of the instance has a point of makespan at most 8**, weakly dominating `(15, 8)`,
in every network with these hub durations and a central flight of duration 2 from city 2 to
city 1. `ℕ × ℕ` is well quasi-ordered, so the points of the plans below `(15, 8)` have a minimal
one. -/
theorem front_le (dc' : Fin 2 → Fin 2 → ℕ) (h : dc' 1 0 = 2) :
    ∃ y ≤ ((15, 8) : ℕ × ℕ), Minimal (· ∈ achievable ⟨d, db, dc'⟩ c 3 2) y :=
  (Set.isPWO_of_wellQuasiOrderedLE _).exists_le_minimal
    ⟨plan, plan_feasible dc' h, by rw [plan_cost, plan_makespan]⟩

/-! #### The augmented instance -/

/-- The cities of the augmented instance: cities 1 and 2, then the virtual cities of the
situations through `(1, 2)` and through `(2, 1)`. -/
def cities : Fin 4 → TCity := fun x =>
  (augment d db c dc).getD x ⟨0, 0, 0, 0, 0, 0, 0, 0, false⟩

theorem augment_length : (augment d db c dc).length = 4 := by decide +kernel

theorem cities_0 : cities 0 = ⟨4, 4, 2, 6, 6, 6, 6, 6, false⟩ := by decide +kernel

theorem cities_1 : cities 1 = ⟨4, 4, 6, 2, 1, 1, 1, 1, false⟩ := by decide +kernel

theorem cities_2 : cities 2 = ⟨4, 8, 2, 6, 7, 7, 6, 1, true⟩ := by decide +kernel

theorem cities_3 : cities 3 = ⟨4, 4, 6, 2, 7, 7, 1, 6, true⟩ := by decide +kernel

/-- **Every configuration of the augmented instance has a plane that flies at least 10**, with or
without the shuttle counted, and whatever its number of landings. With 3 passengers, each plane
flies an `A` (4), so there is at most one `B B̄` pair; without a pair a plane flies `A Ā A` (12 or
more), and a pair at one city lasts `(2, 6)` or `(6, 2)`, in every city. -/
theorem load_ge (shuttle : Bool) (cfg : TConfig 2 4) (h : cfg.Valid cities shuttle 3) :
    10 ≤ cfg.load cities 0 ∨ 10 ≤ cfg.load cities 1 := by
  obtain ⟨halt, hbal, hpax, -⟩ := h
  have h₀ := halt 0
  have h₁ := halt 1
  have hb₀ := hbal 0
  have hb₁ := hbal 1
  have hb₂ := hbal 2
  have hb₃ := hbal 3
  simp only [TConfig.load, Fin.sum_univ_two, Fin.sum_univ_four, cities_0, cities_1, cities_2,
    cities_3] at *
  omega

/-- So every point of the construction has makespan at least 10. -/
theorem points_ge (shuttle : Bool) : ∀ x ∈ points cities shuttle 3 2, 10 ≤ x.2 := by
  rintro x ⟨cfg, hv, -, -, hload⟩
  rcases load_ge shuttle cfg hv with h | h
  · exact h.trans (hload 0)
  · exact h.trans (hload 1)

/-- A configuration of the construction, cost 4 and loads 10 and 6: both planes cross at city 2,
and plane 1 drops a passenger there that plane 2 picks up. It is valid in both readings. -/
def cfg4 : TConfig 2 4 where
  a := fun _ x => if x = 1 then 1 else 0
  ab := fun _ _ => 0
  b := fun k x => if k = 0 ∧ x = 1 then 1 else 0
  bb := fun k x => if k = 1 ∧ x = 1 then 1 else 0

/-- `(4, 10)` is a point of the construction, in both readings. -/
theorem mem_points (shuttle : Bool) : ((4, 10) : ℕ × ℕ) ∈ points cities shuttle 3 2 :=
  ⟨cfg4, ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ => by decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Example 5.10: the shuttle construction of arXiv §3.3 misses the front.** On
`d = (1, 3)`, `d̄ = (3, 1)`, a central flight of duration 2, `c = (6, 1)`, `t = 3`, `p = 2`, (AΔ)
holds, the front of the instance has a point of makespan at most 8, and every point of the
augmented instance, as printed, has makespan at least 10, whether or not the shuttle is counted.
So the construction's front is not the instance's front. -/
theorem shuttle_misses (shuttle : Bool) :
    net.ATri ∧ (∃ y ≤ ((15, 8) : ℕ × ℕ), Minimal (· ∈ achievable net c 3 2) y) ∧
      (∀ x ∈ points cities shuttle 3 2, 10 ≤ x.2) ∧
      ¬ ∀ x, Minimal (· ∈ achievable net c 3 2) x ↔ Minimal (· ∈ points cities shuttle 3 2) x := by
  obtain ⟨y, hy, hmin⟩ := front_le dc rfl
  refine ⟨net_ATri, ⟨y, hy, hmin⟩, points_ge shuttle, fun h => ?_⟩
  have h₁ := points_ge shuttle y ((h y).mp hmin).prop
  have h₂ := (Prod.le_def.mp hy).2
  omega

end Shuttle

end ZenoFront
