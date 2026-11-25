/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Examples
public import ZenoFront.Graph
public import ZenoFront.Solver
public import ZenoFront.TriSegments

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
`(260, 60)` (`Examples.lptCounterexample_front`). No PPP of cost at most 260 gets a greedy makespan
at most 60, for either greedy (`evocop_misses_lpt`, `arxiv_misses_lpt`). On the landings of
`(260, 60)`, EvoCOP's Algorithm 1 without P3 ends at `(52, 68)` (`evocop_lpt_noP3`), as §5 of the
note says. With its best `β`, EvoCOP's greedy reaches 64 (`evocop_lpt_ppp`).

The `p3First` instance is `d = (1, 3)`, `c = (9, 5)`, `t = 4`, `p = 2`. Its exact front contains
`(42, 12)` (`p3First_front`). No PPP of cost at most 42 gets an arXiv makespan at most 12
(`arxiv_misses_p3First`). EvoCOP's greedy finds that point (`evocop_p3First_front`).

The papers leave some choices open. The definitions here take:

* ties of `ArgMin` to the smallest plane index (EvoCOP's worked example on p. 7 agrees);
* in EvoCOP's Step 2, for `p = 1`, both halves of a P3 to the single plane;
* in arXiv Step 2, the `p` largest crossings in decreasing order, each to the least-loaded plane
  that has none yet ("each plane must receive one");
* in arXiv Step 3, the least-loaded plane among those whose next pattern (`Ā` after `A`, `A` after
  `Ā`) is still available. Read literally ("while it remains some elements in `a` and `ā`, select
  the plane with the minimal duration"), the step can stop or get stuck with crossings left over.

On the 27 golden instances (`tests/golden/instances.txt`), `evocopPoints` gives the front of the
2016 `zenoSolver`, and `arxivPoints` that of `zenoSolver_noDuplicate` on 25 of them.

## Example 4.13: the triangles through a hub cannot be dropped

On `d = d̄ = (2, 3, 9, 11)`, `c = (50, 44, 17, 0)`, `t = 6`, `p = 3`, with a central flight of
duration 1 between cities 3 and 4, a plan of cost 260 and makespan 39 flies that central flight
(`Ex413.plan_feasible`). The checker of format v1 accepts hub flights only, so the plan is
simulated on its duration table (`planOKDur`, `Graph.lean`). Every admissible partition of 9
landings with loads `δ(X_k) ≤ 19` costs at least 264 (`Ex413.minCost_19`), so no admissible point
weakly dominates `(260, 39)` (`Ex413.not_admissible_le`). The conclusion of Theorem 4.10 and
Corollary 4.8 fail there (`Ex413.no_admissible_partition`, `Ex413.not_isParetoFront`).

## Main results

* `ZenoFront.Greedy.evocop_misses_lpt`, `ZenoFront.Greedy.arxiv_misses_lpt`: neither greedy reaches
  the front point `(260, 60)` of the `lpt` instance.
* `ZenoFront.Greedy.arxiv_misses_p3First`: the arXiv greedy does not reach the front point
  `(42, 12)` of the `p3First` instance.
* `ZenoFront.Ex413.plan_feasible`, `ZenoFront.Ex413.not_admissible_le`,
  `ZenoFront.Ex413.not_isParetoFront`: Example 4.13.
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

/-! ### The `lpt` instance: `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2` -/

/-- The landings of the front point `(260, 60)` as a PPP: eastbound `e` = three landings in city 1
(`d = 6`) and two in city 2 (`d = 10`), westbound `w` = two in city 1 and one in city 2. Its cost
is 260. -/
theorem lpt_ppp_cost : costOf ![40, 20] [3, 2] + costOf ![40, 20] [2, 1] = 260 := by decide +kernel

/-- **§5 of the note.** On the landings of `(260, 60)`, EvoCOP's Algorithm 1 without P3 gives
every plane a crossing of 20 first and ends with the private makespans `(52, 68)`. -/
theorem evocop_lpt_noP3 :
    evocopLoads 2 (durs ![6, 10] [3, 2]) (durs ![6, 10] [2, 1]) [] = [52, 68] := by decide +kernel

/-- With its best set of P3 patterns, EvoCOP's greedy schedules the landings of `(260, 60)` in 64,
still above 60. -/
theorem evocop_lpt_ppp : evocopMakespan ![6, 10] 2 [3, 2] [2, 1] = 64 := by decide +kernel

/-- The front EvoCOP's algorithm returns on the `lpt` instance. -/
theorem evocop_lpt_front : paretoMin (evocopPoints ![6, 10] ![40, 20] 5 2) =
    [(160, 80), (200, 72), (240, 64), (280, 56), (320, 48)] := by decide +kernel

/-- The front the four steps of arXiv §3.2 return on the `lpt` instance: the same. -/
theorem arxiv_lpt_front : paretoMin (arxivPoints ![6, 10] ![40, 20] 5 2) =
    [(160, 80), (200, 72), (240, 64), (280, 56), (320, 48)] := by decide +kernel

/-- **EvoCOP's greedy is not exact (§5).** On `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2`, the
point `(260, 60)` is Pareto-optimal among all feasible plans, whatever the central flights, but no
PPP of EvoCOP's algorithm reaches cost at most 260 and makespan at most 60. -/
theorem evocop_misses_lpt (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![6, 10], ![6, 10], dc⟩ ![40, 20] 5 2) (260, 60) ∧
      ∀ x ∈ evocopPoints ![6, 10] ![40, 20] 5 2, ¬ (x.1 ≤ 260 ∧ x.2 ≤ 60) :=
  ⟨((Examples.lptCounterexample_front dc).mem_iff_minimal _).mp (by decide),
    by decide +kernel⟩

/-- **The greedy of arXiv §3.2 is not exact.** On the same instance, no PPP `(a, ā, b)` reaches cost
at most 260 and makespan at most 60 with the four steps. -/
theorem arxiv_misses_lpt (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![6, 10], ![6, 10], dc⟩ ![40, 20] 5 2) (260, 60) ∧
      ∀ x ∈ arxivPoints ![6, 10] ![40, 20] 5 2, ¬ (x.1 ≤ 260 ∧ x.2 ≤ 60) :=
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

/-- EvoCOP's algorithm finds the front of the `p3First` instance. -/
theorem evocop_p3First_front : paretoMin (evocopPoints ![1, 3] ![9, 5] 4 2) =
    [(30, 18), (38, 14), (42, 12), (46, 10), (50, 8), (54, 6)] := by decide +kernel

/-- The four steps of arXiv §3.2 miss `(42, 12)` on the `p3First` instance. -/
theorem arxiv_p3First_front : paretoMin (arxivPoints ![1, 3] ![9, 5] 4 2) =
    [(30, 18), (38, 14), (46, 10), (50, 8), (54, 6)] := by decide +kernel

/-- **The greedy of arXiv §3.2 is not exact (§5).** On `d = (1, 3)`, `c = (9, 5)`, `t = 4`, `p = 2`,
the point `(42, 12)` is Pareto-optimal among all feasible plans, whatever the central flights, but
no PPP `(a, ā, b)` reaches cost at most 42 and makespan at most 12 with the four steps. -/
theorem arxiv_misses_p3First (dc : Fin 2 → Fin 2 → ℕ) :
    Minimal (· ∈ achievable ⟨![1, 3], ![1, 3], dc⟩ ![9, 5] 4 2) (42, 12) ∧
      ∀ x ∈ arxivPoints ![1, 3] ![9, 5] 4 2, ¬ (x.1 ≤ 42 ∧ x.2 ≤ 12) :=
  ⟨((p3First_front dc).mem_iff_minimal _).mp (by decide), by decide +kernel⟩

end Greedy

/-! ### Example 4.13: without (A1) and (AΔ), a plan beats the admissible partitions -/

namespace Ex413

/-- The hub durations of Example 4.13, `d = d̄ = (2, 3, 9, 11)` (cities numbered from `0` here). -/
def d : Fin 4 → ℕ := ![2, 3, 9, 11]

/-- The landing costs of Example 4.13, `c = (50, 44, 17, 0)`. -/
def c : Fin 4 → ℕ := ![50, 44, 17, 0]

/-- The central flights of Example 4.13: `d₁₂ = 1`, `d₁₃ = 5`, `d₁₄ = 6`, `d₂₃ = 3`, `d₂₄ = 6`,
`d₃₄ = 1` in the note's numbering. The diagonal is never flown. -/
def dc : Fin 4 → Fin 4 → ℕ := ![![0, 1, 5, 6], ![1, 0, 3, 6], ![5, 3, 0, 1], ![6, 6, 1, 0]]

/-- The network of Example 4.13: symmetric hub durations and the central flights `dc`. -/
def net : Network 4 := ⟨d, d, dc⟩

/-- The plan of Example 4.13 (passengers numbered from `0`). Plane 1 crosses at city 1, picks up
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

/-- The plan is feasible in the network of Example 4.13. -/
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

/-- They violate even the triangles through a hub (`ATriHub`), all that Theorem 4.10 uses. -/
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
makespan below 40 by Lemma 3.4) is 260, the plan's cost. -/
theorem relaxedBound_19 : relaxedBoundAt 3 9 19 (oneplaneTable d c 19 9) 19 = 260 := by
  decide +kernel

/-- **The conclusion of Theorem 4.10 fails for the plan**: no admissible partition of
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
/-- **The front of admissible partitions** of Example 4.13, computed by the verified solver in the
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

/-- **Corollary 4.8 fails for Example 4.13**: the front of admissible partitions, which the solver
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

end ZenoFront
