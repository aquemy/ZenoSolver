/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Examples

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

## Main results

* `ZenoFront.Greedy.evocop_misses_lpt`, `ZenoFront.Greedy.arxiv_misses_lpt`: neither greedy reaches
  the front point `(260, 60)` of the `lpt` instance.
* `ZenoFront.Greedy.arxiv_misses_p3First`: the arXiv greedy does not reach the front point
  `(42, 12)` of the `p3First` instance.
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

end ZenoFront
