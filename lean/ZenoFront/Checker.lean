/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.PlanBounds
public import ZenoFront.Relaxation
public import ZenoFront.Simulate
public import ZenoFront.ConverseTri
public import ZenoFront.TreeBound

/-!
# A verified checker for front certificates (format v1)

`Cert` is a parsed certificate of `doc/certificate-format.md`. `Cert.check` verifies the four
obligations of the format, mirroring `checkCertificate` in `src/zeno/certificate.cpp`:

1. every point's plan is feasible (simulated) with exactly the point's cost and makespan;
2. the first makespan is `2 · d_min · ⌈s/p⌉`;
3. at every gap, the named bound at the gap level `⌊⌊(M_{i+1} − 1)/2⌋ / g⌋` (durations divided by
   their gcd `g`) is at least `C_i`: the relaxation `L` for a `relaxed` gap, and, for a `forest`
   gap (which needs assumption `A1` listed), the least cost `E` of an admissible partition,
   computed by the σ-DP;
4. the last cost is `s · c_min`;

plus the header (`1 ≤ n`, `1 ≤ p ≤ t`, symmetric durations, assumption `S` listed) and strict
monotonicity of the points.

**Soundness** (`Cert.check_sound_hub`): if `check` accepts, the listed points are exactly the
Pareto front of the (cost, makespan) pairs of the feasible plans of the instance (every point is
achieved, every feasible plan is weakly dominated by a listed point, and the points are pairwise
incomparable) for every table of central flight durations satisfying the triangles through a hub
(`Network.ATriHub`), and for every table at all if every gap is `relaxed`
(`Cert.check_sound_relaxed`). The `forest` gaps use Theorem 4.10
(`Feasible.exists_admissible_hub`). Under (A1) this is `Cert.check_sound`, under (AΔ)
`Cert.check_sound_ATri`. `IsParetoFront.mem_iff_minimal` restates it as "a pair is listed iff it
is a minimal achievable pair".
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Pareto fronts -/

/-- The (cost, makespan) pairs of the feasible plans. -/
def achievable (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ P : Plan n t p, Feasible N P ∧ (planCost c P, planMakespan P) = x}

/-- `F` is the Pareto front of `S` (for the product order on (cost, makespan)): its points are in
`S`, weakly dominate every point of `S`, and are pairwise incomparable. -/
structure IsParetoFront {α : Type*} [PartialOrder α] (S : Set α) (F : List α) : Prop where
  achieved : ∀ x ∈ F, x ∈ S
  dominates : ∀ y ∈ S, ∃ x ∈ F, x ≤ y
  antichain : F.Pairwise fun a b => ¬ a ≤ b ∧ ¬ b ≤ a

/-- A Pareto front lists exactly the minimal elements. -/
theorem IsParetoFront.mem_iff_minimal {α : Type*} [PartialOrder α] {S : Set α} {F : List α}
    (h : IsParetoFront S F) (x : α) : x ∈ F ↔ Minimal (· ∈ S) x := by
  constructor
  · intro hx
    refine ⟨h.achieved x hx, fun y hy hyx => ?_⟩
    obtain ⟨x', hx', hx'y⟩ := h.dominates y hy
    have hx'x : x' ≤ x := hx'y.trans hyx
    by_cases heq : x' = x
    · subst heq
      exact hx'y
    · exfalso
      have : Std.Symm fun a b : α => ¬ a ≤ b ∧ ¬ b ≤ a := ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
      exact (h.antichain.forall hx' hx heq).1 hx'x
  · intro ⟨hx, hmin⟩
    obtain ⟨x', hx', hx'x⟩ := h.dominates x hx
    have := le_antisymm hx'x (hmin (h.achieved x' hx') hx'x)
    exact this ▸ hx'

/-! ### Closed-form bounds -/

/-- The least value of a function on `Fin n` (`0` if `n = 0`). -/
def minOf (f : Fin n → ℕ) : ℕ :=
  if h : 0 < n then univ.inf' ⟨⟨0, h⟩, mem_univ _⟩ f else 0

theorem minOf_le (f : Fin n → ℕ) (i : Fin n) : minOf f ≤ f i := by
  have h : 0 < n := Fin.pos i
  simp only [minOf, h, dite_true]
  exact Finset.inf'_le _ (mem_univ i)

theorem card_mul_minOf_le_sum (f : Fin n → ℕ) (Y : Multiset (Fin n)) :
    Y.card * minOf f ≤ (Y.map f).sum := by
  have := Multiset.card_nsmul_le_sum (s := Y.map f) (a := minOf f) fun x hx => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact minOf_le f i
  simpa using this

/-- Some group has at least `⌈size / p⌉` landings. -/
theorem exists_ceil_le_card (Y : Groups n p) (hp : 1 ≤ p) :
    ∃ k, (size Y + p - 1) / p ≤ (Y k).card := by
  by_contra hall
  push Not at hall
  set q := (size Y + p - 1) / p
  have h₁ : ∑ k, ((Y k).card + 1) ≤ ∑ _k : Fin p, q := Finset.sum_le_sum fun k _ => hall k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at h₁
  have h₂ : q * p ≤ size Y + p - 1 := Nat.div_mul_le_self _ _
  rw [mul_comm] at h₂
  change size Y + p ≤ p * q at h₁
  omega

/-- **Obligation 2.** Under (S), every feasible plan has makespan at least
`2 · d_min · ⌈s/p⌉`. -/
theorem Feasible.minOf_le_makespan {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hp : 1 ≤ p) (hpt : p ≤ t) :
    2 * minOf N.d * ((2 * t - p + p - 1) / p) ≤ planMakespan P := by
  obtain ⟨Y, -, hsize, hload, -⟩ := hP.exists_relaxation hS c hpt
  obtain ⟨k, hk⟩ := exists_ceil_le_card Y hp
  rw [hsize] at hk
  have h₁ := card_mul_minOf_le_sum N.d (Y k)
  have h₂ := hload k
  calc 2 * minOf N.d * ((2 * t - p + p - 1) / p)
      ≤ 2 * minOf N.d * (Y k).card := Nat.mul_le_mul_left _ hk
    _ = 2 * ((Y k).card * minOf N.d) := by rw [mul_assoc, mul_comm (minOf N.d)]
    _ ≤ 2 * load N.d (Y k) := Nat.mul_le_mul_left _ h₁
    _ ≤ planMakespan P := h₂

/-- **Obligation 4.** Under (S), every feasible plan costs at least `s · c_min`. -/
theorem Feasible.minOf_le_cost {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    (2 * t - p) * minOf c ≤ planCost c P := by
  obtain ⟨Y, -, hsize, -, hcost⟩ := hP.exists_relaxation hS c hpt
  refine le_trans ?_ hcost
  rw [← hsize, size, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => card_mul_minOf_le_sum c (Y k)

/-- **Obligation 4**, for any durations: every feasible plan costs at least `s · c_min`. -/
theorem Feasible.minOf_le_cost_emin {N : Network n} (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    (2 * t - p) * minOf c ≤ planCost c P := by
  obtain ⟨Y, -, hsize, -, hcost⟩ := hP.exists_relaxation_emin c hpt
  refine le_trans ?_ hcost
  rw [← hsize, size, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => card_mul_minOf_le_sum c (Y k)

/-! ### Certificates -/

/-- The lower bound named for a gap. -/
inductive GapKind where
  | relaxed
  | forest
  deriving DecidableEq, Repr

/-- A parsed certificate of format v1: the instance (`n` cities, `t` passengers, `p` planes,
durations `d` and `dbar`, costs `c`), the listed assumptions, the front points
`(cost, makespan)` by increasing makespan, one plan per point, and one lower-bound kind per gap. -/
structure Cert where
  n : ℕ
  t : ℕ
  p : ℕ
  d : Fin n → ℕ
  dbar : Fin n → ℕ
  c : Fin n → ℕ
  assumptions : List String
  front : List (ℕ × ℕ)
  plans : List (Plan n t p)
  gaps : List GapKind

/-- Points strictly increasing in makespan and strictly decreasing in cost. -/
def strictlyMonotone : List (ℕ × ℕ) → Bool
  | x :: y :: rest => decide (x.2 < y.2 ∧ y.1 < x.1) && strictlyMonotone (y :: rest)
  | _ => true

theorem pairwise_of_strictlyMonotone : ∀ {F : List (ℕ × ℕ)}, strictlyMonotone F = true →
    F.Pairwise fun a b => a.2 < b.2 ∧ b.1 < a.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: rest, h => by
    simp only [strictlyMonotone, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictlyMonotone h.2
    refine List.Pairwise.cons (fun b hb => ?_) ih
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · have := List.rel_of_pairwise_cons ih hb
      exact ⟨h.1.1.trans this.1, this.2.trans h.1.2⟩

/-- The gaps: each consecutive pair `(x, y)` with named bound `g` has `C_x ≤ bound g M_y`. -/
def gapsOK {κ : Type} (bound : κ → ℕ → WithTop ℕ) : List (ℕ × ℕ) → List κ → Bool
  | [_], [] => true
  | x :: y :: rest, g :: gs =>
    decide ((x.1 : WithTop ℕ) ≤ bound g y.2) && gapsOK bound (y :: rest) gs
  | _, _ => false

/-- **The domination argument along a front.** For a point `y`, if every consecutive pair
`(x, z)` of the list has `C_x ≤ y.1` as soon as `y` is faster than `z`, the first point is at least
as fast as `y` and the last at least as cheap, then some listed point weakly dominates `y`. -/
theorem exists_le_of_chain (y : ℕ × ℕ) : ∀ F : List (ℕ × ℕ), F ≠ [] →
    F.IsChain (fun x z => y.2 < z.2 → x.1 ≤ y.1) → (∀ x ∈ F.head?, x.2 ≤ y.2) →
      (∀ x ∈ F.getLast?, x.1 ≤ y.1) → ∃ x ∈ F, x ≤ y
  | [], h, _, _, _ => absurd rfl h
  | [x], _, _, hh, hl => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
      List.getLast?_singleton] at hh hl
    exact ⟨x, List.mem_singleton_self x, Prod.le_def.mpr ⟨hl, hh⟩⟩
  | x :: z :: rest, _, hc, hh, hl => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hh
    by_cases hz : y.2 < z.2
    · exact ⟨x, List.mem_cons_self, Prod.le_def.mpr ⟨hc.1 hz, hh⟩⟩
    · rw [List.getLast?_cons_cons] at hl
      obtain ⟨x', hx', hle⟩ := exists_le_of_chain y (z :: rest) (List.cons_ne_nil _ _) hc.2
        (by simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']; omega) hl
      exact ⟨x', List.mem_cons_of_mem _ hx', hle⟩

/-- The gaps give the chain of `exists_le_of_chain`: if `bound g M` is a lower bound on the cost
of `y` whenever `y`'s makespan is below `M`, every consecutive pair `(x, z)` has `C_x ≤ y.1` as
soon as `y` is faster than `z`. -/
theorem isChain_of_gapsOK {κ : Type} (bound : κ → ℕ → WithTop ℕ) (y : ℕ × ℕ) :
    ∀ (F : List (ℕ × ℕ)) (gs : List κ),
      (∀ g ∈ gs, ∀ M, y.2 < M → bound g M ≤ (y.1 : WithTop ℕ)) → gapsOK bound F gs = true →
      F ≠ [] ∧ F.IsChain (fun x z => y.2 < z.2 → x.1 ≤ y.1)
  | [], _, _, h => by simp [gapsOK] at h
  | [_], [], _, _ => ⟨List.cons_ne_nil _ _, List.IsChain.singleton _⟩
  | [_], _ :: _, _, h => by simp [gapsOK] at h
  | _ :: _ :: _, [], _, h => by simp [gapsOK] at h
  | x :: z :: rest, g :: gs, hb, h => by
    simp only [gapsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨List.cons_ne_nil _ _, List.isChain_cons_cons.mpr ⟨fun hz => ?_,
      (isChain_of_gapsOK bound y (z :: rest) gs (fun g' hg' => hb g' (List.mem_cons_of_mem _ hg'))
        h.2).2⟩⟩
    exact WithTop.coe_le_coe.mp (h.1.trans (hb g List.mem_cons_self z.2 hz))

/-- The domination argument of the checker: if, for every named bound `g`, `bound g M` is a lower
bound on the cost of `y` whenever `y`'s makespan is below `M`, the first point is at least as fast
as `y`, and the last at least as cheap, then some listed point weakly dominates `y`. -/
theorem exists_le_of_gapsOK {κ : Type} (bound : κ → ℕ → WithTop ℕ) (y : ℕ × ℕ)
    (F : List (ℕ × ℕ)) (gs : List κ)
    (hb : ∀ g ∈ gs, ∀ M, y.2 < M → bound g M ≤ (y.1 : WithTop ℕ)) (h : gapsOK bound F gs = true)
    (hh : ∀ x ∈ F.head?, x.2 ≤ y.2) (hl : ∀ x ∈ F.getLast?, x.1 ≤ y.1) : ∃ x ∈ F, x ≤ y :=
  have hc := isChain_of_gapsOK bound y F gs hb h
  exists_le_of_chain y F hc.1 hc.2 hh hl

/-- **Theorem 9.1 (obligations imply the front).** Let `S` be a set of (cost, makespan) points and
`F = (C_1, M_1), …, (C_r, M_r)`, `r ≥ 1`, with `M_1 < ⋯ < M_r` and `C_1 > ⋯ > C_r`. If (1) every
listed point is in `S`, (2) every point of `S` has makespan at least `M_1`, (3) for `i < r` every
point of `S` with makespan below `M_{i+1}` costs at least `C_i`, and (4) every point of `S` costs at
least `C_r`, then `F` is the Pareto front of `S`. -/
theorem isParetoFront_of_obligations {S : Set (ℕ × ℕ)} {F : List (ℕ × ℕ)} (hne : F ≠ [])
    (hmono : F.IsChain fun a b => a.2 < b.2 ∧ b.1 < a.1) (h₁ : ∀ x ∈ F, x ∈ S)
    (h₂ : ∀ x ∈ F.head?, ∀ y ∈ S, x.2 ≤ y.2)
    (h₃ : F.IsChain fun x z => ∀ y ∈ S, y.2 < z.2 → x.1 ≤ y.1)
    (h₄ : ∀ x ∈ F.getLast?, ∀ y ∈ S, x.1 ≤ y.1) : IsParetoFront S F := by
  refine ⟨h₁, fun y hy => ?_, ?_⟩
  · exact exists_le_of_chain y F hne (h₃.imp fun x z h => h y hy) (fun x hx => h₂ x hx y hy)
      fun x hx => h₄ x hx y hy
  · have : Trans (fun a b : ℕ × ℕ => a.2 < b.2 ∧ b.1 < a.1)
        (fun a b : ℕ × ℕ => a.2 < b.2 ∧ b.1 < a.1) (fun a b : ℕ × ℕ => a.2 < b.2 ∧ b.1 < a.1) :=
      ⟨fun hab hbc => ⟨hab.1.trans hbc.1, hbc.2.trans hab.2⟩⟩
    refine hmono.pairwise.imp fun {a b} hab =>
      ⟨fun hle => ?_, fun hle => ?_⟩
    · exact absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2)
    · exact absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)

theorem exists_mem_zip_of_mem {α β : Type*} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → ∀ {b : β}, b ∈ l₂ → ∃ a, (a, b) ∈ l₁.zip l₂
  | [], [], _, _, h => absurd h List.not_mem_nil
  | a :: l₁, b' :: l₂, hlen, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨a, List.mem_cons_self⟩
    · obtain ⟨a', ha'⟩ := exists_mem_zip_of_mem (by simpa using hlen) h
      exact ⟨a', List.mem_cons_of_mem _ ha'⟩

namespace Cert

variable (C : Cert)

/-- The number of landings of a front plan, `s = 2t − p`. -/
def s : ℕ := 2 * C.t - C.p

/-- The instance's flight network, with central flight durations `dc`. -/
def network (dc : Fin C.n → Fin C.n → ℕ) : Network C.n := ⟨C.d, C.dbar, dc⟩

/-- The level of the gap below a point of makespan `M`: `⌊⌊(M − 1)/2⌋ / g⌋`, with `g` the scale
of the durations (their gcd). -/
def gapLevel (M : ℕ) : ℕ := (M - 1) / 2 / durationScale C.d

/-- The highest gap level of the certificate; the one-plane table covers `0, …, maxLevel`. -/
def maxLevel : ℕ := (C.front.map fun x => C.gapLevel x.2).foldr max 0

/-- The header: `1 ≤ n`, `1 ≤ p ≤ t`, symmetric durations, and assumption `S` listed. -/
def headerOK : Bool :=
  decide (1 ≤ C.n) && decide (1 ≤ C.p) && decide (C.p ≤ C.t) &&
    decide (∀ i, C.d i = C.dbar i) && C.assumptions.contains "S"

/-- Obligation 1: one plan per point, each feasible with the point's cost and makespan. -/
def plansOK : Bool :=
  decide (C.plans.length = C.front.length) &&
    (C.plans.zip C.front).all fun x => planOK C.d C.dbar x.1 &&
      decide (planCost C.c x.1 = x.2.1) && decide (planMakespan x.1 = x.2.2)

/-- Obligation 2: the first makespan is `2 · d_min · ⌈s/p⌉`. -/
def firstOK : Bool :=
  match C.front.head? with
  | some x => decide (x.2 = 2 * minOf C.d * ((C.s + C.p - 1) / C.p))
  | none => false

/-- Obligation 4: the last cost is `s · c_min`. -/
def lastOK : Bool :=
  match C.front.getLast? with
  | some x => decide (x.1 = C.s * minOf C.c)
  | none => false

/-- The relaxed bound for the gap below a point of makespan `M`, read from `table`. -/
def gapBound (table : Array (Array (WithTop ℕ))) (M : ℕ) : WithTop ℕ :=
  relaxedBoundAt C.p C.s C.maxLevel table (C.gapLevel M)

/-- The forest bound (the least cost of an admissible partition, by the σ-DP) for the gap below a
point of makespan `M`, read from `table`; `0` (no bound) unless assumption `A1` is listed. -/
def forestGapBound (table : Array (Array (WithTop ℕ))) (M : ℕ) : WithTop ℕ :=
  if C.assumptions.contains "A1" then
    forestBoundAt (scaledDurations C.d) C.c C.p C.t C.s C.maxLevel table (C.gapLevel M)
  else 0

/-- The bound named by a gap. -/
def boundOf (table : Array (Array (WithTop ℕ))) : GapKind → ℕ → WithTop ℕ
  | .relaxed => C.gapBound table
  | .forest => C.forestGapBound table

/-- The bound named by a gap, from precomputed values: the scale of the durations, the highest
level, the scaled durations and the one-plane table. `gapsCheck` computes them once; the result
is `boundOf` (`boundOf_eq`). -/
def boundWith (scale Tmax : ℕ) (dS : Fin C.n → ℕ) (table : Array (Array (WithTop ℕ))) :
    GapKind → ℕ → WithTop ℕ
  | .relaxed => fun M => relaxedBoundAt C.p C.s Tmax table ((M - 1) / 2 / scale)
  | .forest => fun M =>
    if C.assumptions.contains "A1" then
      forestBoundAt dS C.c C.p C.t C.s Tmax table ((M - 1) / 2 / scale)
    else 0

/-- The one-plane table on scaled durations: rows `0, …, s`, columns `0, …, maxLevel`. -/
def table : Array (Array (WithTop ℕ)) :=
  oneplaneTable (scaledDurations C.d) C.c C.maxLevel C.s

/-- Obligation 3: at every gap, the named bound reaches the cost of the point above. -/
def gapsCheck : Bool :=
  let scale := durationScale C.d
  let Tmax := (C.front.map fun x => (x.2 - 1) / 2 / scale).foldr max 0
  let dArr := Array.ofFn (n := C.n) fun i => C.d i / scale
  let dS : Fin C.n → ℕ := fun i => dArr.getD i 0
  gapsOK (C.boundWith scale Tmax dS (oneplaneTable dS C.c Tmax C.s)) C.front C.gaps

theorem boundOf_eq (table : Array (Array (WithTop ℕ))) :
    C.boundOf table = C.boundWith (durationScale C.d) C.maxLevel (scaledDurations C.d) table := by
  funext g M
  cases g <;> rfl

/-- `gapsCheck` is obligation 3 for the bounds `boundOf`. -/
theorem gapsCheck_eq : C.gapsCheck = gapsOK (C.boundOf C.table) C.front C.gaps := by
  have hdS : (fun i : Fin C.n => (Array.ofFn (n := C.n) fun i => C.d i / durationScale C.d).getD
      i 0) = scaledDurations C.d := by
    funext i
    simp [Array.getD_eq_getD_getElem?, scaledDurations]
  simp only [gapsCheck]
  rw [hdS, boundOf_eq]
  rfl

/-- **The checker.** -/
def check : Bool :=
  C.headerOK && strictlyMonotone C.front && C.plansOK && C.firstOK && C.lastOK && C.gapsCheck

/-- The relaxed gap bound is sound: a feasible plan with makespan below `M` costs at least
`gapBound M`. -/
theorem gapBound_le {dc : Fin C.n → Fin C.n → ℕ} (hS : C.dbar = C.d) (hpt : C.p ≤ C.t)
    {P : Plan C.n C.t C.p} (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.gapBound C.table M ≤ (planCost C.c P : WithTop ℕ) := by
  obtain ⟨Y, hpos, hsize, hload, hcost⟩ := hP.exists_relaxation (c := C.c) hS hpt
  refine (relaxedBoundAt_le_totalCost (scaledDurations C.d) C.c Y hpos hsize fun k => ?_).trans
    (WithTop.coe_le_coe.mpr hcost)
  apply load_scaled_le_of_load_le
  have := hload k
  change 2 * load C.d (Y k) ≤ planMakespan P at this
  rw [Nat.le_div_iff_mul_le Nat.two_pos]
  omega

/-- The forest gap bound is sound under the triangles through a hub: a feasible plan with
makespan below `M` costs at least `forestGapBound M`. This is where the converse (Theorem 4.10) is
used. -/
theorem forestGapBound_le_hub {dc : Fin C.n → Fin C.n → ℕ} (hS : C.dbar = C.d)
    (hL : (C.network dc).ATriHub) (hp : 1 ≤ C.p) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.forestGapBound C.table M ≤ (planCost C.c P : WithTop ℕ) := by
  unfold forestGapBound
  split_ifs
  · obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_hub (c := C.c) hS hL hpt
    refine (forestBoundAt_le_totalCost (scaledDurations C.d) C.c hp hpt hX hsize fun k => ?_).trans
      (WithTop.coe_le_coe.mpr hcost)
    apply load_scaled_le_of_load_le
    have := (hload k).1.trans (hload k).2
    change 2 * load C.d (X k) ≤ planMakespan P at this
    rw [Nat.le_div_iff_mul_le Nat.two_pos]
    omega
  · exact bot_le

/-- The forest gap bound is sound under (A1). -/
theorem forestGapBound_le {dc : Fin C.n → Fin C.n → ℕ} (hS : C.dbar = C.d)
    (hA1 : (C.network dc).A1) (hp : 1 ≤ C.p) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.forestGapBound C.table M ≤ (planCost C.c P : WithTop ℕ) :=
  C.forestGapBound_le_hub hS hA1.hub hp hpt hP hM

/-- The forest gap bound is sound under (AΔ). -/
theorem forestGapBound_le_ATri {dc : Fin C.n → Fin C.n → ℕ} (hS : C.dbar = C.d)
    (hA : (C.network dc).ATri) (hp : 1 ≤ C.p) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.forestGapBound C.table M ≤ (planCost C.c P : WithTop ℕ) :=
  C.forestGapBound_le_hub hS hA.hub hp hpt hP hM

/-- **Soundness of the checker.** If `check` accepts a certificate, its points are exactly the
Pareto front of the instance (every point is achieved by a feasible plan, every feasible plan is
weakly dominated by a point, and the points are pairwise incomparable) for every table `dc` of
central flight durations that satisfies the triangles through a hub, or for every table if all
gaps are `relaxed`. -/
theorem check_sound_hub (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).ATriHub ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hhead, hmono⟩, hplans⟩, hfirst⟩, hlast⟩, hgaps⟩ := h
  rw [gapsCheck_eq] at hgaps
  simp only [headerOK, Bool.and_eq_true, decide_eq_true_eq] at hhead
  obtain ⟨⟨⟨⟨-, hp⟩, hpt⟩, hsym⟩, -⟩ := hhead
  have hS : (C.network dc).dbar = (C.network dc).d := funext fun i => (hsym i).symm
  have hS' : C.dbar = C.d := hS
  simp only [plansOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hplans
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · -- 1. Every point is achieved by its plan.
    obtain ⟨P, hPx⟩ := exists_mem_zip_of_mem hplans.1 hx
    obtain ⟨⟨hok, hcost⟩, hmk⟩ := hplans.2 _ hPx
    exact ⟨P, planOK_feasible dc hok, Prod.ext hcost hmk⟩
  · -- 2–4. Every feasible plan is weakly dominated.
    obtain ⟨P, hP, rfl⟩ := hy
    refine exists_le_of_gapsOK (C.boundOf C.table) _ C.front C.gaps
      (fun g hg M hM => ?_) hgaps (fun x hx => ?_) (fun x hx => ?_)
    · cases g with
      | relaxed => exact C.gapBound_le hS' hpt hP hM
      | forest =>
        rcases hdc with hL | hrel
        · exact C.forestGapBound_le_hub hS' hL hp hpt hP hM
        · exact absurd (hrel _ hg) (by decide)
    · simp only [firstOK] at hfirst
      rw [Option.mem_def] at hx
      rw [hx] at hfirst
      simp only [decide_eq_true_eq] at hfirst
      rw [hfirst]
      exact hP.minOf_le_makespan hS C.c hp hpt
    · simp only [lastOK] at hlast
      rw [Option.mem_def] at hx
      rw [hx] at hlast
      simp only [decide_eq_true_eq] at hlast
      rw [hlast]
      exact hP.minOf_le_cost hS C.c hpt
  · -- The points are pairwise incomparable.
    refine (pairwise_of_strictlyMonotone hmono).imp fun {a b} hab => ⟨fun hle => ?_, fun hle => ?_⟩
    · exact absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2)
    · exact absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)

/-- **Soundness of the checker under (A1)**, or for every table if all gaps are `relaxed`. -/
theorem check_sound (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).A1 ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound_hub h dc (hdc.imp_left Network.A1.hub)

/-- **Soundness under (A1).** If `check` accepts, the points are the Pareto front for every
table of central flight durations satisfying (A1), whatever the gap kinds. -/
theorem check_sound_A1 (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA1 : (C.network dc).A1) : IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound h dc (Or.inl hA1)

/-- **Soundness of relaxed certificates.** If `check` accepts and every gap is `relaxed`, the
points are the Pareto front for **every** table of central flight durations (no (A1)). -/
theorem check_sound_relaxed (h : C.check = true) (hrel : ∀ g ∈ C.gaps, g = .relaxed)
    (dc : Fin C.n → Fin C.n → ℕ) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound_hub h dc (Or.inr hrel)

/-- **Soundness of the checker under (AΔ).** If `check` accepts a certificate, its points are
exactly the Pareto front of the instance for every table `dc` of central flight durations that
satisfies (AΔ), whatever the gap kinds. -/
theorem check_sound_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound_hub h dc (Or.inl hA.hub)

/-- **Soundness, minimal-elements form.** If `check` accepts, a pair is listed iff it is a
minimal (cost, makespan) pair of a feasible plan, for every table of central flight durations
satisfying (A1), or every table if all gaps are `relaxed`. -/
theorem check_sound_minimal (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).A1 ∨ ∀ g ∈ C.gaps, g = .relaxed) (x : ℕ × ℕ) :
    x ∈ C.front ↔ Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x :=
  (C.check_sound h dc hdc).mem_iff_minimal x

/-- **Soundness under (AΔ), minimal-elements form.** If `check` accepts, a pair is listed iff it
is a minimal (cost, makespan) pair of a feasible plan, for every table satisfying (AΔ). -/
theorem check_sound_minimal_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) (x : ℕ × ℕ) :
    x ∈ C.front ↔ Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x :=
  (C.check_sound_ATri h dc hA).mem_iff_minimal x

end Cert

end ZenoFront
