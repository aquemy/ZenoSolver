/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Converse

/-!
# Assumption (A1-NS), splitting central flights, role loads

**(A1-NS).** A central flight is no shorter than a detour through one of the hubs:
`dc a b ≥ min(d_a + d_b, d̄_a + d̄_b)` (`Network.A1NS`).

**Splitting** (`Feasible.split`, Step 1 of Theorem 6.9). Replace every central flight `a → b` by
`a → h → b`, `h` the hub of the shorter detour (`splitLeg`). By (A1-NS) the plane reaches `b` no
later, and waits there; a passenger on board stays on board through `h`. The plan stays
feasible, has the same cost and no larger makespan, and has no central flight.

**Role loads** (`RoleConfig.roleLoad`). The role load of plane `k` of a role configuration is
`2 δ(Dr_k) + 2 δ̄(Pk_k) + δ(Cr_k) + δ̄(Cr_k)`: a drop-off at `x` weighs `2 d_x`, a pick-up
`2 d̄_x`, a crossing `d_x + d̄_x`. Theorem 6.1 bounds them by the makespan
(`Feasible.exists_roleConfig_of_domination`, `NSFront.lean`).

## Main results

* `ZenoFront.Network.A1NS`: assumption (A1-NS).
* `ZenoFront.Feasible.split`: under (A1-NS), a feasible plan without central flights of the same
  cost and no larger makespan.
* `ZenoFront.RoleConfig.roleLoad`: the role load of a plane.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- Assumption (A1-NS): a central flight is no shorter than a detour through one of the hubs. -/
def Network.A1NS (N : Network n) : Prop :=
  ∀ i j, min (N.d i + N.d j) (N.dbar i + N.dbar j) ≤ N.dc i j

/-- Whether a leg joins two central cities. -/
def Leg.central (ℓ : Leg n t) : Bool := !ℓ.src.isHub && !ℓ.dst.isHub

/-! ### Step 1: removing central flights -/

/-- Replace a central flight `a → b` by `a → h → b` through the hub of the shorter detour, with
the same passenger; other legs are kept. -/
def splitLeg (N : Network n) (ℓ : Leg n t) : List (Leg n t) :=
  match ℓ.src, ℓ.dst with
  | .city a, .city b =>
    if N.d a + N.d b ≤ N.dbar a + N.dbar b then
      [⟨.city a, .ci, ℓ.dep, ℓ.dep + N.d a, ℓ.pax⟩,
       ⟨.ci, .city b, ℓ.dep + N.d a, ℓ.dep + N.d a + N.d b, ℓ.pax⟩]
    else
      [⟨.city a, .cg, ℓ.dep, ℓ.dep + N.dbar a, ℓ.pax⟩,
       ⟨.cg, .city b, ℓ.dep + N.dbar a, ℓ.dep + N.dbar a + N.dbar b, ℓ.pax⟩]
  | _, _ => [ℓ]

/-- A plan with every central flight split. -/
def splitPlan (N : Network n) (P : Plan n t p) : Plan n t p := fun k => (P k).flatMap (splitLeg N)

theorem IsRoute.mono : ∀ {x : Loc n} {τ τ' : ℕ} {l : List (Leg n t)},
    IsRoute x τ l → τ' ≤ τ → IsRoute x τ' l
  | _, _, _, [], _, _ => trivial
  | _, _, _, _ :: _, ⟨h₁, h₂, h₃⟩, h => ⟨h₁, h.trans h₂, h₃⟩

theorem isRoute_append : ∀ {x : Loc n} {τ : ℕ} (L M : List (Leg n t)),
    IsRoute x τ (L ++ M) ↔ IsRoute x τ L ∧ IsRoute (finalLoc x L) (endTime τ L) M
  | _, _, [], _ => by simp
  | x, τ, ℓ :: L, M => by
    simp only [List.cons_append, IsRoute, finalLoc_cons, endTime_cons, isRoute_append L M]
    tauto

theorem finalLoc_append (x : Loc n) : ∀ (L M : List (Leg n t)),
    finalLoc x (L ++ M) = finalLoc (finalLoc x L) M
  | [], _ => rfl
  | ℓ :: L, M => finalLoc_append ℓ.dst L M

theorem endTime_append (τ : ℕ) : ∀ (L M : List (Leg n t)),
    endTime τ (L ++ M) = endTime (endTime τ L) M
  | [], _ => rfl
  | ℓ :: L, M => endTime_append ℓ.arr L M

theorem endTime_mono {a b : ℕ} (h : a ≤ b) : ∀ M : List (Leg n t), endTime a M ≤ endTime b M
  | [] => h
  | _ :: _ => le_rfl

/-- What splitting a leg gives, for a flight of the network under (A1-NS). -/
theorem splitLeg_spec {N : Network n} (hA : N.A1NS) {ℓ : Leg n t} (hℓ : Flies N ℓ) :
    (∀ m ∈ splitLeg N ℓ, Flies N m ∧ m.central = false ∧ m.pax = ℓ.pax) ∧
    (∀ τ, τ ≤ ℓ.dep → IsRoute ℓ.src τ (splitLeg N ℓ)) ∧
    (∀ x, finalLoc x (splitLeg N ℓ) = ℓ.dst) ∧
    (∀ τ, endTime τ (splitLeg N ℓ) ≤ ℓ.arr) ∧
    (∀ c : Fin n → ℕ, ((splitLeg N ℓ).map (landCost c)).sum = landCost c ℓ) := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ₀, hdur, harr⟩ := hℓ
  simp only at hdur harr
  cases src with
  | city a =>
    cases dst with
    | city b =>
      simp only [Network.duration, Option.some.injEq] at hdur
      have hA' := hA a b
      simp only [splitLeg]
      split_ifs with hab
      · refine ⟨fun m hm => ?_, fun τ hτ => ?_, fun x => rfl, fun τ => ?_, fun c => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨rfl, hτ, rfl, le_rfl, trivial⟩
        · simp only [endTime_cons, endTime_nil]
          rw [min_eq_left hab] at hA'
          omega
        · simp [landCost]
      · refine ⟨fun m hm => ?_, fun τ hτ => ?_, fun x => rfl, fun τ => ?_, fun c => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨rfl, hτ, rfl, le_rfl, trivial⟩
        · simp only [endTime_cons, endTime_nil]
          rw [min_eq_right (by omega)] at hA'
          omega
        · simp [landCost]
    | ci =>
      simp only [splitLeg]
      exact ⟨fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm; exact ⟨⟨τ₀, hdur, harr⟩, rfl, rfl⟩,
        fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
    | cg =>
      simp only [splitLeg]
      exact ⟨fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm; exact ⟨⟨τ₀, hdur, harr⟩, rfl, rfl⟩,
        fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
  | ci =>
    simp only [splitLeg]
    exact ⟨fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact ⟨⟨τ₀, hdur, harr⟩, by simp [Leg.central], rfl⟩,
      fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
  | cg =>
    simp only [splitLeg]
    exact ⟨fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact ⟨⟨τ₀, hdur, harr⟩, by simp [Leg.central], rfl⟩,
      fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩

section Split

variable {N : Network n} (hA : N.A1NS)
include hA

theorem isRoute_flatMap_split : ∀ {x : Loc n} {τ : ℕ} {l : List (Leg n t)}, IsRoute x τ l →
    (∀ ℓ ∈ l, Flies N ℓ) → IsRoute x τ (l.flatMap (splitLeg N))
  | _, _, [], _, _ => trivial
  | x, τ, ℓ :: rest, ⟨hsrc, hdep, hrest⟩, hf => by
    obtain ⟨-, hroute, hfin, hend, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, isRoute_append]
    refine ⟨hsrc ▸ hroute τ hdep, ?_⟩
    rw [hfin]
    exact (isRoute_flatMap_split hrest fun m hm => hf m (List.mem_cons_of_mem _ hm)).mono
      (hend τ)

theorem finalLoc_flatMap_split : ∀ (x : Loc n) {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    finalLoc x (l.flatMap (splitLeg N)) = finalLoc x l
  | _, [], _ => rfl
  | x, ℓ :: rest, hf => by
    obtain ⟨-, -, hfin, -, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, finalLoc_append, hfin, finalLoc_cons]
    exact finalLoc_flatMap_split ℓ.dst fun m hm => hf m (List.mem_cons_of_mem _ hm)

theorem endTime_flatMap_split : ∀ (τ : ℕ) {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    endTime τ (l.flatMap (splitLeg N)) ≤ endTime τ l
  | _, [], _ => le_rfl
  | τ, ℓ :: rest, hf => by
    obtain ⟨-, -, -, hend, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, endTime_append, endTime_cons]
    exact (endTime_mono (hend τ) _).trans
      (endTime_flatMap_split ℓ.arr fun m hm => hf m (List.mem_cons_of_mem _ hm))

theorem landCost_flatMap_split (c : Fin n → ℕ) : ∀ {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    ((l.flatMap (splitLeg N)).map (landCost c)).sum = (l.map (landCost c)).sum
  | [], _ => rfl
  | ℓ :: rest, hf => by
    obtain ⟨-, -, -, -, hcost⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, List.map_append, List.sum_append, hcost, List.map_cons, List.sum_cons,
      landCost_flatMap_split c fun m hm => hf m (List.mem_cons_of_mem _ hm)]

theorem mem_flatMap_split {l : List (Leg n t)} (hf : ∀ ℓ ∈ l, Flies N ℓ) {m : Leg n t}
    (hm : m ∈ l.flatMap (splitLeg N)) :
    ∃ ℓ ∈ l, Flies N m ∧ m.central = false ∧ m.pax = ℓ.pax := by
  obtain ⟨ℓ, hℓ, hmℓ⟩ := List.mem_flatMap.mp hm
  exact ⟨ℓ, hℓ, (splitLeg_spec hA (hf ℓ hℓ)).1 m hmℓ⟩

theorem filter_flatMap_split (π : Fin t) : ∀ {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    (l.flatMap (splitLeg N)).filter (fun ℓ => decide (ℓ.pax = some π)) =
      (l.filter fun ℓ => decide (ℓ.pax = some π)).flatMap (splitLeg N)
  | [], _ => rfl
  | ℓ :: rest, hf => by
    have hpax := fun m hm => ((splitLeg_spec hA (hf ℓ List.mem_cons_self)).1 m hm).2.2
    have ih := filter_flatMap_split π fun m hm => hf m (List.mem_cons_of_mem _ hm)
    rw [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
    by_cases hℓ : ℓ.pax = some π
    · rw [List.filter_eq_self.mpr fun m hm => by simp [hpax m hm, hℓ]]
      simp [hℓ]
    · rw [List.filter_eq_nil_iff.mpr fun m hm => by simp [hpax m hm, hℓ]]
      simp [hℓ]

/-- **Step 1 of Theorem 6.9.** Under (A1-NS), splitting every central flight keeps a plan
feasible, with the same cost, no larger makespan, and no central flight. -/
theorem Feasible.split {P : Plan n t p} (hP : Feasible N P) :
    Feasible N (splitPlan N P) ∧ (∀ c, planCost c (splitPlan N P) = planCost c P) ∧
      planMakespan (splitPlan N P) ≤ planMakespan P ∧
      ∀ k, ∀ m ∈ splitPlan N P k, m.central = false := by
  have hall : allLegs (splitPlan N P) = (allLegs P).flatMap (splitLeg N) := by
    simp only [allLegs, List.flatMap_assoc]
    rfl
  have hflies : ∀ ℓ ∈ allLegs P, Flies N ℓ := fun ℓ hℓ => hP.flies_of_mem_allLegs hℓ
  refine ⟨⟨fun k => ⟨fun m hm => ?_, ?_, ?_⟩, fun π => ?_⟩, fun c => ?_, ?_, fun k m hm => ?_⟩
  · obtain ⟨ℓ, -, h, -⟩ := mem_flatMap_split hA (hP.planes k).flies hm
    exact h
  · exact isRoute_flatMap_split hA (hP.planes k).route (hP.planes k).flies
  · rw [splitPlan, finalLoc_flatMap_split hA _ (hP.planes k).flies]
    exact (hP.planes k).ends
  · obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    have hrf : ∀ ℓ ∈ route, Flies N ℓ := fun ℓ hℓ =>
      hflies ℓ (List.mem_filter.mp (hperm.mem_iff.mp hℓ)).1
    refine ⟨route.flatMap (splitLeg N), ?_, isRoute_flatMap_split hA hroute hrf, ?_⟩
    · rw [paxLegs, hall, filter_flatMap_split hA π hflies]
      exact hperm.flatMap_right _
    · rw [finalLoc_flatMap_split hA _ hrf]
      exact hfin
  · exact Finset.sum_congr rfl fun k _ => landCost_flatMap_split hA c (hP.planes k).flies
  · exact Finset.sup_le fun k _ =>
      (endTime_flatMap_split hA 0 (hP.planes k).flies).trans (endTime_le_planMakespan P k)
  · obtain ⟨ℓ, -, -, h, -⟩ := mem_flatMap_split hA (hP.planes k).flies hm
    exact h

end Split

/-! ### Role loads -/

/-- The role load of plane `k` of a role configuration. -/
def RoleConfig.roleLoad (N : Network n) (cfg : RoleConfig n p) (k : Fin p) : ℕ :=
  2 * load N.d (cfg.drop k) + 2 * load N.dbar (cfg.pick k) + load N.d (cfg.cross k) +
    load N.dbar (cfg.cross k)

end ZenoFront
