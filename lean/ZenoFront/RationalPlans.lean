/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Checker
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Cast.Order

/-!
# Plans with rational times

The plans of a certificate have integer times, but the competitors in the soundness theorem
need not: this file extends `Cert.check_sound` to plans whose departures and arrivals are
rational (durations stay the instance's integers).

The reduction is by rounding down. A feasible plan with rational times, its times all rounded
down, is a feasible plan with integer times, of the same cost and of no larger makespan: a leg
`arr = dep + τ` with `τ` an integer gives `⌊arr⌋ = ⌊dep⌋ + τ`, and rounding down keeps every
inequality `arrival ≤ next departure`, for planes and for passengers (`QFeasible.floor`). An
integer plan is a rational plan with the same cost and makespan (`Feasible.toRat`).

## Main results

* `ZenoFront.QFeasible.floor`, `ZenoFront.planMakespan_floor_le`: rounding a rational plan down.
* `ZenoFront.Cert.check_sound_rat_hub`: if `check` accepts, the listed points are exactly the
  Pareto front of the (cost, makespan) pairs of the feasible plans **with rational times**, for
  every table of central flight durations satisfying the triangles through a hub (or every table
  if all gaps are `relaxed`); under (A1) `Cert.check_sound_rat`, under (AΔ)
  `Cert.check_sound_rat_ATri`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- A leg with rational times. -/
structure QLeg (n t : ℕ) where
  src : Loc n
  dst : Loc n
  dep : ℚ
  arr : ℚ
  pax : Option (Fin t)
  deriving DecidableEq

/-- A plan with rational times. -/
abbrev QPlan (n t p : ℕ) := Fin p → List (QLeg n t)

namespace QLeg

/-- Round both times down. -/
def floor (ℓ : QLeg n t) : Leg n t := ⟨ℓ.src, ℓ.dst, ⌊ℓ.dep⌋₊, ⌊ℓ.arr⌋₊, ℓ.pax⟩

/-- An integer leg, as a rational one. -/
def ofLeg (ℓ : Leg n t) : QLeg n t := ⟨ℓ.src, ℓ.dst, ℓ.dep, ℓ.arr, ℓ.pax⟩

@[simp] theorem floor_ofLeg (ℓ : Leg n t) : (ofLeg ℓ).floor = ℓ := by
  simp [floor, ofLeg]

end QLeg

/-- A rational leg is a flight of the network, of exactly its (integer) duration. -/
def QFlies (N : Network n) (ℓ : QLeg n t) : Prop :=
  ∃ τ : ℕ, N.duration ℓ.src ℓ.dst = some τ ∧ ℓ.arr = ℓ.dep + τ

/-- `QIsRoute x τ legs`: as `IsRoute`, with rational times. -/
def QIsRoute : Loc n → ℚ → List (QLeg n t) → Prop
  | _, _, [] => True
  | x, τ, ℓ :: rest => ℓ.src = x ∧ τ ≤ ℓ.dep ∧ QIsRoute ℓ.dst ℓ.arr rest

/-- When a rational route starting at time `τ` ends. -/
def qEndTime : ℚ → List (QLeg n t) → ℚ
  | τ, [] => τ
  | _, ℓ :: rest => qEndTime ℓ.arr rest

/-- A feasible plane, with rational times. -/
structure QPlaneFeasible (N : Network n) (legs : List (QLeg n t)) : Prop where
  flies : ∀ ℓ ∈ legs, QFlies N ℓ
  route : QIsRoute .ci 0 legs
  ends : finalLoc .ci (legs.map QLeg.floor) = .cg

/-- All legs of a rational plan. -/
def qAllLegs (P : QPlan n t p) : List (QLeg n t) := (List.finRange p).flatMap P

/-- The legs carrying passenger `π`. -/
def qPaxLegs (P : QPlan n t p) (π : Fin t) : List (QLeg n t) :=
  (qAllLegs P).filter fun ℓ => decide (ℓ.pax = some π)

/-- A feasible plan with rational times. -/
structure QFeasible (N : Network n) (P : QPlan n t p) : Prop where
  planes : ∀ k, QPlaneFeasible N (P k)
  pax : ∀ π, ∃ route : List (QLeg n t), route.Perm (qPaxLegs P π) ∧ QIsRoute .ci 0 route ∧
    finalLoc .ci (route.map QLeg.floor) = .cg

/-- The cost of a rational plan (landings only). -/
def qPlanCost (c : Fin n → ℕ) (P : QPlan n t p) : ℕ :=
  ∑ k, ((P k).map fun ℓ => landCost c ℓ.floor).sum

/-- The makespan of a rational plan. -/
def qPlanMakespan (P : QPlan n t p) : ℚ :=
  (List.finRange p).foldr (fun k m => max (qEndTime 0 (P k)) m) 0

/-- The (cost, makespan) pairs of the feasible plans with rational times. -/
def achievableQ (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℚ) :=
  {x | ∃ P : QPlan n t p, QFeasible N P ∧ (qPlanCost c P, qPlanMakespan P) = x}

/-! ### Rounding down -/

/-- A rational plan with its times rounded down. -/
def floorPlan (P : QPlan n t p) : Plan n t p := fun k => (P k).map QLeg.floor

/-- An integer plan as a rational one. -/
def ofPlan (P : Plan n t p) : QPlan n t p := fun k => (P k).map QLeg.ofLeg

theorem QIsRoute.floor {N : Network n} : ∀ {x : Loc n} {τ : ℚ} {l : List (QLeg n t)},
    0 ≤ τ → QIsRoute x τ l → (∀ ℓ ∈ l, QFlies N ℓ) →
      IsRoute x ⌊τ⌋₊ (l.map QLeg.floor) ∧ ∀ ℓ ∈ l, 0 ≤ ℓ.dep
  | _, _, [], _, _, _ => ⟨trivial, by simp⟩
  | x, τ, ℓ :: rest, hτ, h, hf => by
    obtain ⟨hsrc, hdep, hrest⟩ := h
    obtain ⟨d, -, harr⟩ := hf ℓ List.mem_cons_self
    have hdep0 : 0 ≤ ℓ.dep := hτ.trans hdep
    have harr0 : 0 ≤ ℓ.arr := by rw [harr]; positivity
    obtain ⟨ih₁, ih₂⟩ := QIsRoute.floor harr0 hrest fun m hm => hf m (List.mem_cons_of_mem _ hm)
    refine ⟨⟨hsrc, Nat.floor_le_floor hdep, ih₁⟩, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hdep0
    · exact ih₂ m hm

theorem QFlies.floor {N : Network n} {ℓ : QLeg n t} (h : QFlies N ℓ) (h0 : 0 ≤ ℓ.dep) :
    Flies N ℓ.floor := by
  obtain ⟨τ, hdur, harr⟩ := h
  refine ⟨τ, hdur, ?_⟩
  simp only [QLeg.floor, harr]
  exact Nat.floor_add_natCast h0 τ

theorem qEndTime_floor : ∀ (τ : ℚ) (l : List (QLeg n t)),
    endTime ⌊τ⌋₊ (l.map QLeg.floor) = ⌊qEndTime τ l⌋₊
  | _, [] => rfl
  | _, ℓ :: rest => qEndTime_floor ℓ.arr rest

theorem floorPlan_allLegs (P : QPlan n t p) :
    allLegs (floorPlan P) = (qAllLegs P).map QLeg.floor := by
  simp only [allLegs, qAllLegs, List.map_flatMap]
  rfl

theorem floorPlan_paxLegs (P : QPlan n t p) (π : Fin t) :
    paxLegs (floorPlan P) π = (qPaxLegs P π).map QLeg.floor := by
  simp only [paxLegs, qPaxLegs, floorPlan_allLegs, List.filter_map]
  rfl

theorem QFeasible.mem_qAllLegs_flies {N : Network n} {P : QPlan n t p} (hP : QFeasible N P)
    {ℓ : QLeg n t} (h : ℓ ∈ qAllLegs P) : QFlies N ℓ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact (hP.planes k).flies ℓ hk

/-- **Rounding down keeps feasibility.** -/
theorem QFeasible.floor {N : Network n} {P : QPlan n t p} (hP : QFeasible N P) :
    Feasible N (floorPlan P) := by
  refine ⟨fun k => ⟨fun ℓ hℓ => ?_, ?_, (hP.planes k).ends⟩, fun π => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hℓ
    have := (QIsRoute.floor le_rfl (hP.planes k).route (hP.planes k).flies).2 m hm
    exact ((hP.planes k).flies m hm).floor this
  · have := (QIsRoute.floor le_rfl (hP.planes k).route (hP.planes k).flies).1
    simpa [floorPlan] using this
  · obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    have hflies : ∀ ℓ ∈ route, QFlies N ℓ := fun ℓ hℓ =>
      hP.mem_qAllLegs_flies (List.mem_filter.mp (hperm.mem_iff.mp hℓ)).1
    refine ⟨route.map QLeg.floor, ?_, ?_, hfin⟩
    · rw [floorPlan_paxLegs]
      exact hperm.map _
    · simpa using (QIsRoute.floor le_rfl hroute hflies).1

theorem qPlanCost_eq (c : Fin n → ℕ) (P : QPlan n t p) :
    planCost c (floorPlan P) = qPlanCost c P := by
  simp [planCost, qPlanCost, floorPlan, List.map_map, Function.comp_def]

theorem le_foldr_max {ι : Type*} (f : ι → ℚ) : ∀ (l : List ι) (b : ℚ),
    b ≤ l.foldr (fun k m => max (f k) m) b ∧ ∀ k ∈ l, f k ≤ l.foldr (fun k m => max (f k) m) b
  | [], b => ⟨le_rfl, by simp⟩
  | k :: l, b => by
    obtain ⟨h₁, h₂⟩ := le_foldr_max f l b
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨h₁.trans (le_max_right _ _), le_max_left _ _,
      fun k' hk' => (h₂ k' hk').trans (le_max_right _ _)⟩

theorem foldr_max_le {ι : Type*} (f : ι → ℚ) {M : ℚ} : ∀ (l : List ι) (b : ℚ), b ≤ M →
    (∀ k ∈ l, f k ≤ M) → l.foldr (fun k m => max (f k) m) b ≤ M
  | [], _, hb, _ => hb
  | k :: l, b, hb, h => by
    simp only [List.foldr_cons]
    exact max_le (h k List.mem_cons_self)
      (foldr_max_le f l b hb fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))

theorem le_qEndTime {N : Network n} : ∀ {x : Loc n} {τ : ℚ} {l : List (QLeg n t)},
    QIsRoute x τ l → (∀ ℓ ∈ l, QFlies N ℓ) → τ ≤ qEndTime τ l
  | _, _, [], _, _ => le_rfl
  | _, τ, ℓ :: rest, ⟨_, hdep, hrest⟩, hf => by
    obtain ⟨d, -, harr⟩ := hf ℓ List.mem_cons_self
    have : ℓ.dep ≤ ℓ.arr := by rw [harr]; exact le_add_of_nonneg_right (Nat.cast_nonneg d)
    exact hdep.trans (this.trans (le_qEndTime hrest fun m hm => hf m (List.mem_cons_of_mem _ hm)))

/-- **Rounding down does not increase the makespan.** -/
theorem planMakespan_floor_le {N : Network n} {P : QPlan n t p} (hP : QFeasible N P) :
    (planMakespan (floorPlan P) : ℚ) ≤ qPlanMakespan P := by
  have hk : ∀ k, (endTime 0 (floorPlan P k) : ℚ) ≤ qPlanMakespan P := by
    intro k
    have h₁ : endTime 0 (floorPlan P k) = ⌊qEndTime 0 (P k)⌋₊ := by
      simpa [floorPlan] using qEndTime_floor 0 (P k)
    have h₂ : 0 ≤ qEndTime 0 (P k) := le_qEndTime (hP.planes k).route (hP.planes k).flies
    rw [h₁]
    exact (Nat.floor_le h₂).trans
      ((le_foldr_max (fun k => qEndTime 0 (P k)) (List.finRange p) 0).2 k (List.mem_finRange k))
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp [planMakespan, qPlanMakespan]
  · obtain ⟨k, -, hk'⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin p))
      ⟨⟨0, hp⟩, Finset.mem_univ _⟩ fun k => endTime 0 (floorPlan P k)
    rw [planMakespan, hk']
    exact hk k

/-! ### Integer plans are rational plans -/

theorem IsRoute.toRat : ∀ {x : Loc n} {τ : ℕ} {l : List (Leg n t)},
    IsRoute x τ l → QIsRoute x (τ : ℚ) (l.map QLeg.ofLeg)
  | _, _, [], _ => trivial
  | _, _, ℓ :: rest, ⟨hsrc, hdep, hrest⟩ =>
    ⟨hsrc, by simp only [QLeg.ofLeg]; exact_mod_cast hdep, IsRoute.toRat hrest⟩

theorem qEndTime_ofLeg : ∀ (τ : ℕ) (l : List (Leg n t)),
    qEndTime (τ : ℚ) (l.map QLeg.ofLeg) = (endTime τ l : ℚ)
  | _, [] => rfl
  | _, ℓ :: rest => qEndTime_ofLeg ℓ.arr rest

theorem ofPlan_qAllLegs (P : Plan n t p) : qAllLegs (ofPlan P) = (allLegs P).map QLeg.ofLeg := by
  simp only [qAllLegs, allLegs, List.map_flatMap]
  rfl

theorem ofPlan_qPaxLegs (P : Plan n t p) (π : Fin t) :
    qPaxLegs (ofPlan P) π = (paxLegs P π).map QLeg.ofLeg := by
  simp only [qPaxLegs, paxLegs, ofPlan_qAllLegs, List.filter_map]
  rfl

theorem map_floor_ofLeg (l : List (Leg n t)) : (l.map QLeg.ofLeg).map QLeg.floor = l := by
  simp [List.map_map, Function.comp_def]

/-- **An integer plan is a rational plan**, with the same cost and makespan. -/
theorem Feasible.toRat {N : Network n} (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) :
    QFeasible N (ofPlan P) ∧ qPlanCost c (ofPlan P) = planCost c P ∧
      qPlanMakespan (ofPlan P) = (planMakespan P : ℚ) := by
  refine ⟨⟨fun k => ⟨fun ℓ hℓ => ?_, ?_, ?_⟩, fun π => ?_⟩, ?_, ?_⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hℓ
    obtain ⟨τ, hdur, harr⟩ := (hP.planes k).flies m hm
    exact ⟨τ, hdur, by simp [QLeg.ofLeg, harr]⟩
  · simpa [ofPlan] using IsRoute.toRat (hP.planes k).route
  · simpa [ofPlan, List.map_map, Function.comp_def] using (hP.planes k).ends
  · obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    refine ⟨route.map QLeg.ofLeg, ?_, by simpa [ofPlan] using IsRoute.toRat hroute, ?_⟩
    · rw [ofPlan_qPaxLegs]
      exact hperm.map _
    · rw [map_floor_ofLeg]
      exact hfin
  · simp [qPlanCost, planCost, ofPlan, List.map_map, Function.comp_def]
  · have hk : ∀ k, qEndTime 0 (ofPlan P k) = (endTime 0 (P k) : ℚ) := fun k => by
      simpa [ofPlan] using qEndTime_ofLeg 0 (P k)
    refine le_antisymm (foldr_max_le _ _ 0 (Nat.cast_nonneg _) fun k _ => ?_) ?_
    · rw [hk]
      exact_mod_cast endTime_le_planMakespan P k
    · rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        simp [planMakespan, qPlanMakespan]
      · obtain ⟨k, -, hk'⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin p))
          ⟨⟨0, hp⟩, Finset.mem_univ _⟩ fun k => endTime 0 (P k)
        rw [planMakespan, hk', ← hk]
        exact (le_foldr_max (fun k => qEndTime 0 (ofPlan P k)) (List.finRange p) 0).2 k
          (List.mem_finRange k)

/-! ### Soundness for rational plans -/

namespace Cert

variable (C : Cert)

/-- **Soundness for plans with rational times.** If `check` accepts, the listed points are
exactly the Pareto front of the (cost, makespan) pairs of the feasible plans with rational times,
for every table of central flight durations satisfying the triangles through a hub, or every
table if all gaps are `relaxed`. -/
theorem check_sound_rat_hub (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).ATriHub ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievableQ (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : ℚ))) := by
  have H := C.check_sound_hub h dc hdc
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    obtain ⟨P, hP, hPx⟩ := H.achieved x' hx'
    obtain ⟨hQ, hcost, hmk⟩ := hP.toRat C.c
    refine ⟨ofPlan P, hQ, ?_⟩
    rw [hcost, hmk, ← hPx]
  · obtain ⟨P, hP, rfl⟩ := hy
    obtain ⟨x, hx, hle⟩ := H.dominates _ ⟨floorPlan P, hP.floor, rfl⟩
    refine ⟨(x.1, (x.2 : ℚ)), List.mem_map.mpr ⟨x, hx, rfl⟩, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · have := (Prod.le_def.mp hle).1
      rw [qPlanCost_eq] at this
      exact this
    · have := (Prod.le_def.mp hle).2
      exact (Nat.cast_le.mpr this).trans (planMakespan_floor_le hP)
  · refine (List.pairwise_map.mpr ?_)
    refine H.antichain.imp fun {a b} hab => ⟨fun hle => hab.1 ?_, fun hle => hab.2 ?_⟩
    · obtain ⟨h₁, h₂⟩ := Prod.le_def.mp hle
      simp only at h₁ h₂
      exact Prod.le_def.mpr ⟨h₁, by exact_mod_cast h₂⟩
    · obtain ⟨h₁, h₂⟩ := Prod.le_def.mp hle
      simp only at h₁ h₂
      exact Prod.le_def.mpr ⟨h₁, by exact_mod_cast h₂⟩

/-- **Soundness for plans with rational times, under (A1)**, or for every table if all gaps are
`relaxed`. -/
theorem check_sound_rat (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).A1 ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievableQ (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : ℚ))) :=
  C.check_sound_rat_hub h dc (hdc.imp_left Network.A1.hub)

/-- **Soundness for plans with rational times, under (AΔ).** -/
theorem check_sound_rat_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievableQ (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : ℚ))) :=
  C.check_sound_rat_hub h dc (Or.inl hA.hub)

end Cert

end ZenoFront
