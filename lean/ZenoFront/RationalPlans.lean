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
# Plans with rational or real times

The plans of a certificate have integer times, but the competitors in the soundness theorem
need not: this file extends `Cert.check_sound_hub` to plans whose departures and arrivals lie in
any ordered ring with a floor function `𝕂`, such as `ℚ` or `ℝ` (durations stay the instance's
integers).

The reduction is by rounding down (**Lemma 1.3**). A feasible plan with times in `𝕂`, its times
all rounded down, is a feasible plan with integer times, of the same cost and of no larger
makespan: a leg `arr = dep + τ` with `τ` an integer gives `⌊arr⌋ = ⌊dep⌋ + τ`, and rounding down
keeps every inequality `arrival ≤ next departure`, for planes and for passengers
(`QFeasible.floor`, `qPlanCost_eq`, `planMakespan_floor_le`). An integer plan is a plan with times
in `𝕂` of the same cost and makespan (`Feasible.toRat`).

## Main results

* `ZenoFront.QFeasible.floor`, `ZenoFront.qPlanCost_eq`, `ZenoFront.planMakespan_floor_le`,
  `ZenoFront.Feasible.toRat`: **Lemma 1.3**, rounding the times of a plan down, over any
  `FloorRing`.
* `ZenoFront.Cert.check_sound_rat_hub`: if `check` accepts, the listed points are exactly the
  Pareto front of the (cost, makespan) pairs of the feasible plans **with times in `𝕂`**, for
  every table of central flight durations satisfying the triangles through a hub (or every table
  if all gaps are `relaxed`); under (A1) `Cert.check_sound_rat`, under (AΔ)
  `Cert.check_sound_rat_ATri`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- A leg with times in `𝕂` (rational or real times). -/
structure QLeg (𝕂 : Type*) (n t : ℕ) where
  src : Loc n
  dst : Loc n
  dep : 𝕂
  arr : 𝕂
  pax : Option (Fin t)

/-- A plan with times in `𝕂`. -/
abbrev QPlan (𝕂 : Type*) (n t p : ℕ) := Fin p → List (QLeg 𝕂 n t)

variable {𝕂 : Type*} [Ring 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] [FloorRing 𝕂]

namespace QLeg

/-- Round both times down. -/
def floor (ℓ : QLeg 𝕂 n t) : Leg n t := ⟨ℓ.src, ℓ.dst, ⌊ℓ.dep⌋₊, ⌊ℓ.arr⌋₊, ℓ.pax⟩

variable (𝕂) in
/-- An integer leg, as a leg with times in `𝕂`. -/
def ofLeg (ℓ : Leg n t) : QLeg 𝕂 n t := ⟨ℓ.src, ℓ.dst, ℓ.dep, ℓ.arr, ℓ.pax⟩

omit [IsStrictOrderedRing 𝕂] in
@[simp] theorem floor_ofLeg (ℓ : Leg n t) : (ofLeg 𝕂 ℓ).floor = ℓ := by
  simp [floor, ofLeg]

end QLeg

/-- A leg with times in `𝕂` is a flight of the network, of exactly its (integer) duration. -/
def QFlies (N : Network n) (ℓ : QLeg 𝕂 n t) : Prop :=
  ∃ τ : ℕ, N.duration ℓ.src ℓ.dst = some τ ∧ ℓ.arr = ℓ.dep + τ

/-- `QIsRoute x τ legs`: as `IsRoute`, with times in `𝕂`. -/
def QIsRoute : Loc n → 𝕂 → List (QLeg 𝕂 n t) → Prop
  | _, _, [] => True
  | x, τ, ℓ :: rest => ℓ.src = x ∧ τ ≤ ℓ.dep ∧ QIsRoute ℓ.dst ℓ.arr rest

/-- When a route with times in `𝕂` starting at time `τ` ends. -/
def qEndTime : 𝕂 → List (QLeg 𝕂 n t) → 𝕂
  | τ, [] => τ
  | _, ℓ :: rest => qEndTime ℓ.arr rest

/-- A feasible plane, with times in `𝕂`. -/
structure QPlaneFeasible (N : Network n) (legs : List (QLeg 𝕂 n t)) : Prop where
  flies : ∀ ℓ ∈ legs, QFlies N ℓ
  route : QIsRoute .ci 0 legs
  ends : finalLoc .ci (legs.map QLeg.floor) = .cg

/-- All legs of a plan with times in `𝕂`. -/
def qAllLegs (P : QPlan 𝕂 n t p) : List (QLeg 𝕂 n t) := (List.finRange p).flatMap P

/-- The legs carrying passenger `π`. -/
def qPaxLegs (P : QPlan 𝕂 n t p) (π : Fin t) : List (QLeg 𝕂 n t) :=
  (qAllLegs P).filter fun ℓ => decide (ℓ.pax = some π)

/-- A feasible plan with times in `𝕂`. -/
structure QFeasible (N : Network n) (P : QPlan 𝕂 n t p) : Prop where
  planes : ∀ k, QPlaneFeasible N (P k)
  pax : ∀ π, ∃ route : List (QLeg 𝕂 n t), route.Perm (qPaxLegs P π) ∧ QIsRoute .ci 0 route ∧
    finalLoc .ci (route.map QLeg.floor) = .cg

/-- The cost of a plan with times in `𝕂` (landings only). -/
def qPlanCost (c : Fin n → ℕ) (P : QPlan 𝕂 n t p) : ℕ :=
  ∑ k, ((P k).map fun ℓ => landCost c ℓ.floor).sum

/-- The makespan of a plan with times in `𝕂`. -/
def qPlanMakespan (P : QPlan 𝕂 n t p) : 𝕂 :=
  (List.finRange p).foldr (fun k m => max (qEndTime 0 (P k)) m) 0

variable (𝕂) in
/-- The (cost, makespan) pairs of the feasible plans with times in `𝕂`. -/
def achievableQ (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × 𝕂) :=
  {x | ∃ P : QPlan 𝕂 n t p, QFeasible N P ∧ (qPlanCost c P, qPlanMakespan P) = x}

/-! ### Rounding down -/

/-- A plan with times in `𝕂`, with its times rounded down. -/
def floorPlan (P : QPlan 𝕂 n t p) : Plan n t p := fun k => (P k).map QLeg.floor

variable (𝕂) in
/-- An integer plan as a plan with times in `𝕂`. -/
def ofPlan (P : Plan n t p) : QPlan 𝕂 n t p := fun k => (P k).map (QLeg.ofLeg 𝕂)

theorem QIsRoute.floor {N : Network n} : ∀ {x : Loc n} {τ : 𝕂} {l : List (QLeg 𝕂 n t)},
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

theorem QFlies.floor {N : Network n} {ℓ : QLeg 𝕂 n t} (h : QFlies N ℓ) (h0 : 0 ≤ ℓ.dep) :
    Flies N ℓ.floor := by
  obtain ⟨τ, hdur, harr⟩ := h
  refine ⟨τ, hdur, ?_⟩
  simp only [QLeg.floor, harr]
  exact Nat.floor_add_natCast h0 τ

omit [IsStrictOrderedRing 𝕂] in
theorem qEndTime_floor : ∀ (τ : 𝕂) (l : List (QLeg 𝕂 n t)),
    endTime ⌊τ⌋₊ (l.map QLeg.floor) = ⌊qEndTime τ l⌋₊
  | _, [] => rfl
  | _, ℓ :: rest => qEndTime_floor ℓ.arr rest

omit [IsStrictOrderedRing 𝕂] in
theorem floorPlan_allLegs (P : QPlan 𝕂 n t p) :
    allLegs (floorPlan P) = (qAllLegs P).map QLeg.floor := by
  simp only [allLegs, qAllLegs, List.map_flatMap]
  rfl

omit [IsStrictOrderedRing 𝕂] in
theorem floorPlan_paxLegs (P : QPlan 𝕂 n t p) (π : Fin t) :
    paxLegs (floorPlan P) π = (qPaxLegs P π).map QLeg.floor := by
  simp only [paxLegs, qPaxLegs, floorPlan_allLegs, List.filter_map]
  rfl

omit [IsStrictOrderedRing 𝕂] in
theorem QFeasible.mem_qAllLegs_flies {N : Network n} {P : QPlan 𝕂 n t p} (hP : QFeasible N P)
    {ℓ : QLeg 𝕂 n t} (h : ℓ ∈ qAllLegs P) : QFlies N ℓ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact (hP.planes k).flies ℓ hk

/-- **Rounding down keeps feasibility.** -/
theorem QFeasible.floor {N : Network n} {P : QPlan 𝕂 n t p} (hP : QFeasible N P) :
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

omit [IsStrictOrderedRing 𝕂] in
theorem qPlanCost_eq (c : Fin n → ℕ) (P : QPlan 𝕂 n t p) :
    planCost c (floorPlan P) = qPlanCost c P := by
  simp [planCost, qPlanCost, floorPlan, List.map_map, Function.comp_def]

theorem le_foldr_max {ι β : Type*} [LinearOrder β] (f : ι → β) : ∀ (l : List ι) (b : β),
    b ≤ l.foldr (fun k m => max (f k) m) b ∧ ∀ k ∈ l, f k ≤ l.foldr (fun k m => max (f k) m) b
  | [], b => ⟨le_rfl, by simp⟩
  | k :: l, b => by
    obtain ⟨h₁, h₂⟩ := le_foldr_max f l b
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨h₁.trans (le_max_right _ _), le_max_left _ _,
      fun k' hk' => (h₂ k' hk').trans (le_max_right _ _)⟩

theorem foldr_max_le {ι β : Type*} [LinearOrder β] (f : ι → β) {M : β} :
    ∀ (l : List ι) (b : β), b ≤ M → (∀ k ∈ l, f k ≤ M) → l.foldr (fun k m => max (f k) m) b ≤ M
  | [], _, hb, _ => hb
  | k :: l, b, hb, h => by
    simp only [List.foldr_cons]
    exact max_le (h k List.mem_cons_self)
      (foldr_max_le f l b hb fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))

omit [FloorRing 𝕂] in
theorem le_qEndTime {N : Network n} : ∀ {x : Loc n} {τ : 𝕂} {l : List (QLeg 𝕂 n t)},
    QIsRoute x τ l → (∀ ℓ ∈ l, QFlies N ℓ) → τ ≤ qEndTime τ l
  | _, _, [], _, _ => le_rfl
  | _, τ, ℓ :: rest, ⟨_, hdep, hrest⟩, hf => by
    obtain ⟨d, -, harr⟩ := hf ℓ List.mem_cons_self
    have : ℓ.dep ≤ ℓ.arr := by rw [harr]; exact le_add_of_nonneg_right (Nat.cast_nonneg d)
    exact hdep.trans (this.trans (le_qEndTime hrest fun m hm => hf m (List.mem_cons_of_mem _ hm)))

/-- **Rounding down does not increase the makespan.** -/
theorem planMakespan_floor_le {N : Network n} {P : QPlan 𝕂 n t p} (hP : QFeasible N P) :
    (planMakespan (floorPlan P) : 𝕂) ≤ qPlanMakespan P := by
  have hk : ∀ k, (endTime 0 (floorPlan P k) : 𝕂) ≤ qPlanMakespan P := by
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

/-! ### Integer plans are plans with times in `𝕂` -/

theorem IsRoute.toRat : ∀ {x : Loc n} {τ : ℕ} {l : List (Leg n t)},
    IsRoute x τ l → QIsRoute x (τ : 𝕂) (l.map (QLeg.ofLeg 𝕂))
  | _, _, [], _ => trivial
  | _, _, ℓ :: rest, ⟨hsrc, hdep, hrest⟩ =>
    ⟨hsrc, by simp only [QLeg.ofLeg]; exact_mod_cast hdep, IsRoute.toRat hrest⟩

omit [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] [FloorRing 𝕂] in
theorem qEndTime_ofLeg : ∀ (τ : ℕ) (l : List (Leg n t)),
    qEndTime (τ : 𝕂) (l.map (QLeg.ofLeg 𝕂)) = (endTime τ l : 𝕂)
  | _, [] => rfl
  | _, ℓ :: rest => qEndTime_ofLeg ℓ.arr rest

omit [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] [FloorRing 𝕂] in
theorem ofPlan_qAllLegs (P : Plan n t p) :
    qAllLegs (ofPlan 𝕂 P) = (allLegs P).map (QLeg.ofLeg 𝕂) := by
  simp only [qAllLegs, allLegs, List.map_flatMap]
  rfl

omit [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] [FloorRing 𝕂] in
theorem ofPlan_qPaxLegs (P : Plan n t p) (π : Fin t) :
    qPaxLegs (ofPlan 𝕂 P) π = (paxLegs P π).map (QLeg.ofLeg 𝕂) := by
  simp only [qPaxLegs, paxLegs, ofPlan_qAllLegs, List.filter_map]
  rfl

omit [IsStrictOrderedRing 𝕂] in
theorem map_floor_ofLeg (l : List (Leg n t)) : (l.map (QLeg.ofLeg 𝕂)).map QLeg.floor = l := by
  simp [List.map_map, Function.comp_def]

variable (𝕂) in
/-- **An integer plan is a plan with times in `𝕂`**, with the same cost and makespan. -/
theorem Feasible.toRat {N : Network n} (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) :
    QFeasible N (ofPlan 𝕂 P) ∧ qPlanCost c (ofPlan 𝕂 P) = planCost c P ∧
      qPlanMakespan (ofPlan 𝕂 P) = (planMakespan P : 𝕂) := by
  refine ⟨⟨fun k => ⟨fun ℓ hℓ => ?_, ?_, ?_⟩, fun π => ?_⟩, ?_, ?_⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hℓ
    obtain ⟨τ, hdur, harr⟩ := (hP.planes k).flies m hm
    exact ⟨τ, hdur, by simp [QLeg.ofLeg, harr]⟩
  · simpa [ofPlan] using IsRoute.toRat (hP.planes k).route
  · simpa [ofPlan, List.map_map, Function.comp_def] using (hP.planes k).ends
  · obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    refine ⟨route.map (QLeg.ofLeg 𝕂), ?_, by simpa [ofPlan] using IsRoute.toRat hroute, ?_⟩
    · rw [ofPlan_qPaxLegs]
      exact hperm.map _
    · rw [map_floor_ofLeg]
      exact hfin
  · simp [qPlanCost, planCost, ofPlan, List.map_map, Function.comp_def]
  · have hk : ∀ k, qEndTime 0 (ofPlan 𝕂 P k) = (endTime 0 (P k) : 𝕂) := fun k => by
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
        exact (le_foldr_max (fun k => qEndTime 0 (ofPlan 𝕂 P k)) (List.finRange p) 0).2 k
          (List.mem_finRange k)

/-! ### Soundness for plans with rational or real times -/

namespace Cert

variable (C : Cert)

variable (𝕂) in
/-- **Soundness for plans with times in `𝕂`** (rational or real). If `check` accepts, the listed
points are exactly the Pareto front of the (cost, makespan) pairs of the feasible plans with times
in `𝕂`, for every table of central flight durations satisfying the triangles through a hub, or
every table if all gaps are `relaxed`. -/
theorem check_sound_rat_hub (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).ATriHub ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievableQ 𝕂 (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : 𝕂))) := by
  have H := C.check_sound_hub h dc hdc
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    obtain ⟨P, hP, hPx⟩ := H.achieved x' hx'
    obtain ⟨hQ, hcost, hmk⟩ := hP.toRat 𝕂 C.c
    refine ⟨ofPlan 𝕂 P, hQ, ?_⟩
    rw [hcost, hmk, ← hPx]
  · obtain ⟨P, hP, rfl⟩ := hy
    obtain ⟨x, hx, hle⟩ := H.dominates _ ⟨floorPlan P, hP.floor, rfl⟩
    refine ⟨(x.1, (x.2 : 𝕂)), List.mem_map.mpr ⟨x, hx, rfl⟩, Prod.le_def.mpr ⟨?_, ?_⟩⟩
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

variable (𝕂) in
/-- **Soundness for plans with times in `𝕂`, under (A1)**, or for every table if all gaps are
`relaxed`. -/
theorem check_sound_rat (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hdc : (C.network dc).A1 ∨ ∀ g ∈ C.gaps, g = .relaxed) :
    IsParetoFront (achievableQ 𝕂 (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : 𝕂))) :=
  C.check_sound_rat_hub 𝕂 h dc (hdc.imp_left Network.A1.hub)

variable (𝕂) in
/-- **Soundness for plans with times in `𝕂`, under (AΔ).** -/
theorem check_sound_rat_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievableQ 𝕂 (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : 𝕂))) :=
  C.check_sound_rat_hub 𝕂 h dc (Or.inl hA.hub)

end Cert

end ZenoFront
