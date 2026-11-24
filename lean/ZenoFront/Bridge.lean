/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.AddPlane
public import ZenoFront.Checker

/-!
# Planes ending anywhere (Theorem 4.9, bridge B3)

The format's semantics (`Feasible`) makes every plane end in `C_G`. The PDDL semantics without
plane goals lets planes end anywhere, and the makespan is the last arrival (`FeasibleAnywhere`;
`planMakespan` already is the latest arrival of a plane, `0` for a plane that never flies).
Passengers must still reach `C_G`.

**Theorem 4.9.** Under (S) and (A1), every plan of the variant with cost `C` and makespan `M′`
is weakly dominated by an admissible partition: some admissible `X_1, …, X_p` has
`Σ_k |X_k| = 2t − p`, `2 δ(X_k) ≤ M′` for every plane and `c(X) ≤ C`
(`FeasibleAnywhere.exists_admissible`). Conversely every feasible plan is a plan of the variant
(`Feasible.anywhere`).

The proof follows Steps 1–4 of the note (§4.5) on the routes:

* **Steps 1 and 2.** Central flights are treated as through `C_G`, as in Theorem 4.7, and every
  passenger `π` gets a transfer: its last departure `C_I → x` and the next leg, which leaves `x`
  not towards `C_I` and departs no earlier than the first one arrives (`exists_transfer_le`).
* **Cutting** (`cutRoute`). Every route is cut after its last leg that is a transfer leg. If that
  leg is `C_I → x`, the leg `x → C_G` leaving on arrival is appended. It arrives no later than
  the passenger's second leg, so no later than `M′`. If it is a central flight `x → y`, it is
  redirected to `x → C_G` (shorter under (S) and (A1)). Every cut route is empty (an idle plane)
  or ends in `C_G`, lands no more, and every transfer survives.
* **Step 3.** On the `q` planes that are not idle, Theorem 4.7 from transfers
  (`exists_admissible_of_transfers`) gives an admissible partition of `2t − q` landings.
* **Step 4.** Lemma 4.6 (AP), once per idle plane, brings it to `p` planes and `2t − p`
  landings (`Admissible.addPlanes_le`).

## Fronts

The note's last step (Corollary 4.8) uses Theorem 4.1, which builds a feasible plan from every
admissible partition. Theorem 4.1 is not formalised. So:

* `Cert.check_sound_anywhere`: if `check` accepts a certificate (format v1), its points are the
  Pareto front of the variant too, for every table `dc` satisfying (A1). With
  `Cert.check_sound_A1`, the two fronts are equal on every certified instance
  (`Cert.minimal_achievable_iff_anywhere`).
* `minimal_achievable_iff_anywhere`: for every instance, the two fronts are equal under (S),
  (A1) and Theorem 4.1, taken as the hypothesis `AdmissibleAchievable`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### The variant -/

/-- A plane of the variant: its legs are flights and form a route from `C_I` at time `0`. It may
end anywhere. -/
structure PlaneFeasibleAnywhere (N : Network n) (legs : List (Leg n t)) : Prop where
  flies : ∀ ℓ ∈ legs, Flies N ℓ
  route : IsRoute .ci 0 legs

/-- A plan of the variant (PDDL without plane goals): every plane flies a route from `C_I` at
time `0` and may end anywhere, and the legs carrying each passenger form, in some order, a route
from `C_I` at time `0` that ends in `C_G`. Its makespan is `planMakespan`, the last arrival. -/
structure FeasibleAnywhere (N : Network n) (P : Plan n t p) : Prop where
  planes : ∀ k, PlaneFeasibleAnywhere N (P k)
  pax : ∀ π, ∃ route : List (Leg n t), route.Perm (paxLegs P π) ∧ IsRoute .ci 0 route ∧
    finalLoc .ci route = .cg

/-- A feasible plan is a plan of the variant, with the same cost and makespan (the same plan). -/
theorem Feasible.anywhere {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    FeasibleAnywhere N P :=
  ⟨fun k => ⟨(hP.planes k).flies, (hP.planes k).route⟩, hP.pax⟩

/-- The (cost, makespan) pairs of the plans of the variant. -/
def achievableAnywhere (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ P : Plan n t p, FeasibleAnywhere N P ∧ (planCost c P, planMakespan P) = x}

theorem achievable_subset_achievableAnywhere (N : Network n) (c : Fin n → ℕ) (t p : ℕ) :
    achievable N c t p ⊆ achievableAnywhere N c t p := by
  rintro x ⟨P, hP, rfl⟩
  exact ⟨P, hP.anywhere, rfl⟩

theorem FeasibleAnywhere.flies_of_mem_allLegs {N : Network n} {P : Plan n t p}
    (hP : FeasibleAnywhere N P) {ℓ : Leg n t} (h : ℓ ∈ allLegs P) : Flies N ℓ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact (hP.planes k).flies ℓ hk

/-! ### Routes and times -/

theorem le_endTime : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs →
    (∀ ℓ ∈ legs, ℓ.dep ≤ ℓ.arr) → τ ≤ endTime τ legs := by
  intro legs x τ h hdep
  have := add_durSum_le_endTime legs x τ h hdep
  omega

/-- A leg of a route arrives no later than the route ends. -/
theorem arr_le_endTime : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs →
    (∀ ℓ ∈ legs, ℓ.dep ≤ ℓ.arr) → ∀ ℓ ∈ legs, ℓ.arr ≤ endTime τ legs
  | [], _, _, _, _, ℓ, h => absurd h List.not_mem_nil
  | m :: rest, x, τ, hr, hdep, ℓ, h => by
    have hdep' : ∀ ℓ ∈ rest, ℓ.dep ≤ ℓ.arr := fun ℓ hℓ => hdep ℓ (List.mem_cons_of_mem _ hℓ)
    rw [endTime_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_endTime rest _ _ hr.2.2 hdep'
    · exact arr_le_endTime rest _ _ hr.2.2 hdep' ℓ h

/-- A leg leaving city `x`, not towards `C_I`, lasts at least `d̄_x` when central flights are no
shorter than `d̄` (under (S) and (A1)). -/
theorem Flies.dep_add_dbar_le {N : Network n} (hdc : ∀ i j, N.dbar i ≤ N.dc i j) {ℓ : Leg n t}
    (h : Flies N ℓ) {x : Fin n} (hs : ℓ.src = .city x) (hd : ℓ.dst ≠ .ci) :
    ℓ.dep + N.dbar x ≤ ℓ.arr := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, harr⟩ := h
  simp only at hs hd hdur harr ⊢
  subst hs
  cases dst with
  | ci => exact absurd rfl hd
  | cg =>
    simp only [Network.duration, Option.some.injEq] at hdur
    omega
  | city y =>
    simp only [Network.duration, Option.some.injEq] at hdur
    have := hdc x y
    omega

/-- **Step 2 with times.** A route from `C_I` to `C_G` has a leg `C_I → x` followed, later, by a
leg leaving `x` that does not arrive at `C_I` and departs no earlier than the first one arrives:
the last departure from `C_I` and the next leg. -/
theorem exists_transfer_le {N : Network n} : ∀ (l : List (Leg n t)) (τ : ℕ), IsRoute .ci τ l →
    (∀ ℓ ∈ l, Flies N ℓ) → finalLoc .ci l = .cg →
    ∃ x : Fin n, ∃ ℓo ∈ l, ∃ ℓn ∈ l, ℓo.src = .ci ∧ ℓo.dst = .city x ∧ ℓn.src = .city x ∧
      ℓn.dst ≠ .ci ∧ ℓo.arr ≤ ℓn.dep
  | [], _, _, _, h => by simp at h
  | [ℓ], _, hr, hf, h => by
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).dst_city_of_src_isHub (by simp [hr.1])
    simp [hx] at h
  | ℓ :: ℓ' :: rest, τ, hr, hf, h => by
    obtain ⟨hsrc, -, hrest⟩ := hr
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).dst_city_of_src_isHub (by simp [hsrc])
    have hsrc' : ℓ'.src = .city x := by rw [hrest.1, hx]
    by_cases hd : ℓ'.dst = .ci
    · obtain ⟨-, -, hrest'⟩ := hrest
      rw [hd] at hrest'
      have hfin : finalLoc .ci rest = .cg := by
        simpa [finalLoc_cons, hd] using h
      obtain ⟨y, ℓo, hℓo, ℓn, hℓn, h₁, h₂, h₃, h₄, h₅⟩ := exists_transfer_le rest ℓ'.arr hrest'
        (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) hfin
      exact ⟨y, ℓo, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓo), ℓn,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓn), h₁, h₂, h₃, h₄, h₅⟩
    · exact ⟨x, ℓ, List.mem_cons_self, ℓ', List.mem_cons_of_mem _ List.mem_cons_self, hsrc, hx,
        hsrc', hd, hrest.2.1⟩

/-- **Step 2 for a plan of the variant.** Every passenger has a transfer, with times. -/
theorem FeasibleAnywhere.exists_transfers {N : Network n} {P : Plan n t p}
    (hP : FeasibleAnywhere N P) :
    ∀ π : Fin t, ∃ x : Fin n, ∃ ℓo ∈ paxLegs P π, ∃ ℓn ∈ paxLegs P π,
      ℓo.src = .ci ∧ ℓo.dst = .city x ∧ ℓn.src = .city x ∧ ℓn.dst ≠ .ci ∧ ℓo.arr ≤ ℓn.dep := by
  intro π
  obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
  obtain ⟨x, ℓo, hℓo, ℓn, hℓn, h⟩ := exists_transfer_le route 0 hroute
    (fun ℓ hℓ => hP.flies_of_mem_allLegs
      (mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)).1) hfin
  exact ⟨x, ℓo, hperm.mem_iff.mp hℓo, ℓn, hperm.mem_iff.mp hℓn, h⟩

/-! ### Cutting a route -/

/-- How a cut route ends at its last kept leg `ℓ`: after `C_I → x`, the flight `x → C_G` leaving
on arrival is appended; a central flight `x → y` is redirected to `x → C_G`; other legs are
kept. -/
def closeLeg (N : Network n) (ℓ : Leg n t) : List (Leg n t) :=
  match ℓ.src, ℓ.dst with
  | .ci, .city x => [ℓ, ⟨.city x, .cg, ℓ.arr, ℓ.arr + N.dbar x, ℓ.pax⟩]
  | .city x, .city _ => [⟨.city x, .cg, ℓ.dep, ℓ.dep + N.dbar x, ℓ.pax⟩]
  | _, _ => [ℓ]

/-- The route cut after its last leg satisfying `U`, closed by `closeLeg`; empty if no leg
satisfies `U`. -/
def cutRoute (N : Network n) (U : Leg n t → Bool) : List (Leg n t) → List (Leg n t)
  | [] => []
  | ℓ :: rest =>
    match cutRoute N U rest with
    | [] => if U ℓ then closeLeg N ℓ else []
    | m :: r => ℓ :: m :: r

section closeLeg

variable {N : Network n}

theorem isRoute_closeLeg {ℓ : Leg n t} {x : Loc n} {τ : ℕ} (hs : ℓ.src = x) (hτ : τ ≤ ℓ.dep) :
    IsRoute x τ (closeLeg N ℓ) := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  simp only at hs hτ
  subst hs
  cases src <;> cases dst <;> simp [closeLeg, hτ]

theorem flies_closeLeg {ℓ : Leg n t} (h : Flies N ℓ) : ∀ m ∈ closeLeg N ℓ, Flies N m := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases src <;> cases dst <;>
    simp only [closeLeg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] <;>
    first
    | exact h
    | exact ⟨h, ⟨_, rfl, rfl⟩⟩
    | exact ⟨_, rfl, rfl⟩

theorem finalLoc_closeLeg {ℓ : Leg n t} (h : Flies N ℓ) (hs : ℓ.src ≠ .cg) (hd : ℓ.dst ≠ .ci)
    (x : Loc n) : finalLoc x (closeLeg N ℓ) = .cg := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, -⟩ := h
  simp only at hs hd hdur
  cases src <;> cases dst <;> simp_all [closeLeg, Network.duration]

theorem landCostSum_closeLeg_le (c : Fin n → ℕ) (ℓ : Leg n t) :
    landCostSum c (closeLeg N ℓ) ≤ landCost c ℓ := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases src <;> cases dst <;> simp [closeLeg, landCostSum, landCost]

theorem endTime_closeLeg_le (hdc : ∀ i j, N.dbar i ≤ N.dc i j) {ℓ : Leg n t} (h : Flies N ℓ)
    {B : ℕ} (harr : ∀ y, ℓ.src = .ci → ℓ.dst = .city y → ℓ.arr + N.dbar y ≤ B)
    (hB : ℓ.arr ≤ B) (τ : ℕ) : endTime τ (closeLeg N ℓ) ≤ B := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases src with
  | ci => cases dst <;> simp_all [closeLeg]
  | cg => cases dst <;> simp_all [closeLeg]
  | city x =>
    cases dst with
    | city y =>
      have := h.dep_add_dbar_le hdc (x := x) rfl (by simp)
      simp only [closeLeg, endTime_cons, endTime_nil] at this hB ⊢
      omega
    | ci => simpa [closeLeg] using hB
    | cg => simpa [closeLeg] using hB

theorem mem_closeLeg_of_src_ci {ℓ : Leg n t} (hs : ℓ.src = .ci) : ℓ ∈ closeLeg N ℓ := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  simp only at hs
  subst hs
  cases dst <;> simp [closeLeg]

theorem exists_mem_closeLeg (ℓ : Leg n t) : ∃ m ∈ closeLeg N ℓ, m.src = ℓ.src ∧ m.pax = ℓ.pax ∧
    (ℓ.dst ≠ .ci → m.dst ≠ .ci) := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases src <;> cases dst <;> simp [closeLeg]

theorem closeLeg_ne_nil (ℓ : Leg n t) : closeLeg N ℓ ≠ [] := by
  obtain ⟨m, hm, -⟩ := exists_mem_closeLeg (N := N) ℓ
  exact List.ne_nil_of_mem hm

end closeLeg

section cutRoute

variable {N : Network n} {U : Leg n t → Bool}

theorem isRoute_cutRoute : ∀ (L : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ L →
    IsRoute x τ (cutRoute N U L)
  | [], _, _, _ => trivial
  | ℓ :: rest, x, τ, h => by
    have ih := isRoute_cutRoute rest ℓ.dst ℓ.arr h.2.2
    simp only [cutRoute]
    split
    · split_ifs
      · exact isRoute_closeLeg h.1 h.2.1
      · trivial
    · rename_i m r hmr
      rw [hmr] at ih
      exact ⟨h.1, h.2.1, ih⟩

theorem flies_cutRoute : ∀ (L : List (Leg n t)), (∀ ℓ ∈ L, Flies N ℓ) →
    ∀ m ∈ cutRoute N U L, Flies N m
  | [], _ => by simp [cutRoute]
  | ℓ :: rest, h => by
    have ih := flies_cutRoute rest
      fun m hm => h m (List.mem_cons_of_mem _ hm)
    simp only [cutRoute]
    split
    · split_ifs
      · exact flies_closeLeg (h ℓ List.mem_cons_self)
      · simp
    · rename_i m r hmr
      rw [hmr] at ih
      intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact h _ List.mem_cons_self
      · exact ih m' hm'

theorem finalLoc_cutRoute : ∀ (L : List (Leg n t)) (x : Loc n), (∀ ℓ ∈ L, Flies N ℓ) →
    (∀ ℓ ∈ L, U ℓ = true → ℓ.src ≠ .cg ∧ ℓ.dst ≠ .ci) → cutRoute N U L ≠ [] →
    finalLoc x (cutRoute N U L) = .cg
  | [], _, _, _, hne => absurd rfl hne
  | ℓ :: rest, x, hf, hU, hne => by
    have ih := finalLoc_cutRoute rest ℓ.dst
      (fun m hm => hf m (List.mem_cons_of_mem _ hm))
      (fun m hm => hU m (List.mem_cons_of_mem _ hm))
    simp only [cutRoute] at hne ⊢
    split at hne
    · split_ifs at hne ⊢ with hu
      · obtain ⟨hs, hd⟩ := hU ℓ List.mem_cons_self hu
        exact finalLoc_closeLeg (hf ℓ List.mem_cons_self) hs hd x
      · exact absurd rfl hne
    · rename_i m r hmr
      rw [hmr] at ih
      exact ih (List.cons_ne_nil _ _)

theorem landCostSum_cutRoute_le (c : Fin n → ℕ) : ∀ L : List (Leg n t),
    landCostSum c (cutRoute N U L) ≤ landCostSum c L
  | [] => le_rfl
  | ℓ :: rest => by
    have ih := landCostSum_cutRoute_le c rest
    simp only [cutRoute]
    split
    · split_ifs
      · refine (landCostSum_closeLeg_le c ℓ).trans ?_
        simp [landCostSum]
      · simp [landCostSum]
    · rename_i m r hmr
      rw [hmr] at ih
      simp only [landCostSum, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem endTime_cutRoute_le (hdc : ∀ i j, N.dbar i ≤ N.dc i j) {B : ℕ} :
    ∀ (L : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ L → (∀ ℓ ∈ L, Flies N ℓ) →
    (∀ ℓ ∈ L, U ℓ = true → ∀ y, ℓ.src = .ci → ℓ.dst = .city y → ℓ.arr + N.dbar y ≤ B) →
    endTime τ L ≤ B → endTime τ (cutRoute N U L) ≤ B
  | [], _, _, _, _, _, hB => hB
  | ℓ :: rest, x, τ, hr, hf, harr, hB => by
    have hf' : ∀ m ∈ rest, Flies N m := fun m hm => hf m (List.mem_cons_of_mem _ hm)
    have ih := endTime_cutRoute_le hdc rest ℓ.dst ℓ.arr hr.2.2 hf'
      (fun m hm => harr m (List.mem_cons_of_mem _ hm)) hB
    have hℓ : ℓ.arr ≤ endTime ℓ.arr rest :=
      le_endTime rest _ _ hr.2.2 fun m hm => (hf' m hm).dep_le_arr
    rw [endTime_cons] at hB
    simp only [cutRoute]
    split
    · split_ifs with hu
      · exact endTime_closeLeg_le hdc (hf ℓ List.mem_cons_self)
          (harr ℓ List.mem_cons_self hu) (hℓ.trans hB) τ
      · simp only [endTime_nil]
        have := (hf ℓ List.mem_cons_self).dep_le_arr
        have := hr.2.1
        omega
    · rename_i m r hmr
      rw [hmr] at ih
      simpa using ih

/-- Every leg satisfying `U` is kept, or replaced by its closing legs. -/
theorem mem_cutRoute : ∀ (L : List (Leg n t)), ∀ ℓ ∈ L, U ℓ = true →
    ℓ ∈ cutRoute N U L ∨ ∀ m ∈ closeLeg N ℓ, m ∈ cutRoute N U L
  | [], ℓ, h, _ => absurd h List.not_mem_nil
  | ℓ₀ :: rest, ℓ, h, hu => by
    simp only [cutRoute]
    split
    · rename_i hnil
      rcases List.mem_cons.mp h with rfl | h
      · simp only [hu, ↓reduceIte]
        exact Or.inr fun m hm => hm
      · exfalso
        rcases mem_cutRoute rest ℓ h hu with h' | h'
        · rw [hnil] at h'
          exact List.not_mem_nil h'
        · obtain ⟨m, hm, -⟩ := exists_mem_closeLeg (N := N) ℓ
          have := h' m hm
          rw [hnil] at this
          exact List.not_mem_nil this
    · rename_i m r hmr
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_cutRoute rest ℓ h hu with h' | h'
        · rw [hmr] at h'
          exact Or.inl (List.mem_cons_of_mem _ h')
        · rw [hmr] at h'
          exact Or.inr fun m' hm' => List.mem_cons_of_mem _ (h' m' hm')

end cutRoute

/-! ### Step 4: adding the idle planes -/

/-- **Lemma 4.6 (AP)** from `q` to `p` planes, `q ≤ p ≤ t`. -/
theorem Admissible.addPlanes_le {q : ℕ} (d c : Fin n → ℕ) {X : Groups n q} (hX : Admissible X)
    (hqp : q ≤ p) (hpt : p ≤ t) (hsize : size X = 2 * t - q) :
    ∃ Y : Groups n p, Admissible Y ∧ size Y = 2 * t - p ∧ totalCost c Y ≤ totalCost c X ∧
      ∀ T, (∀ k, load d (X k) ≤ T) → ∀ k, load d (Y k) ≤ T := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  exact hX.addPlanes d c m hsize hpt

/-! ### Theorem 4.9 -/

/-- **Theorem 4.9 (bridge B3), converse direction.** Under (S) and (A1), with `p ≤ t`, every
plan whose planes may end anywhere is weakly dominated by an admissible partition: some
admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`, `2 δ(X_k) ≤` the makespan (the last arrival)
for every plane, and total cost at most the plan's cost. -/
theorem FeasibleAnywhere.exists_admissible {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P := by
  classical
  have hdc : ∀ i j, N.dbar i ≤ N.dc i j := fun i j => by
    have := hA1 i j
    rw [hS]
    omega
  have hmemP : ∀ ℓ ∈ allLegs P, ∃ k, ℓ ∈ P k := fun ℓ h => by
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
    exact ⟨k, hk⟩
  -- Step 2: every passenger's transfer.
  choose xπ ℓo hℓo ℓn hℓn hsrc_o hdst_o hsrc_n hdst_n htime using hP.exists_transfers
  have hmo := fun π => mem_allLegs_of_mem_paxLegs (hℓo π)
  have hmn := fun π => mem_allLegs_of_mem_paxLegs (hℓn π)
  -- Cutting every route after its last transfer leg.
  set U : Leg n t → Bool := fun ℓ => decide (∃ π, ℓ = ℓo π ∨ ℓ = ℓn π) with hU
  set P' : Plan n t p := fun k => cutRoute N U (P k) with hP'
  have hUend : ∀ ℓ, U ℓ = true → ℓ.src ≠ .cg ∧ ℓ.dst ≠ .ci := by
    intro ℓ h
    obtain ⟨π, rfl | rfl⟩ := of_decide_eq_true h
    · simp [hsrc_o π, hdst_o π]
    · simp [hsrc_n π, hdst_n π]
  have hUarr : ∀ ℓ, U ℓ = true → ∀ y, ℓ.src = .ci → ℓ.dst = .city y →
      ℓ.arr + N.dbar y ≤ planMakespan P := by
    intro ℓ h y hs hd
    obtain ⟨π, rfl | rfl⟩ := of_decide_eq_true h
    · rw [hdst_o π, Loc.city.injEq] at hd
      subst hd
      obtain ⟨k, hk⟩ := hmemP _ (hmn π).1
      have h₁ := ((hP.planes k).flies _ hk).dep_add_dbar_le hdc (hsrc_n π) (hdst_n π)
      have h₂ := arr_le_endTime (P k) .ci 0 (hP.planes k).route
        (fun m hm => ((hP.planes k).flies m hm).dep_le_arr) _ hk
      have h₃ := endTime_le_planMakespan P k
      have h₄ := htime π
      omega
    · rw [hsrc_n π] at hs
      cases hs
  have hroute' : ∀ k, IsRoute .ci 0 (P' k) := fun k =>
    isRoute_cutRoute (P k) .ci 0 (hP.planes k).route
  have hflies' : ∀ k, ∀ m ∈ P' k, Flies N m := fun k =>
    flies_cutRoute (P k) (hP.planes k).flies
  have hends' : ∀ k, P' k ≠ [] → finalLoc .ci (P' k) = .cg := fun k =>
    finalLoc_cutRoute (P k) .ci (hP.planes k).flies fun ℓ _ => hUend ℓ
  have hend' : ∀ k, endTime 0 (P' k) ≤ planMakespan P := fun k =>
    endTime_cutRoute_le hdc (P k) .ci 0 (hP.planes k).route (hP.planes k).flies
      (fun ℓ _ => hUarr ℓ) (endTime_le_planMakespan P k)
  -- The transfers survive the cut.
  have hmo' : ∀ π, ∃ k, ℓo π ∈ P' k := by
    intro π
    obtain ⟨k, hk⟩ := hmemP _ (hmo π).1
    refine ⟨k, ?_⟩
    have hu : U (ℓo π) = true := by
      simp only [hU, decide_eq_true_eq]
      exact ⟨π, Or.inl rfl⟩
    rcases mem_cutRoute (N := N) (P k) (ℓo π) hk hu with h | h
    · exact h
    · exact h _ (mem_closeLeg_of_src_ci (hsrc_o π))
  have hmn' : ∀ π, ∃ k, ∃ m ∈ P' k, m.src = .city (xπ π) ∧ m.pax = some π ∧ m.dst ≠ .ci := by
    intro π
    obtain ⟨k, hk⟩ := hmemP _ (hmn π).1
    refine ⟨k, ?_⟩
    have hu : U (ℓn π) = true := by
      simp only [hU, decide_eq_true_eq]
      exact ⟨π, Or.inr rfl⟩
    rcases mem_cutRoute (N := N) (P k) (ℓn π) hk hu with h | h
    · exact ⟨ℓn π, h, hsrc_n π, (hmn π).2, hdst_n π⟩
    · obtain ⟨m, hm, hms, hmp, hmd⟩ := exists_mem_closeLeg (N := N) (ℓn π)
      exact ⟨m, h m hm, hms.trans (hsrc_n π), hmp.trans (hmn π).2, hmd (hdst_n π)⟩
  -- Step 3: the planes that are not idle.
  set Q : Finset (Fin p) := univ.filter fun k => P' k ≠ [] with hQ
  set e : Fin Q.card ≃ Q := Q.equivFin.symm with he
  set P'' : Plan n t Q.card := fun i => P' (e i) with hP''
  have hplanes : ∀ i, PlaneFeasible N (P'' i) := fun i =>
    ⟨hflies' _, hroute' _, hends' _ (mem_filter.mp (e i).2).2⟩
  have hmem'' : ∀ k, ∀ m ∈ P' k, m ∈ allLegs P'' := by
    intro k m hm
    have hkQ : k ∈ Q := mem_filter.mpr ⟨mem_univ _, List.ne_nil_of_mem hm⟩
    refine List.mem_flatMap.mpr ⟨e.symm ⟨k, hkQ⟩, List.mem_finRange _, ?_⟩
    simpa [hP''] using hm
  have htr : ∀ π : Fin t, ∃ x : Fin n, ∃ ℓ₁ ∈ paxLegs P'' π, ∃ ℓ₂ ∈ paxLegs P'' π,
      ℓ₁.src = .ci ∧ ℓ₁.dst = .city x ∧ ℓ₂.src = .city x ∧ ℓ₂.dst ≠ .ci := by
    intro π
    obtain ⟨k, hk⟩ := hmo' π
    obtain ⟨k', m, hm, hms, hmp, hmd⟩ := hmn' π
    refine ⟨xπ π, ℓo π, ?_, m, ?_, hsrc_o π, hdst_o π, hms, hmd⟩
    · simp [paxLegs, List.mem_filter, hmem'' k _ hk, (hmo π).2]
    · simp [paxLegs, List.mem_filter, hmem'' k' _ hm, hmp]
  have hqp : Q.card ≤ p := by simpa using Q.card_le_univ
  obtain ⟨X, hX, hXsize, hXload, hXcost⟩ :=
    exists_admissible_of_transfers hS hA1 c hplanes htr (hqp.trans hpt)
  have hmk : planMakespan P'' ≤ planMakespan P := Finset.sup_le fun i _ => hend' _
  have hcost : planCost c P'' ≤ planCost c P := by
    calc planCost c P'' = ∑ k : Q, landCostSum c (P' k) :=
          e.sum_comp fun k : Q => landCostSum c (P' k)
      _ = ∑ k ∈ Q, landCostSum c (P' k) := Finset.sum_coe_sort Q fun k => landCostSum c (P' k)
      _ ≤ ∑ k ∈ Q, landCostSum c (P k) :=
          Finset.sum_le_sum fun k _ => landCostSum_cutRoute_le c (P k)
      _ ≤ ∑ k, landCostSum c (P k) := Finset.sum_le_sum_of_subset (subset_univ Q)
      _ = planCost c P := rfl
  -- Step 4: one more plane per idle plane (AP).
  obtain ⟨Y, hY, hYsize, hYcost, hYload⟩ := hX.addPlanes_le N.d c hqp hpt hXsize
  refine ⟨Y, hY, hYsize, fun k => ?_, hYcost.trans (hXcost.trans hcost)⟩
  have := hYload (planMakespan P / 2) (fun i => by have := hXload i; omega) k
  omega

/-! ### Fronts -/

/-- If `A ⊆ A′` and every point of `A′` is weakly dominated by a point of `A`, the two sets have
the same minimal elements. -/
theorem minimal_iff_of_subset_of_dominated {α : Type*} [PartialOrder α] {A A' : Set α}
    (hsub : A ⊆ A') (hdom : ∀ y ∈ A', ∃ x ∈ A, x ≤ y) (x : α) :
    Minimal (· ∈ A) x ↔ Minimal (· ∈ A') x := by
  constructor
  · intro ⟨hx, hmin⟩
    refine ⟨hsub hx, fun y hy hyx => ?_⟩
    obtain ⟨z, hz, hzy⟩ := hdom y hy
    exact (hmin hz (hzy.trans hyx)).trans hzy
  · intro ⟨hx, hmin⟩
    obtain ⟨z, hz, hzx⟩ := hdom x hx
    have hzx' : z = x := le_antisymm hzx (hmin (hsub hz) hzx)
    subst hzx'
    exact ⟨hz, fun y hy hyz => hmin (hsub hy) hyz⟩

/-- **Theorem 4.1 (achievability), as a hypothesis on an instance.** Every admissible partition
of `2t − p` landings is achieved, up to weak domination, by a feasible plan of cost at most
`c(X)` and makespan at most `2 max_k δ(X_k)`. The note proves it under (S) (Theorem 4.1); it is
not formalised here. -/
def AdmissibleAchievable (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Prop :=
  ∀ X : Groups n p, Admissible X → size X = 2 * t - p →
    ∃ P : Plan n t p, Feasible N P ∧ planCost c P ≤ totalCost c X ∧
      planMakespan P ≤ 2 * maxLoad N.d X

/-- Under (S), (A1) and Theorem 4.1, every plan of the variant is weakly dominated by a feasible
plan. -/
theorem FeasibleAnywhere.exists_feasible_le {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    {c : Fin n → ℕ} (h41 : AdmissibleAchievable N c t p) {P : Plan n t p}
    (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ P' : Plan n t p, Feasible N P' ∧ planCost c P' ≤ planCost c P ∧
      planMakespan P' ≤ planMakespan P := by
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible hS hA1 c hpt
  obtain ⟨P', hP', hc, hm⟩ := h41 X hX hsize
  refine ⟨P', hP', hc.trans hcost, hm.trans ?_⟩
  have : maxLoad N.d X ≤ planMakespan P / 2 :=
    (maxLoad_le_iff _ _ _).mpr fun k => by have := hload k; omega
  omega

/-- **Theorem 4.9 (bridge B3), front form.** Under (S), (A1), `p ≤ t` and Theorem 4.1 (as the
hypothesis `AdmissibleAchievable`), the feasible plans and the plans whose planes end anywhere
have the same minimal (cost, makespan) pairs. -/
theorem minimal_achievable_iff_anywhere {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    {c : Fin n → ℕ} (h41 : AdmissibleAchievable N c t p) (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ achievableAnywhere N c t p) x := by
  refine minimal_iff_of_subset_of_dominated (achievable_subset_achievableAnywhere N c t p)
    (fun y hy => ?_) x
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨P', hP', hc, hm⟩ := hP.exists_feasible_le hS hA1 h41 hpt
  exact ⟨_, ⟨P', hP', rfl⟩, Prod.le_def.mpr ⟨hc, hm⟩⟩

/-! ### The checker, for planes ending anywhere -/

namespace Cert

variable (C : Cert)

/-- What `check` reads off the header: `1 ≤ p ≤ t` and symmetric durations. -/
theorem check_header (h : C.check = true) : 1 ≤ C.p ∧ C.p ≤ C.t ∧ C.dbar = C.d := by
  simp only [check, headerOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hp⟩, hpt⟩, hsym⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hp, hpt, funext fun i => (hsym i).symm⟩

/-- **Domination by a listed point, from an admissible partition.** If `check` accepts, every
admissible partition with `s` landings, loads `2 δ(X_k) ≤ M` and cost at most `K` is weakly
dominated by a listed point: some point has cost `≤ K` and makespan `≤ M`. This needs no
assumption on central flights. -/
theorem exists_le_of_admissible (h : C.check = true) {X : Groups C.n C.p} (hX : Admissible X)
    (hsize : size X = C.s) {y : ℕ × ℕ} (hload : ∀ k, 2 * load C.d (X k) ≤ y.2)
    (hcost : totalCost C.c X ≤ y.1) : ∃ x ∈ C.front, x ≤ y := by
  obtain ⟨hp, hpt, -⟩ := C.check_header h
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hfirst⟩, hlast⟩, hgaps⟩ := h
  rw [gapsCheck_eq] at hgaps
  refine exists_le_of_gapsOK (C.boundOf C.table) y C.front C.gaps
    (fun g _ M hM => ?_) hgaps (fun x hx => ?_) (fun x hx => ?_)
  · -- Obligation 3: the bound at the gap level.
    have hlev : ∀ k, load (scaledDurations C.d) (X k) ≤ C.gapLevel M := fun k => by
      apply load_scaled_le_of_load_le
      have := hload k
      rw [Nat.le_div_iff_mul_le Nat.two_pos]
      omega
    cases g with
    | relaxed =>
      exact (relaxedBoundAt_le_totalCost (scaledDurations C.d) C.c X
        (fun k => hX.card_pos k) hsize hlev).trans (WithTop.coe_le_coe.mpr hcost)
    | forest =>
      show C.forestGapBound C.table M ≤ _
      unfold forestGapBound
      split_ifs
      · exact (forestBoundAt_le_totalCost (scaledDurations C.d) C.c hp hpt hX hsize hlev).trans
          (WithTop.coe_le_coe.mpr hcost)
      · exact bot_le
  · -- Obligation 2: the first makespan.
    simp only [firstOK] at hfirst
    rw [Option.mem_def] at hx
    rw [hx] at hfirst
    simp only [decide_eq_true_eq] at hfirst
    rw [hfirst]
    obtain ⟨k, hk⟩ := exists_ceil_le_card X hp
    rw [hsize] at hk
    have h₁ := card_mul_minOf_le_sum C.d (X k)
    have h₂ := hload k
    calc 2 * minOf C.d * ((C.s + C.p - 1) / C.p)
        ≤ 2 * minOf C.d * (X k).card := Nat.mul_le_mul_left _ hk
      _ = 2 * ((X k).card * minOf C.d) := by rw [mul_assoc, mul_comm (minOf C.d)]
      _ ≤ 2 * load C.d (X k) := Nat.mul_le_mul_left _ h₁
      _ ≤ y.2 := h₂
  · -- Obligation 4: the last cost.
    simp only [lastOK] at hlast
    rw [Option.mem_def] at hx
    rw [hx] at hlast
    simp only [decide_eq_true_eq] at hlast
    rw [hlast]
    refine le_trans ?_ hcost
    rw [← hsize, size, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => card_mul_minOf_le_sum C.c (X k)

/-- **Soundness of the checker for planes ending anywhere.** If `check` accepts, the listed
points are exactly the Pareto front of the plans whose planes may end anywhere (makespan = last
arrival), for every table of central flight durations satisfying (A1). -/
theorem check_sound_anywhere (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA1 : (C.network dc).A1) :
    IsParetoFront (achievableAnywhere (C.network dc) C.c C.t C.p) C.front := by
  have hF := C.check_sound_A1 h dc hA1
  obtain ⟨-, hpt, hsym⟩ := C.check_header h
  have hS : (C.network dc).dbar = (C.network dc).d := hsym
  refine ⟨fun x hx => achievable_subset_achievableAnywhere _ _ _ _ (hF.achieved x hx),
    fun y hy => ?_, hF.antichain⟩
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible hS hA1 C.c hpt
  exact C.exists_le_of_admissible h hX hsize hload hcost

/-- **Bridge B3 on certified instances.** If `check` accepts, the feasible plans and the plans
whose planes end anywhere have the same minimal (cost, makespan) pairs, the listed points, for
every table of central flight durations satisfying (A1). -/
theorem minimal_achievable_iff_anywhere (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA1 : (C.network dc).A1) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x ↔
      Minimal (· ∈ achievableAnywhere (C.network dc) C.c C.t C.p) x := by
  rw [← (C.check_sound_A1 h dc hA1).mem_iff_minimal,
    ← (C.check_sound_anywhere h dc hA1).mem_iff_minimal]

end Cert

end ZenoFront
