/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.AddPlane
public import ZenoFront.Checker

/-!
# Planes ending anywhere (Theorem 4.5, bridge B3)

The format's semantics (`Feasible`) makes every plane end in `C_G`. The PDDL semantics without
plane goals lets planes end anywhere, and the makespan is the last arrival (`FeasibleAnywhere`;
`planMakespan` already is the latest arrival of a plane, `0` for a plane that never flies).
Passengers must still reach `C_G`.

**Theorem 4.5, converse direction.** Under (S) and the triangles through a hub
(`Network.ATriHub`), every plan of the variant with cost `C` and makespan `M′` is weakly dominated
by an admissible partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤ M′` for every plane and `c(X) ≤ C` (`FeasibleAnywhere.exists_admissible_hub`; under
(A1) `FeasibleAnywhere.exists_admissible`, under (AΔ) `FeasibleAnywhere.exists_admissible_ATri`).
Conversely every feasible plan is a plan of the variant (`Feasible.anywhere`).

The proof cuts every route after its last leg on a passenger's chain (`cutTri`). If that leg
lands in a central city `b` at time `a`, an empty flight `b → C_G` leaving at `a` is appended.
This is the second use of the triangles through a hub: the rest of the chain from `b` lasts at
least `d̄_b`, so the appended flight arrives by the makespan (`ToGoal.arr_add_d_le`). The planes
that are not idle then end in `C_G` with every chain intact, and Theorem 4.4 from chains
(`exists_admissible_of_chains`) applies to them. Lemma 4.2 (AP) adds the idle planes
(`Admissible.addPlanes_le`).

## Main results

* `ZenoFront.FeasibleAnywhere`, `ZenoFront.achievableAnywhere`: the variant and its points.
* `ZenoFront.FeasibleAnywhere.exists_admissible_hub`: **Theorem 4.5**, converse direction.
* `ZenoFront.Cert.check_sound_anywhere_hub`: if `check` accepts a certificate (format v1), its
  points are the Pareto front of the variant too, for every table `dc` satisfying the triangles
  through a hub; with `Cert.check_sound_hub`, the two fronts are equal on every certified
  instance (`Cert.minimal_achievable_iff_anywhere_hub`).

The front form on every instance, which needs Theorem 4.1, is in `Achievability.lean`
(`minimal_achievable_iff_anywhere_hub`).
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

/-! ### Chains: times -/

/-- **The second use of the triangles through a hub.** A chain from a central city `y` lasts at
least `d_y`: under (S) and the triangles through a hub, `d_y ≤ dc y y' + d_{y'}` along every
central leg. -/
theorem ToGoal.add_d_le_endTime {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub) :
    ∀ (l : List (Leg n t)) (y : Fin n) (τ : ℕ), ToGoal (.city y) τ l → (∀ ℓ ∈ l, Flies N ℓ) →
      τ + N.d y ≤ endTime τ l
  | [], _, _, h, _ => absurd h id
  | ℓ :: rest, y, τ, h, hf => by
    obtain ⟨hsrc, hdep, hcase⟩ := h
    obtain ⟨τ', hdur, harr⟩ := hf ℓ List.mem_cons_self
    rw [hsrc] at hdur
    rcases hcase with ⟨hd, rfl⟩ | ⟨⟨y', hy'⟩, h'⟩
    · rw [hd] at hdur
      simp only [Network.duration, hS, Option.some.injEq] at hdur
      simp only [endTime_cons, endTime_nil]
      omega
    · rw [hy'] at hdur h'
      simp only [Network.duration, Option.some.injEq] at hdur
      have ih := ToGoal.add_d_le_endTime hS hL rest y' ℓ.arr h'
        (fun m hm => hf m (List.mem_cons_of_mem _ hm))
      have := (hL y y').2
      simp only [endTime_cons]
      omega

/-- Every leg of a chain that lands in a central city `y` arrives at least `d_y` before the
chain ends. -/
theorem ToGoal.arr_add_d_le {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub) :
    ∀ (ch : List (Leg n t)) (x : Loc n) (τ : ℕ), ToGoal x τ ch → (∀ ℓ ∈ ch, Flies N ℓ) →
      ∀ ℓ ∈ ch, ∀ y : Fin n, ℓ.dst = .city y → ℓ.arr + N.d y ≤ endTime τ ch
  | [], _, _, h, _, _, _, _, _ => absurd h id
  | ℓ₀ :: rest, x, τ, h, hf, ℓ, hℓ, y, hy => by
    obtain ⟨-, -, hcase⟩ := h
    have hf' : ∀ m ∈ rest, Flies N m := fun m hm => hf m (List.mem_cons_of_mem _ hm)
    rcases hcase with ⟨hd, rfl⟩ | ⟨-, h'⟩
    · rw [List.mem_singleton] at hℓ
      subst hℓ
      rw [hd] at hy
      cases hy
    · rw [endTime_cons]
      by_cases hℓ₀ : ℓ = ℓ₀
      · subst hℓ₀
        rw [hy] at h'
        exact ToGoal.add_d_le_endTime hS hL rest y _ h' hf'
      · exact ToGoal.arr_add_d_le hS hL rest _ _ h' hf' ℓ
          ((List.mem_cons.mp hℓ).resolve_left hℓ₀) y hy

theorem ToGoal.dst_ne_ci : ∀ {x : Loc n} {τ : ℕ} {ch : List (Leg n t)}, ToGoal x τ ch →
    ∀ ℓ ∈ ch, ℓ.dst ≠ .ci
  | _, _, [], h, _, _ => absurd h id
  | _, _, ℓ₀ :: rest, h, ℓ, hℓ => by
    rcases h.2.2 with ⟨hd, rfl⟩ | ⟨⟨y, hy⟩, h'⟩
    · rw [List.mem_singleton] at hℓ
      subst hℓ
      rw [hd]
      simp
    · rcases List.mem_cons.mp hℓ with rfl | hℓ
      · rw [hy]
        simp
      · exact ToGoal.dst_ne_ci h' ℓ hℓ

theorem exists_mem_arr_endTime : ∀ (l : List (Leg n t)) (τ : ℕ), l ≠ [] →
    ∃ ℓ ∈ l, endTime τ l = ℓ.arr
  | [], _, h => absurd rfl h
  | [ℓ], _, _ => ⟨ℓ, List.mem_cons_self, rfl⟩
  | ℓ :: ℓ' :: rest, _, _ => by
    obtain ⟨m, hm, h⟩ := exists_mem_arr_endTime (ℓ' :: rest) ℓ.arr (List.cons_ne_nil _ _)
    exact ⟨m, List.mem_cons_of_mem _ hm, h⟩

/-! ### Cutting a route after its last chain leg -/

/-- How a cut route ends at its last kept leg `ℓ`: if `ℓ` lands in a central city `y`, the empty
flight `y → C_G` leaving on arrival is appended. -/
def closeTri (N : Network n) (ℓ : Leg n t) : List (Leg n t) :=
  match ℓ.dst with
  | .city y => [ℓ, ⟨.city y, .cg, ℓ.arr, ℓ.arr + N.dbar y, none⟩]
  | _ => [ℓ]

/-- The route cut after its last leg satisfying `U`, closed by `closeTri`; empty if no leg
satisfies `U`. -/
def cutTri (N : Network n) (U : Leg n t → Bool) : List (Leg n t) → List (Leg n t)
  | [] => []
  | ℓ :: rest =>
    match cutTri N U rest with
    | [] => if U ℓ then closeTri N ℓ else []
    | m :: r => ℓ :: m :: r

section cutTri

variable {N : Network n} {U : Leg n t → Bool}

theorem isRoute_closeTri {ℓ : Leg n t} {x : Loc n} {τ : ℕ} (hs : ℓ.src = x) (hτ : τ ≤ ℓ.dep) :
    IsRoute x τ (closeTri N ℓ) := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  simp only at hs hτ
  subst hs
  cases dst <;> simp [closeTri, hτ]

theorem flies_closeTri {ℓ : Leg n t} (h : Flies N ℓ) : ∀ m ∈ closeTri N ℓ, Flies N m := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases dst <;>
    simp only [closeTri, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] <;>
    first
    | exact h
    | exact ⟨h, ⟨_, rfl, rfl⟩⟩

theorem finalLoc_closeTri {ℓ : Leg n t} (hd : ℓ.dst ≠ .ci) (hd' : ℓ.dst.isHub = true → ℓ.dst = .cg)
    (x : Loc n) : finalLoc x (closeTri N ℓ) = .cg := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  simp only at hd hd' ⊢
  cases dst <;> simp_all [closeTri]

theorem landCostSum_closeTri (c : Fin n → ℕ) (ℓ : Leg n t) :
    landCostSum c (closeTri N ℓ) = landCost c ℓ := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases dst <;> simp [closeTri, landCostSum, landCost]

theorem endTime_closeTri_le {ℓ : Leg n t} {B : ℕ}
    (harr : ∀ y, ℓ.dst = .city y → ℓ.arr + N.dbar y ≤ B) (hB : ℓ.arr ≤ B) (τ : ℕ) :
    endTime τ (closeTri N ℓ) ≤ B := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases dst with
  | city y => simpa [closeTri] using harr y rfl
  | ci => simpa [closeTri] using hB
  | cg => simpa [closeTri] using hB

theorem mem_closeTri (ℓ : Leg n t) : ℓ ∈ closeTri N ℓ := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases dst <;> simp [closeTri]

theorem isRoute_cutTri : ∀ (L : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ L →
    IsRoute x τ (cutTri N U L)
  | [], _, _, _ => trivial
  | ℓ :: rest, x, τ, h => by
    have ih := isRoute_cutTri rest ℓ.dst ℓ.arr h.2.2
    simp only [cutTri]
    split
    · split_ifs
      · exact isRoute_closeTri h.1 h.2.1
      · trivial
    · rename_i m r hmr
      rw [hmr] at ih
      exact ⟨h.1, h.2.1, ih⟩

theorem flies_cutTri : ∀ (L : List (Leg n t)), (∀ ℓ ∈ L, Flies N ℓ) →
    ∀ m ∈ cutTri N U L, Flies N m
  | [], _ => by simp [cutTri]
  | ℓ :: rest, h => by
    have ih := flies_cutTri rest fun m hm => h m (List.mem_cons_of_mem _ hm)
    simp only [cutTri]
    split
    · split_ifs
      · exact flies_closeTri (h ℓ List.mem_cons_self)
      · simp
    · rename_i m r hmr
      rw [hmr] at ih
      intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact h _ List.mem_cons_self
      · exact ih m' hm'

theorem finalLoc_cutTri : ∀ (L : List (Leg n t)) (x : Loc n),
    (∀ ℓ ∈ L, U ℓ = true → ℓ.dst ≠ .ci ∧ (ℓ.dst.isHub = true → ℓ.dst = .cg)) →
    cutTri N U L ≠ [] → finalLoc x (cutTri N U L) = .cg
  | [], _, _, hne => absurd rfl hne
  | ℓ :: rest, x, hU, hne => by
    have ih := finalLoc_cutTri rest ℓ.dst fun m hm => hU m (List.mem_cons_of_mem _ hm)
    simp only [cutTri] at hne ⊢
    split at hne
    · split_ifs at hne ⊢ with hu
      · obtain ⟨hd, hd'⟩ := hU ℓ List.mem_cons_self hu
        exact finalLoc_closeTri hd hd' x
      · exact absurd rfl hne
    · rename_i m r hmr
      rw [hmr] at ih
      exact ih (List.cons_ne_nil _ _)

theorem landCostSum_cutTri_le (c : Fin n → ℕ) : ∀ L : List (Leg n t),
    landCostSum c (cutTri N U L) ≤ landCostSum c L
  | [] => le_rfl
  | ℓ :: rest => by
    have ih := landCostSum_cutTri_le c rest
    simp only [cutTri]
    split
    · split_ifs
      · rw [landCostSum_closeTri]
        simp [landCostSum]
      · simp [landCostSum]
    · rename_i m r hmr
      rw [hmr] at ih
      simp only [landCostSum, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem endTime_cutTri_le {B : ℕ} :
    ∀ (L : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ L → (∀ ℓ ∈ L, Flies N ℓ) →
    (∀ ℓ ∈ L, U ℓ = true → ∀ y, ℓ.dst = .city y → ℓ.arr + N.dbar y ≤ B) →
    endTime τ L ≤ B → endTime τ (cutTri N U L) ≤ B
  | [], _, _, _, _, _, hB => hB
  | ℓ :: rest, x, τ, hr, hf, harr, hB => by
    have hf' : ∀ m ∈ rest, Flies N m := fun m hm => hf m (List.mem_cons_of_mem _ hm)
    have ih := endTime_cutTri_le rest ℓ.dst ℓ.arr hr.2.2 hf'
      (fun m hm => harr m (List.mem_cons_of_mem _ hm)) hB
    have hℓ : ℓ.arr ≤ endTime ℓ.arr rest :=
      le_endTime rest _ _ hr.2.2 fun m hm => (hf' m hm).dep_le_arr
    rw [endTime_cons] at hB
    simp only [cutTri]
    split
    · split_ifs with hu
      · exact endTime_closeTri_le (harr ℓ List.mem_cons_self hu) (hℓ.trans hB) τ
      · simp only [endTime_nil]
        have := (hf ℓ List.mem_cons_self).dep_le_arr
        have := hr.2.1
        omega
    · rename_i m r hmr
      rw [hmr] at ih
      simpa using ih

/-- Every leg satisfying `U` is kept. -/
theorem mem_cutTri : ∀ (L : List (Leg n t)), ∀ ℓ ∈ L, U ℓ = true → ℓ ∈ cutTri N U L
  | [], ℓ, h, _ => absurd h List.not_mem_nil
  | ℓ₀ :: rest, ℓ, h, hu => by
    simp only [cutTri]
    split
    · rename_i hnil
      rcases List.mem_cons.mp h with rfl | h
      · simp only [hu, ↓reduceIte]
        exact mem_closeTri ℓ
      · have := mem_cutTri rest ℓ h hu
        rw [hnil] at this
        exact absurd this List.not_mem_nil
    · rename_i m r hmr
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · have := mem_cutTri rest ℓ h hu
        rw [hmr] at this
        exact List.mem_cons_of_mem _ this

end cutTri

/-! ### Adding the idle planes -/

/-- **Lemma 4.2 (AP)** from `q` to `p` planes, `q ≤ p ≤ t`. -/
theorem Admissible.addPlanes_le {q : ℕ} (d c : Fin n → ℕ) {X : Groups n q} (hX : Admissible X)
    (hqp : q ≤ p) (hpt : p ≤ t) (hsize : size X = 2 * t - q) :
    ∃ Y : Groups n p, Admissible Y ∧ size Y = 2 * t - p ∧ totalCost c Y ≤ totalCost c X ∧
      ∀ T, (∀ k, load d (X k) ≤ T) → ∀ k, load d (Y k) ≤ T := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  exact hX.addPlanes d c m hsize hpt

/-! ### Theorem 4.5 -/

/-- **The passengers' chains**, for planes ending anywhere. -/
theorem FeasibleAnywhere.exists_chains {N : Network n} {P : Plan n t p}
    (hP : FeasibleAnywhere N P) :
    ∀ π : Fin t, ∃ ch : List (Leg n t), (∃ τ, ToGoal .ci τ ch) ∧
      ∀ ℓ ∈ ch, ℓ ∈ allLegs P ∧ ℓ.pax = some π := by
  intro π
  obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
  have hmem : ∀ ℓ ∈ route, ℓ ∈ allLegs P ∧ ℓ.pax = some π := fun ℓ hℓ =>
    mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)
  have hci : ∃ ℓ ∈ route, ℓ.src = .ci := by
    cases route with
    | nil => simp at hfin
    | cons ℓ r => exact ⟨ℓ, List.mem_cons_self, hroute.1⟩
  obtain ⟨c, hc, hg⟩ := exists_chain route .ci 0 hroute
    (fun ℓ hℓ => hP.flies_of_mem_allLegs (hmem ℓ hℓ).1) hfin hci
  exact ⟨c, hg, fun ℓ hℓ => hmem ℓ (hc ℓ hℓ)⟩

open Classical in
/-- **Theorem 4.5 (bridge B3), converse direction.** Under (S) and the triangles through a hub,
with `p ≤ t`, every plan whose planes may end anywhere is weakly dominated by an admissible
partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`, `2 δ(X_k) ≤` the makespan
(the last arrival) for every plane, and total cost at most the plan's cost. -/
theorem FeasibleAnywhere.exists_admissible_hub {N : Network n} (hS : N.dbar = N.d)
    (hL : N.ATriHub) (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P)
    (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P := by
  have hmemP : ∀ ℓ ∈ allLegs P, ∃ k, ℓ ∈ P k := fun ℓ h => by
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
    exact ⟨k, hk⟩
  choose ch hτ hchm using hP.exists_chains
  -- Cut every route after its last chain leg.
  set U : Leg n t → Bool := fun ℓ => decide (∃ π, ℓ ∈ ch π) with hU
  set P' : Plan n t p := fun k => cutTri N U (P k) with hP'
  have hUend : ∀ ℓ, U ℓ = true → ℓ.dst ≠ .ci ∧ (ℓ.dst.isHub = true → ℓ.dst = .cg) := by
    intro ℓ h
    obtain ⟨π, hπ⟩ := of_decide_eq_true h
    have hne := (hτ π).choose_spec.dst_ne_ci ℓ hπ
    refine ⟨hne, fun hh => ?_⟩
    obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
    cases dst <;> simp_all
  have hUarr : ∀ ℓ, U ℓ = true → ∀ y, ℓ.dst = .city y → ℓ.arr + N.dbar y ≤ planMakespan P := by
    intro ℓ h y hy
    obtain ⟨π, hπ⟩ := of_decide_eq_true h
    have hf : ∀ m ∈ ch π, Flies N m := fun m hm => hP.flies_of_mem_allLegs (hchm π m hm).1
    have h₁ := ToGoal.arr_add_d_le hS hL (ch π) _ _ (hτ π).choose_spec hf ℓ hπ y hy
    obtain ⟨m, hm, hme⟩ := exists_mem_arr_endTime (ch π) (hτ π).choose
      (List.ne_nil_of_mem hπ)
    obtain ⟨k, hk⟩ := hmemP _ (hchm π m hm).1
    have h₂ := arr_le_endTime (P k) .ci 0 (hP.planes k).route
      (fun m hm => ((hP.planes k).flies m hm).dep_le_arr) _ hk
    have h₃ := endTime_le_planMakespan P k
    rw [hS]
    omega
  have hroute' : ∀ k, IsRoute .ci 0 (P' k) := fun k =>
    isRoute_cutTri (P k) .ci 0 (hP.planes k).route
  have hflies' : ∀ k, ∀ m ∈ P' k, Flies N m := fun k =>
    flies_cutTri (P k) (hP.planes k).flies
  have hends' : ∀ k, P' k ≠ [] → finalLoc .ci (P' k) = .cg := fun k =>
    finalLoc_cutTri (P k) .ci fun ℓ _ => hUend ℓ
  have hend' : ∀ k, endTime 0 (P' k) ≤ planMakespan P := fun k =>
    endTime_cutTri_le (P k) .ci 0 (hP.planes k).route (hP.planes k).flies
      (fun ℓ _ => hUarr ℓ) (endTime_le_planMakespan P k)
  -- The chains survive the cut.
  have hkept : ∀ π, ∀ ℓ ∈ ch π, ∃ k, ℓ ∈ P' k := fun π ℓ hℓ => by
    obtain ⟨k, hk⟩ := hmemP _ (hchm π ℓ hℓ).1
    exact ⟨k, mem_cutTri (P k) ℓ hk (by simp only [hU, decide_eq_true_eq]; exact ⟨π, hℓ⟩)⟩
  -- The planes that are not idle.
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
  have hch'' : ∀ π : Fin t, ∃ ch' : List (Leg n t), (∃ τ, ToGoal .ci τ ch') ∧
      ∀ ℓ ∈ ch', ℓ ∈ allLegs P'' ∧ ℓ.pax = some π := fun π =>
    ⟨ch π, hτ π, fun ℓ hℓ => by
      obtain ⟨k, hk⟩ := hkept π ℓ hℓ
      exact ⟨hmem'' k ℓ hk, (hchm π ℓ hℓ).2⟩⟩
  have hqp : Q.card ≤ p := by simpa using Q.card_le_univ
  obtain ⟨X, hX, hXsize, hXload, hXcost⟩ :=
    exists_admissible_of_chains hS hL c hplanes hch'' (hqp.trans hpt)
  have hXload' : ∀ i, 2 * load N.d (X i) ≤ planMakespan P := fun i =>
    (hXload i).trans (((hplanes i).durSum_le_planMakespan).trans
      (Finset.sup_le fun i _ => hend' _))
  have hcost : planCost c P'' ≤ planCost c P := by
    calc planCost c P'' = ∑ k : Q, landCostSum c (P' k) :=
          e.sum_comp fun k : Q => landCostSum c (P' k)
      _ = ∑ k ∈ Q, landCostSum c (P' k) := Finset.sum_coe_sort Q fun k => landCostSum c (P' k)
      _ ≤ ∑ k ∈ Q, landCostSum c (P k) :=
          Finset.sum_le_sum fun k _ => landCostSum_cutTri_le c (P k)
      _ ≤ ∑ k, landCostSum c (P k) := Finset.sum_le_sum_of_subset (subset_univ Q)
      _ = planCost c P := rfl
  -- Lemma 4.2 (AP), once per idle plane.
  obtain ⟨Y, hY, hYsize, hYcost, hYload⟩ := hX.addPlanes_le N.d c hqp hpt hXsize
  refine ⟨Y, hY, hYsize, fun k => ?_, hYcost.trans (hXcost.trans hcost)⟩
  have := hYload (planMakespan P / 2) (fun i => by have := hXload' i; omega) k
  omega

/-- **Theorem 4.5, converse direction, under (A1).** -/
theorem FeasibleAnywhere.exists_admissible {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P :=
  hP.exists_admissible_hub hS hA1.hub c hpt

/-- **Theorem 4.5, converse direction, under (AΔ).** -/
theorem FeasibleAnywhere.exists_admissible_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P :=
  hP.exists_admissible_hub hS hA.hub c hpt

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
arrival), for every table of central flight durations satisfying the triangles through a hub. -/
theorem check_sound_anywhere_hub (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hL : (C.network dc).ATriHub) :
    IsParetoFront (achievableAnywhere (C.network dc) C.c C.t C.p) C.front := by
  have hF := C.check_sound_hub h dc (Or.inl hL)
  obtain ⟨-, hpt, hsym⟩ := C.check_header h
  have hS : (C.network dc).dbar = (C.network dc).d := hsym
  refine ⟨fun x hx => achievable_subset_achievableAnywhere _ _ _ _ (hF.achieved x hx),
    fun y hy => ?_, hF.antichain⟩
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_hub hS hL C.c hpt
  exact C.exists_le_of_admissible h hX hsize hload hcost

/-- **Soundness for planes ending anywhere, under (A1).** -/
theorem check_sound_anywhere (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA1 : (C.network dc).A1) :
    IsParetoFront (achievableAnywhere (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound_anywhere_hub h dc hA1.hub

/-- **Soundness for planes ending anywhere, under (AΔ).** -/
theorem check_sound_anywhere_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievableAnywhere (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound_anywhere_hub h dc hA.hub

/-- **Bridge B3 on certified instances.** If `check` accepts, the feasible plans and the plans
whose planes end anywhere have the same minimal (cost, makespan) pairs, the listed points, for
every table of central flight durations satisfying the triangles through a hub. -/
theorem minimal_achievable_iff_anywhere_hub (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hL : (C.network dc).ATriHub) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x ↔
      Minimal (· ∈ achievableAnywhere (C.network dc) C.c C.t C.p) x := by
  rw [← (C.check_sound_hub h dc (Or.inl hL)).mem_iff_minimal,
    ← (C.check_sound_anywhere_hub h dc hL).mem_iff_minimal]

/-- **Bridge B3 on certified instances, under (A1).** -/
theorem minimal_achievable_iff_anywhere (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA1 : (C.network dc).A1) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x ↔
      Minimal (· ∈ achievableAnywhere (C.network dc) C.c C.t C.p) x :=
  C.minimal_achievable_iff_anywhere_hub h dc hA1.hub x

/-- **Bridge B3 on certified instances, under (AΔ).** -/
theorem minimal_achievable_iff_anywhere_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x ↔
      Minimal (· ∈ achievableAnywhere (C.network dc) C.c C.t C.p) x :=
  C.minimal_achievable_iff_anywhere_hub h dc hA.hub x

end Cert

end ZenoFront
