/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.ConverseTri
public import ZenoFront.RationalPlans
public import ZenoFront.Solver

/-!
# The fronts under (S) and (AΔ) (Corollary 4.12)

**Corollary 4.12.** Under (S) and (AΔ), Corollary 4.8, Theorem 4.9 and Proposition 7.1 hold, and
`forest` gaps are sound. Every statement here is the (A1) one with Theorem 4.10
(`Feasible.exists_admissible_ATri`) in place of Theorem 4.7; Theorem 4.1 needs no assumption on
central flights.

* **Theorem 4.9** (`FeasibleAnywhere.exists_admissible_ATri`). Planes ending anywhere: every
  route is cut after its last leg on a passenger's chain. If that leg lands in a central city `b`
  at time `a`, an empty flight `b → C_G` leaving at `a` is appended (`cutTri`). This is the second
  use of (AΔ): the rest of the chain from `b` lasts at least `d̄_b`, so the appended flight
  arrives by the makespan (`ToGoal.arr_add_d_le`). The planes that are not idle then end in
  `C_G` with every chain intact, and Theorem 4.10 from chains (`exists_admissible_of_chains`)
  applies to them. Lemma 4.6 (AP) adds the idle planes.
* **Fronts**: `minimal_achievable_iff_multisetPoints_ATri` (Corollary 4.8),
  `minimal_achievable_iff_anywhere_of_ATri` (Theorem 4.9), `minimal_achievable_iff_minCost_ATri`
  (Proposition 7.1), `solveFront_isParetoFront_ATri` (the solver).
* **Checker**: `Cert.forestGapBound_le_ATri` (obligation 3 for `forest` gaps) and
  `Cert.check_sound_ATri`: if `check` accepts, the listed points are the Pareto front for every
  table of central flights satisfying (AΔ). Also for planes ending anywhere
  (`Cert.check_sound_anywhere_ATri`) and rational times (`Cert.check_sound_rat_ATri`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Chains: times -/

/-- **The second use of (AΔ).** A chain from a central city `y` lasts at least `d_y`: under (S)
and the triangles through a hub, `d_y ≤ dc y y' + d_{y'}` along every central leg. -/
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

/-! ### Theorem 4.9 under (AΔ) -/

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
/-- **Theorem 4.9 (bridge B3) under (AΔ), converse direction.** Under (S) and (AΔ) on the
triangles through a hub, with `p ≤ t`, every plan whose planes may end anywhere is weakly
dominated by an admissible partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤` the makespan (the last arrival) for every plane, and total cost at most the plan's
cost. -/
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
  -- Lemma 4.6 (AP), once per idle plane.
  obtain ⟨Y, hY, hYsize, hYcost, hYload⟩ := hX.addPlanes_le N.d c hqp hpt hXsize
  refine ⟨Y, hY, hYsize, fun k => ?_, hYcost.trans (hXcost.trans hcost)⟩
  have := hYload (planMakespan P / 2) (fun i => by have := hXload' i; omega) k
  omega

/-- **Theorem 4.9 under (AΔ), converse direction.** Under (S) and (AΔ), with `p ≤ t`, every plan
whose planes may end anywhere gives an admissible partition with `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤` the makespan and total cost at most the plan's. -/
theorem FeasibleAnywhere.exists_admissible_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P :=
  hP.exists_admissible_hub hS hA.hub c hpt

/-! ### Fronts under (AΔ) -/

/-- Under (S), (AΔ) and Theorem 4.1, every plan of the variant is weakly dominated by a feasible
plan. -/
theorem FeasibleAnywhere.exists_feasible_le_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) {P : Plan n t p} (hP : FeasibleAnywhere N P) (hpt : p ≤ t) :
    ∃ P' : Plan n t p, Feasible N P' ∧ planCost c P' ≤ planCost c P ∧
      planMakespan P' ≤ planMakespan P := by
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri hS hA c hpt
  obtain ⟨P', hP', hc, hm⟩ := admissibleAchievable hS c hpt X hX hsize
  refine ⟨P', hP', hc.trans hcost, hm.trans ?_⟩
  have : maxLoad N.d X ≤ planMakespan P / 2 :=
    (maxLoad_le_iff _ _ _).mpr fun k => by have := hload k; omega
  omega

/-- **Theorem 4.9 under (AΔ)** (Corollary 4.12). Under (S) and (AΔ), with `p ≤ t`, the feasible
plans and the plans whose planes end anywhere have the same minimal (cost, makespan) pairs. -/
theorem minimal_achievable_iff_anywhere_of_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ achievableAnywhere N c t p) x := by
  refine minimal_iff_of_subset_of_dominated (achievable_subset_achievableAnywhere N c t p)
    (fun y hy => ?_) x
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨P', hP', hc, hm⟩ := hP.exists_feasible_le_ATri hS hA c hpt
  exact ⟨_, ⟨P', hP', rfl⟩, Prod.le_def.mpr ⟨hc, hm⟩⟩

/-- **Corollary 4.8 under (AΔ), partition form.** Under (S) and (AΔ), with `p ≤ t`, the front of
the feasible plans is the set of minimal admissible points. -/
theorem minimal_achievable_iff_admissiblePoints_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ admissiblePoints N c t p) x := by
  refine minimal_iff_of_dominated (fun y hy => ?_)
    (fun y hy => ⟨y, admissiblePoints_subset_achievable hS c hpt hy, le_rfl⟩) x
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri_makespan hS hA c hpt
  exact admissiblePoint_le hX hsize hload hcost

/-- **Corollary 4.8 under (AΔ)** (Corollary 4.12). Under (S) and (AΔ), with `p ≤ t`, the front is
`Min 𝒳`, with `𝒳` the points `(c(Y), M(Y))` of the multisets of `2t − p` landings that have an
admissible partition. -/
theorem minimal_achievable_iff_multisetPoints_ATri {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ multisetPoints N c t p) x :=
  (minimal_achievable_iff_admissiblePoints_ATri hS hA c hpt x).trans
    (minimal_admissiblePoints_iff_multisetPoints N c x)

/-- **Corollary 4.8 under (AΔ) for planes ending anywhere.** -/
theorem minimal_achievableAnywhere_iff_admissiblePoints_ATri {N : Network n}
    (hS : N.dbar = N.d) (hA : N.ATri) (c : Fin n → ℕ) (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievableAnywhere N c t p) x ↔ Minimal (· ∈ admissiblePoints N c t p) x :=
  (minimal_achievable_iff_anywhere_of_ATri hS hA c hpt x).symm.trans
    (minimal_achievable_iff_admissiblePoints_ATri hS hA c hpt x)

/-- **Proposition 7.1 under (AΔ)** (Corollary 4.12). Under (S) and (AΔ), with `p ≤ t`, a pair
`(C, M)` is on the front iff `M = 2T` with `E(T) = C` and `E(T') > C` for every `T' < T`: the
front is the set of breakpoints of `E`. -/
theorem minimal_achievable_iff_minCost_ATri {N : Network n} (hS : N.dbar = N.d) (hA : N.ATri)
    (c : Fin n → ℕ) (hpt : p ≤ t) (C M : ℕ) :
    Minimal (· ∈ achievable N c t p) (C, M) ↔
      ∃ T, M = 2 * T ∧ minCost N.d c t p T = C ∧
        ∀ T' < T, (C : WithTop ℕ) < minCost N.d c t p T' :=
  (minimal_achievable_iff_admissiblePoints_ATri hS hA c hpt (C, M)).trans
    (minimal_admissiblePoints_iff N c C M)

/-- **The solver is correct under (AΔ).** Under (S) and (AΔ), with `1 ≤ p ≤ t`, `solveFront` is
the Pareto front of the (cost, makespan) pairs of the feasible plans. -/
theorem solveFront_isParetoFront_ATri {N : Network n} (hS : N.dbar = N.d) (hA : N.ATri)
    (c : Fin n → ℕ) (hp : 1 ≤ p) (hpt : p ≤ t) :
    IsParetoFront (achievable N c t p) (solveFront N.d c t p) := by
  classical
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · exact ((minimal_achievable_iff_admissiblePoints_ATri hS hA c hpt x).mpr
      ((mem_solveFront_iff N c hp hpt x).mp hx)).prop
  · obtain ⟨P, hP, rfl⟩ := hy
    obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri_makespan hS hA c hpt
    set T := planMakespan P / 2 with hTdef
    have hXT : ∀ k, load N.d (X k) ≤ T := fun k => by have := hload k; omega
    have hET : minCost N.d c t p T ≤ planCost c P :=
      (minCost_le N.d c hX hsize hXT).trans (WithTop.coe_le_coe.mpr hcost)
    obtain ⟨C₀, hC₀⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hET)
    have hC₀' : minCost N.d c t p T = ((C₀ : ℕ) : WithTop ℕ) := hC₀.symm
    have hex : ∃ T', minCost N.d c t p T' ≤ minCost N.d c t p T := ⟨T, le_rfl⟩
    set T₁ := Nat.find hex with hT₁
    have hT₁T : T₁ ≤ T := Nat.find_min' hex le_rfl
    have hE₁ : minCost N.d c t p T₁ = C₀ := by
      rw [← hC₀']
      exact le_antisymm (Nat.find_spec hex) (minCost_antitone N.d c t p hT₁T)
    have hlt : ∀ T' < T₁, ((C₀ : ℕ) : WithTop ℕ) < minCost N.d c t p T' := fun T' hT' => by
      rw [← hC₀']
      exact not_le.mp (Nat.find_min hex hT')
    refine ⟨(C₀, 2 * T₁), (mem_solveFront_iff N c hp hpt _).mpr
      ((minimal_admissiblePoints_iff N c C₀ (2 * T₁)).mpr ⟨T₁, rfl, hE₁, hlt⟩),
      Prod.le_def.mpr ⟨?_, by simp only; omega⟩⟩
    rw [hC₀'] at hET
    exact_mod_cast hET
  · rw [solveFront_eq N.d c hp hpt]
    exact (scanFront_pairwise _ 0 _ ⊤).2.imp fun {a b} hab =>
      ⟨fun hle => absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2),
        fun hle => absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)⟩

/-! ### The checker under (AΔ) -/

namespace Cert

variable (C : Cert)

/-- The forest gap bound is sound under (AΔ): a feasible plan with makespan below `M` costs at
least `forestGapBound M`. This is where Theorem 4.10 is used. -/
theorem forestGapBound_le_ATri {dc : Fin C.n → Fin C.n → ℕ} (hS : C.dbar = C.d)
    (hA : (C.network dc).ATri) (hp : 1 ≤ C.p) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.forestGapBound C.table M ≤ (planCost C.c P : WithTop ℕ) := by
  unfold forestGapBound
  split_ifs
  · obtain ⟨X, hX, hsize, hload, hcost⟩ :=
      hP.exists_admissible_ATri_makespan (c := C.c) hS hA hpt
    refine (forestBoundAt_le_totalCost (scaledDurations C.d) C.c hp hpt hX hsize fun k => ?_).trans
      (WithTop.coe_le_coe.mpr hcost)
    apply load_scaled_le_of_load_le
    have := hload k
    change 2 * load C.d (X k) ≤ planMakespan P at this
    rw [Nat.le_div_iff_mul_le Nat.two_pos]
    omega
  · exact bot_le

/-- **Soundness of the checker under (AΔ).** If `check` accepts a certificate, its points are
exactly the Pareto front of the instance for every table `dc` of central flight durations that
satisfies (AΔ), whatever the gap kinds. -/
theorem check_sound_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front := by
  obtain ⟨-, hpt, hsym⟩ := C.check_header h
  have hS : (C.network dc).dbar = (C.network dc).d := hsym
  have h' := h
  simp only [check, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨-, hmono⟩, hplans⟩, -⟩, -⟩, -⟩ := h'
  simp only [plansOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hplans
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · -- Every point is achieved by its plan.
    obtain ⟨P, hPx⟩ := exists_mem_zip_of_mem hplans.1 hx
    obtain ⟨⟨hok, hcost⟩, hmk⟩ := hplans.2 _ hPx
    exact ⟨P, planOK_feasible dc hok, Prod.ext hcost hmk⟩
  · -- Every feasible plan is weakly dominated: Theorem 4.10, then the obligations.
    obtain ⟨P, hP, rfl⟩ := hy
    obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri_makespan hS hA C.c hpt
    exact C.exists_le_of_admissible h hX hsize hload hcost
  · -- The points are pairwise incomparable.
    refine (pairwise_of_strictlyMonotone hmono).imp fun {a b} hab => ⟨fun hle => ?_, fun hle => ?_⟩
    · exact absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2)
    · exact absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)

/-- **Soundness under (AΔ), minimal-elements form.** If `check` accepts, a pair is listed iff it
is a minimal (cost, makespan) pair of a feasible plan, for every table satisfying (AΔ). -/
theorem check_sound_minimal_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) (x : ℕ × ℕ) :
    x ∈ C.front ↔ Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x :=
  (C.check_sound_ATri h dc hA).mem_iff_minimal x

/-- **Soundness for planes ending anywhere, under (AΔ).** If `check` accepts, the listed points
are exactly the Pareto front of the plans whose planes may end anywhere, for every table of
central flight durations satisfying (AΔ). -/
theorem check_sound_anywhere_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievableAnywhere (C.network dc) C.c C.t C.p) C.front := by
  have hF := C.check_sound_ATri h dc hA
  obtain ⟨-, hpt, hsym⟩ := C.check_header h
  have hS : (C.network dc).dbar = (C.network dc).d := hsym
  refine ⟨fun x hx => achievable_subset_achievableAnywhere _ _ _ _ (hF.achieved x hx),
    fun y hy => ?_, hF.antichain⟩
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri hS hA C.c hpt
  exact C.exists_le_of_admissible h hX hsize hload hcost

/-- **Soundness against rational times, under (AΔ).** If `check` accepts, the listed points are
exactly the Pareto front of the feasible plans with rational times, for every table satisfying
(AΔ). -/
theorem check_sound_rat_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) :
    IsParetoFront (achievableQ (C.network dc) C.c C.t C.p)
      (C.front.map fun x => (x.1, (x.2 : ℚ))) := by
  have H := C.check_sound_ATri h dc hA
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

/-- **Bridge B3 on certified instances, under (AΔ).** If `check` accepts, the feasible plans and
the plans whose planes end anywhere have the same minimal (cost, makespan) pairs, the listed
points, for every table of central flight durations satisfying (AΔ). -/
theorem minimal_achievable_iff_anywhere_ATri (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).ATri) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x ↔
      Minimal (· ∈ achievableAnywhere (C.network dc) C.c C.t C.p) x := by
  rw [← (C.check_sound_ATri h dc hA).mem_iff_minimal,
    ← (C.check_sound_anywhere_ATri h dc hA).mem_iff_minimal]

end Cert

end ZenoFront
