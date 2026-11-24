/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Achievability

/-!
# `E(T)`, the least cost of an admissible partition

`minCost d c t p T` is `E(T)`: the least cost of an admissible partition of `2t − p` landings
into `p` groups whose loads are all at most `T` (`⊤` if there is none). It is non-increasing
(`minCost_antitone`) and attained when finite (`minCost_attained`). The σ-DP
(`sigmaBoundAt_eq_minCost`) and the link-forest DP (`treeBoundAt_eq_minCost`) compute it.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### `E(T)` -/

/-- `E(T)`: the least cost of an admissible partition of `2t − p` landings into `p` groups whose
loads are all at most `T` (`⊤` if there is none). -/
noncomputable def minCost (d c : Fin n → ℕ) (t p T : ℕ) : WithTop ℕ :=
  sInf {x | ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧ (∀ k, load d (X k) ≤ T) ∧
    (totalCost c X : WithTop ℕ) = x}

theorem minCost_le (d c : Fin n → ℕ) {t T : ℕ} {X : Groups n p} (hX : Admissible X)
    (hsize : size X = 2 * t - p) (hT : ∀ k, load d (X k) ≤ T) :
    minCost d c t p T ≤ totalCost c X :=
  sInf_le ⟨X, hX, hsize, hT, rfl⟩

/-- `E(T)` is attained when it is finite. -/
theorem minCost_attained (d c : Fin n → ℕ) {t T C : ℕ} (h : minCost d c t p T = C) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧ (∀ k, load d (X k) ≤ T) ∧
      totalCost c X = C := by
  set S : Set (WithTop ℕ) := {x | ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
    (∀ k, load d (X k) ≤ T) ∧ (totalCost c X : WithTop ℕ) = x} with hS
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : minCost d c t p T = ⊤ := by
      change sInf S = ⊤
      rw [hne, sInf_empty]
    rw [this] at h
    exact WithTop.top_ne_coe h
  obtain ⟨X, hX, hsize, hT, hcost⟩ := csInf_mem hne
  refine ⟨X, hX, hsize, hT, ?_⟩
  have : (totalCost c X : WithTop ℕ) = C := hcost.trans h
  exact WithTop.coe_injective this

/-- `E` is non-increasing. -/
theorem minCost_antitone (d c : Fin n → ℕ) (t p : ℕ) : Antitone (minCost d c t p) :=
  fun _ _ hTT' => sInf_le_sInf fun _ ⟨X, hX, hsize, hT, hx⟩ =>
    ⟨X, hX, hsize, fun k => (hT k).trans hTT', hx⟩

/-! ### Attained infima -/

theorem exists_mem_eq_of_inf_eq {ι : Type*} (s : Finset ι) (f : ι → WithTop ℕ) {v : ℕ}
    (h : s.inf f = v) : ∃ i ∈ s, f i = v := by
  have hne : s.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    subst h'
    exact WithTop.top_ne_coe h
  obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf s hne f
  exact ⟨i, hi, hfi ▸ h⟩

end ZenoFront
