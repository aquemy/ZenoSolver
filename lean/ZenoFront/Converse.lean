/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.PlanBounds
public import ZenoFront.Shrink

/-!
# Landings of a route, and assumption (A1)

The central landings of a list of legs and their cost, assumption (A1) of the note (§1.4), and
small lemmas on legs and counts shared by the converses: Theorem 4.4
(`Feasible.exists_admissible_hub`, `ConverseTri.lean`), which also covers (A1)
(`Network.A1.hub`), and Theorem 5.3 (`schedulableDomination_all`, `DominationAll.lean`).

## Main results

* `ZenoFront.Network.A1`: assumption (A1).
* `ZenoFront.routeLandings`, `ZenoFront.landCostSum_eq_cost`: the central landings of a route
  and their cost.
* `ZenoFront.Feasible.flies_of_mem_allLegs`: every leg of a feasible plan is a flight.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- Assumption (A1): central flights are useless, `dc i j ≥ d i + d j` (under (S)). -/
def Network.A1 (N : Network n) : Prop := ∀ i j, N.d i + N.d j ≤ N.dc i j

/-! ### Landings -/

/-- The central landings of a list of legs. -/
def routeLandings : List (Leg n t) → Multiset (Fin n)
  | [] => 0
  | ℓ :: rest =>
    match ℓ.dst with
    | .city i => i ::ₘ routeLandings rest
    | _ => routeLandings rest

theorem landCostSum_eq_cost (c : Fin n → ℕ) : ∀ legs : List (Leg n t),
    landCostSum c legs = cost c (routeLandings legs)
  | [] => by simp [landCostSum, routeLandings]
  | ⟨src, dst, dep, arr, pax⟩ :: rest => by
    have ih := landCostSum_eq_cost c rest
    simp only [landCostSum, List.map_cons, List.sum_cons] at ih ⊢
    cases dst <;> simp [routeLandings, landCost, ih]

/-! ### Legs and counts -/

theorem Flies.dst_city_of_src_isHub {N : Network n} {ℓ : Leg n t} (h : Flies N ℓ)
    (hs : ℓ.src.isHub = true) : ∃ x, ℓ.dst = .city x := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, -⟩ := h
  simp only at hdur hs ⊢
  cases src <;> cases dst <;> simp_all [Network.duration]

theorem Feasible.flies_of_mem_allLegs {N : Network n} {P : Plan n t p} (hP : Feasible N P)
    {ℓ : Leg n t} (h : ℓ ∈ allLegs P) : Flies N ℓ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact (hP.planes k).flies ℓ hk

/-- Distinct elements of `l` satisfying `q`, indexed by a set of passengers. -/
theorem card_le_countP_of_injective {α : Type*} [DecidableEq α] (S : Finset (Fin t))
    (l : List α) (q : α → Bool) (f : Fin t → α) (hf : Function.Injective f)
    (hmem : ∀ π ∈ S, f π ∈ l ∧ q (f π) = true) : S.card ≤ l.countP q := by
  calc S.card = (S.image f).card := (card_image_of_injective _ hf).symm
    _ ≤ (l.filter q).toFinset.card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨π, hπ, rfl⟩ := mem_image.mp hx
        simpa [List.mem_toFinset, List.mem_filter] using hmem π hπ
    _ ≤ (l.filter q).length := List.toFinset_card_le _
    _ = l.countP q := List.countP_eq_length_filter.symm

/-- Choosing counts below `a` with a given total `μ ≤ Σ a`. -/
theorem exists_le_sum_eq (a : Fin p → ℕ) : ∀ μ : ℕ, μ ≤ ∑ k, a k →
    ∃ b : Fin p → ℕ, (∀ k, b k ≤ a k) ∧ ∑ k, b k = μ
  | 0, _ => ⟨0, fun _ => Nat.zero_le _, by simp⟩
  | μ + 1, h => by
    classical
    obtain ⟨b, hb, hsum⟩ := exists_le_sum_eq a μ (by omega)
    obtain ⟨k₀, hk₀⟩ : ∃ k, b k < a k := by
      by_contra hall
      push Not at hall
      have : ∑ k, a k ≤ ∑ k, b k := Finset.sum_le_sum fun k _ => hall k
      omega
    refine ⟨Function.update b k₀ (b k₀ + 1), fun k => ?_, ?_⟩
    · by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hk]; exact hb k
    · rw [Finset.sum_update_of_mem (Finset.mem_univ k₀), Finset.sdiff_singleton_eq_erase]
      have := Finset.add_sum_erase (univ : Finset (Fin p)) b (Finset.mem_univ k₀)
      omega

end ZenoFront
