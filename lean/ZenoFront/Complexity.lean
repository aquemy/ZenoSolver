/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Solver

/-!
# Complexity (§8)

The reductions of §8 work on partitions in which no city lies in two groups. For those,
admissibility is a parity condition on the sizes of the groups alone.

## Main results

* `admissible_iff_odd_of_disjoint` (**Lemma 2.4, disjoint groups**): if no city lies in two
  groups, a partition is admissible iff every group has an odd number of landings.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### Lemma 2.4: disjoint groups -/

/-- **Lemma 2.4 (disjoint groups).** If no city lies in two groups, a partition is admissible iff
every group has an odd number of landings. A parity witness can only use a city at the one plane
that lands there, so every city has degree `0` and the witness is empty; then the row condition
says `|X_k| + 1` is even. -/
theorem admissible_iff_odd_of_disjoint {X : Groups n p}
    (hX : ∀ i k k', i ∈ X k → i ∈ X k' → k = k') : Admissible X ↔ ∀ k, Odd (X k).card := by
  constructor
  · rintro ⟨h, hw⟩ k
    have hempty : h k = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hone : #{k' | i ∈ h k'} = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨k, Finset.ext fun k' => ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        refine ⟨fun hk' => hX i k' k ?_ ?_, fun hk' => hk' ▸ hi⟩
        · exact Multiset.mem_toFinset.mp (hw.subset k' hk')
        · exact Multiset.mem_toFinset.mp (hw.subset k hi)
      have := hw.col i
      rw [hone] at this
      exact absurd this (by decide)
    have := hw.row k
    rw [hempty, Finset.card_empty] at this
    rw [Nat.odd_iff]
    omega
  · intro hodd
    refine ⟨fun _ => ∅, ⟨fun k => Finset.empty_subset _, fun k => ?_, fun i => ?_⟩⟩
    · have := Nat.odd_iff.mp (hodd k)
      simp only [Finset.card_empty]
      omega
    · simp

end ZenoFront
