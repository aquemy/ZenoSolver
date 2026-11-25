/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Admissible

/-!
# Role configurations

A *role configuration* gives every plane `k` three multisets of landings:

* `drop k` (`D_k`): drop-off halves, `C_I → i → C_I` carrying a passenger to `i`;
* `pick k` (`P_k`): pick-up halves, `C_G → i → C_G` carrying a passenger from `i`;
* `cross k` (`Cr_k`): crossings `C_I → i → C_G` or `C_G → i → C_I`, an odd number of them
  (every plane makes one more crossing towards `C_G` than back, Lemma 2.1 of the note);

and every city receives as many drop-offs as pick-ups: `Σ_k D_k = Σ_k P_k`.

This is the abstraction of a plan used by the non-symmetric converse (Theorem 6.1) and its
bounds. Every feasible plan gives one (Lemma 4.3(b), `Feasible.exists_roleConfig_records`). Its
grouping is `X_k = D_k + P_k + Cr_k`.

## Main results

* `ZenoFront.RoleConfig`, `ZenoFront.RoleConfig.groups`: role configurations and their groupings.
* `ZenoFront.RoleConfig.isParityWitness_witness` (Lemma 4.5, PAR): the grouping of a role
  configuration is admissible, with the explicit witness `h_{k,i} = (D_k(i) + P_k(i)) mod 2`.
  Nothing else uses it; it is kept until revision 3 archives Lemma 4.5 (WP8).
* `ZenoFront.IsParityWitness.exists_roleConfig`: from any parity witness `h` of `X`, build a role
  configuration with grouping `X` and `D_k + P_k = h k`, by splitting the planes of `h` at every
  city into two halves of equal size.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- A role configuration: per plane, drop-off halves, pick-up halves and an odd number of
crossings, with as many drop-offs as pick-ups at every city. -/
structure RoleConfig (n p : ℕ) where
  /-- Drop-off halves `D_k` of each plane. -/
  drop : Fin p → Multiset (Fin n)
  /-- Pick-up halves `P_k` of each plane. -/
  pick : Fin p → Multiset (Fin n)
  /-- Crossings `Cr_k` of each plane. -/
  cross : Fin p → Multiset (Fin n)
  odd_card_cross : ∀ k, Odd (cross k).card
  sum_drop_eq_sum_pick : ∑ k, drop k = ∑ k, pick k

namespace RoleConfig

variable (R : RoleConfig n p)

/-- The grouping of a role configuration, `X_k = D_k + P_k + Cr_k`. -/
def groups : Groups n p := fun k => R.drop k + R.pick k + R.cross k

/-- The parity witness of PAR: `i ∈ h k` iff `D_k(i) + P_k(i)` is odd. Kept until revision 3
archives Lemma 4.5 (WP8). -/
def witness (k : Fin p) : Finset (Fin n) :=
  {i | Odd ((R.drop k + R.pick k).count i)}

theorem mem_witness {k : Fin p} {i : Fin n} :
    i ∈ R.witness k ↔ Odd ((R.drop k + R.pick k).count i) := by
  simp [witness]

theorem card_groups (k : Fin p) :
    (R.groups k).card = (R.drop k).card + (R.pick k).card + (R.cross k).card := by
  simp [groups]

/-- The parity of the number of odd terms of a sum of naturals is the parity of the sum. -/
private theorem card_filter_odd_mod_two {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    #{x ∈ s | Odd (f x)} % 2 = (∑ x ∈ s, f x) % 2 := by
  have := Finset.even_sum_iff_even_card_odd (s := s) f
  rw [Nat.even_iff, Nat.even_iff] at this
  omega

/-- **PAR (Lemma 4.5).** The grouping of a role configuration is admissible, with witness
`h_{k,i} = (D_k(i) + P_k(i)) mod 2`. Kept until revision 3 archives Lemma 4.5 (WP8). -/
theorem isParityWitness_witness : IsParityWitness R.groups R.witness where
  subset k i hi := by
    rw [mem_witness] at hi
    have : 0 < (R.drop k + R.pick k).count i := hi.pos
    rw [Multiset.count_pos] at this
    simp only [groups, Multiset.mem_toFinset, Multiset.mem_add] at this ⊢
    tauto
  row k := by
    have h₁ : (R.witness k).card % 2 = (∑ i, (R.drop k + R.pick k).count i) % 2 := by
      simpa [witness] using card_filter_odd_mod_two univ fun i => (R.drop k + R.pick k).count i
    rw [Multiset.sum_count_eq_card (by simp)] at h₁
    have h₂ := R.odd_card_cross k
    rw [Nat.odd_iff] at h₂
    rw [card_groups, h₁, Multiset.card_add]
    omega
  col i := by
    have h₁ : #{k | i ∈ R.witness k} % 2 = (∑ k, (R.drop k + R.pick k).count i) % 2 := by
      simpa [mem_witness] using card_filter_odd_mod_two univ fun k => (R.drop k + R.pick k).count i
    have h₂ : ∑ k, (R.drop k + R.pick k).count i = 2 * (∑ k, R.drop k).count i := by
      simp only [Multiset.count_add, Finset.sum_add_distrib, ← Multiset.count_sum',
        R.sum_drop_eq_sum_pick]
      omega
    rw [Nat.even_iff, h₁, h₂]
    omega

/-- **PAR (Lemma 4.5)**, admissibility form. Kept until revision 3 archives Lemma 4.5 (WP8). -/
theorem admissible_groups : Admissible R.groups := ⟨_, R.isParityWitness_witness⟩

end RoleConfig

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

theorem val_le (hw : IsParityWitness X h) (k : Fin p) : (h k).val ≤ X k := by
  rw [Multiset.le_iff_subset (h k).nodup]
  intro i hi
  simpa using hw.subset k hi

/-- **Role configurations from a parity witness.** A parity witness `h` of `X` gives a role
configuration with grouping `X` whose drop-offs and pick-ups at plane `k` are exactly the cities
of `h k`: at every city, the (even number of) planes of `h` are split into two halves of equal
size, the first half dropping and the second half picking up. The remaining `|X_k| − |h k|`
landings, an odd number, are crossings. -/
theorem exists_roleConfig (hw : IsParityWitness X h) :
    ∃ R : RoleConfig n p, R.groups = X ∧ ∀ k, R.drop k + R.pick k = (h k).val := by
  -- At each city `i`, choose half `A i` of the planes `K i = {k | i ∈ h k}`.
  have hhalf : ∀ i : Fin n, ∃ A ⊆ ({k | i ∈ h k} : Finset (Fin p)),
      A.card = #{k | i ∈ h k} / 2 :=
    fun i => Finset.exists_subset_card_eq (Nat.div_le_self _ _)
  choose A hAsub hAcard using hhalf
  have hcount : ∀ (k : Fin p) (q : Fin n → Prop) [DecidablePred q] (i : Fin n),
      ((h k).filter q).val.count i = if i ∈ h k ∧ q i then 1 else 0 := by
    intro k q _ i
    rw [Multiset.count_eq_of_nodup ((h k).filter q).nodup]
    simp
  refine ⟨{ drop := fun k => ((h k).filter fun i => k ∈ A i).val
            pick := fun k => ((h k).filter fun i => k ∉ A i).val
            cross := fun k => X k - (h k).val
            odd_card_cross := fun k => ?_
            sum_drop_eq_sum_pick := ?_ }, ?_, fun k => ?_⟩
  · rw [Multiset.card_sub (hw.val_le k), Finset.card_val, Nat.odd_iff]
    have := hw.row k
    have := hw.card_add_one_le k
    omega
  · ext i
    simp only [Multiset.count_sum', hcount, ← Finset.card_filter]
    have hK := hw.col i
    rw [Nat.even_iff] at hK
    have h₁ : ({k | i ∈ h k ∧ k ∈ A i} : Finset (Fin p)) = A i := by
      ext k
      constructor
      · intro hk
        exact (Finset.mem_filter.mp hk).2.2
      · intro hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hAsub i hk)).2, hk⟩
    have h₂ : ({k | i ∈ h k ∧ k ∉ A i} : Finset (Fin p)) =
        ({k | i ∈ h k} : Finset (Fin p)) \ A i := by
      ext k
      simp
    rw [h₁, h₂, Finset.card_sdiff_of_subset (hAsub i), hAcard i]
    omega
  · funext k
    simp only [RoleConfig.groups]
    rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not,
      add_tsub_cancel_of_le (hw.val_le k)]
  · simp only
    rw [Finset.filter_val, Finset.filter_val]
    exact Multiset.filter_add_not _ _

end IsParityWitness

/-- Every admissible grouping is the grouping of a role configuration. -/
theorem Admissible.exists_roleConfig {X : Groups n p} (hX : Admissible X) :
    ∃ R : RoleConfig n p, R.groups = X := by
  obtain ⟨h, hw⟩ := hX
  obtain ⟨R, hR, -⟩ := hw.exists_roleConfig
  exact ⟨R, hR⟩

end ZenoFront
