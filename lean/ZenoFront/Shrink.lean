/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SupportBound
public import ZenoFront.Roles
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Shrinking and merging admissible partitions

Two operations that keep a grouping admissible:

* **Shrinking** (`Admissible.exists_shrink`). An admissible grouping with at least `s ≥ p`
  landings, `s ≡ p (mod 2)`, contains an admissible grouping with exactly `s` landings. This is
  Lemma 4.3 (shrinking) of the note. It works on the groups directly: remove two
  free landings of a plane that has at least three, or else remove the two copies of a city that
  carry a link.
* **Merging cities** (`Admissible.map`). Relabelling the cities by any map `rep` keeps a
  grouping admissible. With `rep` sending each city to a city that is no slower and no more
  expensive, this is the dominance reduction of §6: it lowers neither admissibility nor cost
  nor loads.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

/-- The size of an admissible grouping has the parity of `p`. -/
theorem size_mod_two (hw : IsParityWitness X h) : size X % 2 = p % 2 := by
  have hedge : edgeCount h % 2 = 0 := by
    rw [edgeCount_eq_sum_degree, Finset.sum_nat_mod,
      Finset.sum_eq_zero fun i _ => by obtain ⟨r, hr⟩ := hw.col i; omega]
    rfl
  have h₁ : size X % 2 = (∑ k, ((h k).card + 1)) % 2 := by
    rw [size, Finset.sum_nat_mod, Finset.sum_nat_mod (f := fun k => (h k).card + 1)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by have := hw.row k; omega
  have h₂ : ∑ k, ((h k).card + 1) = edgeCount h + p := by
    simp [edgeCount, Finset.sum_add_distrib]
  omega

/-- One shrinking step: an admissible grouping with more than `s ≥ p` landings contains one with
two fewer landings. -/
theorem exists_shrink_step (hw : IsParityWitness X h) {s : ℕ} (hps : p ≤ s) (hs : s < size X) :
    ∃ Y : Groups n p, ∃ h' : Fin p → Finset (Fin n), IsParityWitness Y h' ∧
      (∀ k, Y k ≤ X k) ∧ size Y + 2 = size X := by
  classical
  by_cases hfree : ∃ k₀, (h k₀).card + 3 ≤ (X k₀).card
  · -- Case (a): a plane has at least three free landings; remove two of them.
    obtain ⟨k₀, hk₀⟩ := hfree
    set F := X k₀ - (h k₀).val with hF
    have hle := hw.val_le k₀
    have hFcard : F.card = (X k₀).card - (h k₀).card := by
      rw [hF, Multiset.card_sub hle, Finset.card_val]
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < F.card)
    have hcard1 : (F.erase y).card = F.card - 1 := by
      rw [Multiset.card_erase_of_mem hy]; rfl
    obtain ⟨y', hy'⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (F.erase y).card)
    have hcard2 : ((F.erase y).erase y').card = F.card - 2 := by
      rw [Multiset.card_erase_of_mem hy', hcard1, Nat.pred_eq_sub_one]; omega
    set Z := (h k₀).val + (F.erase y).erase y' with hZ
    have hZle : Z ≤ X k₀ := by
      have : (h k₀).val + F = X k₀ := by rw [hF, add_comm, Multiset.sub_add_cancel hle]
      rw [← this, hZ]
      exact Multiset.add_le_add_left ((Multiset.erase_le _ _).trans (Multiset.erase_le _ _))
    have hZcard : Z.card + 2 = (X k₀).card := by
      rw [hZ, Multiset.card_add, hcard2, Finset.card_val]; omega
    refine ⟨Function.update X k₀ Z, h, ⟨fun k => ?_, fun k => ?_, hw.col⟩, fun k => ?_, ?_⟩
    · by_cases hk : k = k₀
      · subst hk
        intro i hi
        simp only [Function.update_self, Multiset.mem_toFinset, hZ, Multiset.mem_add]
        exact Or.inl (Finset.mem_val.mpr hi)
      · rw [Function.update_of_ne hk]; exact hw.subset k
    · by_cases hk : k = k₀
      · subst hk
        rw [Function.update_self]
        have := hw.row k
        omega
      · rw [Function.update_of_ne hk]; exact hw.row k
    · by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact hZle
      · rw [Function.update_of_ne hk]
    · have h₁ := Finset.sum_update_of_mem (Finset.mem_univ k₀) (fun k => (X k).card) Z.card
      have h₂ := Finset.add_sum_erase (univ : Finset (Fin p)) (fun k => (X k).card)
        (Finset.mem_univ k₀)
      have h₃ : size (Function.update X k₀ Z) =
          ∑ k, Function.update (fun k => (X k).card) k₀ Z.card k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = k₀
        · subst hk; simp
        · simp [Function.update_of_ne hk]
      rw [Finset.sdiff_singleton_eq_erase] at h₁
      rw [h₃, h₁, size, ← h₂]
      omega
  · -- Case (b): every plane has exactly one free landing; remove a link.
    push Not at hfree
    have hone : ∀ k, (X k).card = (h k).card + 1 := fun k => by
      have h₁ := hw.card_add_one_le k
      have h₂ := hw.row k
      have h₃ := hfree k
      omega
    have hsize : size X = edgeCount h + p := by
      simp only [size, edgeCount, hone, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, 0 < (h k₀).card := by
      by_contra hall
      push Not at hall
      have : edgeCount h = 0 := Finset.sum_eq_zero fun k _ => by have := hall k; omega
      omega
    obtain ⟨i, hi₀⟩ := Finset.card_pos.mp hk₀
    have hcol : 2 ≤ #{k | i ∈ h k} := by
      obtain ⟨r, hr⟩ := hw.col i
      have : 0 < #{k | i ∈ h k} := Finset.card_pos.mpr ⟨k₀, by simpa using hi₀⟩
      omega
    obtain ⟨k₁, hk₁, hne⟩ : ∃ k₁, i ∈ h k₁ ∧ k₁ ≠ k₀ := by
      by_contra hall
      push Not at hall
      have : ({k | i ∈ h k} : Finset (Fin p)) ⊆ {k₀} := fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simpa using hall k hk
      have := Finset.card_le_card this
      simp at this
      omega
    set pair : Finset (Fin p) := {k₀, k₁} with hpair
    have hpaircard : pair.card = 2 := by
      rw [hpair, Finset.card_pair hne.symm]
    refine ⟨fun k => if k ∈ pair then (X k).erase i else X k,
      fun k => if k ∈ pair then (h k).erase i else h k, ⟨fun k => ?_, fun k => ?_, fun j => ?_⟩,
      fun k => ?_, ?_⟩
    · split_ifs with hk
      · intro j hj
        rw [Finset.mem_erase] at hj
        rw [Multiset.mem_toFinset]
        exact (Multiset.mem_erase_of_ne hj.1).mpr (Multiset.mem_toFinset.mp (hw.subset k hj.2))
      · exact hw.subset k
    · split_ifs with hk
      · have hik : i ∈ h k := by
          rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hi₀
          · exact hk₁
        have hiX : i ∈ X k := Multiset.mem_toFinset.mp (hw.subset k hik)
        rw [Finset.card_erase_of_mem hik, Multiset.card_erase_of_mem hiX, hone k]
        have := hw.row k
        simp only [Nat.pred_eq_sub_one]
        have : 1 ≤ (h k).card := Finset.card_pos.mpr ⟨i, hik⟩
        omega
      · exact hw.row k
    · by_cases hji : j = i
      · subst hji
        have hset : ({k | j ∈ if k ∈ pair then (h k).erase j else h k} : Finset (Fin p)) =
            ({k | j ∈ h k} : Finset (Fin p)) \ pair := by
          ext k
          by_cases hk : k ∈ pair <;> simp [hk]
        have hsub : pair ⊆ ({k | j ∈ h k} : Finset (Fin p)) := by
          intro k hk
          rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · simpa using hi₀
          · simpa using hk₁
        rw [hset, Finset.card_sdiff_of_subset hsub, hpaircard]
        obtain ⟨r, hr⟩ := hw.col j
        exact ⟨r - 1, by omega⟩
      · have hset : ({k | j ∈ if k ∈ pair then (h k).erase i else h k} : Finset (Fin p)) =
            ({k | j ∈ h k} : Finset (Fin p)) := by
          ext k
          by_cases hk : k ∈ pair <;> simp [hk, hji]
        rw [hset]
        exact hw.col j
    · dsimp only
      split_ifs
      · exact Multiset.erase_le _ _
      · exact le_rfl
    · have hk : ∀ k, (if k ∈ pair then (X k).erase i else X k).card +
          (if k ∈ pair then 1 else 0) = (X k).card := by
        intro k
        split_ifs with hkp
        · have hik : i ∈ h k := by
            rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hkp
            rcases hkp with rfl | rfl
            · exact hi₀
            · exact hk₁
          rw [Multiset.card_erase_of_mem (Multiset.mem_toFinset.mp (hw.subset k hik))]
          have := hone k
          simp only [Nat.pred_eq_sub_one]
          omega
        · rfl
      have hsum := Finset.sum_congr rfl fun k (_ : k ∈ (univ : Finset (Fin p))) => hk k
      have h2 : ∑ k : Fin p, (if k ∈ pair then 1 else 0) = 2 := by
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, hpaircard]
      rw [Finset.sum_add_distrib, h2] at hsum
      exact hsum

end IsParityWitness

theorem exists_shrink_aux {s : ℕ} (hps : p ≤ s) : ∀ (N : ℕ) (X : Groups n p)
    (h : Fin p → Finset (Fin n)), IsParityWitness X h → size X = s + 2 * N →
    ∃ Y : Groups n p, Admissible Y ∧ (∀ k, Y k ≤ X k) ∧ size Y = s
  | 0, X, h, hw, hN => ⟨X, ⟨h, hw⟩, fun _ => le_rfl, by omega⟩
  | N + 1, X, h, hw, hN => by
    obtain ⟨Y, h', hw', hle, hsize⟩ := hw.exists_shrink_step hps (by omega)
    obtain ⟨Z, hZ, hZle, hZsize⟩ := exists_shrink_aux hps N Y h' hw' (by omega)
    exact ⟨Z, hZ, fun k => (hZle k).trans (hle k), hZsize⟩

/-- **Shrinking** (Lemma 4.3): an admissible grouping with at least
`s` landings, where `p ≤ s` and `s ≡ p (mod 2)`, contains an admissible grouping with exactly
`s` landings. -/
theorem Admissible.exists_shrink {X : Groups n p} (hX : Admissible X) {s : ℕ} (hps : p ≤ s)
    (hpar : s % 2 = p % 2) (hs : s ≤ size X) :
    ∃ Y : Groups n p, Admissible Y ∧ (∀ k, Y k ≤ X k) ∧ size Y = s := by
  obtain ⟨h, hw⟩ := hX
  have hmod := hw.size_mod_two
  exact exists_shrink_aux hps ((size X - s) / 2) X h hw (by omega)

/-! ### Merging cities -/

/-- **Merging cities.** Relabelling the cities of an admissible grouping by any map keeps it
admissible. The witness of a city `j` at plane `k` is the parity of the number of cities of
`h k` sent to `j`. -/
theorem Admissible.map {X : Groups n p} (hX : Admissible X) (rep : Fin n → Fin n) :
    Admissible fun k => (X k).map rep := by
  classical
  obtain ⟨h, hw⟩ := hX
  have hmod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ),
      #{x ∈ s | Odd (f x)} % 2 = (∑ x ∈ s, f x) % 2 := fun s f => by
    have := Finset.even_sum_iff_even_card_odd (s := s) f
    rw [Nat.even_iff, Nat.even_iff] at this
    omega
  refine ⟨fun k => {j | Odd #{i ∈ h k | rep i = j}}, ⟨fun k j hj => ?_, fun k => ?_, fun j => ?_⟩⟩
  · rw [Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hj.2.pos
    simp only [Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, Multiset.mem_map]
    exact ⟨i, Multiset.mem_toFinset.mp (hw.subset k hi.1), hi.2⟩
  · have h₁ := hmod univ fun j => #{i ∈ h k | rep i = j}
    have h₂ : ∑ j, #{i ∈ h k | rep i = j} = (h k).card :=
      (Finset.card_eq_sum_card_fiberwise fun i _ => Finset.mem_univ (rep i)).symm
    rw [Multiset.card_map, ← hw.row k, ← h₂, ← h₁]
  · -- column `j`: the parity of `Σ_k #{i ∈ h k | rep i = j} = Σ_{i ↦ j} #{k | i ∈ h k}`
    have h₁ := hmod univ fun k => #{i ∈ h k | rep i = j}
    have h₂ : ∑ k, #{i ∈ h k | rep i = j} = ∑ i, if rep i = j then #{k | i ∈ h k} else 0 := by
      have hk : ∀ k, #{i ∈ h k | rep i = j} = ∑ i, if i ∈ h k ∧ rep i = j then 1 else 0 :=
        fun k => by
          rw [← Finset.card_filter]
          congr 1
          ext i
          simp
      simp only [hk]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rw [Finset.card_filter]
        exact Finset.sum_congr rfl fun k _ => by simp [hi]
      · exact Finset.sum_eq_zero fun k _ => by simp [hi]
    have h₃ : (∑ i, if rep i = j then #{k | i ∈ h k} else 0) % 2 = 0 := by
      rw [Finset.sum_nat_mod, Finset.sum_eq_zero fun i _ => by
        split_ifs
        · obtain ⟨r, hr⟩ := hw.col i; omega
        · rfl]
      rfl
    rw [Nat.even_iff]
    have h₄ : ({k | j ∈ ({j | Odd #{i ∈ h k | rep i = j}} : Finset (Fin n))} : Finset (Fin p)) =
        ({k | Odd #{i ∈ h k | rep i = j}} : Finset (Fin p)) := by
      ext k
      simp
    rw [h₄, h₁, h₂, h₃]

end ZenoFront
