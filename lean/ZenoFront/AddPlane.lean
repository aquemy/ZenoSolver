/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Shrink

/-!
# Adding a plane (Lemma 4.2, AP)

**Lemma 4.2 (AP).** An admissible grouping of `q` planes with `2t − q` landings, `t ≥ q + 1`,
becomes an admissible grouping of `q + 1` planes with `2t − q − 1` landings, of no larger cost
and no larger largest load. This is the step of bridge B3 (Theorem 4.5) that gives the idle
planes of a plan whose planes may end anywhere a group of their own.

The proof reuses the shrinking step (`IsParityWitness.exists_shrink_step`): it removes two
landings, either two free landings of one plane or the two copies of a linked city. One of the
removed landings becomes the group of the new plane, with an empty witness set: a group of one
landing is odd and needs no link. The new group is no slower than the group it came from, and
the cost drops by the other removed landing.

## Main results

* `ZenoFront.Admissible.addPlane`: Lemma 4.2.
* `ZenoFront.Admissible.addPlanes`: Lemma 4.2 applied `m` times, from `q` to `q + m ≤ t` planes.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n q : ℕ}

theorem size_snoc (X : Groups n q) (Y : Multiset (Fin n)) :
    size (Fin.snoc (α := fun _ => Multiset (Fin n)) X Y) = size X + Y.card := by
  simp [size, Fin.sum_univ_castSucc]

theorem totalCost_snoc (c : Fin n → ℕ) (X : Groups n q) (Y : Multiset (Fin n)) :
    totalCost c (Fin.snoc (α := fun _ => Multiset (Fin n)) X Y) = totalCost c X + cost c Y := by
  simp [totalCost, Fin.sum_univ_castSucc]

/-- **Lemma 4.2 (AP), general form.** An admissible grouping of `q` planes with at least `q + 2`
landings gives an admissible grouping of `q + 1` planes with one landing less, no larger cost,
and loads bounded by every bound on the old loads. -/
theorem Admissible.addPlane {X : Groups n q} (hX : Admissible X) (hq : q + 2 ≤ size X)
    (d c : Fin n → ℕ) :
    ∃ Y : Groups n (q + 1), Admissible Y ∧ size Y + 1 = size X ∧
      totalCost c Y ≤ totalCost c X ∧ ∀ T, (∀ k, load d (X k) ≤ T) → ∀ k, load d (Y k) ≤ T := by
  classical
  obtain ⟨h, hw⟩ := hX
  obtain ⟨Y, h', hw', hle, hsize⟩ := hw.exists_shrink_step (s := size X - 2) (by omega) (by omega)
  -- A plane that lost a landing, and one of its lost landings.
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, Y k₀ ≠ X k₀ := by
    by_contra hall
    push Not at hall
    have : size Y = size X := by simp [size, hall]
    omega
  obtain ⟨y, hy⟩ : ∃ y, y ∈ X k₀ - Y k₀ := by
    refine Multiset.exists_mem_of_ne_zero fun h0 => hk₀ (le_antisymm (hle k₀) ?_)
    exact (tsub_eq_zero_iff_le.mp h0)
  have hyX : y ∈ X k₀ := Multiset.mem_of_le (Multiset.sub_le_self _ _) hy
  have hcons : Y k₀ + {y} ≤ X k₀ := by
    calc Y k₀ + {y} ≤ Y k₀ + (X k₀ - Y k₀) :=
          add_le_add le_rfl (Multiset.singleton_le.mpr hy)
      _ = X k₀ := add_tsub_cancel_of_le (hle k₀)
  set Y' : Groups n (q + 1) := Fin.snoc (α := fun _ => Multiset (Fin n)) Y {y} with hY'
  set h'' : Fin (q + 1) → Finset (Fin n) := Fin.snoc (α := fun _ => Finset (Fin n)) h' ∅ with hh''
  have hw'' : IsParityWitness Y' h'' := by
    refine ⟨fun k => ?_, fun k => ?_, fun i => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [hh'']
      · simpa [hY', hh''] using hw'.subset j
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [hY', hh'']
      · simpa [hY', hh''] using hw'.row j
    · have := hw'.col i
      rw [Finset.card_filter] at this ⊢
      rw [Fin.sum_univ_castSucc]
      simpa [hh''] using this
  refine ⟨Y', ⟨h'', hw''⟩, ?_, ?_, ?_⟩
  · rw [hY', size_snoc]
    simp only [Multiset.card_singleton]
    omega
  · rw [hY', totalCost_snoc]
    have hk : ∀ k, cost c (Y k) ≤ cost c (X k) := fun k => cost_mono c (hle k)
    have h₀ : cost c (Y k₀) + cost c {y} ≤ cost c (X k₀) := by
      rw [← cost_add]; exact cost_mono c hcons
    simp only [totalCost]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀),
      ← Finset.add_sum_erase _ (fun k => cost c (X k)) (Finset.mem_univ k₀)]
    have := Finset.sum_le_sum fun k (_ : k ∈ univ.erase k₀) => hk k
    omega
  · intro T hT k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · have : load d {y} ≤ load d (X k₀) :=
        load_mono d (Multiset.singleton_le.mpr hyX)
      simpa [hY'] using this.trans (hT k₀)
    · simpa [hY'] using (load_mono d (hle j)).trans (hT j)

/-- **Lemma 4.2 (AP), as in the note**: with `Σ_k |X_k| = 2t − q` and `t ≥ q + 1`, the new
grouping has `2t − q − 1` landings. -/
theorem Admissible.addPlane_of_size {t : ℕ} {X : Groups n q} (hX : Admissible X)
    (hsize : size X = 2 * t - q) (ht : q + 1 ≤ t) (d c : Fin n → ℕ) :
    ∃ Y : Groups n (q + 1), Admissible Y ∧ size Y = 2 * t - (q + 1) ∧
      totalCost c Y ≤ totalCost c X ∧ ∀ T, (∀ k, load d (X k) ≤ T) → ∀ k, load d (Y k) ≤ T := by
  obtain ⟨Y, hY, hs, hc, hl⟩ := hX.addPlane (by omega) d c
  exact ⟨Y, hY, by omega, hc, hl⟩

/-- **Lemma 4.2 applied `m` times**: from `q` planes to `q + m ≤ t` planes, `2t − (q + m)`
landings, no larger cost and no larger largest load. -/
theorem Admissible.addPlanes {t : ℕ} (d c : Fin n → ℕ) : ∀ (m : ℕ) {X : Groups n q},
    Admissible X → size X = 2 * t - q → q + m ≤ t →
    ∃ Y : Groups n (q + m), Admissible Y ∧ size Y = 2 * t - (q + m) ∧
      totalCost c Y ≤ totalCost c X ∧ ∀ T, (∀ k, load d (X k) ≤ T) → ∀ k, load d (Y k) ≤ T
  | 0, X, hX, hsize, _ => ⟨X, hX, hsize, le_rfl, fun _ hT => hT⟩
  | m + 1, X, hX, hsize, hm => by
    obtain ⟨Y, hY, hYs, hYc, hYl⟩ := Admissible.addPlanes d c m hX hsize (by omega)
    obtain ⟨Z, hZ, hZs, hZc, hZl⟩ := hY.addPlane_of_size hYs (by omega) d c
    exact ⟨Z, hZ, hZs, hZc.trans hYc, fun T hT => hZl T (hYl T hT)⟩

end ZenoFront
