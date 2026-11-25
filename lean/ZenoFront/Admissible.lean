/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Model
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset

/-!
# Admissible groupings

A grouping `X_1, …, X_p` is *admissible* (`doc/theory/exact-front.md`, §2) when, in the bipartite
graph `H` joining plane `k` to city `i` whenever `i ∈ X_k`, every connected component contains an
even number of *even planes* (planes with `|X_k|` even). By Lemma 2.4 of the note this is the
same as the existence of a `T`-join of `H`, `T` being the set of even planes.

We take the `T`-join form as the definition (Claim A of the note, §7): a *parity witness* is a
family `h : Fin p → Finset (Fin n)` (the set of `T`-join edges at each plane) with

* `h k ⊆ supp X_k` (only edges of `H`);
* `|h k| ≡ |X_k| + 1 (mod 2)` (even planes have odd degree, odd planes even degree);
* every city `i` lies in an even number of the `h k` (cities have even degree).

The component form of Lemma 2.4 is not formalised yet (see `lean/README.md`).

## Main definitions

* `ZenoFront.IsParityWitness X h`: `h` is a parity witness (a `T`-join) for `X`.
* `ZenoFront.Admissible X`: some parity witness exists. It is decidable, by a finite search over
  the subsets of the supports.

## Main results

* `ZenoFront.IsParityWitness.card_add_one_le`: Lemma 2.5, `|h k| + 1 ≤ |X_k|`.
* `ZenoFront.Admissible.card_pos`: every group of an admissible grouping is non-empty.
* `ZenoFront.IsParityWitness.sum_card_add_le`: `Σ_k |h k| + p ≤ Σ_k |X_k|`.
* `ZenoFront.admissible_iff_exists_natWitness`: Lemma 2.3, the integer form of admissibility.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- `h` is a *parity witness* for the grouping `X` (Claim A of the note): `h k` is a set of
cities of `X k` whose size has the parity of `|X k| + 1`, and every city lies in an even number
of the sets `h k`. Equivalently, `{(k, i) | i ∈ h k}` is a `T`-join of the plane–city graph,
`T` being the set of planes with an even number of landings. -/
structure IsParityWitness (X : Groups n p) (h : Fin p → Finset (Fin n)) : Prop where
  /-- Only edges of the plane–city graph are used. -/
  subset : ∀ k, h k ⊆ (X k).toFinset
  /-- Plane `k` has degree `≡ |X_k| + 1 (mod 2)`. -/
  row : ∀ k, (h k).card % 2 = ((X k).card + 1) % 2
  /-- Every city has even degree. -/
  col : ∀ i, Even #{k | i ∈ h k}

/-- A grouping is *admissible* if it has a parity witness (Claim A of the note, equivalent to
the component condition by Lemma 2.4). -/
def Admissible (X : Groups n p) : Prop := ∃ h, IsParityWitness X h

theorem isParityWitness_iff (X : Groups n p) (h : Fin p → Finset (Fin n)) :
    IsParityWitness X h ↔
      (∀ k, h k ⊆ (X k).toFinset) ∧ (∀ k, (h k).card % 2 = ((X k).card + 1) % 2) ∧
        ∀ i, Even #{k | i ∈ h k} :=
  ⟨fun hw => ⟨hw.subset, hw.row, hw.col⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

instance (X : Groups n p) : DecidablePred (IsParityWitness X) := fun h =>
  decidable_of_iff _ (isParityWitness_iff X h).symm

/-- The search space of the decision procedure: every `h` with `h k ⊆ supp X_k`. -/
def witnessCandidates (X : Groups n p) : Finset (Fin p → Finset (Fin n)) :=
  Fintype.piFinset fun k => (X k).toFinset.powerset

theorem IsParityWitness.mem_witnessCandidates {X : Groups n p} {h : Fin p → Finset (Fin n)}
    (hw : IsParityWitness X h) : h ∈ witnessCandidates X := by
  simpa [witnessCandidates] using hw.subset

theorem admissible_iff_exists_mem_witnessCandidates (X : Groups n p) :
    Admissible X ↔ ∃ h ∈ witnessCandidates X, IsParityWitness X h :=
  ⟨fun ⟨h, hw⟩ => ⟨h, hw.mem_witnessCandidates, hw⟩, fun ⟨h, _, hw⟩ => ⟨h, hw⟩⟩

instance (X : Groups n p) : Decidable (Admissible X) :=
  decidable_of_iff _ (admissible_iff_exists_mem_witnessCandidates X).symm

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

theorem card_le_card_toFinset (hw : IsParityWitness X h) (k : Fin p) :
    (h k).card ≤ (X k).toFinset.card :=
  card_le_card (hw.subset k)

/-- Lemma 2.5 of the note: a plane has `T`-join degree at most `|X_k| − 1`. It holds for every
`T`-join, not only for forests: `|h k| ≤ |supp X_k| ≤ |X_k|`, and equality is excluded by
parity. -/
theorem card_add_one_le (hw : IsParityWitness X h) (k : Fin p) :
    (h k).card + 1 ≤ (X k).card := by
  have h₁ := hw.card_le_card_toFinset k
  have h₂ := Multiset.toFinset_card_le (X k)
  have h₃ := hw.row k
  omega

/-- Summing Lemma 2.5: `Σ_k |h k| + p ≤ Σ_k |X_k|`. -/
theorem sum_card_add_le (hw : IsParityWitness X h) :
    ∑ k, (h k).card + p ≤ size X := by
  have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin p))) => hw.card_add_one_le k
  simpa [size, Finset.sum_add_distrib] using this

end IsParityWitness

/-- Every group of an admissible grouping is non-empty (so the non-emptiness required in the
note's definition is automatic). -/
theorem Admissible.card_pos {X : Groups n p} (hX : Admissible X) (k : Fin p) :
    0 < (X k).card := by
  obtain ⟨h, hw⟩ := hX
  have := hw.card_add_one_le k
  omega

/-- An admissible grouping has at least `p` landings. -/
theorem Admissible.p_le_size {X : Groups n p} (hX : Admissible X) : p ≤ size X := by
  obtain ⟨h, hw⟩ := hX
  have := hw.sum_card_add_le
  omega

/-! ### The integer form (Lemma 2.3) -/

/-- The number of points where `f` is odd has the parity of the sum of `f`. -/
theorem card_filter_odd_mod_two {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    #{x ∈ s | Odd (f x)} % 2 = (∑ x ∈ s, f x) % 2 := by
  have := Finset.even_sum_iff_even_card_odd (s := s) f
  rw [Nat.even_iff, Nat.even_iff] at this
  omega

/-- **Lemma 2.3 (integer form).** A grouping is admissible iff some matrix `w` of naturals has
`w k i ≤ X_k(i)` (the multiplicity of `i` in `X_k`), `Σ_i w k i ≡ |X_k| + 1 (mod 2)` for every
plane `k`, and `Σ_k w k i` even for every city `i`. A parity witness is such a matrix with entries
`0` and `1`; conversely the entries of odd value of a matrix form a parity witness. -/
theorem admissible_iff_exists_natWitness (X : Groups n p) :
    Admissible X ↔ ∃ w : Fin p → Fin n → ℕ, (∀ k i, w k i ≤ (X k).count i) ∧
      (∀ k, (∑ i, w k i) % 2 = ((X k).card + 1) % 2) ∧ ∀ i, Even (∑ k, w k i) := by
  constructor
  · rintro ⟨h, hw⟩
    refine ⟨fun k i => if i ∈ h k then 1 else 0, fun k i => ?_, fun k => ?_, fun i => ?_⟩
    · dsimp only
      split_ifs with hi
      · exact Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp (hw.subset k hi))
      · exact Nat.zero_le _
    · rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact hw.row k
    · rw [← Finset.card_filter]
      exact hw.col i
  · rintro ⟨w, hle, hrow, hcol⟩
    refine ⟨fun k => {i | Odd (w k i)}, fun k i hi => ?_, fun k => ?_, fun i => ?_⟩
    · have hodd : Odd (w k i) := (Finset.mem_filter.mp hi).2
      exact Multiset.mem_toFinset.mpr
        (Multiset.one_le_count_iff_mem.mp (hodd.pos.trans_le (hle k i)))
    · rw [card_filter_odd_mod_two, hrow k]
    · have h₁ : #{k | i ∈ ({j | Odd (w k j)} : Finset (Fin n))} = #{k | Odd (w k i)} := by
        congr 1
        ext k
        simp
      rw [h₁, Nat.even_iff, card_filter_odd_mod_two, ← Nat.even_iff]
      exact hcol i

/-! ### Examples

Cities and planes are numbered from `0`. Each example is checked by the kernel. -/

section Examples

/-- One plane with two landings: a lone even plane is inadmissible. -/
example : ¬ Admissible (n := 2) (p := 1) ![{0, 1}] := by decide

/-- One plane with an odd number of landings is always admissible (`h = ∅`). -/
example : Admissible (n := 2) (p := 1) ![{0, 1, 1}] := by decide

/-- Two even planes with disjoint supports (the situation of the hardness proof, §8): each
component of `H` has one even plane, so the grouping is inadmissible. -/
example : ¬ Admissible (n := 2) (p := 2) ![{0, 0}, {1, 1}] := by decide

/-- The same multiset `{0, 0, 1, 1}` split as two odd groups is admissible. -/
example : Admissible (n := 2) (p := 2) ![{0}, {0, 1, 1}] := by decide

/-- Two even planes sharing city `1` are admissible: link them through `1`. -/
example : Admissible (n := 2) (p := 2) ![{0, 1}, {1, 1}] := by decide

/-- An even plane linked only to an odd plane is inadmissible: its component holds one even
plane. -/
example : ¬ Admissible (n := 2) (p := 2) ![{0, 1}, {0}] := by decide

/-- An empty group is an even plane alone in its component. -/
example : ¬ Admissible (n := 1) (p := 2) ![0, {0}] := by decide

/-- The "pairs are not enough" example of §7: durations `(4, 2, 6, 7)` (cities `0, 1, 2, 3`),
groups `{6, 6}`, `{4, 7}`, `{4, 2, 6}`. The two even planes share no city and are linked through
the odd one, with witness `h = ({2}, {0}, {0, 2})`. -/
example : IsParityWitness (n := 4) (p := 3) ![{2, 2}, {0, 3}, {0, 1, 2}] ![{2}, {0}, {0, 2}] := by
  decide

example : Admissible (n := 4) (p := 3) ![{2, 2}, {0, 3}, {0, 1, 2}] := by decide

end Examples

end ZenoFront
