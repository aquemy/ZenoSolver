/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SupportBound
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Field.ZMod

/-!
# Minimal parity witnesses (Claim B′, `p − 1` part)

**Claim B′, `p − 1` part.** A parity witness `h` with the fewest edges touches at most `p − 1`
cities.

The note's argument is graph-theoretic: a cycle in the support of `h` can be removed while
keeping every parity, so the support of a minimal `h` is a forest, and a forest whose city
vertices all have degree `≥ 2` has fewer cities than planes. We formalise the same argument in
its linear-algebra form over `ZMod 2`, which Mathlib supports directly:

* every edge `(k, i)` of `h` gives the vector `e_k + e_i` in `ZMod 2 ^ (planes ⊕ touched cities)`;
* if these vectors are linearly dependent, a non-empty set of edges sums to `0`, i.e. every
  vertex meets an even number of them (an "even subgraph", a union of cycles); deleting it keeps
  every parity and gives a witness with fewer edges;
* so the edge vectors of a minimal witness are linearly independent. They all lie in the
  hyperplane `Σ_j x_j = 0`, which misses `e_{k₀}`; adding `e_{k₀}` keeps them independent, so
  `#edges + 1 ≤ p + #touched`;
* every touched city has degree `≥ 2`, so `2 · #touched ≤ #edges`, hence `#touched ≤ p − 1`.

## Main results

* `ZenoFront.IsParityWitness.exists_edgeCount_lt`: a witness whose edge vectors are dependent can
  be replaced by a witness with fewer edges (contained in it).
* `ZenoFront.IsParityWitness.card_touched_le_of_minimal`: a witness with the fewest edges touches
  at most `p − 1` cities.
* `ZenoFront.Admissible.exists_minimal`: an admissible grouping has a witness with the fewest
  edges.
* `ZenoFront.Admissible.exists_card_touched_le`: **Claim B′.** With `Σ_k |X_k| = s`, an admissible
  grouping has a witness touching at most `min(p − 1, t − p)` cities.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- The edges of the `T`-join described by `h`: pairs `(k, i)` with `i ∈ h k`. -/
abbrev WitnessEdge (h : Fin p → Finset (Fin n)) := (k : Fin p) × h k

/-- The vertices that matter for `h`: all planes, and the cities `h` touches. -/
abbrev WitnessVertex (h : Fin p → Finset (Fin n)) := Fin p ⊕ touched h

/-- The incidence vector `e_k + e_i` of the edge `(k, i)`, over `ZMod 2`. -/
def edgeVec (h : Fin p → Finset (Fin n)) (e : WitnessEdge h) : WitnessVertex h → ZMod 2 :=
  Pi.single (Sum.inl e.1) 1 + Pi.single (Sum.inr ⟨e.2.1, mem_touched_of_mem e.2.2⟩) 1

theorem card_witnessEdge (h : Fin p → Finset (Fin n)) :
    Fintype.card (WitnessEdge h) = edgeCount h := by
  simp [WitnessEdge, Fintype.card_sigma, edgeCount]

theorem card_witnessVertex (h : Fin p → Finset (Fin n)) :
    Fintype.card (WitnessVertex h) = p + (touched h).card := by
  simp [WitnessVertex]

/-- The sum of the coordinates, as a linear form. -/
def coordSum (h : Fin p → Finset (Fin n)) : (WitnessVertex h → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ j, x j
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem coordSum_edgeVec (h : Fin p → Finset (Fin n)) (e : WitnessEdge h) :
    coordSum h (edgeVec h e) = 0 := by
  simp only [coordSum, LinearMap.coe_mk, AddHom.coe_mk, edgeVec, Pi.add_apply,
    Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true]
  decide

/-- Linearly independent edge vectors: `#edges + 1 ≤ p + #touched`. The edge vectors lie in the
hyperplane `Σ_j x_j = 0`, so `e_{k₀}` can be added to them. -/
theorem edgeCount_add_one_le_of_linearIndependent {h : Fin p → Finset (Fin n)}
    (hli : LinearIndependent (ZMod 2) (edgeVec h)) (k₀ : Fin p) :
    edgeCount h + 1 ≤ p + (touched h).card := by
  have hspan : Submodule.span (ZMod 2) (Set.range (edgeVec h)) ≤ LinearMap.ker (coordSum h) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun e => coordSum_edgeVec h e
  have hu : (Pi.single (Sum.inl k₀) 1 : WitnessVertex h → ZMod 2) ∉
      Submodule.span (ZMod 2) (Set.range (edgeVec h)) := by
    intro hmem
    have := hspan hmem
    rw [LinearMap.mem_ker] at this
    simp only [coordSum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_pi_single',
      Finset.mem_univ, ite_true] at this
    exact absurd this (by decide)
  have := LinearIndependent.fintype_card_le_finrank (hli.option hu)
  rw [Fintype.card_option, card_witnessEdge, Module.finrank_fintype_fun_eq_card,
    card_witnessVertex] at this
  exact this

/-- Over `ZMod 2`, the number of non-zero terms is the sum, mod 2. -/
private theorem natCast_card_filter_ne_zero {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (#{x ∈ s | f x ≠ 0} : ZMod 2) = ∑ x ∈ s, f x := by
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  generalize f x = y
  revert y
  decide

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

/-- **Cycle removal.** If the edge vectors of a parity witness are linearly dependent, a
non-empty set of edges meets every vertex an even number of times; deleting it gives a parity
witness with fewer edges. -/
theorem exists_edgeCount_lt (hw : IsParityWitness X h)
    (hli : ¬ LinearIndependent (ZMod 2) (edgeVec h)) :
    ∃ h', IsParityWitness X h' ∧ (∀ k, h' k ⊆ h k) ∧ edgeCount h' < edgeCount h := by
  classical
  obtain ⟨g, hrel, e₀, he₀⟩ := Fintype.not_linearIndependent_iff.mp hli
  -- The coefficients of the dependency, as a function of (plane, city).
  set G : Fin p → Fin n → ZMod 2 := fun k i => if hi : i ∈ h k then g ⟨k, ⟨i, hi⟩⟩ else 0
    with hG
  have hG_of_not_mem : ∀ k i, i ∉ h k → G k i = 0 := fun k i hi => by simp [hG, hi]
  have hcoord : ∀ j, ∑ e, g e * edgeVec h e j = 0 := fun j => by
    simpa [Finset.sum_apply] using congrFun hrel j
  -- Plane `k` meets an even number of the deleted edges.
  have hrow : ∀ k, ∑ i ∈ h k, G k i = 0 := fun k => by
    have := hcoord (Sum.inl k)
    simp only [edgeVec, Pi.add_apply, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      add_zero, mul_ite, mul_one, mul_zero, Fintype.sum_sigma] at this
    rw [Fintype.sum_eq_single k fun x hx =>
      Finset.sum_eq_zero fun y _ => ite_eq_right (Ne.symm hx)] at this
    simp only [ite_true] at this
    rw [← this, ← Finset.sum_coe_sort (h k) (G k)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [hG, y.2]
  -- City `i` meets an even number of the deleted edges.
  have hcol : ∀ i, ∑ k, G k i = 0 := fun i => by
    by_cases hi : i ∈ touched h
    · have := hcoord (Sum.inr ⟨i, hi⟩)
      simp only [edgeVec, Pi.add_apply, Pi.single_apply, reduceCtorEq, ite_false, Sum.inr.injEq,
        Subtype.mk.injEq, zero_add, mul_ite, mul_one, mul_zero, Fintype.sum_sigma] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hik : i ∈ h k
      · rw [Fintype.sum_eq_single ⟨i, hik⟩]
        · simp [hG, hik]
        · intro y hy
          have : i ≠ y.1 := fun hiy => hy (Subtype.ext hiy.symm)
          simp [this]
      · rw [hG_of_not_mem k i hik]
        refine (Finset.sum_eq_zero fun y _ => ?_).symm
        have : i ≠ y.1 := fun hiy => hik (hiy ▸ y.2)
        simp [this]
    · refine Finset.sum_eq_zero fun k _ => hG_of_not_mem k i fun hik => hi ?_
      exact mem_touched_of_mem hik
  refine ⟨fun k => (h k).filter fun i => G k i = 0, ⟨fun k => ?_, fun k => ?_, fun i => ?_⟩,
    fun k => Finset.filter_subset _ _, ?_⟩
  · exact (Finset.filter_subset _ _).trans (hw.subset k)
  · -- Row parity: an even number of edges was deleted at plane `k`.
    have hsplit := Finset.card_filter_add_card_filter_not (s := h k) (fun i => G k i = 0)
    have heven : Even #{i ∈ h k | ¬ G k i = 0} := by
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_card_filter_ne_zero, hrow k]
    have := hw.row k
    obtain ⟨r, hr⟩ := heven
    omega
  · -- Column parity: an even number of edges was deleted at city `i`.
    set s : Finset (Fin p) := {k | i ∈ h k} with hs
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun k => G k i = 0)
    have hkept : #{k | i ∈ (h k).filter fun i => G k i = 0} = #{k ∈ s | G k i = 0} := by
      congr 1
      ext k
      simp [hs]
    have heven : Even #{k ∈ s | ¬ G k i = 0} := by
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_card_filter_ne_zero, ← hcol i]
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      exact hG_of_not_mem k i fun hik => hk (by simp [hs, hik])
    have hold := hw.col i
    rw [hkept]
    obtain ⟨r, hr⟩ := heven
    obtain ⟨q, hq⟩ := hold
    rw [← hs] at hq
    exact ⟨q - r, by omega⟩
  · -- At least one edge, `e₀`, was deleted.
    refine Finset.sum_lt_sum (fun k _ => Finset.card_le_card (Finset.filter_subset _ _))
      ⟨e₀.1, Finset.mem_univ _, Finset.card_lt_card ?_⟩
    rw [Finset.filter_ssubset]
    refine ⟨e₀.2.1, e₀.2.2, ?_⟩
    simpa [hG, e₀.2.2] using he₀

/-- **Claim B′, `p − 1` part.** A parity witness with the fewest edges touches at most `p − 1`
cities. -/
theorem card_touched_le_of_minimal (hw : IsParityWitness X h)
    (hmin : ∀ h', IsParityWitness X h' → edgeCount h ≤ edgeCount h') :
    (touched h).card ≤ p - 1 := by
  by_cases hli : LinearIndependent (ZMod 2) (edgeVec h)
  · rcases (touched h).eq_empty_or_nonempty with hC | ⟨i, hi⟩
    · simp [hC]
    · obtain ⟨k₀, -⟩ := mem_touched.mp hi
      have h₁ := edgeCount_add_one_le_of_linearIndependent hli k₀
      have h₂ := hw.two_mul_card_touched_le_edgeCount
      omega
  · obtain ⟨h', hw', -, hlt⟩ := hw.exists_edgeCount_lt hli
    exact absurd (hmin h' hw') (not_le.mpr hlt)

end IsParityWitness

/-- An admissible grouping has a parity witness with the fewest edges. -/
theorem Admissible.exists_minimal {X : Groups n p} (hX : Admissible X) :
    ∃ h, IsParityWitness X h ∧ ∀ h', IsParityWitness X h' → edgeCount h ≤ edgeCount h' := by
  classical
  obtain ⟨h₀, hw₀⟩ := hX
  obtain ⟨h, hmem, hmin⟩ := Finset.exists_min_image
    ((witnessCandidates X).filter (IsParityWitness X)) edgeCount
    ⟨h₀, Finset.mem_filter.mpr ⟨hw₀.mem_witnessCandidates, hw₀⟩⟩
  exact ⟨h, (Finset.mem_filter.mp hmem).2, fun h' hw' =>
    hmin h' (Finset.mem_filter.mpr ⟨hw'.mem_witnessCandidates, hw'⟩)⟩

/-- An admissible grouping has a parity witness touching at most `p − 1` cities. -/
theorem Admissible.exists_card_touched_le_sub_one {X : Groups n p} (hX : Admissible X) :
    ∃ h, IsParityWitness X h ∧ (touched h).card ≤ p - 1 := by
  obtain ⟨h, hw, hmin⟩ := hX.exists_minimal
  exact ⟨h, hw, hw.card_touched_le_of_minimal hmin⟩

/-- **Claim B′.** With `Σ_k |X_k| = s = 2t − p`, an admissible grouping has a parity witness
touching at most `min(p − 1, t − p)` cities (any witness with the fewest edges will do). -/
theorem Admissible.exists_card_touched_le (I : Instance) {X : Groups I.n I.p}
    (hX : Admissible X) (hs : size X = I.s) :
    ∃ h, IsParityWitness X h ∧ (touched h).card ≤ min (I.p - 1) (I.t - I.p) := by
  obtain ⟨h, hw, hmin⟩ := hX.exists_minimal
  exact ⟨h, hw, le_min (hw.card_touched_le_of_minimal hmin) (hw.card_touched_le I hs)⟩

end ZenoFront
