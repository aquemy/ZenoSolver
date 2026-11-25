/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Solver

/-!
# Complexity (§8)

`M(X)` is `minMakespan d p X` (`Achievability.lean`): the least `2 max_k δ(X_k)` over the
admissible partitions of the multiset `X` into `p` groups. Deciding `M(X) ≤ 2T` is strongly
NP-hard, from 3-Partition. This file proves the reduction; the hardness of 3-Partition
(Garey–Johnson) is cited by the note, not formalised.

## Main results

* `admissible_iff_odd_of_disjoint` (**Lemma 2.4, disjoint groups**): if no city lies in two
  groups, a partition is admissible iff every group has an odd number of landings.
* `threePartition_iff` (**Theorem 8.1**): for `a_1, …, a_{3m}`, `B` with `Σ a_i = mB` and
  `B/4 < a_i < B/2`, the instance with durations `a_i` and `p = m` planes (`t = 2m`) has
  `M(X) ≤ 2B`, for `X` every city once, iff the `a_i` split into `m` triples of sum `B`.
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

/-! ### Partitions of a set of cities -/

/-- The partition given by an assignment `g` of every city to a plane: plane `k` lands once at
each city `i` with `g i = k`. -/
def groupsOf (g : Fin n → Fin p) : Groups n p := fun k => ({i | g i = k} : Finset (Fin n)).val

theorem count_landings (X : Groups n p) (i : Fin n) :
    (landings X).count i = ∑ k, (X k).count i := Multiset.count_sum'

theorem count_univ_val (i : Fin n) : (univ.val : Multiset (Fin n)).count i = 1 :=
  Multiset.count_eq_one_of_mem univ.nodup (mem_univ_val i)

/-- Every city is landed at exactly once by `groupsOf g`. -/
theorem landings_groupsOf (g : Fin n → Fin p) : landings (groupsOf g) = univ.val := by
  refine Multiset.ext' fun i => ?_
  rw [count_landings, count_univ_val]
  simp only [groupsOf, Finset.filter_val, Multiset.count_filter, count_univ_val]
  rw [Finset.sum_ite_eq]
  simp

theorem card_groupsOf (g : Fin n → Fin p) (k : Fin p) :
    (groupsOf g k).card = #{i | g i = k} := rfl

theorem load_groupsOf (d : Fin n → ℕ) (g : Fin n → Fin p) (k : Fin p) :
    load d (groupsOf g k) = ∑ i with g i = k, d i := rfl

/-- `groupsOf g` is admissible when every plane gets an odd number of cities (Lemma 2.4). -/
theorem admissible_groupsOf {g : Fin n → Fin p} (hg : ∀ k, Odd #{i | g i = k}) :
    Admissible (groupsOf g) := by
  refine (admissible_iff_odd_of_disjoint fun i k k' hk hk' => ?_).mpr hg
  simp only [groupsOf, Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  exact hk.symm.trans hk'

/-- In a partition of the cities (each landed at once), no city lies in two groups. -/
theorem eq_of_mem_of_landings_eq {X : Groups n p} (hX : landings X = univ.val) {i : Fin n}
    {k k' : Fin p} (hk : i ∈ X k) (hk' : i ∈ X k') : k = k' := by
  by_contra hne
  have h₁ := count_landings X i
  rw [hX, count_univ_val] at h₁
  have h₂ : (X k).count i + (X k').count i ≤ ∑ j, (X j).count i := by
    rw [← Finset.sum_pair (f := fun j => (X j).count i) hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have := Multiset.count_pos.mpr hk
  have := Multiset.count_pos.mpr hk'
  omega

/-- In a partition of the cities, every group lands at most once at each city. -/
theorem nodup_of_landings_eq {X : Groups n p} (hX : landings X = univ.val) (k : Fin p) :
    (X k).Nodup := by
  refine Multiset.nodup_iff_count_le_one.mpr fun i => ?_
  have h₁ := count_landings X i
  rw [hX, count_univ_val] at h₁
  rw [h₁]
  exact Finset.single_le_sum (f := fun j => (X j).count i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ k)

/-- A partition of the cities is the partition of the assignment that sends every city to its
group. -/
theorem exists_eq_groupsOf {X : Groups n p} (hX : landings X = univ.val) :
    ∃ g : Fin n → Fin p, X = groupsOf g := by
  classical
  have hmem : ∀ i : Fin n, ∃ k, i ∈ X k := fun i => by
    have : i ∈ landings X := hX ▸ Finset.mem_univ_val i
    obtain ⟨k, -, hk⟩ := Multiset.mem_sum.mp this
    exact ⟨k, hk⟩
  choose g hg using hmem
  refine ⟨g, funext fun k => ?_⟩
  have hiff : ∀ i, i ∈ X k ↔ g i = k := fun i =>
    ⟨fun hi => eq_of_mem_of_landings_eq hX (hg i) hi, fun h => h ▸ hg i⟩
  rw [← Multiset.dedup_eq_self.mpr (nodup_of_landings_eq hX k)]
  ext i
  simp only [groupsOf, Finset.filter_val, Multiset.count_filter, count_univ_val,
    Multiset.count_dedup, hiff]

theorem load_landings (d : Fin n → ℕ) (X : Groups n p) :
    load d (landings X) = ∑ k, load d (X k) := by
  unfold landings
  induction (Finset.univ : Finset (Fin p)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-! ### `M(X)`, the least makespan of a multiset -/

/-- `M(Y) ≤ 2T` iff some admissible partition of `Y` has all its loads at most `T`, when `Y` has an
admissible partition at all (otherwise `minMakespan` is `0` by convention). -/
theorem minMakespan_le_iff {d : Fin n → ℕ} {Y : Multiset (Fin n)}
    (hY : ∃ X : Groups n p, Admissible X ∧ landings X = Y) (T : ℕ) :
    minMakespan d p Y ≤ 2 * T ↔
      ∃ X : Groups n p, Admissible X ∧ landings X = Y ∧ ∀ k, load d (X k) ≤ T := by
  constructor
  · intro h
    obtain ⟨X, hX, hXY, hm⟩ := Nat.sInf_mem (s := {m | ∃ X : Groups n p, Admissible X ∧
      landings X = Y ∧ 2 * maxLoad d X = m}) (by
        obtain ⟨X, hX, hXY⟩ := hY
        exact ⟨_, X, hX, hXY, rfl⟩)
    refine ⟨X, hX, hXY, fun k => ?_⟩
    have h₁ := load_le_maxLoad d X k
    have h₂ : 2 * maxLoad d X = minMakespan d p Y := hm
    omega
  · rintro ⟨X, hX, hXY, hload⟩
    have h₁ : minMakespan d p Y ≤ 2 * maxLoad d X := Nat.sInf_le ⟨X, hX, hXY, rfl⟩
    have h₂ := (maxLoad_le_iff d X T).mpr hload
    omega

/-! ### Theorem 8.1: the 3-Partition reduction -/

/-- `3m` cities split into `m` triples: city `i` goes to plane `i mod m`, through
`Fin 3 × Fin m ≃ Fin (3m)`. -/
theorem exists_triples (m : ℕ) : ∃ g : Fin (3 * m) → Fin m, ∀ k, #{i | g i = k} = 3 := by
  refine ⟨fun i => (finProdFinEquiv.symm i).2, fun k => ?_⟩
  rw [Finset.card_equiv finProdFinEquiv.symm (t := (univ : Finset (Fin 3)) ×ˢ {k})
    fun i => by simp [eq_comm]]
  simp

/-- **Theorem 8.1 (the 3-Partition reduction).** Let `a_1, …, a_{3m}` and `B` be natural numbers
with `Σ_i a_i = mB` and `B/4 < a_i < B/2` (which make every `a_i`, and `B` when `m ≥ 1`,
positive). In the symmetric instance with one city of duration `a_i` for each `i`, `p = m` planes
(and `t = 2m` passengers, so `s = 3m`), the multiset `X` that lands once at every city has
`M(X) ≤ 2B` iff the `a_i` split into `m` triples of sum `B`, an assignment `g` of the indices to the
triples.

The numbers of the instance are the `a_i`, `B` and `m`, so the reduction preserves strong
NP-hardness (the hardness of 3-Partition is cited, not formalised). -/
theorem threePartition_iff {m B : ℕ} (a : Fin (3 * m) → ℕ) (hsum : ∑ i, a i = m * B)
    (hlo : ∀ i, B < 4 * a i) (hhi : ∀ i, 2 * a i < B) :
    minMakespan a m univ.val ≤ 2 * B ↔
      ∃ g : Fin (3 * m) → Fin m, ∀ k, #{i | g i = k} = 3 ∧ ∑ i with g i = k, a i = B := by
  obtain ⟨g₃, hg₃⟩ := exists_triples m
  rw [minMakespan_le_iff ⟨groupsOf g₃, admissible_groupsOf fun k => by rw [hg₃]; decide,
    landings_groupsOf g₃⟩]
  constructor
  · rintro ⟨X, hX, hXY, hload⟩
    obtain ⟨g, rfl⟩ := exists_eq_groupsOf hXY
    have htot : ∑ k, load a (groupsOf g k) = ∑ _k : Fin m, B := by
      rw [← load_landings, hXY, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, ← hsum]
      rfl
    have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => hload k).mp htot
    refine ⟨g, fun k => ?_⟩
    have hk : ∑ i with g i = k, a i = B := heq k (Finset.mem_univ k)
    refine ⟨?_, hk⟩
    have hne : ({i | g i = k} : Finset (Fin (3 * m))).Nonempty :=
      Finset.card_pos.mp (hX.card_pos k)
    have h₄ : #{i | g i = k} * B < 4 * B := by
      calc #{i | g i = k} * B = ∑ i with g i = k, B := by simp
        _ < ∑ i with g i = k, 4 * a i := Finset.sum_lt_sum_of_nonempty hne fun i _ => hlo i
        _ = 4 * B := by rw [← Finset.mul_sum, hk]
    have h₂ : 2 * B < #{i | g i = k} * B := by
      calc 2 * B = ∑ i with g i = k, 2 * a i := by rw [← Finset.mul_sum, hk]
        _ < ∑ i with g i = k, B := Finset.sum_lt_sum_of_nonempty hne fun i _ => hhi i
        _ = #{i | g i = k} * B := by simp
    have := Nat.lt_of_mul_lt_mul_right h₄
    have := Nat.lt_of_mul_lt_mul_right h₂
    omega
  · rintro ⟨g, hg⟩
    exact ⟨groupsOf g, admissible_groupsOf fun k => by rw [(hg k).1]; decide, landings_groupsOf g,
      fun k => by rw [load_groupsOf, (hg k).2]⟩

/-- The multiset of Theorem 8.1 has `3m = 2t − p` landings, for `t = 2m` and `p = m`. -/
theorem threePartition_card (m : ℕ) :
    (univ.val : Multiset (Fin (3 * m))).card = 2 * (2 * m) - m := by
  rw [Finset.card_val, Finset.card_univ, Fintype.card_fin]
  omega

end ZenoFront
