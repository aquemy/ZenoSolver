/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Solver

/-!
# Complexity (§8): two reductions

`M(X)` is `minMakespan d p X` (`Achievability.lean`): the least `2 max_k δ(X_k)` over the
admissible partitions of the multiset `X` into `p` groups. Deciding `M(X) ≤ 2T` is strongly
NP-hard (from 3-Partition) and stays NP-hard for two planes (from Partition). This file proves the
reductions; the hardness of 3-Partition (Garey–Johnson) and of Partition is cited by the note, not
formalised.

## Main results

* `admissible_iff_odd_of_disjoint` (**Lemma 2.4, disjoint groups**): if no city lies in two
  groups, a partition is admissible iff every group has an odd number of landings.
* `threePartition_iff` (**Theorem 8.1**): for `a_1, …, a_{3m}`, `B` with `Σ a_i = mB` and
  `B/4 < a_i < B/2`, the instance with durations `a_i` and `p = m` planes (`t = 2m`) has
  `M(X) ≤ 2B`, for `X` every city once, iff the `a_i` split into `m` triples of sum `B`.
* `partition_iff` (**Proposition 8.2**, the NP-hard half): for `a_1, …, a_m` with sum `2B`,
  `r ≥ m` odd and `K = B + 1`, the instance with `2r` cities of durations `a_i + K` and `K`
  (`partitionDur`), `p = 2` (`t = r + 1`) has `M(X) ≤ 2(B + rK)` iff some sub-multiset of the
  `a_i` sums to `B`.
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

/-! ### Proposition 8.2: the Partition reduction for two planes -/

/-- The items of the Partition reduction, padded with zeros: `a_i` for `i < m` and `0` for the
other cities. -/
def padItems {m : ℕ} (a : Fin m → ℕ) (N : ℕ) (i : Fin N) : ℕ :=
  if h : i.val < m then a ⟨i, h⟩ else 0

/-- The durations of the Partition reduction: city `i` has duration `a_i + K` if `i < m` and `K`
otherwise. -/
def partitionDur {m : ℕ} (a : Fin m → ℕ) (r K : ℕ) (i : Fin (2 * r)) : ℕ :=
  padItems a (2 * r) i + K

/-- All durations of the Partition reduction are positive. -/
theorem partitionDur_pos {m : ℕ} (a : Fin m → ℕ) (r B : ℕ) (i : Fin (2 * r)) :
    0 < partitionDur a r (B + 1) i := by
  unfold partitionDur
  omega

/-- The padded items of a set of cities sum to the items of the indices it contains. -/
theorem sum_padItems {m N : ℕ} (a : Fin m → ℕ) (hmN : m ≤ N) (Z : Finset (Fin N)) :
    ∑ i ∈ Z, padItems a N i = ∑ j with Fin.castLEEmb hmN j ∈ Z, a j := by
  classical
  have hcast : ∀ j : Fin m, padItems a N (Fin.castLEEmb hmN j) = a j := fun j => by
    simp [padItems, Fin.castLEEmb]
  rw [← Finset.sum_congr rfl fun j _ => hcast j, ← Finset.sum_map _ (Fin.castLEEmb hmN)]
  refine (Finset.sum_subset (fun i hi => ?_) fun i hi hni => ?_).symm
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  · unfold padItems
    split_ifs with h
    · refine absurd (Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        ?_⟩) hni <;> simp [Fin.castLEEmb, hi]
    · rfl

/-- Two planes: the partition into a set `G` of cities and its complement. -/
def halves {N : ℕ} (G : Finset (Fin N)) (i : Fin N) : Fin 2 := if i ∈ G then 0 else 1

theorem filter_halves_zero {N : ℕ} (G : Finset (Fin N)) : ({i | halves G i = 0} : Finset _) = G := by
  ext i
  by_cases hi : i ∈ G <;> simp [halves, hi]

theorem filter_halves_one {N : ℕ} (G : Finset (Fin N)) : ({i | halves G i = 1} : Finset _) = Gᶜ := by
  ext i
  by_cases hi : i ∈ G <;> simp [halves, hi]

/-- Two odd halves are admissible. -/
theorem admissible_halves {r : ℕ} (hr : Odd r) {G : Finset (Fin (2 * r))} (hG : #G = r) :
    Admissible (groupsOf (halves G)) := by
  refine admissible_groupsOf fun k => ?_
  fin_cases k
  · simpa [filter_halves_zero, hG] using hr
  · simp only [Fin.mk_one, filter_halves_one, Finset.card_compl, Fintype.card_fin, hG]
    rwa [show 2 * r - r = r by omega]

/-- **Proposition 8.2 (the Partition reduction for two planes).** Let `a_1, …, a_m` be natural
numbers with sum `2B`, `r ≥ m` odd and `K = B + 1`. In the symmetric instance with `2r` cities,
of durations `a_i + K` for `i ≤ m` and `K` for the other `2r − m` (all positive,
`partitionDur_pos`), `p = 2` planes (and `t = r + 1` passengers, so `s = 2r`), the multiset `X`
that lands once at every city has `M(X) ≤ 2(B + rK)` iff some sub-multiset of the `a_i` sums to
`B`, a set `S` of indices.

The hardness of Partition is cited, not formalised. -/
theorem partition_iff {m r B : ℕ} (a : Fin m → ℕ) (hsum : ∑ i, a i = 2 * B) (hr : Odd r)
    (hmr : m ≤ r) :
    minMakespan (partitionDur a r (B + 1)) 2 univ.val ≤ 2 * (B + r * (B + 1)) ↔
      ∃ S : Finset (Fin m), ∑ i ∈ S, a i = B := by
  classical
  have hm2 : m ≤ 2 * r := by omega
  set K := B + 1 with hK
  set e := partitionDur a r K with he
  have hsumF : ∀ F : Finset (Fin (2 * r)),
      ∑ i ∈ F, e i = ∑ i ∈ F, padItems a (2 * r) i + #F * K := fun F => by
    simp [he, partitionDur, Finset.sum_add_distrib]
  have hall : ∑ i, e i = 2 * B + 2 * r * K := by
    rw [hsumF, sum_padItems a hm2, Finset.card_univ, Fintype.card_fin]
    simp [hsum]
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2 * r)))) (n := r)
    (by simp; omega)
  rw [minMakespan_le_iff ⟨_, admissible_halves hr hG, landings_groupsOf _⟩]
  constructor
  · rintro ⟨X, -, hXY, hload⟩
    obtain ⟨g, rfl⟩ := exists_eq_groupsOf hXY
    set F := ({i | g i = 0} : Finset (Fin (2 * r))) with hF
    have hF1 : ({i | g i = 1} : Finset (Fin (2 * r))) = Fᶜ := by
      ext i
      have : g i = 0 ∨ g i = 1 := by omega
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      omega
    have h₀ := hload 0
    have h₁ := hload 1
    rw [load_groupsOf] at h₀ h₁
    rw [hF1] at h₁
    change ∑ i ∈ F, e i ≤ _ at h₀
    have hsplit := Finset.sum_add_sum_compl F e
    have hc := Finset.card_compl F
    rw [Fintype.card_fin] at hc
    have hcF : #F ≤ 2 * r := (Finset.card_le_univ F).trans (by simp)
    rw [hsumF] at h₀ h₁
    have hlo₀ : #F ≤ r := by
      by_contra hlt
      have := Nat.mul_le_mul_right K (show r + 1 ≤ #F by omega)
      rw [add_mul, one_mul] at this
      omega
    have hlo₁ : #Fᶜ ≤ r := by
      by_contra hlt
      have := Nat.mul_le_mul_right K (show r + 1 ≤ #Fᶜ by omega)
      rw [add_mul, one_mul] at this
      omega
    have hFr : #F = r := by omega
    rw [hsumF, hsumF, hall] at hsplit
    rw [hFr] at h₀ hsplit
    rw [show #Fᶜ = r by omega] at hsplit h₁
    refine ⟨({j | Fin.castLEEmb hm2 j ∈ F} : Finset (Fin m)), ?_⟩
    rw [← sum_padItems a hm2 F]
    have : 2 * r * K = r * K + r * K := by ring
    omega
  · rintro ⟨S, hS⟩
    set ι := Fin.castLEEmb hm2 with hι
    set W : Finset (Fin (2 * r)) := univ \ (univ.map ι \ S.map ι) with hW
    have hSW : S.map ι ⊆ W := fun i hi => by
      simp only [hW, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and, not_not]
      exact fun _ => hi
    have hcardW : r ≤ #W := by
      have h₁ : #(univ.map ι \ S.map ι) = m - #S := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.map_subset_map.mpr
            (Finset.subset_univ S)), Finset.card_map, Finset.card_map, Finset.card_univ,
          Fintype.card_fin]
      have h₂ : #W = 2 * r - (m - #S) := by
        rw [hW, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), h₁,
          Finset.card_univ, Fintype.card_fin]
      have : #S ≤ m := (Finset.card_le_univ S).trans (by simp)
      omega
    have hSr : #(S.map ι) ≤ r := by
      rw [Finset.card_map]
      exact ((Finset.card_le_univ S).trans (by simp)).trans hmr
    obtain ⟨G₀, hSG, hGW, hG₀⟩ := Finset.exists_subsuperset_card_eq hSW hSr hcardW
    refine ⟨_, admissible_halves hr hG₀, landings_groupsOf _, fun k => ?_⟩
    have hpad : ∑ i ∈ G₀, padItems a (2 * r) i = B := by
      rw [sum_padItems a hm2, ← hS]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hj => ?_, fun hj => hSG (Finset.mem_map_of_mem ι hj)⟩
      have := hGW hj
      simp only [hW, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and, not_not] at this
      exact (Finset.mem_map' ι).mp (this (Finset.mem_map_of_mem ι (Finset.mem_univ j)))
    have h₀ : ∑ i ∈ G₀, e i = B + r * K := by rw [hsumF, hpad, hG₀]
    have hsplit := Finset.sum_add_sum_compl G₀ e
    rw [hall, h₀] at hsplit
    fin_cases k
    · simp only [Fin.zero_eta, load_groupsOf, filter_halves_zero]
      omega
    · simp only [Fin.mk_one, load_groupsOf, filter_halves_one]
      have : 2 * r * K = r * K + r * K := by ring
      omega

/-- The multiset of Proposition 8.2 has `2r = 2t − p` landings, for `t = r + 1` and `p = 2`. -/
theorem partition_card (r : ℕ) :
    (univ.val : Multiset (Fin (2 * r))).card = 2 * (r + 1) - 2 := by
  rw [Finset.card_val, Finset.card_univ, Fintype.card_fin]
  omega

end ZenoFront
