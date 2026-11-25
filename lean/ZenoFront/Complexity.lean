/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Solver

/-!
# Complexity (§7): two reductions and the step count of the link-forest DP

`M(X)` is `minMakespan d p X` (`Achievability.lean`): the least `2 max_k δ(X_k)` over the
admissible partitions of the multiset `X` into `p` groups. Deciding `M(X) ≤ 2T` is strongly
NP-hard (from 3-Partition) and stays NP-hard for two planes (from Partition), while `E(T)` and
the front are computed by the link-forest DP in a number of steps polynomial in `n`, `t`, `p` and
the level `T`, so in pseudo-polynomial time. This file proves the reductions and the step count.
The hardness of 3-Partition (Garey–Johnson) and of Partition is cited by the note, not formalised.

## Main results

* `admissible_iff_odd_of_disjoint` (**Lemma 2.3, disjoint groups**): if no city lies in two
  groups, a partition is admissible iff every group has an odd number of landings.
* `threePartition_iff` (**Theorem 7.1**): for `a_1, …, a_{3m}`, `B` with `Σ a_i = mB` and
  `B/4 < a_i < B/2`, the instance with durations `a_i` and `p = m` planes (`t = 2m`) has
  `M(X) ≤ 2B`, for `X` every city once, iff the `a_i` split into `m` triples of sum `B`.
* `partition_iff` (**Proposition 7.2**, the NP-hard half): for `a_1, …, a_m` with sum `2B`,
  `r ≥ m` odd and `K = B + 1`, the instance with `2r` cities of durations `a_i + K` and `K`
  (`partitionDur`), `p = 2` (`t = r + 1`) has `M(X) ≤ 2(B + rK)` iff some sub-multiset of the
  `a_i` sums to `B`.
* `treeBoundSteps`, `treeBoundSteps_value`, `treeBoundSteps_le` (**Theorem 7.3 (a)**, the
  complexity clause of Theorem 6.7): the link-forest DP with a step counter returns the value of
  `treeBoundAt` (`E(T)` at every level `T ≤ Tmax`, `treeBoundSteps_eq_minCost`) in at most
  `P(n, t, p, T) = 30 (n + 1)² (p + 1)² (t + 1)² (T + 1)` steps (`stepBound`).
* `scanSteps`, `scanSteps_fst`, `scanSteps_le`, `scanSteps_isParetoFront`
  (**Theorem 7.3 (b)**): scanning the levels `0, …, Tmax = (2t − p) · d_max` with it gives the
  front of the verified solver (the Pareto front under (S) and (A1)) in at most
  `(Tmax + 1) · P(n, t, p, Tmax)` steps, the one-plane table included.

## The cost model

The counted functions (`…C`) are the functions of `TreeBound.lean` and `OnePlane.lean` line for
line, with every loop replaced by a counted loop; each returns its value and its number of steps,
and the value is proved equal to the uncounted one (`TreeData.valueC_fst`, `oneplaneTableC_fst`,
…). A step is:

* one iteration of a minimum loop (`minUpTo`, `minList`, `minFin`), whose body costs its own
  steps on top; the bodies of the innermost loops (table reads, additions, a comparison) cost
  nothing more;
* one table cell (an entry of `Array.ofFn`), on top of the steps of its computation, and one cell
  of the first row of the one-plane table;
* one element scanned by the membership test `b ∈ reps` of the subtree table (`|reps|` steps);
* for the link labels (`repListC`): `n²` steps for the representatives (`domRep` scans the `n`
  cities once per city) and `n²` for one membership test per city in the list of the `n`
  representatives;
* one level of the scan (`scanFrontC`), on top of the steps of the DP at that level.

Constant-time work outside loops (an `if`, the final read of the table) is free. With `R ≤ n`
labels, `S` landings, `P` planes and level `T`, one level takes at most
`7 (P + 1)² (n + 1)² (T + 1) (S + 2)²` steps (`treeBoundSteps_le_levelBound`); with `S = 2t − p`
this is at most `28 (n + 1)² (p + 1)² (t + 1)² (T + 1)`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### Lemma 2.3: disjoint groups -/

/-- **Lemma 2.3 (disjoint groups).** If no city lies in two groups, a partition is admissible iff
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

/-- `groupsOf g` is admissible when every plane gets an odd number of cities (Lemma 2.3). -/
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

/-! ### Theorem 7.1: the 3-Partition reduction -/

/-- `3m` cities split into `m` triples: city `i` goes to plane `i mod m`, through
`Fin 3 × Fin m ≃ Fin (3m)`. -/
theorem exists_triples (m : ℕ) : ∃ g : Fin (3 * m) → Fin m, ∀ k, #{i | g i = k} = 3 := by
  refine ⟨fun i => (finProdFinEquiv.symm i).2, fun k => ?_⟩
  rw [Finset.card_equiv finProdFinEquiv.symm (t := (univ : Finset (Fin 3)) ×ˢ {k})
    fun i => by simp [eq_comm]]
  simp

/-- **Theorem 7.1 (the 3-Partition reduction).** Let `a_1, …, a_{3m}` and `B` be natural numbers
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

/-- The multiset of Theorem 7.1 has `3m = 2t − p` landings, for `t = 2m` and `p = m`. -/
theorem threePartition_card (m : ℕ) :
    (univ.val : Multiset (Fin (3 * m))).card = 2 * (2 * m) - m := by
  rw [Finset.card_val, Finset.card_univ, Fintype.card_fin]
  omega

/-! ### Proposition 7.2: the Partition reduction for two planes -/

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

/-- **Proposition 7.2 (the Partition reduction for two planes).** Let `a_1, …, a_m` be natural
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

/-- The multiset of Proposition 7.2 has `2r = 2t − p` landings, for `t = r + 1` and `p = 2`. -/
theorem partition_card (r : ℕ) :
    (univ.val : Multiset (Fin (2 * r))).card = 2 * (r + 1) - 2 := by
  rw [Finset.card_val, Finset.card_univ, Fintype.card_fin]
  omega

/-! ### Counted loops

A counted computation returns its value and its number of steps. The loops below are the loops of
the tables (`minUpTo`, `minList`, `Array.ofFn`, `buildLayers`) with a counter: an iteration of a
minimum costs one step plus the steps of its body, and a table cell costs one step (its write)
plus the steps of its computation. -/

/-- `minUpToAux` with a step counter. -/
def minUpToCAux (f : ℕ → WithTop ℕ × ℕ) : ℕ → WithTop ℕ × ℕ → WithTop ℕ × ℕ
  | 0, acc => acc
  | u + 1, acc => minUpToCAux f u (min acc.1 (f u).1, acc.2 + (f u).2 + 1)

/-- `minUpTo` with a step counter: `min_{i < u} f i`, one step per iteration plus the body's. -/
def minUpToC (f : ℕ → WithTop ℕ × ℕ) (u : ℕ) : WithTop ℕ × ℕ := minUpToCAux f u (⊤, 0)

theorem minUpToCAux_fst (f : ℕ → WithTop ℕ × ℕ) : ∀ (u : ℕ) (acc : WithTop ℕ × ℕ),
    (minUpToCAux f u acc).1 = minUpToAux (fun i => (f i).1) u acc.1
  | 0, _ => rfl
  | u + 1, acc => by rw [minUpToCAux, minUpToCAux_fst f u]; rfl

theorem minUpToCAux_snd (f : ℕ → WithTop ℕ × ℕ) : ∀ (u : ℕ) (acc : WithTop ℕ × ℕ),
    (minUpToCAux f u acc).2 = acc.2 + ∑ i ∈ range u, ((f i).2 + 1)
  | 0, _ => by simp [minUpToCAux]
  | u + 1, acc => by
    rw [minUpToCAux, minUpToCAux_snd f u, Finset.sum_range_succ]
    simp only
    omega

@[simp] theorem minUpToC_fst (f : ℕ → WithTop ℕ × ℕ) (u : ℕ) :
    (minUpToC f u).1 = minUpTo (fun i => (f i).1) u :=
  minUpToCAux_fst f u _

theorem minUpToC_snd_le {f : ℕ → WithTop ℕ × ℕ} {u B : ℕ} (h : ∀ i < u, (f i).2 + 1 ≤ B) :
    (minUpToC f u).2 ≤ u * B := by
  rw [minUpToC, minUpToCAux_snd, zero_add]
  calc ∑ i ∈ range u, ((f i).2 + 1) ≤ ∑ _i ∈ range u, B :=
        Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi)
    _ = u * B := by simp

/-- `minList` with a step counter. -/
def minListC {β : Type} (l : List β) (f : β → WithTop ℕ × ℕ) : WithTop ℕ × ℕ :=
  l.foldr (fun b acc => (min (f b).1 acc.1, (f b).2 + 1 + acc.2)) (⊤, 0)

@[simp] theorem minListC_fst {β : Type} (f : β → WithTop ℕ × ℕ) :
    ∀ l : List β, (minListC l f).1 = minList l fun b => (f b).1
  | [] => rfl
  | b :: l => by
    change min (f b).1 (minListC l f).1 = min (f b).1 (minList l fun b => (f b).1)
    rw [minListC_fst f l]

theorem minListC_snd_le {β : Type} {f : β → WithTop ℕ × ℕ} {B : ℕ} :
    ∀ {l : List β}, (∀ b ∈ l, (f b).2 + 1 ≤ B) → (minListC l f).2 ≤ l.length * B
  | [], _ => by simp [minListC]
  | b :: l, h => by
    change (f b).2 + 1 + (minListC l f).2 ≤ (l.length + 1) * B
    have := minListC_snd_le fun b' hb' => h b' (List.mem_cons_of_mem b hb')
    have := h b List.mem_cons_self
    rw [add_mul, one_mul]
    omega

/-- `Array.ofFn` with a step counter: one step per cell plus the steps of its computation. -/
def ofFnC {α : Type} {m : ℕ} (f : Fin m → α × ℕ) : Array α × ℕ :=
  (Array.ofFn fun i => (f i).1, ∑ i, ((f i).2 + 1))

@[simp] theorem ofFnC_fst {α : Type} {m : ℕ} (f : Fin m → α × ℕ) :
    (ofFnC f).1 = Array.ofFn fun i => (f i).1 := rfl

theorem ofFnC_snd_le {α : Type} {m : ℕ} {f : Fin m → α × ℕ} {B : ℕ}
    (h : ∀ i, (f i).2 + 1 ≤ B) : (ofFnC f).2 ≤ m * B := by
  calc ∑ i, ((f i).2 + 1) ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => h i
    _ = m * B := by simp

/-- `buildLayers` with a step counter: the steps of every layer. -/
def buildLayersC {α : Type} (f : (ℕ → α) → ℕ → α × ℕ) (dflt : α) : ℕ → Array α × ℕ
  | 0 => (#[(f (fun _ => dflt) 0).1], (f (fun _ => dflt) 0).2)
  | q + 1 =>
    let a := buildLayersC f dflt q
    let r := f (fun i => a.1.getD i dflt) (q + 1)
    (a.1.push r.1, a.2 + r.2)

theorem buildLayersC_fst {α : Type} (f : (ℕ → α) → ℕ → α × ℕ) (dflt : α) :
    ∀ q, (buildLayersC f dflt q).1 = buildLayers (fun look i => (f look i).1) dflt q
  | 0 => rfl
  | q + 1 => by simp only [buildLayersC, buildLayers, buildLayersC_fst f dflt q]

theorem buildLayersC_snd_le {α : Type} (f : (ℕ → α) → ℕ → α × ℕ) (dflt : α) {B : ℕ} :
    ∀ q, (∀ look i, i ≤ q → (f look i).2 ≤ B) → (buildLayersC f dflt q).2 ≤ (q + 1) * B
  | 0, h => by simpa [buildLayersC] using h _ 0 le_rfl
  | q + 1, h => by
    have ih := buildLayersC_snd_le f dflt q fun look i hi => h look i (by omega)
    have := h (fun i => (buildLayersC f dflt q).1.getD i dflt) (q + 1) le_rfl
    simp only [buildLayersC]
    rw [add_mul, one_mul]
    omega

/-- `x ≤ k·y` gives `x + 1 ≤ (k + 1)·y` when `y ≥ 1`: the step that absorbs the cost of an
iteration into one more factor. -/
theorem succ_le_succ_mul {x k y : ℕ} (h : x ≤ k * y) (hy : 1 ≤ y) : x + 1 ≤ (k + 1) * y := by
  rw [add_mul, one_mul]
  omega

theorem minUpToC_succ_le {f : ℕ → WithTop ℕ × ℕ} {u N B : ℕ} (h : ∀ i < u, (f i).2 + 1 ≤ B)
    (hu : u ≤ N) (hB : 1 ≤ B) : (minUpToC f u).2 + 1 ≤ (N + 1) * B :=
  succ_le_succ_mul ((minUpToC_snd_le h).trans (Nat.mul_le_mul_right B hu)) hB

theorem minListC_succ_le {β : Type} {f : β → WithTop ℕ × ℕ} {l : List β} {N B : ℕ}
    (h : ∀ b ∈ l, (f b).2 + 1 ≤ B) (hl : l.length ≤ N) (hB : 1 ≤ B) :
    (minListC l f).2 + 1 ≤ (N + 1) * B :=
  succ_le_succ_mul ((minListC_snd_le h).trans (Nat.mul_le_mul_right B hl)) hB

theorem ofFnC_succ_le {α : Type} {m : ℕ} {f : Fin m → α × ℕ} {B : ℕ} (h : ∀ i, (f i).2 + 1 ≤ B)
    (hB : 1 ≤ B) : (ofFnC f).2 + 1 ≤ (m + 1) * B :=
  succ_le_succ_mul (ofFnC_snd_le h) hB

theorem one_le_of_ne_zero' {x : ℕ} (h : x ≠ 0) : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr h

/-- The innermost loops have bodies of no steps. -/
theorem minUpToC_const_snd_le {g : ℕ → WithTop ℕ} {u : ℕ} :
    (minUpToC (fun i => (g i, 0)) u).2 ≤ u := by
  simpa using minUpToC_snd_le (f := fun i => (g i, 0)) (u := u) (B := 1) fun _ _ => le_rfl

/-! ### The link-forest DP with a step counter

The functions below are those of `TreeBound.lean`, line for line, with each loop replaced by its
counted version. -/

namespace TreeData

variable (D : TreeData n)

/-- `chEntry` with a step counter. -/
def chEntryC (look : ℕ → TLayer) (q τ j : ℕ) : WithTop ℕ × ℕ :=
  if q = 0 then ((if τ = 0 ∧ j = 0 then 0 else ⊤), 0) else
    minUpToC (fun q₁ =>
      let A := (look (q - 1 - q₁)).1
      let B := (look q₁).2
      minListC D.reps fun b =>
        if D.d b ≤ τ then
          let row := A.getD (τ - D.d b) #[]
          let srow := B.getD b #[]
          minUpToC (fun j₁ =>
            (row.getD (j - 1 - j₁) ⊤ + (D.c b : WithTop ℕ) + srow.getD j₁ ⊤, 0)) j
        else (⊤, 0)) q

/-- `subEntry` with a step counter. -/
def subEntryC (ch : Array (Array (WithTop ℕ))) (b : Fin n) (j₁ : ℕ) : WithTop ℕ × ℕ :=
  let r := minUpToC (fun τ =>
    if D.d b + τ ≤ D.T then
      let row := ch.getD τ #[]
      minUpToC (fun j₂ => (if (j₁ - 1 - j₂) % 2 = 1 then
        row.getD j₂ ⊤ + D.G (j₁ - 1 - j₂) (D.T - D.d b - τ) else ⊤, 0)) j₁
    else (⊤, 0)) (D.T + 1)
  ((D.c b : WithTop ℕ) + r.1, r.2)

/-- `chArr` with a step counter. -/
def chArrC (look : ℕ → TLayer) (q : ℕ) : Array (Array (WithTop ℕ)) × ℕ :=
  ofFnC (m := D.T + 1) fun τ => ofFnC (m := D.S + 1) fun j => D.chEntryC look q τ j

/-- `subArr` with a step counter; the membership test `b ∈ reps` scans the list of labels. -/
def subArrC (ch : Array (Array (WithTop ℕ))) : Array (Array (WithTop ℕ)) × ℕ :=
  ofFnC (m := n) fun b =>
    if b ∈ D.reps then
      let r := ofFnC (m := D.S + 1) fun j₁ => D.subEntryC ch b j₁
      (r.1, D.reps.length + r.2)
    else (#[], D.reps.length)

/-- `layer` with a step counter. -/
def layerC (look : ℕ → TLayer) (q : ℕ) : TLayer × ℕ :=
  let ch := D.chArrC look q
  let sb := D.subArrC ch.1
  ((ch.1, sb.1), ch.2 + sb.2)

/-- `layers` with a step counter. -/
def layersC (Q : ℕ) : Array TLayer × ℕ := buildLayersC D.layerC (#[], #[]) Q

/-- `rootEntry` with a step counter. -/
def rootEntryC (ch : Array (Array (WithTop ℕ))) (j : ℕ) : WithTop ℕ × ℕ :=
  minUpToC (fun τ =>
    let row := ch.getD τ #[]
    minUpToC (fun j₂ => (if (j - j₂) % 2 = 1 then row.getD j₂ ⊤ + D.G (j - j₂) (D.T - τ) else ⊤,
      0)) (j + 1)) (D.T + 1)

/-- `roots` with a step counter. -/
def rootsC (L : Array TLayer) (P : ℕ) : Array (Array (WithTop ℕ)) × ℕ :=
  ofFnC (m := P) fun q => ofFnC (m := D.S + 1) fun j => D.rootEntryC (L.getD q (#[], #[])).1 j

/-- `forEntry` with a step counter. -/
def forEntryC (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' J : ℕ) :
    WithTop ℕ × ℕ :=
  if P' = 0 then ((if J = 0 then 0 else ⊤), 0) else
    minUpToC (fun q =>
      let prev := look (P' - 1 - q)
      let rrow := R.getD q #[]
      minUpToC (fun j => (prev.getD (J - j) ⊤ + rrow.getD j ⊤, 0)) (J + 1)) P'

/-- `forLayer` with a step counter. -/
def forLayerC (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' : ℕ) :
    Array (WithTop ℕ) × ℕ :=
  ofFnC (m := D.S + 1) fun J => forEntryC R look P' J

/-- `value` with a step counter: the value of the DP for `P` planes and its number of steps. -/
def valueC (P : ℕ) : WithTop ℕ × ℕ :=
  let L := D.layersC (P - 1)
  let R := D.rootsC L.1 P
  let F := buildLayersC (D.forLayerC R.1) #[] P
  ((F.1.getD P #[]).getD D.S ⊤, L.2 + R.2 + F.2)

/-! #### The counted tables are the tables -/

theorem chEntryC_fst (look : ℕ → TLayer) (q τ j : ℕ) :
    (D.chEntryC look q τ j).1 = D.chEntry look q τ j := by
  unfold chEntryC chEntry
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · rw [ite_eq_right hq, ite_eq_right hq, minUpToC_fst]
    congr 1
    funext q₁
    dsimp only
    rw [minListC_fst]
    congr 1
    funext b
    split_ifs
    · simp
    · rfl

theorem subEntryC_fst (ch : Array (Array (WithTop ℕ))) (b : Fin n) (j₁ : ℕ) :
    (D.subEntryC ch b j₁).1 = D.subEntry ch b j₁ := by
  unfold subEntryC subEntry
  dsimp only
  rw [minUpToC_fst]
  congr 2
  funext τ
  split_ifs
  · simp
  · rfl

theorem chArrC_fst (look : ℕ → TLayer) (q : ℕ) : (D.chArrC look q).1 = D.chArr look q := by
  simp [chArrC, chArr, chEntryC_fst]

theorem subArrC_fst (ch : Array (Array (WithTop ℕ))) : (D.subArrC ch).1 = D.subArr ch := by
  unfold subArrC subArr
  rw [ofFnC_fst]
  congr 1
  funext b
  split_ifs
  · simp [subEntryC_fst]
  · rfl

theorem layerC_fst (look : ℕ → TLayer) (q : ℕ) : (D.layerC look q).1 = D.layer look q := by
  simp [layerC, layer, chArrC_fst, subArrC_fst]

theorem layersC_fst (Q : ℕ) : (D.layersC Q).1 = D.layers Q := by
  rw [layersC, buildLayersC_fst]
  congr 1
  funext look q
  exact D.layerC_fst look q

theorem rootEntryC_fst (ch : Array (Array (WithTop ℕ))) (j : ℕ) :
    (D.rootEntryC ch j).1 = D.rootEntry ch j := by
  simp [rootEntryC, rootEntry]

theorem rootsC_fst (L : Array TLayer) (P : ℕ) : (D.rootsC L P).1 = D.roots L P := by
  simp [rootsC, roots, rootEntryC_fst]

theorem forEntryC_fst (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' J : ℕ) :
    (forEntryC R look P' J).1 = forEntry R look P' J := by
  unfold forEntryC forEntry
  by_cases hP : P' = 0
  · simp only [hP, ite_true]
  · rw [ite_eq_right hP, ite_eq_right hP, minUpToC_fst]
    congr 1
    funext q
    dsimp only
    rw [minUpToC_fst]

theorem forLayerC_fst (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' : ℕ) :
    (D.forLayerC R look P').1 = D.forLayer R look P' := by
  simp [forLayerC, forLayer, forEntryC_fst]

theorem valueC_fst (P : ℕ) : (D.valueC P).1 = D.value P := by
  simp only [valueC, value, layersC_fst, rootsC_fst, buildLayersC_fst]
  congr 4
  funext look P'
  exact D.forLayerC_fst _ look P'

end TreeData

/-! #### The number of steps of each table

Write `R` for the number of labels (`R ≤ n`), `S` for the number of landings, `T` for the level
and `P` for the number of planes. -/

namespace TreeData

variable (D : TreeData n)

theorem chEntryC_snd_le (hR : D.reps.length ≤ n) (look : ℕ → TLayer) (q τ : ℕ) {j : ℕ}
    (hj : j ≤ D.S) : (D.chEntryC look q τ j).2 ≤ q * ((n + 1) * (D.S + 1)) := by
  unfold chEntryC
  by_cases hq : q = 0
  · simp [hq]
  rw [ite_eq_right hq]
  refine minUpToC_snd_le fun q₁ _ => ?_
  dsimp only
  refine minListC_succ_le (fun b _ => ?_) hR (by omega)
  split_ifs
  · have := minUpToC_const_snd_le (g := fun j₁ =>
      (((look (q - 1 - q₁)).1.getD (τ - D.d b) #[]).getD (j - 1 - j₁) ⊤ + (D.c b : WithTop ℕ) +
        (((look q₁).2.getD b #[]).getD j₁ ⊤))) (u := j)
    omega
  · simp

theorem chArrC_snd_le (hR : D.reps.length ≤ n) (look : ℕ → TLayer) (q : ℕ) :
    (D.chArrC look q).2 ≤ (D.T + 1) * ((D.S + 2) * ((q + 1) * ((n + 1) * (D.S + 1)))) := by
  refine ofFnC_snd_le fun τ => ?_
  refine ofFnC_succ_le (fun j => ?_) (one_le_of_ne_zero' (by positivity))
  exact succ_le_succ_mul (D.chEntryC_snd_le hR look q τ (by omega))
    (one_le_of_ne_zero' (by positivity))

theorem subEntryC_snd_le (ch : Array (Array (WithTop ℕ))) (b : Fin n) {j₁ : ℕ} (hj : j₁ ≤ D.S) :
    (D.subEntryC ch b j₁).2 ≤ (D.T + 1) * (D.S + 1) := by
  unfold subEntryC
  dsimp only
  refine minUpToC_snd_le fun τ _ => ?_
  split_ifs
  · have := minUpToC_const_snd_le (g := fun j₂ => if (j₁ - 1 - j₂) % 2 = 1 then
      (ch.getD τ #[]).getD j₂ ⊤ + D.G (j₁ - 1 - j₂) (D.T - D.d b - τ) else ⊤) (u := j₁)
    omega
  · simp

theorem subArrC_snd_le (hR : D.reps.length ≤ n) (ch : Array (Array (WithTop ℕ))) :
    (D.subArrC ch).2 ≤ n * ((n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2))) := by
  refine ofFnC_snd_le fun b => ?_
  have hrow : (ofFnC (m := D.S + 1) fun j₁ => D.subEntryC ch b j₁).2 ≤
      (D.S + 1) * ((D.T + 1) * (D.S + 2)) := by
    refine ofFnC_snd_le fun j₁ => ?_
    have := D.subEntryC_snd_le ch b (j₁ := j₁) (by omega)
    have h : (D.T + 1) * (D.S + 2) = (D.T + 1) * (D.S + 1) + (D.T + 1) := by ring
    omega
  have key : n + 1 + (D.S + 1) * ((D.T + 1) * (D.S + 2)) ≤
      (n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2)) := by
    have h₁ : 0 < (D.T + 1) * (D.S + 2) := by positivity
    have h₂ : (D.S + 1) * ((D.T + 1) * (D.S + 2)) ≤ (n + 1) * ((D.S + 1) * ((D.T + 1) * (D.S + 2))) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h₃ : n + 1 ≤ (n + 1) * ((D.T + 1) * (D.S + 2)) := Nat.le_mul_of_pos_right _ h₁
    have h₄ : (n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2)) =
        (n + 1) * ((D.S + 1) * ((D.T + 1) * (D.S + 2))) + (n + 1) * ((D.T + 1) * (D.S + 2)) := by
      ring
    omega
  split_ifs
  · dsimp only
    omega
  · dsimp only
    have : 0 ≤ (D.S + 1) * ((D.T + 1) * (D.S + 2)) := Nat.zero_le _
    omega

/-- The bound of one level: `(P + 1)² (n + 1)² (T + 1) (S + 2)²`. -/
def levelBound (n P S T : ℕ) : ℕ := (P + 1) ^ 2 * (n + 1) ^ 2 * (T + 1) * (S + 2) ^ 2

theorem layerC_snd_le (hR : D.reps.length ≤ n) {P : ℕ} (look : ℕ → TLayer) {q : ℕ} (hq : q ≤ P) :
    (D.layerC look q).2 ≤ 2 * ((P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2) := by
  have h₁ := D.chArrC_snd_le hR look q
  have h₂ := D.subArrC_snd_le hR (D.chArrC look q).1
  have h₁' : (D.T + 1) * ((D.S + 2) * ((q + 1) * ((n + 1) * (D.S + 1)))) ≤
      (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 := by
    calc (D.T + 1) * ((D.S + 2) * ((q + 1) * ((n + 1) * (D.S + 1))))
        ≤ (D.T + 1) * ((D.S + 2) * ((P + 1) * ((n + 1) ^ 2 * (D.S + 2)))) := by
          gcongr
          · nlinarith
          · omega
      _ = (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 := by ring
  have h₂' : n * ((n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2))) ≤
      (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 := by
    calc n * ((n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2)))
        ≤ (n + 1) * ((n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2))) := by gcongr; omega
      _ ≤ (P + 1) * ((n + 1) * ((n + 1) * ((D.T + 1) * (D.S + 2) * (D.S + 2)))) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 := by ring
  calc (D.layerC look q).2 = (D.chArrC look q).2 + (D.subArrC (D.chArrC look q).1).2 := rfl
    _ ≤ (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 +
        (P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2 :=
        Nat.add_le_add (h₁.trans h₁') (h₂.trans h₂')
    _ = 2 * ((P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2) := by ring

theorem layersC_snd_le (hR : D.reps.length ≤ n) (P : ℕ) :
    (D.layersC (P - 1)).2 ≤ 2 * levelBound n P D.S D.T := by
  have := buildLayersC_snd_le D.layerC (#[], #[]) (P - 1) fun look i hi =>
    D.layerC_snd_le hR (P := P) look (by omega)
  calc (D.layersC (P - 1)).2
      ≤ (P - 1 + 1) * (2 * ((P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2)) := this
    _ ≤ (P + 1) * (2 * ((P + 1) * (n + 1) ^ 2 * (D.T + 1) * (D.S + 2) ^ 2)) := by
        gcongr
        omega
    _ = 2 * levelBound n P D.S D.T := by unfold levelBound; ring

theorem rootEntryC_snd_le (ch : Array (Array (WithTop ℕ))) {j : ℕ} (hj : j ≤ D.S) :
    (D.rootEntryC ch j).2 ≤ (D.T + 1) * (D.S + 2) := by
  refine minUpToC_snd_le fun τ _ => ?_
  have := minUpToC_const_snd_le (g := fun j₂ => if (j - j₂) % 2 = 1 then
    (ch.getD τ #[]).getD j₂ ⊤ + D.G (j - j₂) (D.T - τ) else ⊤) (u := j + 1)
  dsimp only
  omega

theorem rootsC_snd_le (L : Array TLayer) (P : ℕ) :
    (D.rootsC L P).2 ≤ 2 * levelBound n P D.S D.T := by
  have h : (D.rootsC L P).2 ≤ P * ((D.S + 2) * ((D.T + 1) * (D.S + 2) + 1)) := by
    refine ofFnC_snd_le fun q => ?_
    refine ofFnC_succ_le (fun j => ?_) (by omega)
    have := D.rootEntryC_snd_le (L.getD q (#[], #[])).1 (j := j) (by omega)
    omega
  refine h.trans ?_
  have h₁ : (D.T + 1) * (D.S + 2) + 1 ≤ 2 * ((D.T + 1) * (D.S + 2)) := by
    have : 0 < (D.T + 1) * (D.S + 2) := by positivity
    omega
  have hP : P ≤ (P + 1) ^ 2 * (n + 1) ^ 2 :=
    calc P ≤ P + 1 := by omega
      _ ≤ (P + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
      _ ≤ (P + 1) ^ 2 * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  calc P * ((D.S + 2) * ((D.T + 1) * (D.S + 2) + 1))
      ≤ (P + 1) ^ 2 * (n + 1) ^ 2 * ((D.S + 2) * (2 * ((D.T + 1) * (D.S + 2)))) :=
        Nat.mul_le_mul hP (Nat.mul_le_mul_left _ h₁)
    _ = 2 * levelBound n P D.S D.T := by unfold levelBound; ring

theorem forEntryC_snd_le (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ))
    (P' : ℕ) {J S : ℕ} (hJ : J ≤ S) : (forEntryC R look P' J).2 ≤ P' * (S + 2) := by
  unfold forEntryC
  by_cases hP : P' = 0
  · simp [hP]
  rw [ite_eq_right hP]
  refine minUpToC_snd_le fun q _ => ?_
  have := minUpToC_const_snd_le (g := fun j =>
    (look (P' - 1 - q)).getD (J - j) ⊤ + (R.getD q #[]).getD j ⊤) (u := J + 1)
  dsimp only
  omega

theorem forLayersC_snd_le (R : Array (Array (WithTop ℕ))) (P : ℕ) :
    (buildLayersC (D.forLayerC R) #[] P).2 ≤ levelBound n P D.S D.T := by
  have h := buildLayersC_snd_le (D.forLayerC R) #[] (B := (D.S + 1) * ((P + 1) * (D.S + 2))) P
    fun look P' hP' => by
      refine ofFnC_snd_le fun J => ?_
      exact succ_le_succ_mul ((forEntryC_snd_le R look P' (S := D.S) (by omega)).trans
        (Nat.mul_le_mul_right _ (by omega))) (by omega) |>.trans (by gcongr)
  refine h.trans ?_
  calc (P + 1) * ((D.S + 1) * ((P + 1) * (D.S + 2)))
      ≤ (P + 1) * ((D.S + 2) * ((P + 1) * (D.S + 2))) := by gcongr; omega
    _ = (P + 1) ^ 2 * 1 * 1 * (D.S + 2) ^ 2 := by ring
    _ ≤ levelBound n P D.S D.T :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _
          (one_le_of_ne_zero' (by positivity))) (by omega)) le_rfl

/-- **The number of steps of the DP**, given its labels: at most
`5 (P + 1)² (n + 1)² (T + 1) (S + 2)²`. -/
theorem valueC_snd_le (hR : D.reps.length ≤ n) (P : ℕ) :
    (D.valueC P).2 ≤ 5 * levelBound n P D.S D.T := by
  have h₁ := D.layersC_snd_le hR P
  have h₂ := D.rootsC_snd_le (D.layersC (P - 1)).1 P
  have h₃ := D.forLayersC_snd_le (D.rootsC (D.layersC (P - 1)).1 P).1 P
  simp only [valueC]
  omega

end TreeData

/-! ### Theorem 7.3 (a): one level -/

/-- The link labels with a step counter: the representative of every city (`n` scans of the `n`
cities, `domRep`), then one membership test per city in the list of the `n` representatives. It
lists the labels of `repList`. -/
def repListC (d c : Fin n → ℕ) : List (Fin n) × ℕ :=
  let img := (List.finRange n).map (domRep d c)
  ((List.finRange n).filter fun b => decide (b ∈ img), n * n + n * n)

theorem repListC_fst (d c : Fin n → ℕ) : (repListC d c).1 = repList d c := by
  simp only [repListC, repList]
  congr 1
  funext b
  simp [domReps]

theorem length_repList_le (d c : Fin n → ℕ) : (repList d c).length ≤ n :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

/-- **The link-forest DP with a step counter** at level `T`: the value of `treeBoundAt` and the
number of steps spent computing it (the labels, then the DP), in the cost model of this file.
Above `Tmax` there is no table to read and nothing is computed. -/
def treeBoundSteps (d c : Fin n → ℕ) (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (T : ℕ) :
    WithTop ℕ × ℕ :=
  if T ≤ Tmax then
    let R := repListC d c
    let v := TreeData.valueC ⟨d, c, R.1, fun m τ => (table.getD m #[]).getD τ ⊤, T, s⟩ p
    (v.1, R.2 + v.2)
  else (0, 0)

/-- **Theorem 7.3 (a), value.** The counted DP returns the value of `treeBoundAt`. -/
theorem treeBoundSteps_value (d c : Fin n → ℕ) (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ)))
    (T : ℕ) : (treeBoundSteps d c p s Tmax table T).1 = treeBoundAt d c p s Tmax table T := by
  unfold treeBoundSteps treeBoundAt
  split_ifs
  · simp only [repListC_fst]
    exact TreeData.valueC_fst _ p
  · rfl

/-- The value of the counted DP is `E(T)` at every level `T ≤ Tmax` (`treeBoundAt_eq_minCost`). -/
theorem treeBoundSteps_eq_minCost (d c : Fin n → ℕ) {p t Tmax T : ℕ} (hp : 1 ≤ p)
    (hT : T ≤ Tmax) :
    (treeBoundSteps d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T).1 =
      minCost d c t p T := by
  rw [treeBoundSteps_value, treeBoundAt_eq_minCost d c hp hT]

theorem sq_le_levelBound (n P S T : ℕ) : (n + 1) ^ 2 ≤ TreeData.levelBound n P S T := by
  unfold TreeData.levelBound
  calc (n + 1) ^ 2 = 1 * (n + 1) ^ 2 * 1 * 1 := by ring
    _ ≤ (P + 1) ^ 2 * (n + 1) ^ 2 * (T + 1) * (S + 2) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (one_le_of_ne_zero' (by positivity)) le_rfl)
        (by omega)) (one_le_of_ne_zero' (by positivity))

/-- The steps of one level, for any number `s` of landings:
`7 (p + 1)² (n + 1)² (T + 1) (s + 2)²`. -/
theorem treeBoundSteps_le_levelBound (d c : Fin n → ℕ) (p s Tmax : ℕ)
    (table : Array (Array (WithTop ℕ))) (T : ℕ) :
    (treeBoundSteps d c p s Tmax table T).2 ≤ 7 * TreeData.levelBound n p s T := by
  unfold treeBoundSteps
  split_ifs
  · have hR : (repListC d c).1.length ≤ n := by rw [repListC_fst]; exact length_repList_le d c
    have hv := TreeData.valueC_snd_le
      ⟨d, c, (repListC d c).1, fun m τ => (table.getD m #[]).getD τ ⊤, T, s⟩ hR p
    have hsq := sq_le_levelBound n p s T
    have hnn : n * n ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    change n * n + n * n + _ ≤ _
    change _ ≤ 5 * TreeData.levelBound n p s T at hv
    omega
  · exact Nat.zero_le _

/-- The polynomial of Theorem 7.3: `P(n, t, p, T) = 30 (n + 1)² (p + 1)² (t + 1)² (T + 1)`. -/
def stepBound (n t p T : ℕ) : ℕ := 30 * (n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)

theorem levelBound_le (n t p T : ℕ) :
    7 * TreeData.levelBound n p (2 * t - p) T + 2 * (t + 1) * (n + 1) ≤ stepBound n t p T := by
  have h₁ : 7 * TreeData.levelBound n p (2 * t - p) T ≤
      28 * ((n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)) := by
    calc 7 * TreeData.levelBound n p (2 * t - p) T
        ≤ 7 * ((p + 1) ^ 2 * (n + 1) ^ 2 * (T + 1) * (2 * (t + 1)) ^ 2) := by
          unfold TreeData.levelBound
          gcongr
          omega
      _ = 28 * ((n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)) := by ring
  have h₂ : 2 * (t + 1) * (n + 1) ≤ 2 * ((n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)) := by
    calc 2 * (t + 1) * (n + 1) = 2 * ((n + 1) * 1 * (t + 1) * 1) := by ring
      _ ≤ 2 * ((n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)) := by
        gcongr
        · exact Nat.le_self_pow two_ne_zero _
        · exact one_le_of_ne_zero' (by positivity)
        · exact Nat.le_self_pow two_ne_zero _
        · omega
  have h₃ : stepBound n t p T = 30 * ((n + 1) ^ 2 * (p + 1) ^ 2 * (t + 1) ^ 2 * (T + 1)) := by
    unfold stepBound
    ring
  omega

/-- **Theorem 7.3 (a), steps.** At every level, the counted link-forest DP of an instance with
`n` cities, `t` passengers and `p` planes (`s = 2t − p` landings) takes at most
`P(n, t, p, T) = 30 (n + 1)² (p + 1)² (t + 1)² (T + 1)` steps, whatever the one-plane table. -/
theorem treeBoundSteps_le (d c : Fin n → ℕ) (t p Tmax : ℕ) (table : Array (Array (WithTop ℕ)))
    (T : ℕ) : (treeBoundSteps d c p (2 * t - p) Tmax table T).2 ≤ stepBound n t p T :=
  (treeBoundSteps_le_levelBound d c p _ Tmax table T).trans
    ((Nat.le_add_right _ _).trans (levelBound_le n t p T))

/-! ### Theorem 7.3 (b): the scan of every level -/

/-- `minFin` with a step counter. -/
def minFinC (f : Fin n → WithTop ℕ × ℕ) : WithTop ℕ × ℕ :=
  minUpToC (fun i => if h : i < n then f ⟨i, h⟩ else (⊤, 0)) n

theorem minFinC_fst (f : Fin n → WithTop ℕ × ℕ) : (minFinC f).1 = minFin fun i => (f i).1 := by
  simp only [minFinC, minFin, minUpToC_fst]
  congr 1
  funext i
  split_ifs <;> rfl

/-- `oneplaneNextRow` with a step counter. -/
def oneplaneNextRowC (d c : Fin n → ℕ) (Tmax : ℕ) (row : Array (WithTop ℕ)) :
    Array (WithTop ℕ) × ℕ :=
  ofFnC (m := Tmax + 1) fun T =>
    minFinC fun i => (if d i ≤ (T : ℕ) then (c i : WithTop ℕ) + row.getD (T - d i) ⊤ else ⊤, 0)

/-- `oneplaneTable` with a step counter; the first row costs one step per cell. -/
def oneplaneTableC (d c : Fin n → ℕ) (Tmax : ℕ) : ℕ → Array (Array (WithTop ℕ)) × ℕ
  | 0 => (#[oneplaneRow d c Tmax 0], Tmax + 1)
  | m + 1 =>
    let t := oneplaneTableC d c Tmax m
    let r := oneplaneNextRowC d c Tmax (t.1.back?.getD #[])
    (t.1.push r.1, t.2 + r.2)

theorem oneplaneNextRowC_fst (d c : Fin n → ℕ) (Tmax : ℕ) (row : Array (WithTop ℕ)) :
    (oneplaneNextRowC d c Tmax row).1 = oneplaneNextRow d c Tmax row := by
  simp only [oneplaneNextRowC, oneplaneNextRow, ofFnC_fst, minFinC_fst]

theorem oneplaneTableC_fst (d c : Fin n → ℕ) (Tmax : ℕ) :
    ∀ m, (oneplaneTableC d c Tmax m).1 = oneplaneTable d c Tmax m
  | 0 => rfl
  | m + 1 => by
    simp only [oneplaneTableC, oneplaneTable, oneplaneTableC_fst d c Tmax m, oneplaneNextRowC_fst]

theorem oneplaneNextRowC_snd_le (d c : Fin n → ℕ) (Tmax : ℕ) (row : Array (WithTop ℕ)) :
    (oneplaneNextRowC d c Tmax row).2 ≤ (Tmax + 1) * (n + 1) := by
  refine ofFnC_snd_le fun T => ?_
  have : (minFinC fun i => ((if d i ≤ (T : ℕ) then (c i : WithTop ℕ) + row.getD (T - d i) ⊤
      else ⊤), 0)).2 ≤ n * 1 := by
    refine minUpToC_snd_le fun i _ => ?_
    split_ifs
    simp
  omega

theorem oneplaneTableC_snd_le (d c : Fin n → ℕ) (Tmax : ℕ) :
    ∀ m, (oneplaneTableC d c Tmax m).2 ≤ (m + 1) * ((Tmax + 1) * (n + 1))
  | 0 => by
    change Tmax + 1 ≤ _
    rw [zero_add, one_mul]
    exact Nat.le_mul_of_pos_right _ (by omega)
  | m + 1 => by
    have ih := oneplaneTableC_snd_le d c Tmax m
    have := oneplaneNextRowC_snd_le d c Tmax ((oneplaneTableC d c Tmax m).1.back?.getD #[])
    simp only [oneplaneTableC]
    rw [add_mul, one_mul]
    omega

/-- `scanFront` with a step counter: each level costs one step plus the steps of computing `E` at
it. -/
def scanFrontC (E : ℕ → WithTop ℕ × ℕ) : ℕ → ℕ → WithTop ℕ → List (ℕ × ℕ) × ℕ
  | _, 0, _ => ([], 0)
  | T, k + 1, prev =>
    if (E T).1 < prev then
      let r := scanFrontC E (T + 1) k (E T).1
      (((E T).1.untopD 0, 2 * T) :: r.1, (E T).2 + 1 + r.2)
    else
      let r := scanFrontC E (T + 1) k prev
      (r.1, (E T).2 + 1 + r.2)

theorem scanFrontC_fst (E : ℕ → WithTop ℕ × ℕ) : ∀ (T k : ℕ) (prev : WithTop ℕ),
    (scanFrontC E T k prev).1 = scanFront (fun T => (E T).1) T k prev
  | _, 0, _ => rfl
  | T, k + 1, prev => by
    simp only [scanFrontC, scanFront]
    split_ifs <;> simp [scanFrontC_fst E (T + 1) k]

theorem scanFrontC_snd_le (E : ℕ → WithTop ℕ × ℕ) {B : ℕ} : ∀ (T k : ℕ) (prev : WithTop ℕ),
    (∀ T', T ≤ T' → T' < T + k → (E T').2 + 1 ≤ B) → (scanFrontC E T k prev).2 ≤ k * B
  | _, 0, _, _ => by simp [scanFrontC]
  | T, k + 1, prev, h => by
    have h₀ := h T le_rfl (by omega)
    have ih₁ := scanFrontC_snd_le E (T + 1) k (E T).1 fun T' h₁ h₂ => h T' (by omega) (by omega)
    have ih₂ := scanFrontC_snd_le E (T + 1) k prev fun T' h₁ h₂ => h T' (by omega) (by omega)
    simp only [scanFrontC]
    rw [add_mul, one_mul]
    split_ifs
    · dsimp only
      omega
    · dsimp only
      omega

/-- **The front by scanning every level, with a step counter.** The one-plane table is built once
for the levels `0, …, Tmax = (2t − p) · d_max`; then the counted link-forest DP runs at every level
and the scan keeps the levels where `E` drops. -/
def scanSteps (d c : Fin n → ℕ) (t p : ℕ) : List (ℕ × ℕ) × ℕ :=
  let s := 2 * t - p
  let Tmax := s * maxDur d
  let G := oneplaneTableC d c Tmax s
  let r := scanFrontC (fun T => treeBoundSteps d c p s Tmax G.1 T) 0 (Tmax + 1) ⊤
  (r.1, G.2 + r.2)

/-- **Theorem 7.3 (b), value.** With `1 ≤ p ≤ t`, the scan returns the front of the verified
solver (`solveFront_eq`): the breakpoints of `E`, which under (S) and (A1) are the Pareto front
(`scanSteps_isParetoFront`). -/
theorem scanSteps_fst (d c : Fin n → ℕ) {t p : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t) :
    (scanSteps d c t p).1 = solveFront d c t p := by
  rw [solveFront_eq d c hp hpt]
  simp only [scanSteps, scanFrontC_fst, oneplaneTableC_fst]
  refine scanFront_congr 0 _ ⊤ fun T _ hT => ?_
  exact treeBoundSteps_eq_minCost d c hp (by omega)

/-- **Theorem 7.3 (b), steps.** The scan of the levels `0, …, (2t − p) · d_max` takes at most
`((2t − p) · d_max + 1) · P(n, t, p, (2t − p) · d_max)` steps, the one-plane table included. -/
theorem scanSteps_le (d c : Fin n → ℕ) (t p : ℕ) :
    (scanSteps d c t p).2 ≤
      ((2 * t - p) * maxDur d + 1) * stepBound n t p ((2 * t - p) * maxDur d) := by
  set Tmax := (2 * t - p) * maxDur d with hTmax
  have hG := oneplaneTableC_snd_le d c Tmax (2 * t - p)
  have hscan := scanFrontC_snd_le (fun T => treeBoundSteps d c p (2 * t - p) Tmax
      (oneplaneTableC d c Tmax (2 * t - p)).1 T)
    (B := 7 * TreeData.levelBound n p (2 * t - p) Tmax + 1) 0 (Tmax + 1) ⊤ fun T _ hT => by
      have := treeBoundSteps_le_levelBound d c p (2 * t - p) Tmax
        (oneplaneTableC d c Tmax (2 * t - p)).1 T
      have hmono : TreeData.levelBound n p (2 * t - p) T ≤
          TreeData.levelBound n p (2 * t - p) Tmax := by
        unfold TreeData.levelBound
        gcongr
        omega
      omega
  have hb := levelBound_le n t p Tmax
  have hG' : (2 * t - p + 1) * ((Tmax + 1) * (n + 1)) + (Tmax + 1) ≤
      (Tmax + 1) * (2 * (t + 1) * (n + 1)) := by
    have : 2 * t - p + 1 ≤ 2 * t + 1 := by omega
    calc (2 * t - p + 1) * ((Tmax + 1) * (n + 1)) + (Tmax + 1)
        ≤ (2 * t + 1) * ((Tmax + 1) * (n + 1)) + (Tmax + 1) * (n + 1) := by
          gcongr
          exact Nat.le_mul_of_pos_right _ (by omega)
      _ = (Tmax + 1) * (2 * (t + 1) * (n + 1)) := by ring
  change (oneplaneTableC d c Tmax (2 * t - p)).2 + (scanFrontC _ 0 (Tmax + 1) ⊤).2 ≤ _
  calc (oneplaneTableC d c Tmax (2 * t - p)).2 + (scanFrontC (fun T => treeBoundSteps d c p
          (2 * t - p) Tmax (oneplaneTableC d c Tmax (2 * t - p)).1 T) 0 (Tmax + 1) ⊤).2
      ≤ (2 * t - p + 1) * ((Tmax + 1) * (n + 1)) +
          (Tmax + 1) * (7 * TreeData.levelBound n p (2 * t - p) Tmax + 1) :=
        Nat.add_le_add hG hscan
    _ = (2 * t - p + 1) * ((Tmax + 1) * (n + 1)) + (Tmax + 1) +
          (Tmax + 1) * (7 * TreeData.levelBound n p (2 * t - p) Tmax) := by ring
    _ ≤ (Tmax + 1) * (2 * (t + 1) * (n + 1)) +
          (Tmax + 1) * (7 * TreeData.levelBound n p (2 * t - p) Tmax) := by gcongr
    _ = (Tmax + 1) * (7 * TreeData.levelBound n p (2 * t - p) Tmax + 2 * (t + 1) * (n + 1)) := by
        ring
    _ ≤ (Tmax + 1) * stepBound n t p Tmax := Nat.mul_le_mul_left _ hb

/-- **The scan gives the front.** Under (S) and (A1), with `1 ≤ p ≤ t`, the list computed by the
counted scan is the Pareto front of the feasible plans. -/
theorem scanSteps_isParetoFront {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1) (c : Fin n → ℕ)
    {t p : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t) :
    IsParetoFront (achievable N c t p) (scanSteps N.d c t p).1 := by
  rw [scanSteps_fst N.d c hp hpt]
  exact solveFront_isParetoFront hS hA1 c hp hpt

end ZenoFront
