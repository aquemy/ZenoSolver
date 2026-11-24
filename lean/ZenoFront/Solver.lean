/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Achievability
public import ZenoFront.AdmissibleBound

/-!
# A verified solver for the symmetric front

`solveFront d c t p` computes the Pareto front of a symmetric instance with no certificate, and
`solveFront_isParetoFront` proves that, under (S) and (A1) with `1 ≤ p ≤ t`, its output is exactly
the front of the feasible plans. `lake exe zeno-front FILE` runs it (`ZenoFrontMain.lean`).

* **`E(T)`** (`minCost`): the least cost of an admissible partition of `2t − p` landings into
  `p` groups with all loads `≤ T`. It is non-increasing (`minCost_antitone`) and attained when
  finite (`minCost_attained`).
* **The σ-DP is exact** (`sigmaBoundAt_eq_minCost`). The checker's σ-DP is a lower bound on
  `E(T)` (`sigmaBoundAt_le_totalCost`). Conversely, every finite value of the DP is the cost of
  the groups it chooses (`sigmaDP_attained`): each plane takes its witness set `H` and the
  cheapest other landings of the one-plane table (`groupOption_attained`), and the running
  symmetric differences ending at `∅` make the witness sets a parity witness
  (`isParityWitness_of_list`). No link forest is needed.
* **The front from `E`** (`minimal_admissiblePoints_iff`): `(C, 2T)` is a minimal admissible
  point iff `E(T) = C` and `E(T') > C` for every `T' < T`. Such a breakpoint has
  `T ≤ (2t − p) · d_max` (`breakpoint_le`), so the solver scans the levels `0, …, (2t − p) · d_max`
  and keeps `(E(T), 2T)` whenever `E` drops (`scanFront`, `mem_scanFront`). Corollary 4.8
  (`minimal_achievable_iff_admissiblePoints`) turns the minimal admissible points into the front.

The tables that do not depend on the level (the subsets of non-dominated cities, their
symmetric differences, and the one-plane table) are computed once (`sigmaAt`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### `E(T)` -/

/-- `E(T)`: the least cost of an admissible partition of `2t − p` landings into `p` groups whose
loads are all at most `T` (`⊤` if there is none). -/
noncomputable def minCost (d c : Fin n → ℕ) (t p T : ℕ) : WithTop ℕ :=
  sInf {x | ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧ (∀ k, load d (X k) ≤ T) ∧
    (totalCost c X : WithTop ℕ) = x}

theorem minCost_le (d c : Fin n → ℕ) {t T : ℕ} {X : Groups n p} (hX : Admissible X)
    (hsize : size X = 2 * t - p) (hT : ∀ k, load d (X k) ≤ T) :
    minCost d c t p T ≤ totalCost c X :=
  sInf_le ⟨X, hX, hsize, hT, rfl⟩

/-- `E(T)` is attained when it is finite. -/
theorem minCost_attained (d c : Fin n → ℕ) {t T C : ℕ} (h : minCost d c t p T = C) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧ (∀ k, load d (X k) ≤ T) ∧
      totalCost c X = C := by
  set S : Set (WithTop ℕ) := {x | ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
    (∀ k, load d (X k) ≤ T) ∧ (totalCost c X : WithTop ℕ) = x} with hS
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : minCost d c t p T = ⊤ := by
      change sInf S = ⊤
      rw [hne, sInf_empty]
    rw [this] at h
    exact WithTop.top_ne_coe h
  obtain ⟨X, hX, hsize, hT, hcost⟩ := csInf_mem hne
  refine ⟨X, hX, hsize, hT, ?_⟩
  have : (totalCost c X : WithTop ℕ) = C := hcost.trans h
  exact WithTop.coe_injective this

/-- `E` is non-increasing. -/
theorem minCost_antitone (d c : Fin n → ℕ) (t p : ℕ) : Antitone (minCost d c t p) :=
  fun _ _ hTT' => sInf_le_sInf fun _ ⟨X, hX, hsize, hT, hx⟩ =>
    ⟨X, hX, hsize, fun k => (hT k).trans hTT', hx⟩

/-! ### The σ-DP is attained -/

theorem exists_mem_eq_of_inf_eq {ι : Type*} (s : Finset ι) (f : ι → WithTop ℕ) {v : ℕ}
    (h : s.inf f = v) : ∃ i ∈ s, f i = v := by
  have hne : s.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    subst h'
    exact WithTop.top_ne_coe h
  obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf s hne f
  exact ⟨i, hi, hfi ▸ h⟩

/-- **The σ-DP is attained.** If every finite plane option `opt m H = w` is the cost `w` of a
group `Y` of `m` landings with `Q Y H`, every finite value of the σ-DP is the total cost of a
list of such groups, of the right number and size, whose witness sets have symmetric
difference `σ`. -/
theorem sigmaDP_attained (S : Finset (Finset (Fin n))) (opt : ℕ → Finset (Fin n) → WithTop ℕ)
    (Q : Multiset (Fin n) → Finset (Fin n) → Prop) (w : Multiset (Fin n) → ℕ)
    (hopt : ∀ m H (v : ℕ), opt m H = v → ∃ Y : Multiset (Fin n), Y.card = m ∧ Q Y H ∧ w Y = v) :
    ∀ (j u : ℕ) (σ : Finset (Fin n)) (v : ℕ), sigmaDP S opt j u σ = v →
      ∃ L : List (Multiset (Fin n) × Finset (Fin n)), L.length = j ∧
        (L.map fun yh => yh.1.card).sum = u ∧ L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ = σ ∧
        (∀ yh ∈ L, Q yh.1 yh.2) ∧ (L.map fun yh => w yh.1).sum = v
  | 0, u, σ, v, h => by
    simp only [sigmaDP] at h
    split_ifs at h with hc
    · obtain ⟨rfl, rfl⟩ := hc
      exact ⟨[], rfl, rfl, rfl, by simp, by simpa using WithTop.coe_injective h⟩
    · exact absurd h WithTop.top_ne_coe
  | j + 1, u, σ, v, h => by
    simp only [sigmaDP] at h
    obtain ⟨m, hm, hm'⟩ := exists_mem_eq_of_inf_eq _ _ h
    obtain ⟨H, -, hH⟩ := exists_mem_eq_of_inf_eq _ _ hm'
    rw [Finset.mem_range] at hm
    split_ifs at hH with hS
    · obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.mp hH
      obtain ⟨L, hlen, hsum, hfold, hQ, hw⟩ :=
        sigmaDP_attained S opt Q w hopt j (u - (m + 1)) (symmDiff σ H) a ha.symm
      obtain ⟨Y, hY, hQY, hwY⟩ := hopt (m + 1) H b hb.symm
      refine ⟨(Y, H) :: L, by simp [hlen], ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, hY, hsum]
        omega
      · rw [List.foldr_cons, hfold, symmDiff_comm σ H, symmDiff_symmDiff_cancel_left]
      · intro yh hyh
        rcases List.mem_cons.mp hyh with rfl | hyh
        · exact hQY
        · exact hQ yh hyh
      · have hab' : a + b = v := by exact_mod_cast hab
        simp only [List.map_cons, List.sum_cons, hwY, hw]
        omega
    · exact absurd hH WithTop.top_ne_coe

/-- A finite plane option is a group: `H` plus the cheapest `m − |H|` landings of the one-plane
table. -/
theorem groupOption_attained (d c : Fin n → ℕ) (T m : ℕ) (H : Finset (Fin n)) (v : ℕ)
    (h : groupOption d c (oneplane d c) T m H = v) :
    ∃ Y : Multiset (Fin n), Y.card = m ∧
      (H.val ≤ Y ∧ H.card % 2 = (Y.card + 1) % 2 ∧ load d Y ≤ T) ∧ cost c Y = v := by
  unfold groupOption at h
  split_ifs at h with hc
  · obtain ⟨hcard, hpar, hload⟩ := hc
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.mp h
    have hne : oneplane d c (m - H.card) (T - load d H.val) ≠ ⊤ := by
      rw [← hb]
      exact WithTop.coe_ne_top
    obtain ⟨Z, hZ, hZload, hZcost⟩ := exists_cost_eq_oneplane hne
    have hb' : cost c Z = b := by
      rw [hZcost] at hb
      exact (WithTop.coe_injective hb).symm
    have ha' : cost c H.val = a := (WithTop.coe_injective ha).symm
    have hab' : a + b = v := by exact_mod_cast hab
    refine ⟨H.val + Z, ?_, ⟨Multiset.le_add_right _ _, ?_, ?_⟩, ?_⟩
    · rw [Multiset.card_add, Finset.card_val, hZ]
      omega
    · rw [Multiset.card_add, Finset.card_val, hZ, show H.card + (m - H.card) = m by omega]
      exact hpar
    · rw [load_add]
      omega
    · rw [cost_add, ha', hb', hab']
  · exact absurd h WithTop.top_ne_coe

/-- The groups and witness sets of a list of length `p`, as functions of the planes. -/
theorem isParityWitness_of_list (L : List (Multiset (Fin n) × Finset (Fin n))) (hlen : L.length = p)
    (hQ : ∀ yh ∈ L, yh.2.val ≤ yh.1 ∧ yh.2.card % 2 = (yh.1.card + 1) % 2)
    (hfold : L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ = ∅) :
    IsParityWitness (fun k : Fin p => (L.getD k (0, ∅)).1) (fun k => (L.getD k (0, ∅)).2) := by
  classical
  have hL : (List.finRange p).map (fun k : Fin p => L.getD k (0, ∅)) = L :=
    map_finRange_getD L (0, ∅) hlen
  have hmem : ∀ k : Fin p, L.getD k (0, ∅) ∈ L := fun k => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  refine ⟨fun k i hi => ?_, fun k => (hQ _ (hmem k)).2, fun i => ?_⟩
  · have := Multiset.mem_of_le (hQ _ (hmem k)).1 (Finset.mem_val.mpr hi)
    exact Multiset.mem_toFinset.mpr this
  · have h₁ : i ∉ L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ := by rw [hfold]; simp
    rw [show L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ = (L.map Prod.snd).foldr
        (fun H σ => symmDiff H σ) ∅ by rw [List.foldr_map]] at h₁
    rw [mem_foldr_symmDiff, ← hL, List.map_map, List.countP_map, countP_finRange] at h₁
    simp only [Function.comp_def, decide_eq_true_eq] at h₁
    exact Nat.even_iff.mpr (by omega)

/-- **The σ-DP is exact.** At a level `T ≤ Tmax`, with `1 ≤ p ≤ t`, the bound the checker
computes (`sigmaBoundAt`) is `E(T)`: it is at most the cost of every admissible partition
(`sigmaBoundAt_le_totalCost`), and every finite value is the cost of one. -/
theorem sigmaBoundAt_eq_minCost (d c : Fin n → ℕ) {t Tmax T : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t)
    (hT : T ≤ Tmax) :
    sigmaBoundAt d c p t (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T =
      minCost d c t p T := by
  apply le_antisymm
  · exact le_sInf fun x ⟨X, hX, hsize, hload, hx⟩ =>
      hx ▸ sigmaBoundAt_le_totalCost d c hp hpt hX hsize hload
  · -- Every finite value is attained.
    generalize hv : sigmaBoundAt d c p t (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T
      = v
    cases v using WithTop.recTopCoe with
    | top => exact le_top
    | coe v =>
      unfold sigmaBoundAt at hv
      simp only [hT, ↓reduceIte] at hv
      set subs := smallSubsetList (domReps d c) (min (p - 1) (t - p))
      rw [sigmaValue_eq subs _ _ p (mem_smallSubsetList.mpr ⟨Finset.empty_subset _,
        Nat.zero_le _⟩)] at hv
      rw [sigmaDP_congr subs.toFinset (opt' := groupOption d c (oneplane d c) T) p (2 * t - p) ∅
        fun m H _ hm => by
          unfold groupOption
          split_ifs with hc
          · dsimp only
            rw [oneplaneTable_getD d c (by omega) (by omega)]
          · rfl] at hv
      obtain ⟨L, hlen, hsum, hfold, hQ, hcost⟩ := sigmaDP_attained subs.toFinset
        (groupOption d c (oneplane d c) T)
        (fun Y H => H.val ≤ Y ∧ H.card % 2 = (Y.card + 1) % 2 ∧ load d Y ≤ T) (cost c)
        (groupOption_attained d c T) p (2 * t - p) ∅ v hv
      have hw := isParityWitness_of_list L hlen (fun yh hyh => ⟨(hQ yh hyh).1, (hQ yh hyh).2.1⟩)
        hfold
      have hL : (List.finRange p).map (fun k : Fin p => L.getD k (0, ∅)) = L :=
        map_finRange_getD L (0, ∅) hlen
      have hmem : ∀ k : Fin p, L.getD k (0, ∅) ∈ L := fun k => by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      refine (minCost_le d c ⟨_, hw⟩ ?_ fun k => (hQ _ (hmem k)).2.2).trans (le_of_eq ?_)
      · rw [size, Fin.sum_univ_def, ← hsum]
        conv_rhs => rw [← hL]
        rw [List.map_map]
        rfl
      · rw [totalCost, Fin.sum_univ_def, ← hcost]
        conv_rhs => rw [← hL]
        rw [List.map_map]
        rfl

/-! ### The front from `E` -/

/-- `E(T) ≤ C` iff some admissible partition of `2t − p` landings with loads at most `T` costs at
most `C`. -/
theorem minCost_le_coe_iff (d c : Fin n → ℕ) {t T C : ℕ} :
    minCost d c t p T ≤ C ↔ ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, load d (X k) ≤ T) ∧ totalCost c X ≤ C := by
  constructor
  · intro h
    obtain ⟨C', hC'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    obtain ⟨X, hX, hsize, hload, hcost⟩ := minCost_attained d c hC'.symm
    refine ⟨X, hX, hsize, hload, ?_⟩
    rw [hcost]
    exact WithTop.coe_le_coe.mp (hC' ▸ h)
  · rintro ⟨X, hX, hsize, hload, hcost⟩
    exact (minCost_le d c hX hsize hload).trans (WithTop.coe_le_coe.mpr hcost)

/-- **The minimal admissible points**: `(C, M)` is minimal iff `M = 2T` with `E(T) = C` and
`E(T') > C` for every `T' < T` (the breakpoints of `E`). -/
theorem minimal_admissiblePoints_iff (N : Network n) (c : Fin n → ℕ) {t : ℕ} (C M : ℕ) :
    Minimal (· ∈ admissiblePoints N c t p) (C, M) ↔
      ∃ T, M = 2 * T ∧ minCost N.d c t p T = C ∧
        ∀ T' < T, (C : WithTop ℕ) < minCost N.d c t p T' := by
  constructor
  · rintro ⟨⟨X, hX, hsize, hx⟩, hmin⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hC, hM⟩ := hx
    have hload : ∀ k, load N.d (X k) ≤ maxLoad N.d X := load_le_maxLoad N.d X
    -- Any partition `X'` with loads at most `T'` and cost at most `C` gives a point below.
    have hbelow : ∀ {T' C'}, (∃ X' : Groups n p, Admissible X' ∧ size X' = 2 * t - p ∧
        (∀ k, load N.d (X' k) ≤ T') ∧ totalCost c X' ≤ C') → C' ≤ C → 2 * T' ≤ M →
        C ≤ C' ∧ M ≤ 2 * T' := by
      rintro T' C' ⟨X', hX', hsize', hload', hcost'⟩ hC' hT'
      have hml : maxLoad N.d X' ≤ T' := (maxLoad_le_iff _ _ _).mpr hload'
      have := hmin (y := (totalCost c X', 2 * maxLoad N.d X')) ⟨X', hX', hsize', rfl⟩
        (Prod.le_def.mpr ⟨hcost'.trans hC', by omega⟩)
      rw [Prod.le_def] at this
      exact ⟨this.1.trans hcost', by omega⟩
    refine ⟨maxLoad N.d X, hM.symm, le_antisymm ?_ ?_, fun T' hT' => ?_⟩
    · rw [← hC]
      exact minCost_le N.d c hX hsize hload
    · by_contra hlt
      push Not at hlt
      obtain ⟨C', hC'⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have hC'' : ((C' : ℕ) : WithTop ℕ) = minCost N.d c t p (maxLoad N.d X) := hC'
      rw [← hC''] at hlt
      have hlt' : C' < C := by exact_mod_cast hlt
      have := hbelow ((minCost_le_coe_iff N.d c).mp hC''.symm.le) hlt'.le (by omega)
      omega
    · by_contra hle
      push Not at hle
      have := hbelow ((minCost_le_coe_iff N.d c).mp hle) le_rfl (by omega)
      omega
  · rintro ⟨T, rfl, hE, hlt⟩
    obtain ⟨X, hX, hsize, hload, hcost⟩ := minCost_attained N.d c hE
    have hml : maxLoad N.d X ≤ T := (maxLoad_le_iff _ _ _).mpr hload
    have hT : maxLoad N.d X = T := by
      by_contra hne
      have := hlt (maxLoad N.d X) (by omega)
      rw [← hcost] at this
      exact absurd (minCost_le N.d c hX hsize (load_le_maxLoad N.d X)) (not_le.mpr this)
    refine ⟨⟨X, hX, hsize, by rw [hcost, hT]⟩, ?_⟩
    rintro ⟨C', M'⟩ ⟨X', hX', hsize', hx'⟩ hle
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    rw [Prod.le_def] at hle ⊢
    have h₁ := minCost_le N.d c hX' hsize' (load_le_maxLoad N.d X')
    have h₂ : T ≤ maxLoad N.d X' := by
      by_contra hlt'
      push Not at hlt'
      have := hlt _ hlt'
      exact absurd (h₁.trans (WithTop.coe_le_coe.mpr hle.1)) (not_le.mpr this)
    refine ⟨?_, by omega⟩
    have h₃ : maxLoad N.d X' = T := by omega
    have h₄ := minCost_le N.d c hX' hsize' fun k => h₃ ▸ load_le_maxLoad N.d X' k
    rw [hE] at h₄
    exact_mod_cast h₄

/-- The largest duration. -/
def maxDur (d : Fin n → ℕ) : ℕ := univ.sup d

theorem load_le_card_mul_maxDur (d : Fin n → ℕ) (Y : Multiset (Fin n)) :
    load d Y ≤ Y.card * maxDur d := by
  have := Multiset.sum_le_card_nsmul (Y.map d) (maxDur d) fun x hx => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Finset.le_sup (Finset.mem_univ i)
  simpa [load] using this

/-- A breakpoint of `E` lies at a level at most `(2t − p) · d_max`: every partition of `2t − p`
landings has its loads below that. -/
theorem breakpoint_le (d c : Fin n → ℕ) {t T C : ℕ} (hE : minCost d c t p T = C)
    (hlt : ∀ T' < T, (C : WithTop ℕ) < minCost d c t p T') : T ≤ (2 * t - p) * maxDur d := by
  by_contra hT
  push Not at hT
  obtain ⟨X, hX, hsize, -, hcost⟩ := minCost_attained d c hE
  have hload : ∀ k, load d (X k) ≤ (2 * t - p) * maxDur d := fun k => by
    refine (load_le_card_mul_maxDur d (X k)).trans (Nat.mul_le_mul_right _ ?_)
    rw [← hsize, size]
    exact Finset.single_le_sum (f := fun k => (X k).card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  have := hlt _ hT
  rw [← hcost] at this
  exact absurd (minCost_le d c hX hsize hload) (not_le.mpr this)

/-- The scan of the levels `T₀, …, T₀ + k − 1`: `(E(T), 2T)` is kept when `E(T)` is below the
last kept value `prev`. -/
def scanFront (E : ℕ → WithTop ℕ) : ℕ → ℕ → WithTop ℕ → List (ℕ × ℕ)
  | _, 0, _ => []
  | T, k + 1, prev =>
    if E T < prev then ((E T).untopD 0, 2 * T) :: scanFront E (T + 1) k (E T)
    else scanFront E (T + 1) k prev

theorem mem_scanFront (E : ℕ → WithTop ℕ) : ∀ (T₀ k : ℕ) (prev : WithTop ℕ) (C M : ℕ),
    (C, M) ∈ scanFront E T₀ k prev ↔ ∃ T, T₀ ≤ T ∧ T < T₀ + k ∧ M = 2 * T ∧ E T = C ∧
      (C : WithTop ℕ) < prev ∧ ∀ T', T₀ ≤ T' → T' < T → (C : WithTop ℕ) < E T'
  | T₀, 0, prev, C, M => by simp [scanFront]; omega
  | T₀, k + 1, prev, C, M => by
    simp only [scanFront]
    split_ifs with hlt
    · rw [List.mem_cons, mem_scanFront E (T₀ + 1) k (E T₀) C M]
      obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have he' : ((e : ℕ) : WithTop ℕ) = E T₀ := he
      have hu : (E T₀).untopD 0 = e := by rw [← he]; rfl
      rw [hu]
      constructor
      · rintro (h | ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩)
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨T₀, le_rfl, by omega, rfl, he'.symm, ?_, fun T' h₁ h₂ => by omega⟩
          rw [he']
          exact hlt
        · refine ⟨T, by omega, by omega, h₃, h₄, h₅.trans hlt, fun T' h₇ h₈ => ?_⟩
          rcases Nat.eq_or_lt_of_le h₇ with rfl | h₇
          · exact h₅
          · exact h₆ T' h₇ h₈
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · left
          have : e = C := by exact_mod_cast he'.trans h₄
          rw [this, h₃]
        · right
          exact ⟨T, h₁, by omega, h₃, h₄, h₆ T₀ le_rfl h₁, fun T' h₇ h₈ => h₆ T' (by omega) h₈⟩
    · rw [mem_scanFront E (T₀ + 1) k prev C M]
      push Not at hlt
      constructor
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        refine ⟨T, by omega, by omega, h₃, h₄, h₅, fun T' h₇ h₈ => ?_⟩
        rcases Nat.eq_or_lt_of_le h₇ with rfl | h₇
        · exact h₅.trans_le hlt
        · exact h₆ T' h₇ h₈
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · exact absurd (h₄ ▸ h₅) (not_lt.mpr hlt)
        · exact ⟨T, h₁, by omega, h₃, h₄, h₅, fun T' h₇ h₈ => h₆ T' (by omega) h₈⟩

theorem scanFront_pairwise (E : ℕ → WithTop ℕ) : ∀ (T₀ k : ℕ) (prev : WithTop ℕ),
    (∀ x ∈ scanFront E T₀ k prev, 2 * T₀ ≤ x.2 ∧ (x.1 : WithTop ℕ) < prev) ∧
      (scanFront E T₀ k prev).Pairwise fun a b => a.2 < b.2 ∧ b.1 < a.1
  | T₀, 0, prev => by simp [scanFront]
  | T₀, k + 1, prev => by
    obtain ⟨ih₁, ih₂⟩ := scanFront_pairwise E (T₀ + 1) k (E T₀)
    obtain ⟨ih₁', ih₂'⟩ := scanFront_pairwise E (T₀ + 1) k prev
    simp only [scanFront]
    split_ifs with hlt
    · obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have he' : ((e : ℕ) : WithTop ℕ) = E T₀ := he
      have hu : (E T₀).untopD 0 = e := by rw [← he]; rfl
      rw [hu]
      refine ⟨fun x hx => ?_, List.Pairwise.cons (fun b hb => ?_) ih₂⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨le_rfl, ?_⟩
          show ((e : ℕ) : WithTop ℕ) < prev
          rw [he']
          exact hlt
        · have := ih₁ x hx
          exact ⟨by omega, this.2.trans hlt⟩
      · have := ih₁ b hb
        rw [← he'] at this
        exact ⟨by simp only; omega, by exact_mod_cast this.2⟩
    · exact ⟨fun x hx => by have := ih₁' x hx; exact ⟨by omega, this.2⟩, ih₂'⟩

theorem scanFront_congr {E E' : ℕ → WithTop ℕ} : ∀ (T₀ k : ℕ) (prev : WithTop ℕ),
    (∀ T, T₀ ≤ T → T < T₀ + k → E T = E' T) → scanFront E T₀ k prev = scanFront E' T₀ k prev
  | _, 0, _, _ => rfl
  | T₀, k + 1, prev, h => by
    simp only [scanFront]
    rw [h T₀ le_rfl (by omega),
      scanFront_congr (T₀ + 1) k (E' T₀) fun T h₁ h₂ => h T (by omega) (by omega),
      scanFront_congr (T₀ + 1) k prev fun T h₁ h₂ => h T (by omega) (by omega)]

/-! ### The solver -/

/-- The σ-DP at level `T`, with the tables that do not depend on `T` (the subsets and their
symmetric differences) computed once. -/
def sigmaAt (subs : List (Finset (Fin n))) (xt : Array (Array ℕ)) (d c : Fin n → ℕ) (p s : ℕ)
    (table : Array (Array (WithTop ℕ))) (T : ℕ) : WithTop ℕ :=
  ((sigmaLayer subs s xt (optTable subs
      (groupOption d c (fun m τ => (table.getD m #[]).getD τ ⊤) T) s) p).getD s #[]).getD
    (subs.idxOf ∅) ⊤

/-- **The solver.** The Pareto front of a symmetric instance (durations `d`, costs `c`, `t`
passengers, `p` planes), by increasing makespan: the scan of `E(T)`, computed by the σ-DP, over
the levels `0, …, (2t − p) · d_max`. -/
def solveFront (d c : Fin n → ℕ) (t p : ℕ) : List (ℕ × ℕ) :=
  let s := 2 * t - p
  let Tmax := s * maxDur d
  let table := oneplaneTable d c Tmax s
  let subs := smallSubsetList (domReps d c) (min (p - 1) (t - p))
  let xt := symmDiffTable subs
  scanFront (sigmaAt subs xt d c p s table) 0 (Tmax + 1) ⊤

/-- The solver scans `E` itself. -/
theorem solveFront_eq (d c : Fin n → ℕ) {t : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t) :
    solveFront d c t p = scanFront (minCost d c t p) 0 ((2 * t - p) * maxDur d + 1) ⊤ := by
  unfold solveFront
  refine scanFront_congr 0 _ ⊤ fun T _ hT => ?_
  rw [← sigmaBoundAt_eq_minCost d c hp hpt (Tmax := (2 * t - p) * maxDur d) (by omega)]
  simp only [sigmaBoundAt, show T ≤ (2 * t - p) * maxDur d by omega, ↓reduceIte, sigmaValue,
    sigmaAt]

/-- **The solver lists exactly the minimal admissible points.** -/
theorem mem_solveFront_iff (N : Network n) (c : Fin n → ℕ) {t : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t)
    (x : ℕ × ℕ) : x ∈ solveFront N.d c t p ↔ Minimal (· ∈ admissiblePoints N c t p) x := by
  obtain ⟨C, M⟩ := x
  rw [solveFront_eq N.d c hp hpt, mem_scanFront, minimal_admissiblePoints_iff]
  constructor
  · rintro ⟨T, -, -, hM, hE, -, hlt⟩
    exact ⟨T, hM, hE, fun T' hT' => hlt T' (Nat.zero_le _) hT'⟩
  · rintro ⟨T, hM, hE, hlt⟩
    have hT := breakpoint_le N.d c hE hlt
    exact ⟨T, Nat.zero_le _, by omega, hM, hE, WithTop.coe_lt_top C,
      fun T' _ hT' => hlt T' hT'⟩

/-- **The solver is correct.** Under (S) and (A1), with `1 ≤ p ≤ t`, `solveFront` is the Pareto
front of the (cost, makespan) pairs of the feasible plans: every listed point is achieved, every
feasible plan is weakly dominated by a listed point, and the points are pairwise incomparable. -/
theorem solveFront_isParetoFront {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    (c : Fin n → ℕ) {t : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t) :
    IsParetoFront (achievable N c t p) (solveFront N.d c t p) := by
  classical
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · exact ((minimal_achievable_iff_admissiblePoints hS hA1 c hpt x).mpr
      ((mem_solveFront_iff N c hp hpt x).mp hx)).prop
  · obtain ⟨P, hP, rfl⟩ := hy
    obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible hS hA1 c hpt
    set T := planMakespan P / 2 with hTdef
    have hXT : ∀ k, load N.d (X k) ≤ T := fun k => by have := hload k; omega
    have hET : minCost N.d c t p T ≤ planCost c P :=
      (minCost_le N.d c hX hsize hXT).trans (WithTop.coe_le_coe.mpr hcost)
    obtain ⟨C₀, hC₀⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hET)
    have hC₀' : minCost N.d c t p T = ((C₀ : ℕ) : WithTop ℕ) := hC₀.symm
    have hex : ∃ T', minCost N.d c t p T' ≤ minCost N.d c t p T := ⟨T, le_rfl⟩
    set T₁ := Nat.find hex with hT₁
    have hT₁T : T₁ ≤ T := Nat.find_min' hex le_rfl
    have hE₁ : minCost N.d c t p T₁ = C₀ := by
      rw [← hC₀']
      exact le_antisymm (Nat.find_spec hex) (minCost_antitone N.d c t p hT₁T)
    have hlt : ∀ T' < T₁, ((C₀ : ℕ) : WithTop ℕ) < minCost N.d c t p T' := fun T' hT' => by
      rw [← hC₀']
      exact not_le.mp (Nat.find_min hex hT')
    refine ⟨(C₀, 2 * T₁), (mem_solveFront_iff N c hp hpt _).mpr
      ((minimal_admissiblePoints_iff N c C₀ (2 * T₁)).mpr ⟨T₁, rfl, hE₁, hlt⟩),
      Prod.le_def.mpr ⟨?_, by simp only; omega⟩⟩
    rw [hC₀'] at hET
    exact_mod_cast hET
  · exact (scanFront_pairwise _ 0 _ ⊤).2.imp fun {a b} hab =>
      ⟨fun hle => absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2),
        fun hle => absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)⟩

end ZenoFront
