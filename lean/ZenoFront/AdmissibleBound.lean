/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.OnePlane
public import ZenoFront.Shrink
public import Mathlib.Data.List.GetD

/-!
# A computable lower bound on admissible partitions: the σ-DP

`E(T)`, the least cost of an admissible partition into `p` groups of total size `s` with loads at
most `T`, is the bound behind the `forest` gaps of certificate format v1. The C++ solver computes
it with the link-forest DP. Here it is computed by the σ-DP of Claim C (§7.5 of the note), and
only the direction needed by the checker is proved: the DP is **at most** the cost of every such
partition (`sigmaBoundAt_le_totalCost`).

* A plane with `m` landings whose parity-witness set is `H` costs at least
  `c(H) + G[m − |H|][T − δ(H)]` (`groupOption_le_cost`).
* Processing the planes one by one, the state is the set `σ` of cities whose number of witness
  entries so far is odd; an admissible partition starts and ends at `σ = ∅`
  (`sigmaDP_le`).
* To keep the state space small, cities are first merged into non-dominated representatives
  (`domRep`): merging keeps admissibility (`Admissible.map`) and lowers neither cost nor loads.
  `H` and `σ` then range over subsets of the representatives `R`.
* The memoised version (`sigmaTable`) indexes the subsets of `R` by their position in a list.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### One plane -/

/-- The cheapest group of `m` landings whose witness set is `H`, at level `T`: one copy of each
city of `H` plus `m − |H|` landings of load at most `T − δ(H)` (read from `G`); `⊤` unless
`|H| + 1 ≤ m`, `|H| ≡ m + 1 (mod 2)` and `δ(H) ≤ T`. -/
def groupOption (d c : Fin n → ℕ) (G : ℕ → ℕ → WithTop ℕ) (T m : ℕ) (H : Finset (Fin n)) :
    WithTop ℕ :=
  if H.card + 1 ≤ m ∧ H.card % 2 = (m + 1) % 2 ∧ load d H.val ≤ T then
    (cost c H.val : WithTop ℕ) + G (m - H.card) (T - load d H.val)
  else ⊤

/-- A group with witness set `h k` costs at least its `groupOption`. -/
theorem groupOption_le_cost (d c : Fin n → ℕ) {X : Groups n p} {h : Fin p → Finset (Fin n)}
    (hw : IsParityWitness X h) (k : Fin p) {T : ℕ} (hT : load d (X k) ≤ T) :
    groupOption d c (oneplane d c) T (X k).card (h k) ≤ (cost c (X k) : WithTop ℕ) := by
  have hle := hw.val_le k
  set Y := X k - (h k).val with hY
  have hX : X k = (h k).val + Y := by rw [hY, add_comm, Multiset.sub_add_cancel hle]
  have hcard : Y.card = (X k).card - (h k).card := by
    rw [hY, Multiset.card_sub hle, Finset.card_val]
  have hloadY : load d Y ≤ T - load d (h k).val := by
    have : load d (X k) = load d (h k).val + load d Y := by rw [hX, load_add]
    omega
  have hcond : (h k).card + 1 ≤ (X k).card ∧ (h k).card % 2 = ((X k).card + 1) % 2 ∧
      load d (h k).val ≤ T :=
    ⟨hw.card_add_one_le k, hw.row k, (load_mono d hle).trans hT⟩
  rw [groupOption, ite_eq_left hcond, hX, cost_add, Nat.cast_add]
  rw [← hX]
  exact add_le_add le_rfl (oneplane_le_cost hcard hloadY)

/-! ### The DP over planes -/

/-- The σ-DP: `sigmaDP R opt j u σ` is the cheapest way to give `j` planes `u` landings with
witness sets `H ⊆ R` whose symmetric difference is `σ`, a plane with `m` landings and witness
set `H` costing `opt m H`. -/
def sigmaDP (R : Finset (Fin n)) (opt : ℕ → Finset (Fin n) → WithTop ℕ) :
    ℕ → ℕ → Finset (Fin n) → WithTop ℕ
  | 0, u, σ => if u = 0 ∧ σ = ∅ then 0 else ⊤
  | j + 1, u, σ =>
    (range u).inf fun m => R.powerset.inf fun H =>
      sigmaDP R opt j (u - (m + 1)) (symmDiff σ H) + opt (m + 1) H

/-- The DP is a lower bound, list form. -/
theorem sigmaDP_le (R : Finset (Fin n)) (opt : ℕ → Finset (Fin n) → WithTop ℕ)
    (c : Fin n → ℕ) : ∀ L : List (Multiset (Fin n) × Finset (Fin n)),
      (∀ yh ∈ L, yh.2 ⊆ R ∧ 1 ≤ yh.1.card ∧ opt yh.1.card yh.2 ≤ cost c yh.1) →
      sigmaDP R opt L.length (L.map fun yh => yh.1.card).sum
          (L.foldr (fun yh σ => symmDiff yh.2 σ) ∅) ≤
        ((L.map fun yh => cost c yh.1).sum : ℕ)
  | [], _ => by simp [sigmaDP]
  | ⟨Y, H⟩ :: L, h => by
    obtain ⟨hHR, hY, hopt⟩ := h ⟨Y, H⟩ List.mem_cons_self
    simp only at hHR hY hopt
    have ih := sigmaDP_le R opt c L fun yh hyh => h yh (List.mem_cons_of_mem _ hyh)
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.foldr_cons, sigmaDP]
    have hm : Y.card - 1 ∈ range (Y.card + (L.map fun yh => yh.1.card).sum) := by
      rw [Finset.mem_range]; omega
    refine (Finset.inf_le hm).trans ?_
    refine (Finset.inf_le (Finset.mem_powerset.mpr hHR)).trans ?_
    have h₁ : Y.card - 1 + 1 = Y.card := by omega
    rw [h₁, Nat.add_sub_cancel_left, symmDiff_comm H, symmDiff_symmDiff_cancel_right, Nat.cast_add,
      add_comm (cost c Y : WithTop ℕ)]
    exact add_le_add ih hopt

theorem mem_foldr_symmDiff (i : Fin n) : ∀ L : List (Finset (Fin n)),
    i ∈ L.foldr (fun H σ => symmDiff H σ) ∅ ↔ L.countP (fun H => decide (i ∈ H)) % 2 = 1
  | [] => by simp
  | H :: L => by
    rw [List.foldr_cons, Finset.mem_symmDiff, mem_foldr_symmDiff i L, List.countP_cons]
    by_cases hi : i ∈ H
    · simp [hi]; omega
    · simp [hi]

theorem countP_finRange (f : Fin p → Bool) :
    (List.finRange p).countP f = #{k | f k = true} := by
  rw [Finset.card_filter, Fin.sum_univ_def]
  induction (List.finRange p) with
  | nil => rfl
  | cons a l ih => simp [List.countP_cons, ih, add_comm]

/-- **The σ-DP is a lower bound**: for every admissible grouping whose cities lie in `R`, with
`groupOption`-type plane costs, `sigmaDP R opt p (Σ_k |X_k|) ∅ ≤ Σ_k c(X_k)`. -/
theorem sigmaDP_le_totalCost (R : Finset (Fin n)) (opt : ℕ → Finset (Fin n) → WithTop ℕ)
    (c : Fin n → ℕ) {X : Groups n p} {h : Fin p → Finset (Fin n)} (hw : IsParityWitness X h)
    (hR : ∀ k, h k ⊆ R) (hopt : ∀ k, opt (X k).card (h k) ≤ cost c (X k)) :
    sigmaDP R opt p (size X) ∅ ≤ (totalCost c X : WithTop ℕ) := by
  have := sigmaDP_le R opt c ((List.finRange p).map fun k => (X k, h k)) fun yh hyh => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hyh
    exact ⟨hR k, (Admissible.card_pos ⟨h, hw⟩ k), hopt k⟩
  have hσ : ((List.finRange p).map fun k => (X k, h k)).foldr (fun yh σ => symmDiff yh.2 σ) ∅
      = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    have h₁ := (mem_foldr_symmDiff i ((List.finRange p).map h)).mp
      (by simpa [List.foldr_map] using hi)
    rw [List.countP_map, countP_finRange] at h₁
    obtain ⟨r, hr⟩ := hw.col i
    simp only [Function.comp_def, decide_eq_true_eq] at h₁
    omega
  simp only [List.length_map, List.length_finRange, List.map_map, hσ] at this
  rw [size, totalCost, Fin.sum_univ_def, Fin.sum_univ_def]
  exact this

/-! ### Merging dominated cities -/

/-- A representative of city `i` that is no slower and no more expensive: the first city
`j` (in index order) with the smallest `(d j, c j)` among those dominating `i`. -/
def domRep (d c : Fin n → ℕ) (i : Fin n) : Fin n :=
  (List.finRange n).foldl (fun best j =>
    if d j ≤ d i ∧ c j ≤ c i ∧ (d j < d best ∨ (d j = d best ∧ c j < c best)) then j else best) i

theorem domRep_le (d c : Fin n → ℕ) (i : Fin n) :
    d (domRep d c i) ≤ d i ∧ c (domRep d c i) ≤ c i := by
  have : ∀ (l : List (Fin n)) (b : Fin n), d b ≤ d i ∧ c b ≤ c i →
      d (l.foldl (fun best j => if d j ≤ d i ∧ c j ≤ c i ∧
        (d j < d best ∨ (d j = d best ∧ c j < c best)) then j else best) b) ≤ d i ∧
      c (l.foldl (fun best j => if d j ≤ d i ∧ c j ≤ c i ∧
        (d j < d best ∨ (d j = d best ∧ c j < c best)) then j else best) b) ≤ c i := by
    intro l
    induction l with
    | nil => exact fun b hb => hb
    | cons j l ih =>
      intro b hb
      simp only [List.foldl_cons]
      apply ih
      split_ifs with hj
      · exact ⟨hj.1, hj.2.1⟩
      · exact hb
  exact this _ i ⟨le_rfl, le_rfl⟩

/-- The representatives. -/
def domReps (d c : Fin n → ℕ) : Finset (Fin n) := univ.image (domRep d c)

/-- **The merged bound is a lower bound** on the original grouping: merging every city into its
representative keeps the grouping admissible and its cities in `domReps`, and lowers neither
the cost nor the loads. -/
theorem sigmaDP_domReps_le_totalCost (d c : Fin n → ℕ) {X : Groups n p} (hX : Admissible X)
    {T : ℕ} (hT : ∀ k, load d (X k) ≤ T) :
    sigmaDP (domReps d c) (groupOption d c (oneplane d c) T) p (size X) ∅ ≤
      (totalCost c X : WithTop ℕ) := by
  classical
  set X' : Groups n p := fun k => (X k).map (domRep d c) with hX'
  obtain ⟨h', hw'⟩ := hX.map (domRep d c)
  have hsize : size X' = size X := by simp [size, hX']
  have hload : ∀ k, load d (X' k) ≤ load d (X k) := fun k => by
    simp only [hX', load, Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).1
  have hcost : totalCost c X' ≤ totalCost c X := Finset.sum_le_sum fun k _ => by
    simp only [hX', cost, Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).2
  have hR : ∀ k, h' k ⊆ domReps d c := fun k i hi => by
    have := hw'.subset k hi
    simp only [Multiset.mem_toFinset, Multiset.mem_map] at this
    obtain ⟨j, -, rfl⟩ := this
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have := sigmaDP_le_totalCost (domReps d c) (groupOption d c (oneplane d c) T) c hw' hR
    fun k => groupOption_le_cost d c hw' k ((hload k).trans (hT k))
  rw [hsize] at this
  exact this.trans (WithTop.coe_le_coe.mpr hcost)

/-- `sigmaDP` only reads `opt` on group sizes `1, …, u`. -/
theorem sigmaDP_congr (R : Finset (Fin n)) {opt opt' : ℕ → Finset (Fin n) → WithTop ℕ} :
    ∀ (j u : ℕ) (σ : Finset (Fin n)), (∀ m H, 1 ≤ m → m ≤ u → opt m H = opt' m H) →
      sigmaDP R opt j u σ = sigmaDP R opt' j u σ
  | 0, _, _, _ => rfl
  | j + 1, u, σ, h => by
    simp only [sigmaDP]
    refine Finset.inf_congr rfl fun m hm => Finset.inf_congr rfl fun H _ => ?_
    rw [Finset.mem_range] at hm
    rw [h (m + 1) H (by omega) (by omega),
      sigmaDP_congr R j _ _ fun m' H' h₁ h₂ => h m' H' h₁ (by omega)]

/-! ### The memoised σ-DP -/

/-- The subsets of `R`, listed. -/
def subsetList (R : Finset (Fin n)) : List (Finset (Fin n)) :=
  ((List.finRange n).filter fun i => decide (i ∈ R)).sublists.map List.toFinset

theorem mem_subsetList {R H : Finset (Fin n)} : H ∈ subsetList R ↔ H ⊆ R := by
  classical
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
    intro i hi
    have := (List.mem_sublists.mp hl).subset (List.mem_toFinset.mp hi)
    simpa using this
  · intro h
    refine List.mem_map.mpr ⟨((List.finRange n).filter fun i => decide (i ∈ R)).filter
      (fun i => decide (i ∈ H)), List.mem_sublists.mpr (List.filter_sublist), ?_⟩
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨fun h' => h'.2, fun h' => ⟨h h', h'⟩⟩

theorem getD_subsetList_subset {R : Finset (Fin n)} (b : ℕ) :
    (subsetList R).getD b ∅ ⊆ R := by
  by_cases hb : b < (subsetList R).length
  · rw [List.getD_eq_getElem _ _ hb]
    exact mem_subsetList.mp (List.getElem_mem hb)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Finset.empty_subset _

theorem image_subsetList (R : Finset (Fin n)) :
    (range (subsetList R).length).image (fun b => (subsetList R).getD b ∅) = R.powerset := by
  ext H
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_powerset]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact getD_subsetList_subset b
  · intro h
    obtain ⟨b, hb, hH⟩ := List.mem_iff_getElem.mp (mem_subsetList.mpr h)
    exact ⟨b, hb, by rw [List.getD_eq_getElem _ _ hb, hH]⟩

/-- `subsetList R` indexed: the position of a subset of `R`. -/
theorem getD_idxOf_subsetList {R H : Finset (Fin n)} (h : H ⊆ R) :
    (subsetList R).idxOf H < (subsetList R).length ∧
      (subsetList R).getD ((subsetList R).idxOf H) ∅ = H := by
  have hmem := mem_subsetList.mpr h
  have hlt := List.idxOf_lt_length_iff.mpr hmem
  exact ⟨hlt, by rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]⟩

variable (R : Finset (Fin n)) (opt : ℕ → Finset (Fin n) → WithTop ℕ) (s : ℕ)

/-- The index of `subs[a] ∆ subs[b]`. -/
def symmDiffTable : Array (Array ℕ) :=
  Array.ofFn (n := (subsetList R).length) fun a => Array.ofFn (n := (subsetList R).length) fun b =>
    (subsetList R).idxOf (symmDiff ((subsetList R).getD a ∅) ((subsetList R).getD b ∅))

/-- The plane options, for `m = 0, …, s`. -/
def optTable : Array (Array (WithTop ℕ)) :=
  Array.ofFn (n := s + 1) fun m => Array.ofFn (n := (subsetList R).length) fun b =>
    opt m ((subsetList R).getD b ∅)

/-- Layer `j` of the memoised σ-DP: entry `[u][a]` is `sigmaDP R opt j u (subs[a])`. -/
def sigmaLayer (xt : Array (Array ℕ)) (ot : Array (Array (WithTop ℕ))) : ℕ → Array (Array (WithTop ℕ))
  | 0 => Array.ofFn (n := s + 1) fun u => Array.ofFn (n := (subsetList R).length) fun a =>
      if (u : ℕ) = 0 ∧ (subsetList R).getD a ∅ = ∅ then 0 else ⊤
  | j + 1 =>
    let prev := sigmaLayer xt ot j
    Array.ofFn (n := s + 1) fun u => Array.ofFn (n := (subsetList R).length) fun a =>
      (range u).inf fun m => (range (subsetList R).length).inf fun b =>
        ((prev.getD (u - (m + 1)) #[]).getD ((xt.getD a #[]).getD b 0) ⊤) +
          (ot.getD (m + 1) #[]).getD b ⊤

theorem symmDiffTable_getD {a b : ℕ} (ha : a < (subsetList R).length)
    (hb : b < (subsetList R).length) :
    ((symmDiffTable R).getD a #[]).getD b 0 =
      (subsetList R).idxOf (symmDiff ((subsetList R).getD a ∅) ((subsetList R).getD b ∅)) := by
  simp [symmDiffTable, Array.getD_eq_getD_getElem?, ha, hb]

theorem optTable_getD {m b : ℕ} (hm : m ≤ s) (hb : b < (subsetList R).length) :
    ((optTable R opt s).getD m #[]).getD b ⊤ = opt m ((subsetList R).getD b ∅) := by
  simp [optTable, Array.getD_eq_getD_getElem?, show m < s + 1 by omega, hb]

/-- **The memoised σ-DP agrees with `sigmaDP`.** -/
theorem sigmaLayer_getD : ∀ (j : ℕ) {u a : ℕ}, u ≤ s → a < (subsetList R).length →
    ((sigmaLayer R s (symmDiffTable R) (optTable R opt s) j).getD u #[]).getD a ⊤ =
      sigmaDP R opt j u ((subsetList R).getD a ∅)
  | 0, u, a, hu, ha => by
    simp [sigmaLayer, sigmaDP, Array.getD_eq_getD_getElem?, show u < s + 1 by omega, ha]
  | j + 1, u, a, hu, ha => by
    simp only [sigmaLayer, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      show u < s + 1 by omega, ha, dite_true, Option.getD_some, sigmaDP]
    refine Finset.inf_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← image_subsetList R, Finset.inf_image]
    refine Finset.inf_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    have hsub : symmDiff ((subsetList R).getD a ∅) ((subsetList R).getD b ∅) ⊆ R :=
      fun i hi => by
        rcases Finset.mem_symmDiff.mp hi with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact getD_subsetList_subset a h₁
        · exact getD_subsetList_subset b h₁
    obtain ⟨hlt, hget⟩ := getD_idxOf_subsetList hsub
    simp only [← Array.getD_eq_getD_getElem?]
    rw [symmDiffTable_getD R ha hb, sigmaLayer_getD j (by omega) hlt, hget,
      optTable_getD R opt s (by omega) hb]
    rfl

/-- The σ-DP value: `sigmaDP R opt p s ∅`, computed by the memoised table. -/
def sigmaValue (p : ℕ) : WithTop ℕ :=
  ((sigmaLayer R s (symmDiffTable R) (optTable R opt s) p).getD s #[]).getD
    ((subsetList R).idxOf ∅) ⊤

theorem sigmaValue_eq (p : ℕ) : sigmaValue R opt s p = sigmaDP R opt p s ∅ := by
  obtain ⟨hlt, hget⟩ := getD_idxOf_subsetList (Finset.empty_subset R)
  rw [sigmaValue, sigmaLayer_getD R opt s p le_rfl hlt, hget]

/-! ### The forest bound of the checker -/

/-- The bound the checker uses for a `forest` gap at level `T`: the σ-DP over the non-dominated
cities, with plane options read from the one-plane table `table` (columns `0, …, Tmax`); `0`
(no bound) if `T > Tmax`. -/
def forestBoundAt (d c : Fin n → ℕ) (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ)))
    (T : ℕ) : WithTop ℕ :=
  if T ≤ Tmax then
    sigmaValue (domReps d c) (groupOption d c (fun m τ => (table.getD m #[]).getD τ ⊤) T) s p
  else 0

/-- **The forest bound is a lower bound**: at most the cost of every admissible grouping into
`p` groups of total size `s` with loads at most `T`, for the table `oneplaneTable d c Tmax s`. -/
theorem forestBoundAt_le_totalCost (d c : Fin n → ℕ) {s Tmax T : ℕ} {X : Groups n p}
    (hX : Admissible X) (hsize : size X = s) (hT : ∀ k, load d (X k) ≤ T) :
    forestBoundAt d c p s Tmax (oneplaneTable d c Tmax s) T ≤ (totalCost c X : WithTop ℕ) := by
  unfold forestBoundAt
  split_ifs with hTmax
  · rw [sigmaValue_eq]
    rw [sigmaDP_congr (domReps d c) (opt' := groupOption d c (oneplane d c) T) p s ∅
      fun m H _ hm => by
        unfold groupOption
        split_ifs with hc
        · dsimp only
          rw [oneplaneTable_getD d c (by omega) (by omega)]
        · rfl]
    rw [← hsize]
    exact sigmaDP_domReps_le_totalCost d c hX hT
  · exact bot_le

end ZenoFront
