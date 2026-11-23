/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.OnePlane
public import ZenoFront.Shrink
public import ZenoFront.MinimalWitness
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

/-- The σ-DP over a family `S` of allowed sets: `sigmaDP S opt j u σ` is the cheapest way to give
`j` planes `u` landings with witness sets in `S`, whose running symmetric differences stay in
`S` and end at `σ`; a plane with `m` landings and witness set `H` costs `opt m H`. -/
def sigmaDP (S : Finset (Finset (Fin n))) (opt : ℕ → Finset (Fin n) → WithTop ℕ) :
    ℕ → ℕ → Finset (Fin n) → WithTop ℕ
  | 0, u, σ => if u = 0 ∧ σ = ∅ then 0 else ⊤
  | j + 1, u, σ =>
    (range u).inf fun m => S.inf fun H =>
      if symmDiff σ H ∈ S then sigmaDP S opt j (u - (m + 1)) (symmDiff σ H) + opt (m + 1) H
      else ⊤

theorem foldr_symmDiff_subset (Z : Finset (Fin n)) :
    ∀ L : List (Multiset (Fin n) × Finset (Fin n)), (∀ yh ∈ L, yh.2 ⊆ Z) →
      L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ ⊆ Z
  | [], _ => Finset.empty_subset _
  | yh :: L, h => by
    rw [List.foldr_cons]
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with ⟨hi, -⟩ | ⟨hi, -⟩
    · exact h yh List.mem_cons_self hi
    · exact foldr_symmDiff_subset Z L (fun y hy => h y (List.mem_cons_of_mem _ hy)) hi

/-- The DP is a lower bound, list form: if every witness set lies in `Z` and every subset of `Z`
is allowed, the DP is at most the total cost. -/
theorem sigmaDP_le (S : Finset (Finset (Fin n))) (opt : ℕ → Finset (Fin n) → WithTop ℕ)
    (c : Fin n → ℕ) (Z : Finset (Fin n)) (hZ : ∀ H ⊆ Z, H ∈ S) :
    ∀ L : List (Multiset (Fin n) × Finset (Fin n)),
      (∀ yh ∈ L, yh.2 ⊆ Z ∧ 1 ≤ yh.1.card ∧ opt yh.1.card yh.2 ≤ cost c yh.1) →
      sigmaDP S opt L.length (L.map fun yh => yh.1.card).sum
          (L.foldr (fun yh σ => symmDiff yh.2 σ) ∅) ≤
        ((L.map fun yh => cost c yh.1).sum : ℕ)
  | [], _ => by simp [sigmaDP]
  | ⟨Y, H⟩ :: L, h => by
    obtain ⟨hHZ, hY, hopt⟩ := h ⟨Y, H⟩ List.mem_cons_self
    simp only at hHZ hY hopt
    have ih := sigmaDP_le S opt c Z hZ L fun yh hyh => h yh (List.mem_cons_of_mem _ hyh)
    have hfold : L.foldr (fun yh σ => symmDiff yh.2 σ) ∅ ⊆ Z :=
      foldr_symmDiff_subset Z L fun yh hyh => (h yh (List.mem_cons_of_mem _ hyh)).1
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.foldr_cons, sigmaDP]
    have hm : Y.card - 1 ∈ range (Y.card + (L.map fun yh => yh.1.card).sum) := by
      rw [Finset.mem_range]; omega
    refine (Finset.inf_le hm).trans ?_
    refine (Finset.inf_le (hZ H hHZ)).trans ?_
    have h₁ : Y.card - 1 + 1 = Y.card := by omega
    rw [h₁, Nat.add_sub_cancel_left, symmDiff_comm H, symmDiff_symmDiff_cancel_right,
      ite_eq_left (hZ _ hfold), Nat.cast_add, add_comm (cost c Y : WithTop ℕ)]
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

/-- **The σ-DP is a lower bound**: for every admissible grouping with a witness inside `Z`, every
subset of `Z` being allowed, and plane costs bounded by `opt`,
`sigmaDP S opt p (Σ_k |X_k|) ∅ ≤ Σ_k c(X_k)`. -/
theorem sigmaDP_le_totalCost (S : Finset (Finset (Fin n))) (opt : ℕ → Finset (Fin n) → WithTop ℕ)
    (c : Fin n → ℕ) {X : Groups n p} {h : Fin p → Finset (Fin n)} (hw : IsParityWitness X h)
    (Z : Finset (Fin n)) (hZ : ∀ H ⊆ Z, H ∈ S) (hR : ∀ k, h k ⊆ Z)
    (hopt : ∀ k, opt (X k).card (h k) ≤ cost c (X k)) :
    sigmaDP S opt p (size X) ∅ ≤ (totalCost c X : WithTop ℕ) := by
  have := sigmaDP_le S opt c Z hZ ((List.finRange p).map fun k => (X k, h k)) fun yh hyh => by
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

/-- `sigmaDP` only reads `opt` on group sizes `1, …, u`. -/
theorem sigmaDP_congr (S : Finset (Finset (Fin n))) {opt opt' : ℕ → Finset (Fin n) → WithTop ℕ} :
    ∀ (j u : ℕ) (σ : Finset (Fin n)), (∀ m H, 1 ≤ m → m ≤ u → opt m H = opt' m H) →
      sigmaDP S opt j u σ = sigmaDP S opt' j u σ
  | 0, _, _, _ => rfl
  | j + 1, u, σ, h => by
    simp only [sigmaDP]
    refine Finset.inf_congr rfl fun m hm => Finset.inf_congr rfl fun H _ => ?_
    rw [Finset.mem_range] at hm
    rw [h (m + 1) H (by omega) (by omega),
      sigmaDP_congr S j _ _ fun m' H' h₁ h₂ => h m' H' h₁ (by omega)]

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

/-! ### Small subsets -/

/-- The subsets of `R` with at most `w` elements, listed. -/
def smallSubsetList (R : Finset (Fin n)) (w : ℕ) : List (Finset (Fin n)) :=
  (List.range (w + 1)).flatMap fun k =>
    (((List.finRange n).filter fun i => decide (i ∈ R)).sublistsLen k).map List.toFinset

theorem mem_smallSubsetList {R H : Finset (Fin n)} {w : ℕ} :
    H ∈ smallSubsetList R w ↔ H ⊆ R ∧ H.card ≤ w := by
  classical
  constructor
  · intro h
    obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hl
    rw [List.mem_range] at hk
    refine ⟨fun i hi => ?_, (List.toFinset_card_le l).trans (by omega)⟩
    have := hsub.subset (List.mem_toFinset.mp hi)
    simpa using this
  · rintro ⟨hR, hw⟩
    set l := ((List.finRange n).filter fun i => decide (i ∈ R)).filter fun i => decide (i ∈ H)
    have hl : l.toFinset = H := by
      ext i
      simp only [l, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact ⟨fun h' => h'.2, fun h' => ⟨hR h', h'⟩⟩
    have hnodup : l.Nodup := ((List.nodup_finRange n).filter _).filter _
    have hlen : l.length = H.card := by rw [← hl, List.toFinset_card_of_nodup hnodup]
    refine List.mem_flatMap.mpr ⟨H.card, List.mem_range.mpr (by omega), ?_⟩
    exact List.mem_map.mpr ⟨l, List.mem_sublistsLen.mpr ⟨List.filter_sublist, hlen⟩, hl⟩

/-! ### The memoised σ-DP -/

theorem image_getD (subs : List (Finset (Fin n))) :
    (range subs.length).image (fun b => subs.getD b ∅) = subs.toFinset := by
  ext H
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem hb
  · intro h
    obtain ⟨b, hb, hH⟩ := List.mem_iff_getElem.mp h
    exact ⟨b, hb, by rw [List.getD_eq_getElem _ _ hb, hH]⟩

theorem inf_toFinset_eq (subs : List (Finset (Fin n))) (g : Finset (Fin n) → WithTop ℕ) :
    subs.toFinset.inf g = (range subs.length).inf fun b => g (subs.getD b ∅) := by
  rw [← image_getD subs, Finset.inf_image]
  rfl

variable (subs : List (Finset (Fin n))) (opt : ℕ → Finset (Fin n) → WithTop ℕ) (s : ℕ)

/-- The index of `subs[a] ∆ subs[b]` in `subs` (`subs.length` if it is not listed). -/
def symmDiffTable : Array (Array ℕ) :=
  Array.ofFn (n := subs.length) fun a => Array.ofFn (n := subs.length) fun b =>
    subs.idxOf (symmDiff (subs.getD a ∅) (subs.getD b ∅))

/-- The plane options, for `m = 0, …, s`. -/
def optTable : Array (Array (WithTop ℕ)) :=
  Array.ofFn (n := s + 1) fun m => Array.ofFn (n := subs.length) fun b => opt m (subs.getD b ∅)

/-- Layer `j` of the memoised σ-DP: entry `[u][a]` is `sigmaDP subs.toFinset opt j u (subs[a])`. -/
def sigmaLayer (xt : Array (Array ℕ)) (ot : Array (Array (WithTop ℕ))) :
    ℕ → Array (Array (WithTop ℕ))
  | 0 => Array.ofFn (n := s + 1) fun u => Array.ofFn (n := subs.length) fun a =>
      if (u : ℕ) = 0 ∧ subs.getD a ∅ = ∅ then 0 else ⊤
  | j + 1 =>
    let prev := sigmaLayer xt ot j
    Array.ofFn (n := s + 1) fun u => Array.ofFn (n := subs.length) fun a =>
      minUpTo (fun m => minUpTo (fun b =>
        if (xt.getD a #[]).getD b 0 < subs.length then
          ((prev.getD (u - (m + 1)) #[]).getD ((xt.getD a #[]).getD b 0) ⊤) +
            (ot.getD (m + 1) #[]).getD b ⊤
        else ⊤) subs.length) u

theorem symmDiffTable_getD {a b : ℕ} (ha : a < subs.length) (hb : b < subs.length) :
    ((symmDiffTable subs).getD a #[]).getD b 0 =
      subs.idxOf (symmDiff (subs.getD a ∅) (subs.getD b ∅)) := by
  simp [symmDiffTable, Array.getD_eq_getD_getElem?, ha, hb]

theorem optTable_getD {m b : ℕ} (hm : m ≤ s) (hb : b < subs.length) :
    ((optTable subs opt s).getD m #[]).getD b ⊤ = opt m (subs.getD b ∅) := by
  simp [optTable, Array.getD_eq_getD_getElem?, show m < s + 1 by omega, hb]

/-- **The memoised σ-DP agrees with `sigmaDP`.** -/
theorem sigmaLayer_getD : ∀ (j : ℕ) {u a : ℕ}, u ≤ s → a < subs.length →
    ((sigmaLayer subs s (symmDiffTable subs) (optTable subs opt s) j).getD u #[]).getD a ⊤ =
      sigmaDP subs.toFinset opt j u (subs.getD a ∅)
  | 0, u, a, hu, ha => by
    simp [sigmaLayer, sigmaDP, Array.getD_eq_getD_getElem?, show u < s + 1 by omega, ha]
  | j + 1, u, a, hu, ha => by
    simp only [sigmaLayer, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      show u < s + 1 by omega, ha, dite_true, Option.getD_some, sigmaDP, minUpTo_eq]
    refine Finset.inf_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [inf_toFinset_eq subs]
    refine Finset.inf_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    simp only [← Array.getD_eq_getD_getElem?]
    rw [symmDiffTable_getD subs ha hb]
    by_cases hmem : symmDiff (subs.getD a ∅) (subs.getD b ∅) ∈ subs
    · have hlt := List.idxOf_lt_length_iff.mpr hmem
      have hget : subs.getD (subs.idxOf (symmDiff (subs.getD a ∅) (subs.getD b ∅))) ∅ =
          symmDiff (subs.getD a ∅) (subs.getD b ∅) := by
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]
      rw [ite_eq_left hlt, ite_eq_left (List.mem_toFinset.mpr hmem), sigmaLayer_getD j (by omega) hlt, hget,
        optTable_getD subs opt s (by omega) hb]
    · rw [ite_eq_right (by rw [List.idxOf_eq_length hmem]; omega),
        ite_eq_right (mt List.mem_toFinset.mp hmem)]

/-- The σ-DP value: `sigmaDP subs.toFinset opt p s ∅`, computed by the memoised table. -/
def sigmaValue (p : ℕ) : WithTop ℕ :=
  ((sigmaLayer subs s (symmDiffTable subs) (optTable subs opt s) p).getD s #[]).getD
    (subs.idxOf ∅) ⊤

theorem sigmaValue_eq (p : ℕ) (h : ∅ ∈ subs) :
    sigmaValue subs opt s p = sigmaDP subs.toFinset opt p s ∅ := by
  have hlt := List.idxOf_lt_length_iff.mpr h
  have hget : subs.getD (subs.idxOf ∅) ∅ = ∅ := by
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]
  rw [sigmaValue, sigmaLayer_getD subs opt s p le_rfl hlt, hget]

/-! ### The forest bound of the checker -/

/-- The bound the checker uses for a `forest` gap at level `T`: the σ-DP over the subsets of at
most `w = min(p − 1, t − p)` non-dominated cities (Claim B′), with plane options read from the
one-plane table `table` (columns `0, …, Tmax`); `0` (no bound) if `T > Tmax`. -/
def forestBoundAt (d c : Fin n → ℕ) (p t s Tmax : ℕ) (table : Array (Array (WithTop ℕ)))
    (T : ℕ) : WithTop ℕ :=
  if T ≤ Tmax then
    sigmaValue (smallSubsetList (domReps d c) (min (p - 1) (t - p)))
      (groupOption d c (fun m τ => (table.getD m #[]).getD τ ⊤) T) s p
  else 0

/-- **The forest bound is a lower bound**: at most the cost of every admissible grouping into
`p ≤ t` groups of total size `s = 2t − p` with loads at most `T`, for the table
`oneplaneTable d c Tmax s`. The proof merges dominated cities, then takes a witness touching at
most `min(p − 1, t − p)` cities (Claim B′), so that every state of the DP is a small subset. -/
theorem forestBoundAt_le_totalCost (d c : Fin n → ℕ) {t Tmax T : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t)
    {X : Groups n p} (hX : Admissible X) (hsize : size X = 2 * t - p)
    (hT : ∀ k, load d (X k) ≤ T) :
    forestBoundAt d c p t (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T ≤
      (totalCost c X : WithTop ℕ) := by
  classical
  unfold forestBoundAt
  split_ifs with hTmax
  · set w := min (p - 1) (t - p)
    set R := domReps d c
    set subs := smallSubsetList R w
    rw [sigmaValue_eq subs _ _ p (mem_smallSubsetList.mpr ⟨Finset.empty_subset _, Nat.zero_le _⟩)]
    rw [sigmaDP_congr subs.toFinset (opt' := groupOption d c (oneplane d c) T) p (2 * t - p) ∅
      fun m H _ hm => by
        unfold groupOption
        split_ifs with hc
        · dsimp only
          rw [oneplaneTable_getD d c (by omega) (by omega)]
        · rfl]
    -- Merge every city into its representative.
    set X' : Groups n p := fun k => (X k).map (domRep d c) with hX'
    have hX'adm : Admissible X' := hX.map (domRep d c)
    have hsize' : size X' = 2 * t - p := by rw [← hsize]; simp [size, hX']
    have hload : ∀ k, load d (X' k) ≤ load d (X k) := fun k => by
      simp only [hX', load, Multiset.map_map]
      exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).1
    have hcost : totalCost c X' ≤ totalCost c X := Finset.sum_le_sum fun k _ => by
      simp only [hX', cost, Multiset.map_map]
      exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).2
    -- A witness of the merged grouping touching at most `w` cities (Claim B′).
    let I : Instance := ⟨n, t, p, d, c, hp, hpt⟩
    obtain ⟨h', hw', htouch⟩ := hX'adm.exists_card_touched_le I hsize'
    have hZR : touched h' ⊆ R := fun i hi => by
      obtain ⟨k, hk⟩ := mem_touched.mp hi
      have := hw'.subset k hk
      simp only [hX', Multiset.mem_toFinset, Multiset.mem_map] at this
      obtain ⟨j, -, rfl⟩ := this
      exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have hZ : ∀ H ⊆ touched h', H ∈ subs.toFinset := fun H hH => by
      rw [List.mem_toFinset, mem_smallSubsetList]
      exact ⟨hH.trans hZR, (Finset.card_le_card hH).trans htouch⟩
    have := sigmaDP_le_totalCost subs.toFinset (groupOption d c (oneplane d c) T) c hw'
      (touched h') hZ (fun k i hi => mem_touched_of_mem hi)
      fun k => groupOption_le_cost d c hw' k ((hload k).trans (hT k))
    rw [hsize'] at this
    exact this.trans (WithTop.coe_le_coe.mpr hcost)
  · exact bot_le

end ZenoFront
