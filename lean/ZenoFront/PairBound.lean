/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.TreeExact
public import ZenoFront.Relaxation

/-!
# The bracket `L(T) ≤ E(T) ≤ U₂(T)`

The solver evaluates `E(T)` at every breakpoint level. As the C++ solver does
(`src/zeno/solve.cpp`), it first brackets the level between two cheap bounds, and runs an exact
DP only if they differ:

* `L(T)`, the relaxation (`relaxedBoundAt`), is at most `E(T)` (`relaxedBoundAt_le_minCost`);
* `U₂(T)`, the pairs bound (`pairsBoundAt`), is the cheapest forest whose trees have one or two
  planes: single planes with an odd number of landings, and pairs linked at a city `b`, each plane
  with one copy of `b` and an odd number of free landings. Every finite value is the cost of such
  a forest (`pairCost_attained`, `pairRows_attained`), whose groups are admissible
  (`admissible_forestPartition`). So `E(T) ≤ U₂(T)` (`minCost_le_pairsBoundAt`).

Where `L(T) = U₂(T)`, both are `E(T)` (`minCost_eq_of_bracket`). `U₂` costs `O(n′ s² + p s²)`
per level, with no factor `T`. On the large regimes of the benchmark suite every level closes
this way, as in the C++ solver.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n : ℕ}

/-! ### Pairs -/

/-- The cheapest pair of planes linked at a city `b`, with `j` landings in all, at level `T`:
each plane holds one copy of `b` and an odd number of free landings within `T − d_b`, `r` for
the first and `j − 2 − r` for the second. The two are interchangeable, so only `r = 2k + 1` with
`2r + 2 ≤ j` is tried. -/
def pairCost (d c : Fin n → ℕ) (reps : List (Fin n)) (G : ℕ → ℕ → WithTop ℕ) (T j : ℕ) :
    WithTop ℕ :=
  minList reps fun b =>
    if d b ≤ T then
      minUpTo (fun k => if (j - 2 - (2 * k + 1)) % 2 = 1 ∧ 2 * (2 * k + 1) + 2 ≤ j then
        ((2 * c b : ℕ) : WithTop ℕ) + G (2 * k + 1) (T - d b) +
          G (j - 2 - (2 * k + 1)) (T - d b) else ⊤) (j / 4 + 1)
    else ⊤

/-- Row `P'` of the forests of single planes and linked pairs: entry `J` is the cheapest such
forest with `P'` planes and `J` landings; `single m` is the cost of one plane with `m` landings
and `pair j` that of a pair with `j`. A single plane has an odd number of landings and a pair
an even number, so only those are tried. -/
def pairRow (single pair : ℕ → WithTop ℕ) (S : ℕ) (look : ℕ → Array (WithTop ℕ)) (P' : ℕ) :
    Array (WithTop ℕ) :=
  Array.ofFn (n := S + 1) fun J =>
    if P' = 0 then (if (J : ℕ) = 0 then 0 else ⊤) else
      min (minUpTo (fun k => if 2 * k + 1 ≤ J then
          (look (P' - 1)).getD (J - (2 * k + 1)) ⊤ + single (2 * k + 1) else ⊤) ((J + 1) / 2))
        (if 2 ≤ P' then minUpTo (fun k => if 2 * k ≤ J then
          (look (P' - 2)).getD (J - 2 * k) ⊤ + pair (2 * k) else ⊤) (J / 2 + 1)
          else ⊤)

theorem pairRow_congr (single pair : ℕ → WithTop ℕ) (S : ℕ) (look look' : ℕ → Array (WithTop ℕ))
    (q : ℕ) (h : ∀ i < q, look i = look' i) :
    pairRow single pair S look q = pairRow single pair S look' q := by
  unfold pairRow
  congr 1
  funext J
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · rw [ite_eq_right hq, ite_eq_right hq, h (q - 1) (by omega)]
    by_cases h2 : 2 ≤ q
    · rw [ite_eq_left h2, ite_eq_left h2, h (q - 2) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2]

/-- **The pairs bound** `U₂(T)` at level `T`: the cheapest admissible partition whose link forest
has trees of at most two planes, from the one-plane table `table` (columns `0, …, Tmax`); `⊤` (no
bound) if `T > Tmax`. -/
def pairsBoundAt (d c : Fin n → ℕ) (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (T : ℕ) :
    WithTop ℕ :=
  if T ≤ Tmax then
    let G : ℕ → ℕ → WithTop ℕ := fun m τ => (table.getD m #[]).getD τ ⊤
    let reps := repList d c
    let pr := Array.ofFn (n := s + 1) fun j =>
      if (j : ℕ) % 2 = 0 then pairCost d c reps G T j else ⊤
    ((buildLayers (pairRow (fun m => G m T) (fun j => pr.getD j ⊤) s) #[] p).getD p #[]).getD s ⊤
  else ⊤

/-! ### The pairs bound is attained -/

/-- The one-plane table is attained: a finite entry is the cost of a multiset of that size and
load at most that budget. -/
theorem oneplaneTable_attained (d c : Fin n → ℕ) {Tmax s m τ w : ℕ} (hm : m ≤ s) (hτ : τ ≤ Tmax)
    (h : ((oneplaneTable d c Tmax s).getD m #[]).getD τ ⊤ = w) :
    ∃ Y : Multiset (Fin n), Y.card = m ∧ load d Y ≤ τ ∧ cost c Y = w := by
  rw [oneplaneTable_getD d c hm hτ] at h
  obtain ⟨Y, hY, hYload, hYcost⟩ := exists_cost_eq_oneplane (d := d) (c := c)
    (by rw [h]; exact WithTop.coe_ne_top)
  exact ⟨Y, hY, hYload, by rw [hYcost] at h; exact_mod_cast h⟩

/-- A tree, its groups' landings, cost and loads. -/
def TreeOK (d c : Fin n → ℕ) (T : ℕ) (t : LTree n) (q j v : ℕ) : Prop :=
  t.WF ∧ (t.groups 0).card = q ∧ ((t.groups 0).map Multiset.card).sum = j ∧
    ((t.groups 0).map (cost c)).sum = v ∧ ∀ g ∈ t.groups 0, load d g ≤ T

/-- A finite pair cost is a tree of two planes linked at a city. -/
theorem pairCost_attained (d c : Fin n → ℕ) {Tmax s T j w : ℕ} (hT : T ≤ Tmax) (hj : j ≤ s)
    (h : pairCost d c (repList d c) (fun m τ => ((oneplaneTable d c Tmax s).getD m #[]).getD τ ⊤)
      T j = w) : ∃ t : LTree n, TreeOK d c T t 2 j w := by
  unfold pairCost at h
  obtain ⟨b, -, h₁⟩ := minList_attained _ _ h
  split_ifs at h₁ with hdb
  · obtain ⟨k, hk, h₂⟩ := minUpTo_attained _ h₁
    split_ifs at h₂ with hcond
    · set r := 2 * k + 1 with hr
      have hr₁ : r % 2 = 1 := by omega
      obtain ⟨hr₂, hr₃'⟩ := hcond
      have hr₃ : r + 3 ≤ j := by omega
      beta_reduce at h₂
      obtain ⟨x, y, hx, hy, hxy⟩ := TreeData.coe_add_eq h₂
      obtain ⟨x₁, x₂, hx₁, hx₂, hx₁₂⟩ := TreeData.coe_add_eq hx
      have hcb : x₁ = 2 * c b := by exact_mod_cast hx₁.symm
      obtain ⟨Y₁, hY₁, hY₁load, hY₁cost⟩ :=
        oneplaneTable_attained d c (by omega) (by omega) hx₂
      obtain ⟨Y₂, hY₂, hY₂load, hY₂cost⟩ :=
        oneplaneTable_attained d c (by omega) (by omega) hy
      refine ⟨.node Y₁ (.cons b (.node Y₂ .nil) .nil),
        ⟨Nat.odd_iff.mpr (by rw [hY₁]; exact hr₁), ⟨Nat.odd_iff.mpr (by rw [hY₂]; exact hr₂),
          trivial⟩, trivial⟩, ?_, ?_, ?_, ?_⟩
      · simp [LTree.groups, LKids.groups]
      · simp only [LTree.groups, LKids.groups, LKids.labels, Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_zero, Multiset.sum_zero, Multiset.card_add, Multiset.card_cons,
          Multiset.card_zero, Multiset.card_singleton, add_zero, hY₁, hY₂]
        omega
      · simp only [LTree.groups, LKids.groups, LKids.labels, Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_zero, Multiset.sum_zero, cost_add, cost_cons, cost_zero, add_zero,
          hY₁cost, hY₂cost, show cost c {b} = c b by simp [cost]]
        omega
      · intro g hg
        simp only [LTree.groups, LKids.groups, LKids.labels, Multiset.mem_cons, Multiset.add_zero,
          Multiset.notMem_zero, or_false] at hg
        rcases hg with rfl | rfl
        · simp only [load_add, load_cons, load_zero, add_zero]
          omega
        · simp only [load_add, show load d {b} = d b by simp [load]]
          omega
    · exact absurd h₂ WithTop.top_ne_coe
  · exact absurd h₁ WithTop.top_ne_coe

/-- The pair costs at level `T`, for `j = 0, …, s`, from the one-plane table. -/
def pairArr (d c : Fin n → ℕ) (Tmax s T : ℕ) : Array (WithTop ℕ) :=
  Array.ofFn (n := s + 1) fun j => if (j : ℕ) % 2 = 0 then
    pairCost d c (repList d c) (fun m τ => ((oneplaneTable d c Tmax s).getD m #[]).getD τ ⊤) T j
  else ⊤

/-- The rows of forests of single planes and pairs at level `T`, for `0, …, P` planes. -/
def pairRows (d c : Fin n → ℕ) (Tmax s T P : ℕ) : Array (Array (WithTop ℕ)) :=
  buildLayers (pairRow (fun m => ((oneplaneTable d c Tmax s).getD m #[]).getD T ⊤)
    (fun j => (pairArr d c Tmax s T).getD j ⊤) s) #[] P

theorem pairsBoundAt_eq (d c : Fin n → ℕ) {p s Tmax T : ℕ} (hT : T ≤ Tmax) :
    pairsBoundAt d c p s Tmax (oneplaneTable d c Tmax s) T =
      ((pairRows d c Tmax s T p).getD p #[]).getD s ⊤ := by
  simp only [pairsBoundAt, hT, ↓reduceIte]
  rfl

/-- **The forests of single planes and pairs are attained**, by induction on the number of
planes. -/
theorem pairRows_attained (d c : Fin n → ℕ) {Tmax s T : ℕ} (hT : T ≤ Tmax) (P : ℕ) :
    ∀ P', P' ≤ P → ∀ J (v : ℕ), J ≤ s → ((pairRows d c Tmax s T P).getD P' #[]).getD J ⊤ = v →
      ∃ F : List (LTree n), (∀ t ∈ F, t.WF) ∧ (forestGroups F).card = P' ∧
        ((forestGroups F).map Multiset.card).sum = J ∧
        ((forestGroups F).map (cost c)).sum = v ∧ ∀ g ∈ forestGroups F, load d g ≤ T := by
  intro P'
  induction P' using Nat.strong_induction_on with
  | _ P' ih =>
  intro hP' J v hJ h
  rw [pairRows, buildLayers_getD _ _ (pairRow_congr _ _ _) hP'] at h
  simp only [pairRow, getD_ofFn, show J < s + 1 by omega, dite_true] at h
  by_cases hP0 : P' = 0
  · rw [ite_eq_left hP0] at h
    split_ifs at h with hJ0
    · have hv : v = 0 := by exact_mod_cast h.symm
      subst hv hJ0 hP0
      exact ⟨[], by simp, by simp [forestGroups], by simp [forestGroups],
        by simp [forestGroups], by simp [forestGroups]⟩
    · exact absurd h WithTop.top_ne_coe
  rw [ite_eq_right hP0] at h
  -- Prepend a tree to a forest.
  have hcons : ∀ (t : LTree n) (q j w : ℕ) (F : List (LTree n)) (a : ℕ),
      TreeOK d c T t q j w → (∀ t ∈ F, t.WF) → (forestGroups F).card = P' - q →
      ((forestGroups F).map Multiset.card).sum = J - j →
      ((forestGroups F).map (cost c)).sum = a → (∀ g ∈ forestGroups F, load d g ≤ T) →
      q ≤ P' → j ≤ J → a + w = v →
      ∃ F : List (LTree n), (∀ t ∈ F, t.WF) ∧ (forestGroups F).card = P' ∧
        ((forestGroups F).map Multiset.card).sum = J ∧
        ((forestGroups F).map (cost c)).sum = v ∧ ∀ g ∈ forestGroups F, load d g ≤ T := by
    intro t q j w F a ⟨ht₁, ht₂, ht₃, ht₄, ht₅⟩ hF₁ hF₂ hF₃ hF₄ hF₅ hq hj haw
    refine ⟨t :: F, fun u hu => ?_, ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact ht₁
      · exact hF₁ u hu
    · rw [forestGroups_cons, Multiset.card_add, ht₂, hF₂]
      omega
    · rw [forestGroups_cons, Multiset.map_add, Multiset.sum_add, ht₃, hF₃]
      omega
    · rw [forestGroups_cons, Multiset.map_add, Multiset.sum_add, ht₄, hF₄]
      omega
    · intro g hg
      rw [forestGroups_cons, Multiset.mem_add] at hg
      rcases hg with hg | hg
      · exact ht₅ g hg
      · exact hF₅ g hg
  rcases min_eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
  · -- One more single plane.
    obtain ⟨k, hk, h₁⟩ := minUpTo_attained _ h
    split_ifs at h₁ with hmJ
    · set m := 2 * k + 1 with hm
      have hodd : m % 2 = 1 := by omega
      obtain ⟨a, w, ha, hw, haw⟩ := TreeData.coe_add_eq h₁
      obtain ⟨F, hF₁, hF₂, hF₃, hF₄, hF₅⟩ := ih (P' - 1) (by omega) (by omega) (J - m) a
        (by omega) ha
      obtain ⟨Y, hY, hYload, hYcost⟩ := oneplaneTable_attained d c (by omega) hT hw
      refine hcons (.node Y .nil) 1 m w F a ⟨⟨Nat.odd_iff.mpr (by rw [hY]; exact hodd), trivial⟩,
        ?_, ?_, ?_, ?_⟩ hF₁ hF₂ hF₃ hF₄ hF₅ (by omega) (by omega) haw
      · simp [LTree.groups, LKids.groups]
      · simp [LTree.groups, LKids.groups, LKids.labels, hY]
      · simp [LTree.groups, LKids.groups, LKids.labels, hYcost]
      · intro g hg
        simp only [LTree.groups, LKids.groups, LKids.labels, Multiset.mem_cons,
          Multiset.notMem_zero, or_false] at hg
        subst hg
        simpa using hYload
    · exact absurd h₁ WithTop.top_ne_coe
  · -- One more pair.
    split_ifs at h with h2
    · obtain ⟨k, hk, h₁⟩ := minUpTo_attained _ h
      split_ifs at h₁ with hjJ
      swap
      · exact absurd h₁ WithTop.top_ne_coe
      set j := 2 * k with hj
      obtain ⟨a, w, ha, hw, haw⟩ := TreeData.coe_add_eq h₁
      obtain ⟨F, hF₁, hF₂, hF₃, hF₄, hF₅⟩ := ih (P' - 2) (by omega) (by omega) (J - j) a
        (by omega) ha
      have hw' : pairCost d c (repList d c)
          (fun m τ => ((oneplaneTable d c Tmax s).getD m #[]).getD τ ⊤) T j = w := by
        have h₃ := hw
        unfold pairArr at h₃
        rw [getD_ofFn, dite_eq_left (show j < s + 1 by omega)] at h₃
        simpa only [show j % 2 = 0 by omega, ↓reduceIte] using h₃
      obtain ⟨t, ht⟩ := pairCost_attained d c hT (by omega) hw'
      exact hcons t 2 j w F a ht hF₁ hF₂ hF₃ hF₄ hF₅ (by omega) (by omega) haw
    · exact absurd h WithTop.top_ne_coe

/-! ### The bracket -/

/-- **`E(T) ≤ U₂(T)`**: every finite value of the pairs bound is the cost of an admissible
partition of `2t − p` landings with loads at most `T`. -/
theorem minCost_le_pairsBoundAt (d c : Fin n → ℕ) {t p Tmax T : ℕ} (hT : T ≤ Tmax) :
    minCost d c t p T ≤
      pairsBoundAt d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T := by
  generalize hv : pairsBoundAt d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T = v
  cases v using WithTop.recTopCoe with
  | top => exact le_top
  | coe v =>
    rw [pairsBoundAt_eq d c hT] at hv
    obtain ⟨F, hwf, hcard, hsize, hcost, hload⟩ :=
      pairRows_attained d c hT p p le_rfl (2 * t - p) v le_rfl hv
    obtain ⟨hX, hmap⟩ := admissible_forestPartition F hwf hcard
    refine (minCost_le d c hX ?_ fun k => hload _ ?_).trans (le_of_eq ?_)
    · rw [size, Finset.sum_eq_multiset_sum,
        show (fun k => (forestPartition F p k).card) = Multiset.card ∘ forestPartition F p
          from rfl, ← Multiset.map_map, hmap, hsize]
    · rw [← hmap]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
    · rw [totalCost, Finset.sum_eq_multiset_sum,
        show (fun k => cost c (forestPartition F p k)) = cost c ∘ forestPartition F p from rfl,
        ← Multiset.map_map, hmap, hcost]
      rfl

/-- **`L(T) ≤ E(T)`**: the relaxation is at most the cost of every admissible partition. -/
theorem relaxedBoundAt_le_minCost (d c : Fin n → ℕ) {t p Tmax T : ℕ} :
    relaxedBoundAt p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T ≤
      minCost d c t p T :=
  le_sInf fun _ ⟨X, hX, hsize, hload, hx⟩ =>
    hx ▸ relaxedBoundAt_le_totalCost d c X (fun k => hX.card_pos k) hsize hload

/-- **The bracket closes**: where `L(T) = U₂(T)`, both are `E(T)`. -/
theorem minCost_eq_of_bracket (d c : Fin n → ℕ) {t p Tmax T : ℕ} (hT : T ≤ Tmax)
    (h : relaxedBoundAt p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T =
      pairsBoundAt d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T) :
    minCost d c t p T = relaxedBoundAt p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T :=
  le_antisymm (h ▸ minCost_le_pairsBoundAt d c hT) (relaxedBoundAt_le_minCost d c)

end ZenoFront
