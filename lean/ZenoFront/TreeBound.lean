/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.AdmissibleBound
public import ZenoFront.LinkForest

/-!
# The link-forest DP (Theorem 7.5, lower-bound direction)

The σ-DP (`AdmissibleBound.lean`) is exponential in the number of non-dominated cities. The
link-forest DP of §7.4 is polynomial in it, and pseudo-polynomial in the level `T`. This file
computes it and proves the direction the checker needs: the DP is **at most** the cost of every
admissible partition into `p` groups of total size `s` with loads at most `T`
(`treeBoundAt_le_totalCost`).

The tables are those of the note, with `q` the number of planes:

* `Ch_q[τ][j]`: child items (a link label and the subtree hanging from it) whose subtrees have
  `q` planes, whose labels have total duration `τ`, with `j` landings (one per label, in the
  parent, plus the subtrees');
* `Sub_b[q + 1][j]`: a subtree with `q + 1` planes and `j` landings, hanging from a link
  labelled `b` (one copy of `b` in its root's group);
* `Root[q + 1][j]`: a tree with `q + 1` planes and `j` landings;
* `For[P][J]`: a forest with `P` planes and `J` landings.

Each table entry is a minimum over the ways to build its object from smaller ones; a group's
free landings, of odd size `r` and duration at most the remaining budget, cost at least
`G[r][budget]`. The bound follows by induction on the rooted link trees (`LKids.chM_le`,
`LTree.subM_le`) of an admissible partition, which exist by Lemma 2.6
(`Admissible.exists_linkForest`). The other direction (the DP is exactly `E(T)`) is not needed.

The checker uses this DP or the σ-DP, whichever its cost estimate says is cheaper
(`forestBoundAt`); both are lower bounds.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n : ℕ}

/-! ### Small helpers -/

theorem getD_ofFn {α : Type} {m : ℕ} (f : Fin m → α) (i : ℕ) (d : α) :
    (Array.ofFn f).getD i d = if h : i < m then f ⟨i, h⟩ else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs <;> simp_all

theorem getD_push {α : Type} (a : Array α) (x : α) (i : ℕ) (d : α) :
    (a.push x).getD i d = if i < a.size then a.getD i d else if i = a.size then x else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs with h₁ h₂ <;> simp_all

theorem minUpTo_le (f : ℕ → WithTop ℕ) {m u : ℕ} (h : m < u) : minUpTo f u ≤ f m := by
  rw [minUpTo_eq]
  exact Finset.inf_le (mem_range.mpr h)

theorem minUpTo_congr {f g : ℕ → WithTop ℕ} {u : ℕ} (h : ∀ m < u, f m = g m) :
    minUpTo f u = minUpTo g u := by
  simp only [minUpTo_eq]
  exact Finset.inf_congr rfl fun m hm => h m (mem_range.mp hm)

/-- A minimum over a list. -/
def minList {β : Type} (l : List β) (f : β → WithTop ℕ) : WithTop ℕ :=
  l.foldr (fun b acc => min (f b) acc) ⊤

theorem minList_le {β : Type} (f : β → WithTop ℕ) : ∀ {l : List β} {b : β}, b ∈ l →
    minList l f ≤ f b
  | _ :: _, _, .head _ => min_le_left _ _
  | _ :: _, _, .tail _ h => (min_le_right _ _).trans (minList_le f h)

/-! ### Layers computed from the previous ones -/

/-- `buildLayers f dflt q` is `[L 0, …, L q]`, where `L i = f look i` and `look` reads the layers
`L 0, …, L (i − 1)` (and `dflt` beyond). -/
def buildLayers {α : Type} (f : (ℕ → α) → ℕ → α) (dflt : α) : ℕ → Array α
  | 0 => #[f (fun _ => dflt) 0]
  | q + 1 =>
    let a := buildLayers f dflt q
    a.push (f (fun i => a.getD i dflt) (q + 1))

section Layers

variable {α : Type} (f : (ℕ → α) → ℕ → α) (dflt : α)

theorem buildLayers_size : ∀ q, (buildLayers f dflt q).size = q + 1
  | 0 => rfl
  | q + 1 => by simp [buildLayers, buildLayers_size q]

theorem buildLayers_getD_of_le {i : ℕ} : ∀ {q : ℕ}, i ≤ q →
    (buildLayers f dflt q).getD i dflt = (buildLayers f dflt i).getD i dflt
  | 0, h => by rw [Nat.le_zero.mp h]
  | q + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · simp only [buildLayers, getD_push, buildLayers_size, show i < q + 1 by omega, ite_true]
      exact buildLayers_getD_of_le (by omega)
    · rfl

/-- **Unfolding a layer**, when `f` reads only the earlier layers. -/
theorem buildLayers_getD
    (hf : ∀ look look' q, (∀ i < q, look i = look' i) → f look q = f look' q)
    {q Q : ℕ} (hq : q ≤ Q) :
    (buildLayers f dflt Q).getD q dflt = f (fun i => (buildLayers f dflt Q).getD i dflt) q := by
  rw [buildLayers_getD_of_le f dflt hq]
  cases q with
  | zero => exact hf _ _ 0 fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ q =>
    simp only [buildLayers, getD_push, buildLayers_size, lt_irrefl, ite_false, ite_true]
    refine hf _ _ _ fun i hi => ?_
    rw [buildLayers_getD_of_le f dflt (show i ≤ q by omega),
      buildLayers_getD_of_le f dflt (show i ≤ Q by omega)]

end Layers

/-! ### The tables -/

/-- The data of the DP at one level: durations, costs, the cities allowed as link labels, the
one-plane table `G`, the level `T` and the number of landings `S`. -/
structure TreeData (n : ℕ) where
  d : Fin n → ℕ
  c : Fin n → ℕ
  reps : List (Fin n)
  G : ℕ → ℕ → WithTop ℕ
  T : ℕ
  S : ℕ

/-- A layer: `Ch_q[τ][j]` and `Sub_b[q + 1][j]`. -/
abbrev TLayer := Array (Array (WithTop ℕ)) × Array (Array (WithTop ℕ))

namespace TreeData

variable (D : TreeData n)

/-- `Ch_q[τ][j]`: add one child item (label `b`, subtree of `q₁ + 1` planes and `j₁` landings) to
child items with `q − 1 − q₁` planes. -/
def chEntry (look : ℕ → TLayer) (q τ j : ℕ) : WithTop ℕ :=
  if q = 0 then (if τ = 0 ∧ j = 0 then 0 else ⊤) else
    minUpTo (fun q₁ =>
      let A := (look (q - 1 - q₁)).1
      let B := (look q₁).2
      minList D.reps fun b =>
        if D.d b ≤ τ then
          let row := A.getD (τ - D.d b) #[]
          let srow := B.getD b #[]
          minUpTo (fun j₁ => row.getD (j - 1 - j₁) ⊤ + (D.c b : WithTop ℕ) + srow.getD j₁ ⊤) j
        else ⊤) q

/-- `Sub_b[q + 1][j₁]` from `ch = Ch_q`: the root holds one copy of `b`, child items of label
duration `τ` and `j₂` landings, and `j₁ − 1 − j₂` (odd) free landings within `T − d_b − τ`. -/
def subEntry (ch : Array (Array (WithTop ℕ))) (b : Fin n) (j₁ : ℕ) : WithTop ℕ :=
  (D.c b : WithTop ℕ) + minUpTo (fun τ =>
    if D.d b + τ ≤ D.T then
      let row := ch.getD τ #[]
      minUpTo (fun j₂ => if (j₁ - 1 - j₂) % 2 = 1 then
        row.getD j₂ ⊤ + D.G (j₁ - 1 - j₂) (D.T - D.d b - τ) else ⊤) j₁
    else ⊤) (D.T + 1)

/-- The table `Ch_q`, for `τ ≤ T` and `j ≤ S`. -/
def chArr (look : ℕ → TLayer) (q : ℕ) : Array (Array (WithTop ℕ)) :=
  Array.ofFn (n := D.T + 1) fun τ => Array.ofFn (n := D.S + 1) fun j => D.chEntry look q τ j

/-- The table `Sub_·[q + 1]`, for the allowed labels. -/
def subArr (ch : Array (Array (WithTop ℕ))) : Array (Array (WithTop ℕ)) :=
  Array.ofFn (n := n) fun b =>
    if b ∈ D.reps then Array.ofFn (n := D.S + 1) fun j₁ => D.subEntry ch b j₁ else #[]

/-- Layer `q`. -/
def layer (look : ℕ → TLayer) (q : ℕ) : TLayer :=
  let ch := D.chArr look q
  (ch, D.subArr ch)

/-- Layers `0, …, Q`. -/
def layers (Q : ℕ) : Array TLayer := buildLayers D.layer (#[], #[]) Q

/-- `Root[q + 1][j]` from `ch = Ch_q`. -/
def rootEntry (ch : Array (Array (WithTop ℕ))) (j : ℕ) : WithTop ℕ :=
  minUpTo (fun τ =>
    let row := ch.getD τ #[]
    minUpTo (fun j₂ => if (j - j₂) % 2 = 1 then row.getD j₂ ⊤ + D.G (j - j₂) (D.T - τ) else ⊤)
      (j + 1)) (D.T + 1)

/-- The table `Root[q + 1]` for `q < P`. -/
def roots (L : Array TLayer) (P : ℕ) : Array (Array (WithTop ℕ)) :=
  Array.ofFn (n := P) fun q => Array.ofFn (n := D.S + 1) fun j => D.rootEntry (L.getD q (#[], #[])).1 j

/-- `For[P'][J]`: add a tree of `q + 1` planes to a forest of `P' − 1 − q` planes. -/
def forEntry (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' J : ℕ) :
    WithTop ℕ :=
  if P' = 0 then (if J = 0 then 0 else ⊤) else
    minUpTo (fun q =>
      let prev := look (P' - 1 - q)
      let rrow := R.getD q #[]
      minUpTo (fun j => prev.getD (J - j) ⊤ + rrow.getD j ⊤) (J + 1)) P'

/-- The table `For[P'][·]`. -/
def forLayer (R : Array (Array (WithTop ℕ))) (look : ℕ → Array (WithTop ℕ)) (P' : ℕ) :
    Array (WithTop ℕ) :=
  Array.ofFn (n := D.S + 1) fun J => forEntry R look P' J

/-- `For[P][S]`, the value of the DP for `P` planes. -/
def value (P : ℕ) : WithTop ℕ :=
  let L := D.layers (P - 1)
  let R := D.roots L P
  ((buildLayers (D.forLayer R) #[] P).getD P #[]).getD D.S ⊤

/-! ### Reading the tables -/

/-- `Ch_q[τ][j]`, as stored. -/
def chM (Q q τ j : ℕ) : WithTop ℕ := (((D.layers Q).getD q (#[], #[])).1.getD τ #[]).getD j ⊤

/-- `Sub_b[q + 1][j]`, as stored. -/
def subM (Q q : ℕ) (b : Fin n) (j : ℕ) : WithTop ℕ :=
  (((D.layers Q).getD q (#[], #[])).2.getD b #[]).getD j ⊤

theorem chArr_congr {look look' : ℕ → TLayer} {q : ℕ} (h : ∀ i < q, look i = look' i) :
    D.chArr look q = D.chArr look' q := by
  unfold chArr
  congr 1
  funext τ
  congr 1
  funext j
  unfold chEntry
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · rw [ite_eq_right hq, ite_eq_right hq]
    refine minUpTo_congr fun q₁ hq₁ => ?_
    simp only [h (q - 1 - q₁) (by omega), h q₁ hq₁]

theorem layer_congr (look look' : ℕ → TLayer) (q : ℕ) (h : ∀ i < q, look i = look' i) :
    D.layer look q = D.layer look' q := by
  simp only [layer, D.chArr_congr h]

theorem layers_getD {Q q : ℕ} (hq : q ≤ Q) :
    (D.layers Q).getD q (#[], #[]) = D.layer (fun i => (D.layers Q).getD i (#[], #[])) q :=
  buildLayers_getD D.layer _ D.layer_congr hq

theorem chM_eq {Q q τ j : ℕ} (hq : q ≤ Q) (hτ : τ ≤ D.T) (hj : j ≤ D.S) :
    D.chM Q q τ j = D.chEntry (fun i => (D.layers Q).getD i (#[], #[])) q τ j := by
  rw [chM, D.layers_getD hq]
  simp only [layer, chArr, getD_ofFn, show τ < D.T + 1 by omega, show j < D.S + 1 by omega,
    dite_true]

theorem subM_eq {Q q : ℕ} {b : Fin n} {j : ℕ} (hq : q ≤ Q) (hb : b ∈ D.reps) (hj : j ≤ D.S) :
    D.subM Q q b j = D.subEntry ((D.layers Q).getD q (#[], #[])).1 b j := by
  rw [subM, D.layers_getD hq]
  simp only [layer, subArr, getD_ofFn, b.isLt, show j < D.S + 1 by omega, dite_true, hb,
    ite_true]

/-! ### One step of each table -/

theorem chM_zero (Q : ℕ) : D.chM Q 0 0 0 = 0 := by
  rw [D.chM_eq (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)]
  simp [chEntry]

/-- `Ch_q` is at most the cost of adding one item to cheaper items. -/
theorem chM_le {Q q τ j q₁ q₂ τ₂ j₁ j₂ : ℕ} {b : Fin n} (hq : q = q₁ + 1 + q₂) (hτ : τ = D.d b + τ₂)
    (hj : j = j₁ + 1 + j₂) (hQ : q ≤ Q) (hT : τ ≤ D.T) (hS : j ≤ D.S) (hb : b ∈ D.reps) :
    D.chM Q q τ j ≤ D.chM Q q₂ τ₂ j₂ + (D.c b : WithTop ℕ) + D.subM Q q₁ b j₁ := by
  rw [D.chM_eq hQ hT hS, chEntry, ite_eq_right (by omega)]
  refine (minUpTo_le _ (show q₁ < q by omega)).trans ?_
  refine (minList_le _ hb).trans ?_
  dsimp only
  rw [ite_eq_left (by omega)]
  refine (minUpTo_le _ (show j₁ < j by omega)).trans (le_of_eq ?_)
  rw [show q - 1 - q₁ = q₂ by omega, show τ - D.d b = τ₂ by omega, show j - 1 - j₁ = j₂ by omega]
  rfl

/-- `Sub_b[q + 1]` is at most the cost of a root holding `b`, child items and free landings. -/
theorem subM_le {Q q j₁ τ j₂ r : ℕ} {b : Fin n} (hj : j₁ = r + 1 + j₂) (hr : r % 2 = 1)
    (hτ : D.d b + τ ≤ D.T) (hQ : q ≤ Q) (hS : j₁ ≤ D.S) (hb : b ∈ D.reps) :
    D.subM Q q b j₁ ≤ (D.c b : WithTop ℕ) + (D.chM Q q τ j₂ + D.G r (D.T - D.d b - τ)) := by
  rw [D.subM_eq hQ hb hS, subEntry]
  refine add_le_add le_rfl ?_
  refine (minUpTo_le _ (show τ < D.T + 1 by omega)).trans ?_
  rw [ite_eq_left hτ]
  refine (minUpTo_le _ (show j₂ < j₁ by omega)).trans (le_of_eq ?_)
  rw [show j₁ - 1 - j₂ = r by omega, ite_eq_left hr]
  rfl

/-- `Root[q + 1]`, as stored. -/
def rootM (Q P q j : ℕ) : WithTop ℕ := ((D.roots (D.layers Q) P).getD q #[]).getD j ⊤

theorem rootM_le {Q P q j τ j₂ r : ℕ} (hj : j = r + j₂) (hr : r % 2 = 1) (hτ : τ ≤ D.T)
    (hP : q < P) (hS : j ≤ D.S) :
    D.rootM Q P q j ≤ D.chM Q q τ j₂ + D.G r (D.T - τ) := by
  simp only [rootM, roots, getD_ofFn, hP, show j < D.S + 1 by omega, dite_true, rootEntry]
  refine (minUpTo_le _ (show τ < D.T + 1 by omega)).trans ?_
  refine (minUpTo_le _ (show j₂ < j + 1 by omega)).trans (le_of_eq ?_)
  rw [show j - j₂ = r by omega, ite_eq_left hr]
  rfl

/-- `For[P']`, as stored. -/
def forM (Q P P' J : ℕ) : WithTop ℕ :=
  ((buildLayers (D.forLayer (D.roots (D.layers Q) P)) #[] P).getD P' #[]).getD J ⊤

theorem forLayer_congr (R : Array (Array (WithTop ℕ))) (look look' : ℕ → Array (WithTop ℕ))
    (q : ℕ) (h : ∀ i < q, look i = look' i) : D.forLayer R look q = D.forLayer R look' q := by
  unfold forLayer
  congr 1
  funext J
  unfold forEntry
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · rw [ite_eq_right hq, ite_eq_right hq]
    refine minUpTo_congr fun q₁ hq₁ => ?_
    simp only [h (q - 1 - q₁) (by omega)]

theorem forM_eq {Q P P' J : ℕ} (hP : P' ≤ P) (hS : J ≤ D.S) :
    D.forM Q P P' J = if P' = 0 then (if J = 0 then 0 else ⊤) else
      minUpTo (fun q => minUpTo (fun j => D.forM Q P (P' - 1 - q) (J - j) + D.rootM Q P q j)
        (J + 1)) P' := by
  rw [forM, buildLayers_getD _ _ (D.forLayer_congr _) hP]
  simp only [forLayer, getD_ofFn, show J < D.S + 1 by omega, dite_true, forEntry]
  rfl

theorem forM_zero (Q P : ℕ) : D.forM Q P 0 0 = 0 := by
  rw [D.forM_eq (Nat.zero_le _) (Nat.zero_le _)]
  simp

theorem forM_le {Q P P' J q P₂ j J₂ : ℕ} (hP' : P' = q + 1 + P₂) (hJ : J = j + J₂) (hP : P' ≤ P)
    (hS : J ≤ D.S) : D.forM Q P P' J ≤ D.forM Q P P₂ J₂ + D.rootM Q P q j := by
  rw [D.forM_eq hP hS, ite_eq_right (by omega)]
  refine (minUpTo_le _ (show q < P' by omega)).trans ?_
  refine (minUpTo_le _ (show j < J + 1 by omega)).trans (le_of_eq ?_)
  rw [show P' - 1 - q = P₂ by omega, show J - j = J₂ by omega]

end TreeData

/-! ### The tables bound the rooted link trees -/

theorem LTree.card_groups_pos (t : LTree n) (e : Multiset (Fin n)) : 0 < (t.groups e).card := by
  cases t with
  | node free kids => simp [LTree.groups]

theorem LTree.exists_mem_groups (t : LTree n) {e : Multiset (Fin n)} {x : Fin n} (hx : x ∈ e) :
    ∃ g ∈ t.groups e, x ∈ g := by
  cases t with
  | node free kids =>
    exact ⟨_, Multiset.mem_cons_self _ _, Multiset.mem_add.mpr (Or.inr hx)⟩

/-- A family of groups is *fine* at level `T` for the labels `reps`: every group has load at most
`T` and uses only cities of `reps`. -/
def FineGroups (D : TreeData n) (M : Multiset (Multiset (Fin n))) : Prop :=
  ∀ g ∈ M, load D.d g ≤ D.T ∧ ∀ x ∈ g, x ∈ D.reps

namespace TreeData

variable (D : TreeData n)

/-- The property of `G` used: `G[m][τ]` is at most the cost of every `m`-multiset of load
at most `τ`. -/
def GSound : Prop :=
  ∀ m τ (Y : Multiset (Fin n)), Y.card = m → m ≤ D.S → τ ≤ D.T → load D.d Y ≤ τ → D.G m τ ≤ cost D.c Y

end TreeData

section Trees

variable (D : TreeData n) (hG : D.GSound) (Q : ℕ)
include hG

set_option linter.unusedSectionVars false in
mutual
/-- **Child items cost at least their `Ch` entry.** -/
theorem LKids.chM_le : ∀ (k : LKids n), k.WF → FineGroups D k.groups → load D.d k.labels ≤ D.T →
    k.groups.card ≤ Q → k.labels.card + (k.groups.map Multiset.card).sum ≤ D.S →
    D.chM Q k.groups.card (load D.d k.labels) (k.labels.card + (k.groups.map Multiset.card).sum) ≤
      ((cost D.c k.labels + (k.groups.map (cost D.c)).sum : ℕ) : WithTop ℕ)
  | .nil, _, _, _, _, _ => by
    simp only [LKids.groups, LKids.labels, Multiset.card_zero, load_zero, Multiset.map_zero,
      Multiset.sum_zero, add_zero, cost_zero, Nat.cast_zero]
    exact (D.chM_zero Q).le
  | .cons b child rest, hwf, hfine, hT, hQ, hS => by
    obtain ⟨hchild, hrest⟩ := hwf
    simp only [LKids.groups, LKids.labels, Multiset.card_add, Multiset.card_cons, load_cons,
      Multiset.map_add, Multiset.sum_add, cost_cons] at hfine hT hQ hS ⊢
    have hfc : FineGroups D (child.groups {b}) := fun g hg => hfine g (Multiset.mem_add.mpr (.inl hg))
    have hfr : FineGroups D rest.groups := fun g hg => hfine g (Multiset.mem_add.mpr (.inr hg))
    have hb : b ∈ D.reps := by
      obtain ⟨g, hg, hbg⟩ := child.exists_mem_groups (Multiset.mem_singleton_self b)
      exact (hfc g hg).2 b hbg
    obtain ⟨q₁, hq₁⟩ : ∃ q₁, (child.groups {b}).card = q₁ + 1 :=
      Nat.exists_eq_add_one.mpr (child.card_groups_pos {b})
    have hstep := D.chM_le (Q := Q) (q := (child.groups {b}).card + rest.groups.card)
      (τ := D.d b + load D.d rest.labels)
      (j := rest.labels.card + 1 + (((child.groups {b}).map Multiset.card).sum +
        (rest.groups.map Multiset.card).sum)) (q₁ := q₁) (q₂ := rest.groups.card)
      (τ₂ := load D.d rest.labels) (j₁ := ((child.groups {b}).map Multiset.card).sum)
      (j₂ := rest.labels.card + (rest.groups.map Multiset.card).sum) (b := b)
      (by omega) rfl (by omega) hQ hT hS hb
    have hR := LKids.chM_le rest hrest hfr (by omega) (by omega) (by omega)
    have hC := LTree.subM_le child b hchild hb hfc (by omega) (by omega)
    rw [hq₁, Nat.add_sub_cancel] at hC
    refine hstep.trans ((add_le_add (add_le_add hR le_rfl) hC).trans (le_of_eq ?_))
    norm_cast
    omega

/-- **A hanging subtree costs at least its `Sub` entry.** -/
theorem LTree.subM_le : ∀ (t : LTree n) (a : Fin n), t.WF → a ∈ D.reps →
    FineGroups D (t.groups {a}) → (t.groups {a}).card ≤ Q + 1 →
    ((t.groups {a}).map Multiset.card).sum ≤ D.S →
    D.subM Q ((t.groups {a}).card - 1) a ((t.groups {a}).map Multiset.card).sum ≤
      (((t.groups {a}).map (cost D.c)).sum : WithTop ℕ)
  | .node free kids, a, hwf, ha, hfine, hQ, hS => by
    obtain ⟨hfree, hkids⟩ := hwf
    have hroot := (hfine _ (Multiset.mem_cons_self _ _)).1
    have hfk : FineGroups D kids.groups := fun g hg => hfine g (Multiset.mem_cons_of_mem hg)
    simp only [LTree.groups, Multiset.card_cons, Nat.add_sub_cancel, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_add, Multiset.card_singleton, load_add,
      cost_add] at hroot hQ hS ⊢
    simp only [show load D.d {a} = D.d a by simp [load], show cost D.c {a} = D.c a by simp [cost]]
      at hroot ⊢
    have hstep := D.subM_le (Q := Q) (q := kids.groups.card) (τ := load D.d kids.labels)
      (j₁ := free.card + kids.labels.card + 1 + (kids.groups.map Multiset.card).sum)
      (j₂ := kids.labels.card + (kids.groups.map Multiset.card).sum) (r := free.card) (b := a)
      (by omega) (Nat.odd_iff.mp hfree) (by omega) (by omega) (by omega) ha
    have hK := LKids.chM_le kids hkids hfk (by omega) (by omega) (by omega)
    have hF := hG free.card (D.T - D.d a - load D.d kids.labels) free rfl (by omega) (by omega)
      (by omega)
    refine hstep.trans ((add_le_add le_rfl (add_le_add hK hF)).trans (le_of_eq ?_))
    norm_cast
    omega
end

/-- **A tree costs at least its `Root` entry.** -/
theorem LTree.rootM_le (P : ℕ) (hPQ : P ≤ Q + 1) (t : LTree n) (hwf : t.WF)
    (hfine : FineGroups D (t.groups 0)) (hP : (t.groups 0).card ≤ P)
    (hS : ((t.groups 0).map Multiset.card).sum ≤ D.S) :
    D.rootM Q P ((t.groups 0).card - 1) ((t.groups 0).map Multiset.card).sum ≤
      (((t.groups 0).map (cost D.c)).sum : WithTop ℕ) := by
  cases t with
  | node free kids =>
    obtain ⟨hfree, hkids⟩ := hwf
    have hroot := (hfine _ (Multiset.mem_cons_self _ _)).1
    have hfk : FineGroups D kids.groups := fun g hg => hfine g (Multiset.mem_cons_of_mem hg)
    simp only [LTree.groups, Multiset.card_cons, Nat.add_sub_cancel, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_add, add_zero, load_add, cost_add] at hroot hP hS ⊢
    have hstep := D.rootM_le (Q := Q) (P := P) (q := kids.groups.card) (τ := load D.d kids.labels)
      (j := free.card + kids.labels.card + (kids.groups.map Multiset.card).sum)
      (j₂ := kids.labels.card + (kids.groups.map Multiset.card).sum) (r := free.card)
      (by omega) (Nat.odd_iff.mp hfree) (by omega) (by omega) (by omega)
    have hK := LKids.chM_le D hG Q kids hkids hfk (by omega) (by omega) (by omega)
    have hF := hG free.card (D.T - load D.d kids.labels) free rfl (by omega) (by omega) (by omega)
    refine hstep.trans ((add_le_add hK hF).trans (le_of_eq ?_))
    norm_cast
    omega

/-- **A forest costs at least its `For` entry.** -/
theorem forM_le_forest (P : ℕ) (hPQ : P ≤ Q + 1) : ∀ (F : List (LTree n)), (∀ t ∈ F, t.WF) →
    FineGroups D (forestGroups F) → (forestGroups F).card ≤ P →
    ((forestGroups F).map Multiset.card).sum ≤ D.S →
    D.forM Q P (forestGroups F).card ((forestGroups F).map Multiset.card).sum ≤
      (((forestGroups F).map (cost D.c)).sum : WithTop ℕ)
  | [], _, _, _, _ => by simp [forestGroups, D.forM_zero]
  | t :: F, hwf, hfine, hP, hS => by
    simp only [forestGroups, List.map_cons, List.sum_cons] at hfine hP hS ⊢
    change FineGroups D (t.groups 0 + forestGroups F) at hfine
    change (t.groups 0 + forestGroups F).card ≤ P at hP
    change ((t.groups 0 + forestGroups F).map Multiset.card).sum ≤ D.S at hS
    change D.forM Q P (t.groups 0 + forestGroups F).card
      ((t.groups 0 + forestGroups F).map Multiset.card).sum ≤
        (((t.groups 0 + forestGroups F).map (cost D.c)).sum : WithTop ℕ)
    simp only [Multiset.card_add, Multiset.map_add, Multiset.sum_add] at hP hS ⊢
    have hft : FineGroups D (t.groups 0) := fun g hg => hfine g (Multiset.mem_add.mpr (.inl hg))
    have hfF : FineGroups D (forestGroups F) := fun g hg =>
      hfine g (Multiset.mem_add.mpr (.inr hg))
    have hpos := t.card_groups_pos 0
    have hstep := D.forM_le (Q := Q) (P := P) (P' := (t.groups 0).card + (forestGroups F).card)
      (J := ((t.groups 0).map Multiset.card).sum + ((forestGroups F).map Multiset.card).sum)
      (q := (t.groups 0).card - 1)
      (P₂ := (forestGroups F).card) (j := ((t.groups 0).map Multiset.card).sum)
      (J₂ := ((forestGroups F).map Multiset.card).sum) (by omega) rfl hP hS
    have hR := t.rootM_le D hG Q P hPQ (hwf t List.mem_cons_self) hft (by omega) (by omega)
    have hF := forM_le_forest P hPQ F (fun u hu => hwf u (List.mem_cons_of_mem _ hu)) hfF
      (by omega) (by omega)
    refine hstep.trans ((add_le_add hF hR).trans (le_of_eq ?_))
    norm_cast
    omega

omit hG in
theorem TreeData.value_eq (P : ℕ) : D.value P = D.forM (P - 1) P P D.S := rfl

/-- **The link-forest DP is a lower bound**: at most the cost of every admissible grouping into
`P` groups of total size `S` whose groups have loads at most `T` and use only the labels
`reps`. -/
theorem TreeData.value_le_totalCost {P : ℕ} (hP : 1 ≤ P) {X : Groups n P} (hX : Admissible X)
    (hsize : size X = D.S) (hfine : ∀ k, load D.d (X k) ≤ D.T ∧ ∀ x ∈ X k, x ∈ D.reps) :
    D.value P ≤ (totalCost D.c X : WithTop ℕ) := by
  obtain ⟨F, hwf, hF⟩ := hX.exists_linkForest
  have hcard : (forestGroups F).card = P := by simp [hF]
  have hsum : ((forestGroups F).map Multiset.card).sum = D.S := by
    rw [hF, ← hsize, size, Multiset.map_map]
    rfl
  have hcost : ((forestGroups F).map (cost D.c)).sum = totalCost D.c X := by
    rw [hF, totalCost, Multiset.map_map]
    rfl
  have hfg : FineGroups D (forestGroups F) := fun g hg => by
    rw [hF] at hg
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hfine k
  have := forM_le_forest D hG (P - 1) P (by omega) F hwf hfg hcard.le hsum.le
  rw [hcard, hsum, hcost] at this
  rw [TreeData.value_eq]
  exact this

end Trees

/-! ### The bound of the checker -/

/-- The link labels: the non-dominated representatives, listed. -/
def repList (d c : Fin n → ℕ) : List (Fin n) := (List.finRange n).filter (· ∈ domReps d c)

theorem mem_repList {d c : Fin n → ℕ} {b : Fin n} : b ∈ repList d c ↔ b ∈ domReps d c := by
  simp [repList]

/-- The tree-DP bound for a `forest` gap at level `T`, with the one-plane table `table` (columns
`0, …, Tmax`); `0` (no bound) if `T > Tmax`. -/
def treeBoundAt (d c : Fin n → ℕ) (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (T : ℕ) :
    WithTop ℕ :=
  if T ≤ Tmax then
    TreeData.value ⟨d, c, repList d c, fun m τ => (table.getD m #[]).getD τ ⊤, T, s⟩ p
  else 0

/-- **The tree-DP bound is a lower bound**: at most the cost of every admissible grouping into
`p ≥ 1` groups of total size `s` with loads at most `T`, for the table `oneplaneTable d c Tmax s`.
Cities are first merged into their non-dominated representatives, the labels of the DP. -/
theorem treeBoundAt_le_totalCost (d c : Fin n → ℕ) {p s Tmax T : ℕ} (hp : 1 ≤ p)
    {X : Groups n p} (hX : Admissible X) (hsize : size X = s) (hT : ∀ k, load d (X k) ≤ T) :
    treeBoundAt d c p s Tmax (oneplaneTable d c Tmax s) T ≤ (totalCost c X : WithTop ℕ) := by
  classical
  unfold treeBoundAt
  split_ifs with hTmax
  · set D : TreeData n := ⟨d, c, repList d c,
      fun m τ => ((oneplaneTable d c Tmax s).getD m #[]).getD τ ⊤, T, s⟩
    have hG : D.GSound := fun m τ Y hY hm hτ hload => by
      simp only [D]
      rw [oneplaneTable_getD d c hm (hτ.trans hTmax)]
      exact oneplane_le_cost hY hload
    set X' : Groups n p := fun k => (X k).map (domRep d c) with hX'
    have hsize' : size X' = s := by rw [← hsize]; simp [size, hX']
    have hload : ∀ k, load d (X' k) ≤ load d (X k) := fun k => by
      simp only [hX', load, Multiset.map_map]
      exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).1
    have hcost : totalCost c X' ≤ totalCost c X := Finset.sum_le_sum fun k _ => by
      simp only [hX', cost, Multiset.map_map]
      exact Multiset.sum_map_le_sum_map _ _ fun i _ => (domRep_le d c i).2
    have hfine : ∀ k, load D.d (X' k) ≤ D.T ∧ ∀ x ∈ X' k, x ∈ D.reps := fun k =>
      ⟨(hload k).trans (hT k), fun x hx => by
        obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
        exact mem_repList.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
    exact (D.value_le_totalCost hG hp (hX.map (domRep d c)) hsize' hfine).trans
      (WithTop.coe_le_coe.mpr hcost)
  · exact bot_le

/-- `m` choose `k`, by the multiplicative formula (for the cost estimate only). -/
def binomEst (m k : ℕ) : ℕ := (List.range k).foldl (fun acc i => acc * (m - i) / (i + 1)) 1

/-- Whether the tree DP is estimated cheaper than the σ-DP at level `T`. The σ-DP's work grows
with the square of its number of states (subsets of at most `min(p − 1, t − p)` labels); the tree
DP's with `p · T` times the number of labels. -/
def useTreeDP (d c : Fin n → ℕ) (p t T : ℕ) : Bool :=
  let R := (repList d c).length
  let states := (List.range (min (p - 1) (t - p) + 1)).foldl (fun acc k => acc + binomEst R k) 0
  decide (p * (T + 1) * R < states * states)

/-- The bound the checker uses for a `forest` gap at level `T`: the tree DP or the σ-DP,
whichever `useTreeDP` estimates cheaper. -/
def forestBoundAt (d c : Fin n → ℕ) (p t s Tmax : ℕ) (table : Array (Array (WithTop ℕ)))
    (T : ℕ) : WithTop ℕ :=
  if useTreeDP d c p t T then treeBoundAt d c p s Tmax table T
  else sigmaBoundAt d c p t s Tmax table T

/-- **The forest bound is a lower bound**: at most the cost of every admissible grouping into
`p ≤ t` groups of total size `s = 2t − p` with loads at most `T`. Both DPs are. -/
theorem forestBoundAt_le_totalCost (d c : Fin n → ℕ) {p t Tmax T : ℕ} (hp : 1 ≤ p) (hpt : p ≤ t)
    {X : Groups n p} (hX : Admissible X) (hsize : size X = 2 * t - p)
    (hT : ∀ k, load d (X k) ≤ T) :
    forestBoundAt d c p t (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T ≤
      (totalCost c X : WithTop ℕ) := by
  unfold forestBoundAt
  split_ifs
  · exact treeBoundAt_le_totalCost d c hp hX hsize hT
  · exact sigmaBoundAt_le_totalCost d c hp hpt hX hsize hT

end ZenoFront
