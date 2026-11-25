/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Model
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Multiset.Sort

/-!
# The `search` kind of format v2: the exhaustive search

A `search` gap of a certificate claims that no role configuration of cost below `C_i` has a
schedule finishing before `M_{i+1}` (`searchGap` and `exactSchedule` in
`src/zeno/ns_search.cpp`). By Theorem 5.3 (schedulable domination) of the theory note this rules
out every feasible plan (`schedulableDomination_all`, `DominationAll.lean`). This file has the
search and its statement:

* `Sched`: a *scheduled configuration*. Per plane it has an ordered list of drop-offs, an ordered
  list of pick-ups and a multiset of crossings, and a *matching* `mate` from pick-up slots
  `(v, l)` to drop-off slots `(u, j)` of the same city.
* `Sched.tmpl`: the closed form of Lemma 5.5. It is the maximum of the role loads and of
  `Pre_u(j) + d_x + d̄_x + Suf_v(l)` over the links, in scaled units.
* `SearchData.closed`: an executable search over every scheduled configuration of cost below the
  bound. It enumerates every drop-off order, pick-up order, crossing multiset and matching (self
  links included), with no reduction.
* `SearchData.closed_sound` (**completeness of the enumeration**): if the search reports the gap
  closed, every valid scheduled configuration with `s` landings and cost below the bound has
  `tmpl > T`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Scheduled configurations and the closed form of Lemma 5.5 -/

/-- A scheduled role configuration: drop-offs and pick-ups in order, crossings, and the matching
from each pick-up slot `(v, l)` to the drop-off slot `(u, j)` whose passenger it collects. -/
structure Sched (n p : ℕ) where
  drops : Fin p → List (Fin n)
  picks : Fin p → List (Fin n)
  cross : Fin p → Multiset (Fin n)
  mate : Fin p → ℕ → Fin p × ℕ

namespace Sched

variable (S : Sched n p)

/-- A valid scheduled configuration: odd crossings, and a matching that sends every pick-up slot
to a drop-off slot of the same city, injectively, with as many drop-offs as pick-ups (so it is a
bijection, and drop-offs and pick-ups balance city by city). -/
structure Valid : Prop where
  odd : ∀ k, Odd (S.cross k).card
  city : ∀ v l, l < (S.picks v).length →
    (S.drops (S.mate v l).1)[(S.mate v l).2]? = (S.picks v)[l]?
  inj : ∀ v l v' l', l < (S.picks v).length → l' < (S.picks v').length →
    S.mate v l = S.mate v' l' → v = v' ∧ l = l'
  count : ∑ k, (S.drops k).length = ∑ k, (S.picks k).length

/-- The number of landings. -/
def size : ℕ := ∑ k, ((S.drops k).length + (S.picks k).length + (S.cross k).card)

/-- The cost. -/
def cost (c : Fin n → ℕ) : ℕ :=
  ∑ k, (((S.drops k).map c).sum + ((S.picks k).map c).sum + ZenoFront.cost c (S.cross k))

/-- The role load of plane `k`, for durations `d` (via `C_I`) and `db` (via `C_G`). -/
def load (d db : Fin n → ℕ) (k : Fin p) : ℕ :=
  2 * ((S.drops k).map d).sum + 2 * ((S.picks k).map db).sum + ZenoFront.load d (S.cross k) +
    ZenoFront.load db (S.cross k)

/-- `Pre_u(j)`: the drop-offs of `u` before its `j`-th. -/
def pre (d : Fin n → ℕ) (u : Fin p) (j : ℕ) : ℕ := 2 * (((S.drops u).take j).map d).sum

/-- `Suf_v(l)`: the pick-ups of `v` after its `l`-th. -/
def suf (db : Fin n → ℕ) (v : Fin p) (l : ℕ) : ℕ := 2 * (((S.picks v).drop (l + 1)).map db).sum

/-- The term of the link into pick-up slot `(v, l)`, at its city `x`. -/
def term (d db : Fin n → ℕ) (v : Fin p) (l : Fin (S.picks v).length) : ℕ :=
  S.pre d (S.mate v l).1 (S.mate v l).2 + d (S.picks v)[l] + db (S.picks v)[l] + S.suf db v l

/-- **The closed form of Lemma 5.5**: the largest role load and link term. -/
def tmpl (d db : Fin n → ℕ) : ℕ :=
  max (univ.sup fun k => S.load d db k) (univ.sup fun v => univ.sup fun l => S.term d db v l)

end Sched

/-! ### The search -/

/-- The data of a search: scaled durations, costs, planes, landings, the level `T` (a
schedule finishing within `T` is a counterexample) and the cost bound `C` (`⊤` for none). -/
structure SearchData (n : ℕ) where
  d : Fin n → ℕ
  db : Fin n → ℕ
  c : Fin n → ℕ
  p : ℕ
  s : ℕ
  T : ℕ
  C : WithTop ℕ

/-- All lists of cities of length at most `L` and weight at most `T`. -/
def wlists (w : Fin n → ℕ) : ℕ → ℕ → List (List (Fin n))
  | 0, _ => [[]]
  | L + 1, T => [] :: (List.finRange n).flatMap fun i =>
      if w i ≤ T then (wlists w L (T - w i)).map (i :: ·) else []

/-- All non-decreasing lists of cities `≥ lo`, of length at most `L` and weight at most `T`. -/
def slists (w : Fin n → ℕ) : ℕ → ℕ → ℕ → List (List (Fin n))
  | 0, _, _ => [[]]
  | L + 1, T, lo => [] :: ((List.finRange n).filter fun i => lo ≤ i.val).flatMap fun i =>
      if w i ≤ T then (slists w L (T - w i) i.val).map (i :: ·) else []

/-- A plane option: drop-offs and pick-ups in order, and crossings (sorted). -/
abbrev POpt (n : ℕ) := List (Fin n) × List (Fin n) × List (Fin n)

namespace SearchData

variable (D : SearchData n)

/-- The role load of a plane option. -/
def optLoad (o : POpt n) : ℕ :=
  2 * (o.1.map D.d).sum + 2 * (o.2.1.map D.db).sum + (o.2.2.map fun i => D.d i + D.db i).sum

/-- The cost of a plane option. -/
def optCost (o : POpt n) : ℕ := (o.1.map D.c).sum + (o.2.1.map D.c).sum + (o.2.2.map D.c).sum

/-- The landings of a plane option. -/
def optLand (o : POpt n) : ℕ := o.1.length + o.2.1.length + o.2.2.length

/-- The plane options: role load at most `T`, an odd number of crossings, at most `s`
landings, cost below `C`. -/
def opts : List (POpt n) :=
  (wlists (fun i => 2 * D.d i) D.s D.T).flatMap fun dr =>
    (wlists (fun i => 2 * D.db i) D.s D.T).flatMap fun pk =>
      (slists (fun i => D.d i + D.db i) D.s D.T 0).filterMap fun cr =>
        let o : POpt n := (dr, pk, cr)
        if D.optLoad o ≤ D.T ∧ cr.length % 2 = 1 ∧ optLand (n := n) o ≤ D.s ∧
            (D.optCost o : WithTop ℕ) < D.C then some o else none

/-- All lists of `k` plane options with total cost below `C` (counting `acc` already spent) and
at most `L` landings. -/
def tuples (os : List (POpt n)) : ℕ → ℕ → ℕ → List (List (POpt n))
  | 0, _, _ => [[]]
  | k + 1, acc, L => os.flatMap fun o =>
      if ((acc + D.optCost o : ℕ) : WithTop ℕ) < D.C ∧ optLand (n := n) o ≤ L then
        (tuples os k (acc + D.optCost o) (L - optLand (n := n) o)).map (o :: ·)
      else []

/-- The drop-off slots `(u, j, city)` and pick-up slots `(v, l, city)` of a tuple. -/
def dropSlots (tu : List (POpt n)) : List (ℕ × ℕ × Fin n) :=
  (List.range tu.length).flatMap fun u =>
    ((tu.getD u ([], [], [])).1.zipIdx).map fun x => (u, x.2, x.1)

/-- The pick-up slots `(v, l, city)` of a tuple. -/
def pickSlots (tu : List (POpt n)) : List (ℕ × ℕ × Fin n) :=
  (List.range tu.length).flatMap fun v =>
    ((tu.getD v ([], [], [])).2.1.zipIdx).map fun x => (v, x.2, x.1)

/-- Every injective assignment of the pick-up slots to available drop-off slots of the same city. -/
def assignments : List (ℕ × ℕ × Fin n) → List (ℕ × ℕ × Fin n) → List (List (ℕ × ℕ × Fin n))
  | [], _ => [[]]
  | x :: xs, avail => (avail.filter fun y => y.2.2 = x.2.2).flatMap fun y =>
      (assignments xs (avail.erase y)).map (y :: ·)

/-- The closed form of a tuple with an assignment: the largest role load and link term. -/
def tmplOf (tu : List (POpt n)) (asg : List (ℕ × ℕ × Fin n)) : ℕ :=
  let loads := (tu.map D.optLoad).foldr max 0
  let terms := ((pickSlots tu).zip asg).map fun (x, y) =>
    let pk := (tu.getD x.1 ([], [], [])).2.1
    let dr := (tu.getD y.1 ([], [], [])).1
    2 * ((dr.take y.2.1).map D.d).sum + D.d x.2.2 + D.db x.2.2 +
      2 * ((pk.drop (x.2.1 + 1)).map D.db).sum
  max loads (terms.foldr max 0)

/-- Whether a tuple is a full configuration: `s` landings, and as many drop-offs as pick-ups.
(An injective assignment of pick-ups to drop-offs of the same city is then a bijection, so they
balance city by city.) -/
def full (tu : List (POpt n)) : Bool :=
  decide ((tu.map (optLand (n := n))).sum = D.s) &&
    decide ((tu.map fun o => o.1.length).sum = (tu.map fun o => o.2.1.length).sum)

/-- **The search**: `true` (the gap is closed) iff no full tuple of plane options has an
assignment whose closed form is at most `T`. -/
def closed : Bool :=
  let os := D.opts
  (D.tuples os D.p 0 D.s).all fun tu =>
    !D.full tu || (assignments (pickSlots tu) (dropSlots tu)).all fun asg => decide (D.T < D.tmplOf tu asg)

/-! ### Completeness of the enumeration -/

theorem mem_wlists (w : Fin n → ℕ) : ∀ (L T : ℕ) (l : List (Fin n)), l.length ≤ L →
    (l.map w).sum ≤ T → l ∈ wlists w L T
  | 0, _, l, hl, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    simp [wlists]
  | _ + 1, _, [], _, _ => by simp [wlists]
  | L + 1, T, i :: l, hl, hw => by
    simp only [List.length_cons, List.map_cons, List.sum_cons] at hl hw
    simp only [wlists]
    refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
    rw [ite_eq_left (by omega)]
    exact List.mem_map.mpr ⟨l, mem_wlists w L (T - w i) l (by omega) (by omega), rfl⟩

theorem mem_slists (w : Fin n → ℕ) : ∀ (L T lo : ℕ) (l : List (Fin n)), l.length ≤ L →
    (l.map w).sum ≤ T → l.Pairwise (· ≤ ·) → (∀ i ∈ l, lo ≤ i.val) → l ∈ slists w L T lo
  | 0, _, _, l, hl, _, _, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    simp [slists]
  | _ + 1, _, _, [], _, _, _, _ => by simp [slists]
  | L + 1, T, lo, i :: l, hl, hw, hs, hlo => by
    obtain ⟨hi, hs'⟩ := List.pairwise_cons.mp hs
    simp only [List.length_cons, List.map_cons, List.sum_cons] at hl hw
    simp only [slists]
    refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr
      ⟨List.mem_finRange i, by simpa using hlo i List.mem_cons_self⟩, ?_⟩)
    rw [ite_eq_left (by omega)]
    exact List.mem_map.mpr ⟨l, mem_slists w L (T - w i) i.val l (by omega) (by omega) hs'
      (fun j hj => hi j hj), rfl⟩

theorem mem_assignments (f : ℕ × ℕ × Fin n → ℕ × ℕ × Fin n) :
    ∀ (xs avail : List (ℕ × ℕ × Fin n)), xs.Nodup → avail.Nodup → (∀ x ∈ xs, f x ∈ avail) →
      (∀ x ∈ xs, (f x).2.2 = x.2.2) → (∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) →
      xs.map f ∈ assignments xs avail
  | [], _, _, _, _, _, _ => by simp [assignments]
  | x :: xs, avail, hxs, hav, hmem, hcity, hinj => by
    obtain ⟨hx, hxs'⟩ := List.nodup_cons.mp hxs
    simp only [assignments, List.map_cons]
    refine List.mem_flatMap.mpr ⟨f x, List.mem_filter.mpr ⟨hmem x List.mem_cons_self,
      by simpa using hcity x List.mem_cons_self⟩, List.mem_map.mpr ⟨xs.map f, ?_, rfl⟩⟩
    refine mem_assignments f xs (avail.erase (f x)) hxs' (hav.erase _) (fun y hy => ?_)
      (fun y hy => hcity y (List.mem_cons_of_mem _ hy))
      (fun y hy z hz => hinj y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))
    have hne : f y ≠ f x := fun h =>
      hx ((hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self h) ▸ hy)
    exact (List.mem_erase_of_ne hne).mpr (hmem y (List.mem_cons_of_mem _ hy))

theorem mem_pickSlots {tu : List (POpt n)} {v l : ℕ} {x : Fin n} :
    (v, l, x) ∈ pickSlots tu ↔ v < tu.length ∧ (tu.getD v ([], [], [])).2.1[l]? = some x := by
  simp only [pickSlots, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨v', hv', ⟨y, i⟩, hy, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hv', List.mem_zipIdx_iff_getElem?.mp hy⟩
  · rintro ⟨hv, hx⟩
    exact ⟨v, hv, (x, l), List.mem_zipIdx_iff_getElem?.mpr hx, rfl⟩

theorem mem_dropSlots {tu : List (POpt n)} {u j : ℕ} {x : Fin n} :
    (u, j, x) ∈ dropSlots tu ↔ u < tu.length ∧ (tu.getD u ([], [], [])).1[j]? = some x := by
  simp only [dropSlots, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨u', hu', ⟨y, i⟩, hy, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hu', List.mem_zipIdx_iff_getElem?.mp hy⟩
  · rintro ⟨hu, hx⟩
    exact ⟨u, hu, (x, j), List.mem_zipIdx_iff_getElem?.mpr hx, rfl⟩

theorem nodup_zipIdx {α : Type} (l : List α) : l.zipIdx.Nodup :=
  List.Nodup.of_map Prod.snd (by rw [List.zipIdx_map_snd]; exact List.nodup_range')

theorem nodup_slots (g : POpt n → List (Fin n)) (tu : List (POpt n)) :
    ((List.range tu.length).flatMap fun v =>
      ((g (tu.getD v ([], [], []))).zipIdx).map fun x => (v, x.2, x.1)).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun v _ => ?_, ?_⟩
  · refine List.Nodup.map (fun a b h => ?_) (nodup_zipIdx _)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2 h.2.1
  · refine List.Pairwise.imp (fun {a b} hab => ?_) List.nodup_range
    refine List.disjoint_left.mpr fun x hx hy => hab ?_
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hy
    exact (Prod.mk.injEq _ _ _ _ ▸ hz).1.symm

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α,
    l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x l ih =>
    exact max_le (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem sort_map_sum (f : Fin n → ℕ) (X : Multiset (Fin n)) :
    ((X.sort (· ≤ ·)).map f).sum = (X.map f).sum := by
  have := Multiset.sort_eq X (· ≤ ·)
  conv_rhs => rw [← this]
  rw [Multiset.map_coe, Multiset.sum_coe]

/-- **Completeness of the enumeration.** If the search reports the gap closed, every valid
scheduled configuration with `s` landings and cost below `C` has closed form above `T`. -/
theorem closed_sound (h : D.closed = true) (S : Sched n D.p) (hv : S.Valid)
    (hsize : S.size = D.s) (hcost : (S.cost D.c : WithTop ℕ) < D.C) :
    D.T < S.tmpl D.d D.db := by
  classical
  by_cases hload : ∃ k, D.T < S.load D.d D.db k
  · obtain ⟨k, hk⟩ := hload
    exact lt_of_lt_of_le hk ((Finset.le_sup (f := fun k => S.load D.d D.db k)
      (Finset.mem_univ k)).trans (le_max_left _ _))
  push Not at hload
  set tu : List (POpt n) := List.ofFn fun k => (S.drops k, S.picks k, (S.cross k).sort (· ≤ ·))
    with htu
  have hlen : tu.length = D.p := by simp [htu]
  have hget : ∀ k : Fin D.p, tu.getD k.val ([], [], []) =
      (S.drops k, S.picks k, (S.cross k).sort (· ≤ ·)) := fun k => by
    simp [htu, List.getD_eq_getElem?_getD]
  have hoptLoad : ∀ k : Fin D.p, D.optLoad (S.drops k, S.picks k, (S.cross k).sort (· ≤ ·)) =
      S.load D.d D.db k := fun k => by
    have e := load_add_fun D.d D.db (S.cross k)
    simp only [optLoad, Sched.load, sort_map_sum]
    simp only [load] at e ⊢
    omega
  have hoptCost : ∀ k : Fin D.p, D.optCost (S.drops k, S.picks k, (S.cross k).sort (· ≤ ·)) =
      ((S.drops k).map D.c).sum + ((S.picks k).map D.c).sum + ZenoFront.cost D.c (S.cross k) :=
    fun k => by simp only [optCost, sort_map_sum]; rfl
  have hoptLand : ∀ k : Fin D.p, optLand (n := n) (S.drops k, S.picks k,
      (S.cross k).sort (· ≤ ·)) = (S.drops k).length + (S.picks k).length + (S.cross k).card :=
    fun k => by simp [optLand]
  have hsumLand : (tu.map (optLand (n := n))).sum = D.s := by
    rw [← hsize, Sched.size]
    simp only [htu, List.map_ofFn, List.sum_ofFn, Function.comp_def, hoptLand]
  have hsumCost : (tu.map D.optCost).sum = S.cost D.c := by
    simp only [htu, List.map_ofFn, List.sum_ofFn, Function.comp_def, hoptCost, Sched.cost]
  have hcardk : ∀ k : Fin D.p, (S.drops k).length + (S.picks k).length + (S.cross k).card ≤ D.s :=
    fun k => by
      rw [← hsize, Sched.size]
      exact Finset.single_le_sum (f := fun k => (S.drops k).length + (S.picks k).length +
        (S.cross k).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hcostk : ∀ k : Fin D.p, ((S.drops k).map D.c).sum + ((S.picks k).map D.c).sum +
      ZenoFront.cost D.c (S.cross k) ≤ S.cost D.c := fun k =>
    Finset.single_le_sum (f := fun k => ((S.drops k).map D.c).sum + ((S.picks k).map D.c).sum +
      ZenoFront.cost D.c (S.cross k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  -- Every plane is an option.
  have hopts : ∀ o ∈ tu, o ∈ D.opts := by
    intro o ho
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    have hl := hload k
    have hc := hcardk k
    rw [← hoptLoad k] at hl
    simp only [optLoad] at hl
    simp only [opts, List.mem_flatMap, List.mem_filterMap]
    refine ⟨S.drops k, mem_wlists _ _ _ _ (by omega) ?_, S.picks k, mem_wlists _ _ _ _ (by omega) ?_,
      (S.cross k).sort (· ≤ ·), mem_slists _ _ _ _ _ (by simp; omega) (by omega)
        (Multiset.pairwise_sort _ _) (fun _ _ => Nat.zero_le _), ?_⟩
    · rw [List.sum_map_mul_left]; omega
    · rw [List.sum_map_mul_left]; omega
    · have hodd := Nat.odd_iff.mp (hv.odd k)
      have hcost' := hcostk k
      rw [ite_eq_left ⟨by rw [hoptLoad]; exact hload k, by simpa using hodd,
        by rw [hoptLand]; exact hc, lt_of_le_of_lt (by exact_mod_cast
          (show D.optCost (S.drops k, S.picks k, (S.cross k).sort (· ≤ ·)) ≤ S.cost D.c by
            rw [hoptCost]; exact hcost')) hcost⟩]
  -- The tuple of planes is enumerated.
  have htuples : ∀ (k acc L : ℕ) (tu' : List (POpt n)), tu'.length = k → (∀ o ∈ tu', o ∈ D.opts) →
      ((acc + (tu'.map D.optCost).sum : ℕ) : WithTop ℕ) < D.C →
      (tu'.map (optLand (n := n))).sum ≤ L → tu' ∈ D.tuples D.opts k acc L := by
    intro k
    induction k with
    | zero => intro acc L tu' hk _ _ _; rw [List.length_eq_zero_iff.mp hk]; simp [tuples]
    | succ k ih =>
      intro acc L tu' hk hos hc hl
      obtain ⟨o, rest, rfl⟩ : ∃ o rest, tu' = o :: rest := by
        cases tu' with
        | nil => simp at hk
        | cons o rest => exact ⟨o, rest, rfl⟩
      simp only [List.length_cons, List.map_cons, List.sum_cons] at hk hc hl
      simp only [tuples]
      refine List.mem_flatMap.mpr ⟨o, hos o List.mem_cons_self, ?_⟩
      have hc' : ((acc + D.optCost o : ℕ) : WithTop ℕ) < D.C :=
        lt_of_le_of_lt (by exact_mod_cast (show acc + D.optCost o ≤
          acc + (D.optCost o + (rest.map D.optCost).sum) by omega)) hc
      rw [ite_eq_left ⟨hc', by omega⟩]
      refine List.mem_map.mpr ⟨rest, ih _ _ rest (by omega)
        (fun o' h => hos o' (List.mem_cons_of_mem _ h)) ?_ (by omega), rfl⟩
      have e : acc + D.optCost o + (rest.map D.optCost).sum =
          acc + (D.optCost o + (rest.map D.optCost).sum) := by omega
      rw [e]
      exact hc
  have htu_mem : tu ∈ D.tuples D.opts D.p 0 D.s :=
    htuples D.p 0 D.s tu hlen hopts (by rw [zero_add, hsumCost]; exact hcost) hsumLand.le
  -- The tuple is full.
  have hfull : D.full tu = true := by
    simp only [full, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hsumLand, ?_⟩
    simp only [htu, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    exact hv.count
  -- The matching as an assignment.
  set f : ℕ × ℕ × Fin n → ℕ × ℕ × Fin n := fun x =>
    if hx : x.1 < D.p then ((S.mate ⟨x.1, hx⟩ x.2.1).1.val, (S.mate ⟨x.1, hx⟩ x.2.1).2, x.2.2)
    else x with hf
  have hslot : ∀ {v l : ℕ} {x : Fin n}, (v, l, x) ∈ pickSlots tu →
      ∃ hv' : v < D.p, (S.picks ⟨v, hv'⟩)[l]? = some x := by
    intro v l x hx
    obtain ⟨hv', hx'⟩ := mem_pickSlots.mp hx
    rw [hlen] at hv'
    refine ⟨hv', ?_⟩
    rw [hget ⟨v, hv'⟩] at hx'
    exact hx'
  have hasg : (pickSlots tu).map f ∈ assignments (pickSlots tu) (dropSlots tu) := by
    refine mem_assignments f _ _ (by unfold pickSlots; exact nodup_slots (fun o => o.2.1) tu)
      (by unfold dropSlots; exact nodup_slots (fun o => o.1) tu) (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · obtain ⟨v, l, c⟩ := x
      obtain ⟨hv', hc⟩ := hslot hx
      have hl : l < (S.picks ⟨v, hv'⟩).length := by
        by_contra hl; rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
      have hcity := hv.city ⟨v, hv'⟩ l hl
      rw [hc] at hcity
      simp only [hf, hv', dite_true]
      refine mem_dropSlots.mpr ⟨by rw [hlen]; exact (S.mate ⟨v, hv'⟩ l).1.isLt, ?_⟩
      rw [hget]
      exact hcity
    · obtain ⟨v, l, c⟩ := x
      obtain ⟨hv', -⟩ := hslot hx
      simp [hf, hv']
    · obtain ⟨v, l, c⟩ := x
      obtain ⟨v', l', c'⟩ := y
      obtain ⟨hv₁, hc₁⟩ := hslot hx
      obtain ⟨hv₂, hc₂⟩ := hslot hy
      have hl₁ : l < (S.picks ⟨v, hv₁⟩).length := by
        by_contra hl; rw [List.getElem?_eq_none (by omega)] at hc₁; simp at hc₁
      have hl₂ : l' < (S.picks ⟨v', hv₂⟩).length := by
        by_contra hl; rw [List.getElem?_eq_none (by omega)] at hc₂; simp at hc₂
      simp only [hf, hv₁, hv₂, dite_true, Prod.mk.injEq] at hxy
      obtain ⟨h₁, h₂, h₃⟩ := hxy
      have hm : S.mate ⟨v, hv₁⟩ l = S.mate ⟨v', hv₂⟩ l' := Prod.ext (Fin.ext h₁) h₂
      obtain ⟨hvv, hll⟩ := hv.inj _ _ _ _ hl₁ hl₂ hm
      simp only [Fin.mk.injEq] at hvv
      subst hvv hll h₃
      rfl
  -- The search checked this assignment.
  have hT : D.T < D.tmplOf tu ((pickSlots tu).map f) := by
    simp only [closed, List.all_eq_true] at h
    have := h tu htu_mem
    rw [hfull, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    simpa using this _ hasg
  refine lt_of_lt_of_le hT ?_
  -- The closed form of the enumeration is at most the configuration's.
  unfold tmplOf
  refine max_le (foldr_max_le fun x hx => ?_) (foldr_max_le fun x hx => ?_)
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    rw [hoptLoad]
    exact (Finset.le_sup (f := fun k => S.load D.d D.db k) (Finset.mem_univ k)).trans
      (le_max_left _ _)
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := List.mem_map.mp hx
    rw [zip_map_self, List.mem_map] at hxy
    obtain ⟨⟨v, l, c⟩, hz, hzxy⟩ := hxy
    simp only [Prod.mk.injEq] at hzxy
    obtain ⟨rfl, rfl⟩ := hzxy
    obtain ⟨hv', hc⟩ := hslot hz
    have hl : l < (S.picks ⟨v, hv'⟩).length := by
      by_contra hl; rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
    have hcx : (S.picks ⟨v, hv'⟩)[l] = c := by
      rw [List.getElem?_eq_getElem hl] at hc; exact Option.some.inj hc
    have hgv : tu.getD v ([], [], []) = (S.drops ⟨v, hv'⟩, S.picks ⟨v, hv'⟩,
        (S.cross ⟨v, hv'⟩).sort (· ≤ ·)) := hget ⟨v, hv'⟩
    have hgu := hget (S.mate ⟨v, hv'⟩ l).1
    refine le_trans (le_of_eq ?_) ((Finset.le_sup (f := fun l => S.term D.d D.db ⟨v, hv'⟩ l)
      (Finset.mem_univ ⟨l, hl⟩)).trans ((Finset.le_sup (f := fun v => univ.sup fun l =>
        S.term D.d D.db v l) (Finset.mem_univ ⟨v, hv'⟩)).trans (le_max_right _ _)))
    simp only [hf, hv', dite_true, hgv, hgu, Sched.term, Sched.pre, Sched.suf, Fin.getElem_fin, hcx]

end SearchData

end ZenoFront
