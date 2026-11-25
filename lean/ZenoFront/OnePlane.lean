/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Model
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The one-plane table `G[m][T]`

Step 1 of the exact algorithm (`doc/theory/exact-front.md`, §6): `G[m][T]` is the cheapest cost
of a multiset of `m` cities with load `δ ≤ T`, or `∞` when there is none. It satisfies

* `G[0][T] = 0`;
* `G[m + 1][T] = min_{i : d_i ≤ T} (c_i + G[m][T − d_i])` (the minimum over the empty set
  being `∞`).

Costs live in `WithTop ℕ` (`⊤` is `∞`); unlike `ℕ∞`, its order and addition are computable.

## Main definitions

* `ZenoFront.oneplane d c m T`: the recursion above (the specification of the table).
* `ZenoFront.oneplaneTable d c mMax Tmax`: the memoised table, rows `m = 0, …, mMax`, columns
  `T = 0, …, Tmax`, in `O(mMax · Tmax · n)` operations.

## Main results

* `ZenoFront.oneplane_le_cost`: `G[m][T]` is at most the cost of every `m`-multiset with load
  `≤ T`.
* `ZenoFront.exists_cost_eq_oneplane`: if `G[m][T] < ∞`, some `m`-multiset with load `≤ T` costs
  exactly `G[m][T]`.
* `ZenoFront.oneplane_eq_top_iff`: `G[m][T] = ∞` iff every `m`-multiset has load `> T`.
* `ZenoFront.isLeast_oneplane`: `G[m][T]` is the least cost of an `m`-multiset with load `≤ T`.
* `ZenoFront.oneplaneTable_getD`: the memoised table agrees with `oneplane`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n : ℕ} (d c : Fin n → ℕ)

/-- One step of the one-plane recursion: choose the first landing `i` (with `d i ≤ T`) and
complete it with the best entry of the previous row `g` at budget `T − d i`. -/
def oneplaneStep (g : ℕ → WithTop ℕ) (T : ℕ) : WithTop ℕ :=
  univ.inf fun i => if d i ≤ T then (c i : WithTop ℕ) + g (T - d i) else ⊤

/-- `G[m][T]`, by the recursion of §6: `G[0][T] = 0` and
`G[m + 1][T] = min_{i : d_i ≤ T} (c_i + G[m][T − d_i])`. -/
def oneplane : ℕ → ℕ → WithTop ℕ
  | 0, _ => 0
  | m + 1, T => oneplaneStep d c (oneplane m) T

@[simp] theorem oneplane_zero (T : ℕ) : oneplane d c 0 T = 0 := rfl

theorem oneplane_succ (m T : ℕ) :
    oneplane d c (m + 1) T = oneplaneStep d c (oneplane d c m) T := rfl

variable {d c}

/-- `G[m][T]` is a lower bound: it is at most the cost of every multiset of `m` cities with load
at most `T`. -/
theorem oneplane_le_cost : ∀ {m T : ℕ} {Y : Multiset (Fin n)}, Y.card = m → load d Y ≤ T →
    oneplane d c m T ≤ cost c Y
  | 0, T, Y, hY, _ => by simp [Multiset.card_eq_zero.mp hY]
  | m + 1, T, Y, hY, hT => by
    obtain ⟨i, Y', rfl, hY'⟩ := Multiset.card_eq_succ_iff.mp hY
    rw [load_cons] at hT
    calc oneplane d c (m + 1) T
        ≤ if d i ≤ T then (c i : WithTop ℕ) + oneplane d c m (T - d i) else ⊤ :=
          Finset.inf_le (f := fun i => if d i ≤ T then (c i : WithTop ℕ) +
            oneplane d c m (T - d i) else ⊤) (mem_univ i)
      _ = (c i : WithTop ℕ) + oneplane d c m (T - d i) := ite_eq_left (by omega)
      _ ≤ (c i : WithTop ℕ) + cost c Y' := by
          gcongr
          exact oneplane_le_cost hY' (by omega)
      _ = cost c (i ::ₘ Y') := by simp

/-- `G[m][T]` is attained: if it is finite, some multiset of `m` cities with load at most `T`
costs exactly `G[m][T]`. -/
theorem exists_cost_eq_oneplane : ∀ {m T : ℕ}, oneplane d c m T ≠ ⊤ →
    ∃ Y : Multiset (Fin n), Y.card = m ∧ load d Y ≤ T ∧ oneplane d c m T = cost c Y
  | 0, T, _ => ⟨0, by simp, by simp, by simp⟩
  | m + 1, T, hne => by
    have huniv : (univ : Finset (Fin n)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [oneplane_succ, oneplaneStep, h] at hne
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf (univ : Finset (Fin n)) huniv
      (fun i => if d i ≤ T then (c i : WithTop ℕ) + oneplane d c m (T - d i) else ⊤)
    rw [oneplane_succ, oneplaneStep] at hne ⊢
    rw [hi] at hne ⊢
    by_cases hdi : d i ≤ T
    · rw [ite_eq_left hdi] at hne ⊢
      have hne' : oneplane d c m (T - d i) ≠ ⊤ := fun h => hne (by simp [h])
      obtain ⟨Y', hY'card, hY'load, hY'cost⟩ := exists_cost_eq_oneplane hne'
      refine ⟨i ::ₘ Y', by simp [hY'card], by simp; omega, ?_⟩
      rw [hY'cost, cost_cons]
      push_cast
      rfl
    · rw [ite_eq_right hdi] at hne
      exact absurd rfl hne

/-- `G[m][T] = ∞` exactly when every multiset of `m` cities has load larger than `T`. -/
theorem oneplane_eq_top_iff {m T : ℕ} :
    oneplane d c m T = ⊤ ↔ ∀ Y : Multiset (Fin n), Y.card = m → T < load d Y := by
  constructor
  · intro htop Y hY
    by_contra hT
    have := oneplane_le_cost (c := c) hY (not_lt.mp hT)
    rw [htop] at this
    exact WithTop.coe_ne_top (top_le_iff.mp this)
  · intro hall
    by_contra hne
    obtain ⟨Y, hY, hT, -⟩ := exists_cost_eq_oneplane hne
    exact absurd (hall Y hY) (not_lt.mpr hT)

/-- **Specification of the one-plane table.** When some multiset of `m` cities has load at most
`T`, `G[m][T]` is the least cost of such a multiset. (Otherwise `G[m][T] = ∞`, by
`oneplane_eq_top_iff`.) -/
theorem isLeast_oneplane {m T : ℕ} (hne : ∃ Y : Multiset (Fin n), Y.card = m ∧ load d Y ≤ T) :
    IsLeast ((fun Y => (cost c Y : WithTop ℕ)) '' {Y | Y.card = m ∧ load d Y ≤ T})
      (oneplane d c m T) := by
  have hfin : oneplane d c m T ≠ ⊤ := by
    obtain ⟨Y, hY, hT⟩ := hne
    rw [Ne, oneplane_eq_top_iff]
    intro hall
    exact absurd (hall Y hY) (not_lt.mpr hT)
  obtain ⟨Y, hY, hT, hcost⟩ := exists_cost_eq_oneplane hfin
  refine ⟨⟨Y, ⟨hY, hT⟩, hcost.symm⟩, ?_⟩
  rintro _ ⟨Y', ⟨hY', hT'⟩, rfl⟩
  exact oneplane_le_cost hY' hT'

/-! ### Allocation-free minima

The memoised tables take minima with these loops instead of `Finset.inf`, which builds the
finset it ranges over at every entry. -/

/-- `min (acc, f (u − 1), …, f 0)`, as a tail-recursive loop. -/
def minUpToAux (f : ℕ → WithTop ℕ) : ℕ → WithTop ℕ → WithTop ℕ
  | 0, acc => acc
  | u + 1, acc => minUpToAux f u (min acc (f u))

/-- `min_{i < u} f i` (`⊤` if `u = 0`), without building `Finset.range u`. -/
def minUpTo (f : ℕ → WithTop ℕ) (u : ℕ) : WithTop ℕ := minUpToAux f u ⊤

theorem minUpToAux_eq (f : ℕ → WithTop ℕ) : ∀ (u : ℕ) (acc : WithTop ℕ),
    minUpToAux f u acc = min acc ((range u).inf f)
  | 0, acc => by simp [minUpToAux]
  | u + 1, acc => by
    rw [minUpToAux, minUpToAux_eq f u, Finset.range_add_one, Finset.inf_insert, min_assoc]

theorem minUpTo_eq (f : ℕ → WithTop ℕ) (u : ℕ) : minUpTo f u = (range u).inf f := by
  rw [minUpTo, minUpToAux_eq]
  exact top_inf_eq _

/-- `min_{i : Fin n} f i`, as a loop. -/
def minFin (f : Fin n → WithTop ℕ) : WithTop ℕ :=
  minUpTo (fun i => if h : i < n then f ⟨i, h⟩ else ⊤) n

theorem minFin_eq (f : Fin n → WithTop ℕ) : minFin f = univ.inf f := by
  rw [minFin, minUpTo_eq]
  refine le_antisymm (Finset.le_inf fun i _ => ?_) (Finset.le_inf fun i hi => ?_)
  · refine (Finset.inf_le (Finset.mem_range.mpr i.isLt)).trans ?_
    simp
  · rw [Finset.mem_range] at hi
    simp only [hi, dite_true]
    exact Finset.inf_le (Finset.mem_univ _)

/-! ### The memoised table -/

variable (d c)

/-- Row `m + 1` of the table from row `m`, for budgets `T = 0, …, Tmax`. Entries of `row` out of
range read as `∞`. -/
def oneplaneNextRow (Tmax : ℕ) (row : Array (WithTop ℕ)) : Array (WithTop ℕ) :=
  Array.ofFn (n := Tmax + 1) fun T =>
    minFin fun i => if d i ≤ (T : ℕ) then (c i : WithTop ℕ) + row.getD (T - d i) ⊤ else ⊤

/-- Row `m` of the table, for budgets `T = 0, …, Tmax`. -/
def oneplaneRow (Tmax : ℕ) : ℕ → Array (WithTop ℕ)
  | 0 => Array.replicate (Tmax + 1) 0
  | m + 1 => oneplaneNextRow d c Tmax (oneplaneRow Tmax m)

/-- The table `G[m][T]` for `m = 0, …, mMax` and `T = 0, …, Tmax`: row `m + 1` is computed once,
from the last row of the table built so far. -/
def oneplaneTable (Tmax : ℕ) : ℕ → Array (Array (WithTop ℕ))
  | 0 => #[oneplaneRow d c Tmax 0]
  | m + 1 =>
    let t := oneplaneTable Tmax m
    t.push (oneplaneNextRow d c Tmax (t.back?.getD #[]))

theorem oneplaneTable_toList (Tmax : ℕ) : ∀ mMax : ℕ,
    (oneplaneTable d c Tmax mMax).toList = (List.range (mMax + 1)).map (oneplaneRow d c Tmax)
  | 0 => rfl
  | m + 1 => by
    have ih := oneplaneTable_toList Tmax m
    have hback : (oneplaneTable d c Tmax m).back? = some (oneplaneRow d c Tmax m) := by
      rw [← Array.getLast?_toList, ih, List.range_succ (n := m), List.map_append]
      simp
    simp only [oneplaneTable, hback, Option.getD_some, Array.toList_push, ih]
    rw [List.range_succ (n := m + 1), List.map_append]
    rfl

theorem oneplaneTable_getElem? (Tmax : ℕ) {mMax m : ℕ} (hm : m ≤ mMax) :
    (oneplaneTable d c Tmax mMax)[m]? = some (oneplaneRow d c Tmax m) := by
  rw [← Array.getElem?_toList, oneplaneTable_toList, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

theorem oneplaneRow_size (Tmax m : ℕ) : (oneplaneRow d c Tmax m).size = Tmax + 1 := by
  cases m <;> simp [oneplaneRow, oneplaneNextRow]

/-- Every row of the memoised table agrees with `oneplane` on `T = 0, …, Tmax`. -/
theorem oneplaneRow_getD {Tmax : ℕ} : ∀ (m : ℕ) {T : ℕ}, T ≤ Tmax →
    (oneplaneRow d c Tmax m).getD T ⊤ = oneplane d c m T
  | 0, T, hT => by
    simp [oneplaneRow, Array.getD, show T < Tmax + 1 by omega]
  | m + 1, T, hT => by
    simp only [oneplaneRow, oneplaneNextRow, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      show T < Tmax + 1 by omega, oneplane_succ, oneplaneStep]
    simp only [dite_true, Option.getD_some, minFin_eq]
    refine Finset.inf_congr rfl fun i _ => ?_
    split_ifs with hdi
    · rw [← Array.getD_eq_getD_getElem?, oneplaneRow_getD m (by omega)]
    · rfl

/-- **The memoised one-plane table is correct**: for `m ≤ mMax` and `T ≤ Tmax`, its entry
`(m, T)` is `G[m][T]`, the least cost of an `m`-multiset with load `≤ T` (`isLeast_oneplane`), or
`∞` when there is none (`oneplane_eq_top_iff`). -/
theorem oneplaneTable_getD {mMax Tmax m T : ℕ} (hm : m ≤ mMax) (hT : T ≤ Tmax) :
    ((oneplaneTable d c Tmax mMax).getD m #[]).getD T ⊤ = oneplane d c m T := by
  rw [Array.getD_eq_getD_getElem? (xs := oneplaneTable d c Tmax mMax),
    oneplaneTable_getElem? d c Tmax hm, Option.getD_some, oneplaneRow_getD d c m hT]

/-! ### Example

Durations `d = (1, 3)` and costs `c = (9, 5)` (the second example of §4 of the note). -/

/-- `G[2][4] = 14`: `{0, 1}` (load `4`, cost `14`) is the only pair of load `≤ 4` besides
`{0, 0}` (cost `18`). -/
example : oneplane ![1, 3] ![9, 5] 2 4 = 14 := by decide

/-- No pair of cities has load `≤ 1`. -/
example : oneplane ![1, 3] ![9, 5] 2 1 = ⊤ := by decide

example : ((oneplaneTable ![1, 3] ![9, 5] 6 3).getD 2 #[]).getD 4 ⊤ = 14 := by decide

end ZenoFront
