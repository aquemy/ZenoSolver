/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.OnePlane
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# The relaxation `L(T)`

`L(T)` is the cheapest way to give `p` planes non-empty groups of landings of total size `s`,
each group of load at most `T`, ignoring admissibility (§7 of the note, step 2, and the
`relaxed` gap bound of certificate format v1). It is a DP over the planes on top of the
one-plane table:

* `relaxCost G 0 u = 0` if `u = 0`, else `∞`;
* `relaxCost G (j + 1) u = min_{1 ≤ m ≤ u} (G m + relaxCost G j (u − m))`.

With `G m = G[m][T]`, `relaxCost G p s` is a lower bound on the cost of every such grouping
(`relaxCost_oneplane_le_totalCost`). The checker evaluates it through the memoised tables
(`relaxedBoundAt_le_totalCost`), on durations divided by their gcd, as the C++ checker does.

## Main results

* `ZenoFront.relaxCost_oneplane_le_totalCost`: `L(T) ≤ Σ_k c(Y_k)` for every grouping into `p`
  non-empty groups of total size `s` and loads `≤ T`.
* `ZenoFront.relaxRow_getD`: the memoised rows agree with `relaxCost`.
* `ZenoFront.relaxedBoundAt_le_totalCost`: the bound the checker computes is a lower bound.
* `ZenoFront.load_eq_scale_mul`: loads in original units are `scale ×` loads in scaled units.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- `relaxCost G j u`: the cheapest way to give `j` planes `u` landings in total, each plane at
least one, a plane with `m` landings costing `G m`. -/
def relaxCost (G : ℕ → WithTop ℕ) : ℕ → ℕ → WithTop ℕ
  | 0, u => if u = 0 then 0 else ⊤
  | j + 1, u => (range u).inf fun m => G (m + 1) + relaxCost G j (u - (m + 1))

/-- `relaxCost` only reads `G` on `1, …, u`. -/
theorem relaxCost_congr {G G' : ℕ → WithTop ℕ} :
    ∀ (j u : ℕ), (∀ m, 1 ≤ m → m ≤ u → G m = G' m) → relaxCost G j u = relaxCost G' j u
  | 0, _, _ => rfl
  | j + 1, u, h => by
    simp only [relaxCost]
    refine Finset.inf_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [h (m + 1) (by omega) (by omega),
      relaxCost_congr j _ fun m' h₁ h₂ => h m' h₁ (by omega)]

/-- The relaxation is a lower bound, list form: for groups `ys`, all non-empty and each of
cost at least `G |y|`, `relaxCost G |ys| (Σ |y|) ≤ Σ c(y)`. -/
theorem relaxCost_le (G : ℕ → WithTop ℕ) (c : Fin n → ℕ) :
    ∀ ys : List (Multiset (Fin n)), (∀ y ∈ ys, 1 ≤ y.card ∧ G y.card ≤ cost c y) →
      relaxCost G ys.length (ys.map Multiset.card).sum ≤ ((ys.map (cost c)).sum : ℕ)
  | [], _ => by simp [relaxCost]
  | y :: ys, h => by
    have ⟨hy, hGy⟩ := h y List.mem_cons_self
    have ih := relaxCost_le G c ys fun y' hy' => h y' (List.mem_cons_of_mem _ hy')
    simp only [List.length_cons, List.map_cons, List.sum_cons, relaxCost]
    have hm : y.card - 1 ∈ range (y.card + (ys.map Multiset.card).sum) := by
      rw [Finset.mem_range]
      omega
    refine (Finset.inf_le hm).trans ?_
    have h₁ : y.card - 1 + 1 = y.card := by omega
    rw [h₁, Nat.add_sub_cancel_left, Nat.cast_add]
    exact add_le_add hGy ih

/-- **The relaxation is a lower bound.** For every grouping into `p` non-empty groups of total
size `s` and loads at most `T`, `L(T) = relaxCost (G[·][T]) p s ≤ Σ_k c(Y_k)`. -/
theorem relaxCost_oneplane_le_totalCost (d c : Fin n → ℕ) {T s : ℕ} (Y : Groups n p)
    (hpos : ∀ k, 1 ≤ (Y k).card) (hsize : size Y = s) (hload : ∀ k, load d (Y k) ≤ T) :
    relaxCost (fun m => oneplane d c m T) p s ≤ (totalCost c Y : WithTop ℕ) := by
  have := relaxCost_le (fun m => oneplane d c m T) c (List.ofFn Y) fun y hy => by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
    exact ⟨hpos k, oneplane_le_cost rfl (hload k)⟩
  simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn] at this
  rw [← hsize]
  exact this

/-! ### Memoised rows -/

/-- Row `j + 1` of the relaxation table from row `j`, for `u = 0, …, s`. -/
def relaxNextRow (G : ℕ → WithTop ℕ) (s : ℕ) (prev : Array (WithTop ℕ)) : Array (WithTop ℕ) :=
  Array.ofFn (n := s + 1) fun u => minUpTo (fun m => G (m + 1) + prev.getD (u - (m + 1)) ⊤) u

/-- Row `j` of the relaxation table, for `u = 0, …, s`. -/
def relaxRow (G : ℕ → WithTop ℕ) (s : ℕ) : ℕ → Array (WithTop ℕ)
  | 0 => Array.ofFn (n := s + 1) fun u => if (u : ℕ) = 0 then 0 else ⊤
  | j + 1 => relaxNextRow G s (relaxRow G s j)

theorem relaxRow_getD (G : ℕ → WithTop ℕ) {s : ℕ} : ∀ (j : ℕ) {u : ℕ}, u ≤ s →
    (relaxRow G s j).getD u ⊤ = relaxCost G j u
  | 0, u, hu => by
    simp [relaxRow, relaxCost, Array.getD_eq_getD_getElem?, show u < s + 1 by omega]
  | j + 1, u, hu => by
    simp only [relaxRow, relaxNextRow, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      show u < s + 1 by omega, relaxCost]
    simp only [dite_true, Option.getD_some, minUpTo_eq]
    refine Finset.inf_congr rfl fun m hm => ?_
    rw [← Array.getD_eq_getD_getElem?, relaxRow_getD G j (by omega)]

/-- The relaxed bound the checker computes at level `T`: the relaxation DP over the column `T` of
a one-plane table with rows `0, …, s` and columns `0, …, Tmax`; `0` (no bound) if `T > Tmax`. -/
def relaxedBoundAt (p s Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (T : ℕ) : WithTop ℕ :=
  if T ≤ Tmax then (relaxRow (fun m => (table.getD m #[]).getD T ⊤) s p).getD s ⊤ else 0

/-- **The checker's relaxed bound is a lower bound**, for the table
`oneplaneTable d c Tmax s`. -/
theorem relaxedBoundAt_le_totalCost (d c : Fin n → ℕ) {s Tmax T : ℕ} (Y : Groups n p)
    (hpos : ∀ k, 1 ≤ (Y k).card) (hsize : size Y = s) (hload : ∀ k, load d (Y k) ≤ T) :
    relaxedBoundAt p s Tmax (oneplaneTable d c Tmax s) T ≤ (totalCost c Y : WithTop ℕ) := by
  unfold relaxedBoundAt
  split_ifs with hT
  · rw [relaxRow_getD _ p le_rfl]
    rw [relaxCost_congr (G' := fun m => oneplane d c m T) p s fun m _ hm =>
      oneplaneTable_getD d c hm hT]
    exact relaxCost_oneplane_le_totalCost d c Y hpos hsize hload
  · exact bot_le

/-! ### Scaling by the gcd of the durations -/

/-- The scale of the durations: their gcd, or `1` if they are all `0` (as in the C++ checker). -/
def durationScale (d : Fin n → ℕ) : ℕ :=
  if univ.gcd d = 0 then 1 else univ.gcd d

theorem durationScale_pos (d : Fin n → ℕ) : 0 < durationScale d := by
  unfold durationScale
  split_ifs with h
  · exact Nat.one_pos
  · exact Nat.pos_of_ne_zero h

theorem durationScale_dvd (d : Fin n → ℕ) (i : Fin n) : durationScale d ∣ d i := by
  unfold durationScale
  split_ifs with h
  · exact one_dvd _
  · exact Finset.gcd_dvd (Finset.mem_univ i)

/-- The durations divided by their scale. -/
def scaledDurations (d : Fin n → ℕ) (i : Fin n) : ℕ := d i / durationScale d

/-- Loads in original units are `scale ×` loads in scaled units. -/
theorem load_eq_scale_mul (d : Fin n → ℕ) (Y : Multiset (Fin n)) :
    load d Y = durationScale d * load (scaledDurations d) Y := by
  have h : d = fun i => durationScale d * scaledDurations d i := funext fun i =>
    (Nat.mul_div_cancel' (durationScale_dvd d i)).symm
  conv_lhs => rw [h]
  simp only [load, Multiset.sum_map_mul_left]

/-- A load at most `h` in original units is at most `⌊h / scale⌋` in scaled units. -/
theorem load_scaled_le_of_load_le (d : Fin n → ℕ) {Y : Multiset (Fin n)} {h : ℕ}
    (hY : load d Y ≤ h) : load (scaledDurations d) Y ≤ h / durationScale d := by
  rw [Nat.le_div_iff_mul_le (durationScale_pos d), mul_comm, ← load_eq_scale_mul]
  exact hY

end ZenoFront
