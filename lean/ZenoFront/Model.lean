/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.BigOperators

/-!
# The symmetric MultiZenoTravel model, combinatorial part

This file fixes the data the combinatorial core of the exact front works with
(`doc/theory/exact-front.md`, §1 and §2):

* `n` central cities, indexed by `Fin n`;
* a one-way duration `d i : ℕ` between a hub (`C_I` or `C_G`) and city `i` (symmetric case (S),
  so the same value serves both hubs), and a landing cost `c i : ℕ`;
* `t` passengers and `p` planes with `1 ≤ p ≤ t`;
* `s = 2t − p`, the number of landings of a front plan (Lemma 3.2 of the note).

A *grouping* `X : Fin p → Multiset (Fin n)` assigns a multiset of landings to every plane.
The load of a group is `δ(Y) = Σ_{w ∈ Y} d w` (the makespan of a plane flying `Y` is `2 δ(Y)`,
which is the note's `ℓ(Y)`), and its cost is `c(Y) = Σ_{w ∈ Y} c w`.

Times and costs are natural numbers here: the exact algorithm works on integer durations
(after scaling, §7 of the note).
-/

@[expose] public section

namespace ZenoFront

/-- A symmetric MultiZenoTravel instance, restricted to the data the combinatorial core needs:
`n` central cities with one-way hub durations `d` and landing costs `c`, `t` passengers and `p`
planes with `1 ≤ p ≤ t`. -/
structure Instance where
  /-- Number of central cities. -/
  n : ℕ
  /-- Number of passengers. -/
  t : ℕ
  /-- Number of planes. -/
  p : ℕ
  /-- One-way duration between a hub and each central city. -/
  d : Fin n → ℕ
  /-- Landing cost of each central city. -/
  c : Fin n → ℕ
  one_le_p : 1 ≤ p
  p_le_t : p ≤ t

/-- The number of landings of a front plan, `s = 2t − p`. -/
def Instance.s (I : Instance) : ℕ := 2 * I.t - I.p

theorem Instance.s_add_p (I : Instance) : I.s + I.p = 2 * I.t := by
  have := I.p_le_t
  unfold Instance.s
  omega

theorem Instance.p_le_s (I : Instance) : I.p ≤ I.s := by
  have := I.p_le_t
  unfold Instance.s
  omega

/-- A grouping of landings: one multiset of central cities per plane. -/
abbrev Groups (n p : ℕ) := Fin p → Multiset (Fin n)

variable {n p : ℕ}

/-- The load `δ(Y) = Σ_{w ∈ Y} d w` of a multiset of landings. The flight time of a plane
serving `Y` without central flights is `2 δ(Y)`. -/
def load (d : Fin n → ℕ) (Y : Multiset (Fin n)) : ℕ := (Y.map d).sum

/-- The cost `c(Y) = Σ_{w ∈ Y} c w` of a multiset of landings. -/
def cost (c : Fin n → ℕ) (Y : Multiset (Fin n)) : ℕ := (Y.map c).sum

@[simp] theorem load_zero (d : Fin n → ℕ) : load d 0 = 0 := by simp [load]

@[simp] theorem load_cons (d : Fin n → ℕ) (i : Fin n) (Y : Multiset (Fin n)) :
    load d (i ::ₘ Y) = d i + load d Y := by simp [load]

@[simp] theorem load_add (d : Fin n → ℕ) (Y Z : Multiset (Fin n)) :
    load d (Y + Z) = load d Y + load d Z := by simp [load]

@[simp] theorem cost_zero (c : Fin n → ℕ) : cost c 0 = 0 := by simp [cost]

@[simp] theorem cost_cons (c : Fin n → ℕ) (i : Fin n) (Y : Multiset (Fin n)) :
    cost c (i ::ₘ Y) = c i + cost c Y := by simp [cost]

@[simp] theorem cost_add (c : Fin n → ℕ) (Y Z : Multiset (Fin n)) :
    cost c (Y + Z) = cost c Y + cost c Z := by simp [cost]

theorem load_mono (d : Fin n → ℕ) {Y Z : Multiset (Fin n)} (h : Y ≤ Z) :
    load d Y ≤ load d Z := by
  obtain ⟨W, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

theorem cost_mono (c : Fin n → ℕ) {Y Z : Multiset (Fin n)} (h : Y ≤ Z) :
    cost c Y ≤ cost c Z := by
  obtain ⟨W, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

/-- All landings of a grouping, `X = X_1 + ⋯ + X_p`. -/
def landings (X : Groups n p) : Multiset (Fin n) := ∑ k, X k

/-- Total number of landings of a grouping, `Σ_k |X_k|`. -/
def size (X : Groups n p) : ℕ := ∑ k, (X k).card

/-- Total cost of a grouping, `c(X) = Σ_k c(X_k)`. -/
def totalCost (c : Fin n → ℕ) (X : Groups n p) : ℕ := ∑ k, cost c (X k)

/-- The largest load of a grouping, `max_k δ(X_k)` (half the makespan of the plan built from an
admissible grouping by Theorem 4.1 of the note). -/
def maxLoad (d : Fin n → ℕ) (X : Groups n p) : ℕ := Finset.univ.sup fun k => load d (X k)

theorem size_eq_card_landings (X : Groups n p) : size X = (landings X).card := by
  simp [size, landings, Multiset.card_sum]

theorem totalCost_eq_cost_landings (c : Fin n → ℕ) (X : Groups n p) :
    totalCost c X = cost c (landings X) := by
  unfold totalCost landings
  induction (Finset.univ : Finset (Fin p)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem maxLoad_le_iff (d : Fin n → ℕ) (X : Groups n p) (T : ℕ) :
    maxLoad d X ≤ T ↔ ∀ k, load d (X k) ≤ T := by
  simp [maxLoad, Finset.sup_le_iff]

theorem load_le_maxLoad (d : Fin n → ℕ) (X : Groups n p) (k : Fin p) :
    load d (X k) ≤ maxLoad d X :=
  Finset.le_sup (f := fun k => load d (X k)) (Finset.mem_univ k)

end ZenoFront
