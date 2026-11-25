/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.PlanBounds

/-!
# Visits: the data of Theorem 5.3, Steps 2–6

Theorem 5.3 (schedulable domination) works on a plan without central flights, seen as the
*visits* of its planes. This file has the data that Step 2 (`exists_rewired`, `Rewire.lean`) and
Steps 3–6 (`exists_sched_of`, `SchedBuild.lean`) share.

## Main results

* A `KLeg` is a leg with a key (`Unit` in `schedulableDomination_all`).
* A `Visit` is a pair of legs: the leg into a central city `x` and the leg out of it.
* `legsOf`, `allK`: the legs of a list of visits and of all planes; `visitCount`: the number of
  visits.
* `isThrough`, `throughCount`: the visits `(ℓα π, ℓβ π)` that carry their passenger through, and
  their number, which every exchange of Step 2 increases.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ} {K : Type}

/-- A leg with a key. -/
structure KLeg (n t : ℕ) (K : Type) where
  leg : Leg n t
  key : K
  deriving DecidableEq

/-- A visit of a central city: the leg into it and the leg out of it. -/
abbrev Visit (n t : ℕ) (K : Type) := KLeg n t K × KLeg n t K

/-- The legs of a list of visits. -/
def legsOf (L : List (Visit n t K)) : List (KLeg n t K) := L.flatMap fun v => [v.1, v.2]

@[simp] theorem legsOf_nil : legsOf ([] : List (Visit n t K)) = [] := rfl

@[simp] theorem legsOf_cons (v : Visit n t K) (L : List (Visit n t K)) :
    legsOf (v :: L) = v.1 :: v.2 :: legsOf L := rfl

@[simp] theorem legsOf_append (A B : List (Visit n t K)) :
    legsOf (A ++ B) = legsOf A ++ legsOf B := List.flatMap_append

/-- All legs of the planes, as a multiset. -/
def allK (R : Fin p → List (Visit n t K)) : Multiset (KLeg n t K) :=
  ∑ k, (legsOf (R k) : Multiset (KLeg n t K))

theorem mem_allK {R : Fin p → List (Visit n t K)} {ℓ : KLeg n t K} :
    ℓ ∈ allK R ↔ ∃ k, ∃ v ∈ R k, ℓ = v.1 ∨ ℓ = v.2 := by
  simp only [allK, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_coe, legsOf,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

/-- The number of visits. -/
def visitCount (R : Fin p → List (Visit n t K)) : ℕ := ∑ k, (R k).length

/-- Updating two distinct coordinates, in a sum. -/
theorem sum_update_update {M : Type*} [AddCommMonoid M] {α : Type*} (R : Fin p → α) (f : α → M)
    {u v : Fin p} (huv : u ≠ v) (a b : α) :
    ∑ k, f (Function.update (Function.update R u a) v b k) + f (R u) + f (R v) =
      ∑ k, f (R k) + f a + f b := by
  classical
  have h₁ := Finset.add_sum_erase univ (fun k => f (Function.update (Function.update R u a) v b k))
    (Finset.mem_univ u)
  have h₂ := Finset.add_sum_erase (univ.erase u)
    (fun k => f (Function.update (Function.update R u a) v b k))
    (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
  have h₃ := Finset.add_sum_erase univ (fun k => f (R k)) (Finset.mem_univ u)
  have h₄ := Finset.add_sum_erase (univ.erase u) (fun k => f (R k))
    (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
  have h₅ : ∑ k ∈ (univ.erase u).erase v, f (Function.update (Function.update R u a) v b k) =
      ∑ k ∈ (univ.erase u).erase v, f (R k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkv, hk⟩ := Finset.mem_erase.mp hk
    rw [Function.update_of_ne hkv, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  simp only [Function.update_self, Function.update_of_ne huv] at h₁ h₂
  rw [← h₁, ← h₂, h₅, ← h₃, ← h₄]
  ac_rfl

/-! ### Passengers carried through -/

variable [LinearOrder K]

/-- Whether a visit carries its passenger through: it is `(ℓα π, ℓβ π)` for some `π`. -/
def isThrough (ℓα ℓβ : Fin t → KLeg n t K) (v : Visit n t K) : Bool :=
  decide (∃ π, v = (ℓα π, ℓβ π))

/-- The number of visits that carry their passenger through. -/
def throughCount (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K)) : ℕ :=
  ∑ k, (R k).countP (isThrough ℓα ℓβ)

theorem throughCount_le (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K)) :
    throughCount ℓα ℓβ R ≤ visitCount R :=
  Finset.sum_le_sum fun _ _ => List.countP_le_length

theorem list_eq_take_cons_drop {α : Type*} (L : List α) (i : ℕ) (hi : i < L.length) :
    L = L.take i ++ L[i] :: L.drop (i + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

end ZenoFront
