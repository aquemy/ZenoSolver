/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Domination
public import ZenoFront.Simulate

/-!
# A computable test that a plan is event-ordered

A certificate of an instance with a city of `d = d̄ = 0` that lists `EO` claims the front of the
*event-ordered* plans (Corollary 6.10 of the note). The plans it lists must then be event-ordered
themselves. `eoOK` tests this with one candidate order and `EventOrdered.of_eoOK` proves the test
sound; the test may reject an event-ordered plan, never accept another one.

The candidate order sorts the legs by `(departure, phase, plane, position)`, encoded in `ℕ`
(`eoRank`). The phase of a leg is that of its segment: `1` for a drop-off (`C_I → x → C_I`), `3` for
a pick-up (`C_G → x → C_G`), `2` for a crossing. In the template schedules of the note (drop-offs,
then crossings, then pick-ups on every plane) phases never decrease along a route, and a hand-off
between planes goes from a drop-off to a pick-up, so the order extends routes and journeys even
when legs of a zero-duration city depart at the same time. The test checks that the order
increases along every route, and that every passenger's legs, sorted by it, form a route from
`C_I` to `C_G`. The departure comes first in the order, so departures do not decrease along it.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- The phase of leg `i` of a route of hub–central legs (segment entries at even positions):
`1` in a drop-off, `3` in a pick-up, `2` in a crossing. -/
def legPhase (L : List (Leg n t)) (i : ℕ) : ℕ :=
  match L[i - i % 2]?, L[i - i % 2 + 1]? with
  | some a, some b =>
    if a.src = .ci ∧ b.dst = .ci then 1 else if a.src = .cg ∧ b.dst = .cg then 3 else 2
  | _, _ => 2

theorem legPhase_lt_four (L : List (Leg n t)) (i : ℕ) : legPhase L i < 4 := by
  unfold legPhase
  split
  · split_ifs <;> omega
  · omega

/-- A bound on the positions of the legs. -/
def posBound (P : Plan n t p) : ℕ := (univ.sup fun k => (P k).length) + 1

theorem lt_posBound (P : Plan n t p) (o : LegId P) : o.2.val < posBound P := by
  have := Finset.le_sup (f := fun k => (P k).length) (Finset.mem_univ o.1)
  have := o.2.isLt
  unfold posBound
  omega

/-- The candidate event order: `(departure, phase, plane, position)`, encoded in `ℕ`. -/
def eoRank (P : Plan n t p) (o : LegId P) : ℕ :=
  (((legAt P o).dep * 4 + legPhase (P o.1) o.2) * p + o.1) * posBound P + o.2

theorem eoRank_div (P : Plan n t p) (o : LegId P) :
    eoRank P o / posBound P / p / 4 = (legAt P o).dep := by
  have hL : 0 < posBound P := by unfold posBound; omega
  have hp : 0 < p := Fin.pos o.1
  have h₁ : eoRank P o / posBound P = ((legAt P o).dep * 4 + legPhase (P o.1) o.2) * p + o.1 := by
    unfold eoRank
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt (lt_posBound P o), zero_add]
  have h₂ : (((legAt P o).dep * 4 + legPhase (P o.1) o.2) * p + o.1) / p =
      (legAt P o).dep * 4 + legPhase (P o.1) o.2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt o.1.isLt, zero_add]
  rw [h₁, h₂, Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num : 0 < 4),
    Nat.div_eq_of_lt (legPhase_lt_four _ _), zero_add]

theorem eoRank_injective (P : Plan n t p) : Function.Injective (eoRank P) := by
  intro o o' h
  have hL : 0 < posBound P := by unfold posBound; omega
  have hp : 0 < p := Fin.pos o.1
  have hi : o.2.val = o'.2.val := by
    have := congrArg (· % posBound P) h
    simp only [eoRank, Nat.add_mul_mod_self_right, Nat.add_comm _ (o.2 : ℕ),
      Nat.add_comm _ (o'.2 : ℕ)] at this
    rwa [Nat.mod_eq_of_lt (lt_posBound P o), Nat.mod_eq_of_lt (lt_posBound P o')] at this
  have hk : o.1 = o'.1 := by
    have := congrArg (fun r => r / posBound P % p) h
    simp only [eoRank] at this
    rw [Nat.add_comm _ (o.2 : ℕ), Nat.add_comm _ (o'.2 : ℕ), Nat.add_mul_div_right _ _ hL,
      Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt (lt_posBound P o),
      Nat.div_eq_of_lt (lt_posBound P o'), zero_add, zero_add, Nat.add_comm _ (o.1 : ℕ),
      Nat.add_comm _ (o'.1 : ℕ), Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt o.1.isLt, Nat.mod_eq_of_lt o'.1.isLt] at this
    exact Fin.ext this
  obtain ⟨k, i⟩ := o
  obtain ⟨k', i'⟩ := o'
  simp only at hk hi
  subst hk
  rw [Fin.ext hi]

theorem dep_le_of_eoRank_lt (P : Plan n t p) {o o' : LegId P} (h : eoRank P o < eoRank P o') :
    (legAt P o).dep ≤ (legAt P o').dep := by
  rw [← eoRank_div P o, ← eoRank_div P o']
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.div_le_div_right h.le))

/-- All legs of a plan, by plane and position. -/
def allIds (P : Plan n t p) : List (LegId P) := (List.finRange p).flatMap (planeIds P)

theorem allIds_map_legAt (P : Plan n t p) : (allIds P).map (legAt P) = allLegs P := by
  simp only [allIds, List.map_flatMap, planeIds_map_legAt]
  rfl

theorem nodup_allIds (P : Plan n t p) : (allIds P).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun k _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i j h => by simpa using h
  · refine (List.nodup_finRange p).pairwise_of_forall_ne fun k _ k' _ hne => ?_
    refine List.disjoint_left.mpr fun o ho ho' => hne ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ho
    obtain ⟨i', -, hi'⟩ := List.mem_map.mp ho'
    exact (congrArg Sigma.fst hi').symm

/-- The legs of passenger `π`, sorted by the candidate order. -/
def eoJourney (P : Plan n t p) (π : Fin t) : List (LegId P) :=
  ((allIds P).filter fun o => decide ((legAt P o).pax = some π)).mergeSort
    fun a b => decide (eoRank P a ≤ eoRank P b)

/-- **The test.** The candidate order increases along every route, and every passenger's legs,
sorted by it, form a route from `C_I` to `C_G`. -/
def eoOK (P : Plan n t p) : Bool :=
  decide (∀ k, ∀ i j : Fin (P k).length, i < j → eoRank P ⟨k, i⟩ < eoRank P ⟨k, j⟩) &&
    (List.finRange t).all fun π =>
      routeOK .ci 0 ((eoJourney P π).map (legAt P)) &&
        decide (finalLoc .ci ((eoJourney P π).map (legAt P)) = .cg)

/-- **The test is sound**: a plan it accepts is event-ordered. -/
theorem EventOrdered.of_eoOK {P : Plan n t p} (h : eoOK P = true) : EventOrdered P := by
  simp only [eoOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨hroute, hpax⟩ := h
  refine ⟨eoRank P, eoRank_injective P, hroute, fun x y hxy => dep_le_of_eoRank_lt P hxy,
    fun π => ⟨eoJourney P π, ?_, isRoute_of_routeOK (hpax π).1, (hpax π).2, ?_⟩⟩
  all_goals
    have hperm := List.mergeSort_perm
      ((allIds P).filter fun o => decide ((legAt P o).pax = some π))
      fun a b => decide (eoRank P a ≤ eoRank P b)
  · have e : ((allIds P).filter fun o => decide ((legAt P o).pax = some π)).map (legAt P) =
        paxLegs P π := by
      rw [paxLegs, ← allIds_map_legAt, List.filter_map]
      rfl
    exact e ▸ hperm.map (legAt P)
  · have hsorted := List.pairwise_mergeSort (le := fun a b => decide (eoRank P a ≤ eoRank P b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      ((allIds P).filter fun o => decide ((legAt P o).pax = some π))
    have hnodup : (eoJourney P π).Nodup := hperm.nodup_iff.mpr ((nodup_allIds P).filter _)
    refine (hsorted.and hnodup).imp fun {a b} hab => ?_
    obtain ⟨hle, hne⟩ := hab
    simp only [decide_eq_true_eq] at hle
    exact lt_of_le_of_ne hle fun he => hne (eoRank_injective P he)

end ZenoFront
