/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Bridge
public import ZenoFront.LinkForest
public import ZenoFront.NonSymmetric

/-!
# Achievability (Theorem 4.1)

**Theorem 4.1.** Under (S), with `p ≤ t`, every admissible partition `X_1, …, X_p` of `2t − p`
landings is achieved by a feasible plan whose planes land exactly at the groups `X_k` (up to
relabelling the planes), so of cost `c(X)`, and whose makespan is `max_k 2 δ(X_k)`
(`Admissible.exists_plan`). The plan flies no central flight.

The construction follows the note (§4.1) on a rooted link forest (`Admissible.exists_linkForest`,
Lemma 2.6). Every plane of a tree, from time `0`:

1. drops off one new passenger at the label of each child link: `C_I → b → C_I`
   (`LKids.dropLegs`);
2. crosses its free landings, an odd number: `C_I → x → C_G` carrying a new passenger,
   `C_G → x → C_I` empty, alternately (`crossLegs`);
3. if it has a parent link at `i`, flies `C_G → i` and leaves `i` once the passenger dropped
   there by its parent has arrived, carrying it to `C_G` (`pickLegs`).

The parent's drop-off reaches `i` at `a` with `a + d_i ≤ 2 δ(X_parent)`, so every plane ends by
`max_k 2 δ(X_k)`, and it flies at least `2 δ(X_k)` (`LTree.feasible_routes`). Passengers are
numbered along the forest (`LTree.units`, `LTree.units_ids`): there are `#links + #A` of them,
which is `t` when `Σ_k |X_k| = 2t − p` (`LTree.two_mul_nUnits`). The legs of the plan are the
two legs `C_I → x → C_G` of every passenger's journey plus empty legs (`LTree.legs_routes`), so
each passenger rides exactly its journey.

## Fronts

* `admissibleAchievable`: Theorem 4.1 in the form `AdmissibleAchievable` of `Bridge.lean`.
* `minimal_achievable_iff_anywhere_of_A1` (**Theorem 4.9**): under (S) and (A1), the front of
  the plans whose planes end anywhere is the front of the feasible plans, on every instance.
* `minimal_achievable_iff_admissiblePoints`, `minimal_achievable_iff_multisetPoints`
  (**Corollary 4.8**): under (S) and (A1), the front is `Min 𝒳`, with `𝒳` the points
  `(c(X), M(X))` of the multisets of `2t − p` landings that have an admissible partition, `M(X)`
  the least `2 max_k δ(X_k)` over their admissible partitions.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t : ℕ}

/-! ### The pieces of a route -/

/-- Passenger number `j` as a passenger of the plan (none if `j ≥ t`). -/
def pid (t j : ℕ) : Option (Fin t) := if h : j < t then some ⟨j, h⟩ else none

/-- The hub of a flag: `C_I` for `true`, `C_G` for `false`. -/
def hubOf : Bool → Loc n
  | true => .ci
  | false => .cg

/-- Crossings at the cities `xs`, from the hub `hubOf b` at time `τ`: `C_I → x → C_G` carrying a
new passenger (numbered from `c`), and `C_G → x → C_I` empty, alternately. -/
def crossLegs (d : Fin n → ℕ) : List (Fin n) → Bool → ℕ → ℕ → List (Leg n t)
  | [], _, _, _ => []
  | x :: xs, true, τ, c =>
    ⟨.ci, .city x, τ, τ + d x, pid t c⟩ :: ⟨.city x, .cg, τ + d x, τ + d x + d x, pid t c⟩ ::
      crossLegs d xs false (τ + d x + d x) (c + 1)
  | x :: xs, false, τ, c =>
    ⟨.cg, .city x, τ, τ + d x, none⟩ :: ⟨.city x, .ci, τ + d x, τ + d x + d x, none⟩ ::
      crossLegs d xs true (τ + d x + d x) c

/-- A passenger's journey `C_I → x → C_G`: its number `j`, the city `x`, and the departure times
`e` of `C_I → x` and `e'` of `x → C_G`. -/
structure PaxUnit (n : ℕ) where
  j : ℕ
  x : Fin n
  e : ℕ
  e' : ℕ

/-- The two legs of a journey. -/
def PaxUnit.legs (d : Fin n → ℕ) (u : PaxUnit n) : Multiset (Leg n t) :=
  (⟨.ci, .city u.x, u.e, u.e + d u.x, pid t u.j⟩ : Leg n t) ::ₘ
    {(⟨.city u.x, .cg, u.e', u.e' + d u.x, pid t u.j⟩ : Leg n t)}

/-- The journeys of the passengers of `crossLegs`. -/
def crossUnits (d : Fin n → ℕ) : List (Fin n) → Bool → ℕ → ℕ → List (PaxUnit n)
  | [], _, _, _ => []
  | x :: xs, true, τ, c => ⟨c, x, τ, τ + d x⟩ :: crossUnits d xs false (τ + d x + d x) (c + 1)
  | x :: xs, false, τ, c => crossUnits d xs true (τ + d x + d x) c

/-- The parent link of a plane: its label `i`, the time `a` at which the parent's drop-off reaches
`i`, and the number `j` of the dropped passenger. -/
abbrev ParentLink (n : ℕ) := Option (Fin n × ℕ × ℕ)

/-- The landing of a parent link. -/
def extraOf : ParentLink n → Multiset (Fin n)
  | none => 0
  | some (i, _, _) => {i}

/-- The pick-up of a plane in `C_G` at time `τ`: `C_G → i`, then `i → C_G` once the passenger
dropped by the parent is there, carrying it. -/
def pickLegs (d : Fin n → ℕ) (τ : ℕ) : ParentLink n → List (Leg n t)
  | none => []
  | some (i, a, j) =>
    [⟨.cg, .city i, τ, τ + d i, none⟩,
      ⟨.city i, .cg, max (τ + d i) a, max (τ + d i) a + d i, pid t j⟩]

/-- The carrying leg of a pick-up. -/
def pickCarry (d : Fin n → ℕ) (τ : ℕ) : ParentLink n → Multiset (Leg n t)
  | none => 0
  | some (i, a, j) => {⟨.city i, .cg, max (τ + d i) a, max (τ + d i) a + d i, pid t j⟩}

/-! ### Rooted link trees -/

namespace LTree

/-- The free landings of the root. -/
def free : LTree n → Multiset (Fin n)
  | .node f _ => f

/-- The child items of the root. -/
def kids : LTree n → LKids n
  | .node _ k => k

end LTree

/-- The number of child items. -/
def LKids.count : LKids n → ℕ
  | .nil => 0
  | .cons _ _ rest => rest.count + 1

/-- The drop-offs of a plane for its child items, from `C_I` at time `τ`: `C_I → b → C_I`, the
first leg carrying passenger `cl`, `cl + 1`, … -/
def LKids.dropLegs (d : Fin n → ℕ) : LKids n → ℕ → ℕ → List (Leg n t)
  | .nil, _, _ => []
  | .cons b _ rest, τ, cl =>
    ⟨.ci, .city b, τ, τ + d b, pid t cl⟩ :: ⟨.city b, .ci, τ + d b, τ + d b + d b, none⟩ ::
      rest.dropLegs d (τ + d b + d b) (cl + 1)

/-- When a plane reaches `C_G` after its drop-offs and crossings. -/
def LTree.crossEnd (d : Fin n → ℕ) : LTree n → ℕ
  | .node free kids => 2 * load d kids.labels + 2 * load d free

/-- The pick-ups of the children, for drop-offs from time `τ` carrying `cl`, `cl + 1`, … -/
def LKids.childPicks (d : Fin n → ℕ) : LKids n → ℕ → ℕ → Multiset (Leg n t)
  | .nil, _, _ => 0
  | .cons b child rest, τ, cl =>
    pickCarry d (child.crossEnd d) (some (b, τ + d b, cl)) +
      rest.childPicks d (τ + d b + d b) (cl + 1)

/-- The journeys of the dropped passengers. -/
def LKids.linkUnits (d : Fin n → ℕ) : LKids n → ℕ → ℕ → List (PaxUnit n)
  | .nil, _, _ => []
  | .cons b child rest, τ, cl =>
    ⟨cl, b, τ, max (child.crossEnd d + d b) (τ + d b)⟩ :: rest.linkUnits d (τ + d b + d b) (cl + 1)

mutual
/-- The number of passengers a tree carries, its parent link excluded. -/
def LTree.nUnits : LTree n → ℕ
  | .node free kids => kids.count + (free.card + 1) / 2 + kids.nUnits
/-- The number of passengers the subtrees of child items carry, their parent links excluded. -/
def LKids.nUnits : LKids n → ℕ
  | .nil => 0
  | .cons _ child rest => child.nUnits + rest.nUnits
end

noncomputable section

mutual
/-- The routes of the planes of a tree, with parent link `par`, numbering its passengers from
`c`: the root drops off its children's passengers, crosses its free landings, and picks up its
parent's passenger. -/
def LTree.routes (d : Fin n → ℕ) : LTree n → ParentLink n → ℕ → List (List (Leg n t))
  | .node free kids, par, c =>
    (kids.dropLegs d 0 c ++
      crossLegs d free.toList true (2 * load d kids.labels) (c + kids.count) ++
      pickLegs d (2 * load d kids.labels + 2 * load d free) par) ::
    kids.routes d 0 c (c + kids.count + (free.card + 1) / 2)
/-- The routes of the subtrees of child items, dropped off from time `τ` with passengers `cl`, …,
and numbering their own passengers from `cs`. -/
def LKids.routes (d : Fin n → ℕ) : LKids n → ℕ → ℕ → ℕ → List (List (Leg n t))
  | .nil, _, _, _ => []
  | .cons b child rest, τ, cl, cs =>
    child.routes d (some (b, τ + d b, cl)) cs ++
      rest.routes d (τ + d b + d b) (cl + 1) (cs + child.nUnits)
end

mutual
/-- The journeys of the passengers of a tree, its parent link excluded. -/
def LTree.units (d : Fin n → ℕ) : LTree n → ℕ → List (PaxUnit n)
  | .node free kids, c =>
    kids.linkUnits d 0 c ++
      crossUnits d free.toList true (2 * load d kids.labels) (c + kids.count) ++
      kids.units d (c + kids.count + (free.card + 1) / 2)
/-- The journeys of the passengers of the subtrees of child items, their parent links excluded. -/
def LKids.units (d : Fin n → ℕ) : LKids n → ℕ → List (PaxUnit n)
  | .nil, _ => []
  | .cons _ child rest, cs => child.units d cs ++ rest.units d (cs + child.nUnits)
end

/-- The routes of a forest, numbering passengers from `c`. -/
def forestRoutes (d : Fin n → ℕ) : List (LTree n) → ℕ → List (List (Leg n t))
  | [], _ => []
  | T :: F, c => T.routes d none c ++ forestRoutes d F (c + T.nUnits)

/-- The journeys of a forest. -/
def forestUnits (d : Fin n → ℕ) : List (LTree n) → ℕ → List (PaxUnit n)
  | [], _ => []
  | T :: F, c => T.units d c ++ forestUnits d F (c + T.nUnits)

end

/-- The number of passengers of a forest. -/
def forestCount : List (LTree n) → ℕ
  | [] => 0
  | T :: F => T.nUnits + forestCount F

/-! ### Crossings -/

section Pieces

variable {N : Network n}

theorem flies_ci_city (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.ci, .city i, e, e + N.d i, π⟩ : Leg n t) := ⟨_, rfl, rfl⟩

theorem flies_city_ci (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.city i, .ci, e, e + N.d i, π⟩ : Leg n t) := ⟨_, rfl, rfl⟩

theorem flies_cg_city (hS : N.dbar = N.d) (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.cg, .city i, e, e + N.d i, π⟩ : Leg n t) :=
  ⟨N.d i, by simp [Network.duration, hS], rfl⟩

theorem flies_city_cg (hS : N.dbar = N.d) (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.city i, .cg, e, e + N.d i, π⟩ : Leg n t) :=
  ⟨N.d i, by simp [Network.duration, hS], rfl⟩

theorem flies_crossLegs (hS : N.dbar = N.d) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    ∀ ℓ ∈ (crossLegs N.d xs b τ c : List (Leg n t)), Flies N ℓ
  | [], _, _, _ => by simp [crossLegs]
  | x :: xs, true, τ, c => by
    intro ℓ hℓ
    simp only [crossLegs, List.mem_cons] at hℓ
    rcases hℓ with rfl | rfl | hℓ
    · exact flies_ci_city x τ _
    · exact flies_city_cg hS x _ _
    · exact flies_crossLegs hS xs false _ _ ℓ hℓ
  | x :: xs, false, τ, c => by
    intro ℓ hℓ
    simp only [crossLegs, List.mem_cons] at hℓ
    rcases hℓ with rfl | rfl | hℓ
    · exact flies_cg_city hS x τ _
    · exact flies_city_ci x _ _
    · exact flies_crossLegs hS xs true _ _ ℓ hℓ

end Pieces

theorem isRoute_crossLegs (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    IsRoute (hubOf b) τ (crossLegs d xs b τ c : List (Leg n t))
  | [], _, _, _ => trivial
  | _ :: xs, true, _, _ => ⟨rfl, le_rfl, rfl, le_rfl, isRoute_crossLegs d xs false _ _⟩
  | _ :: xs, false, _, _ => ⟨rfl, le_rfl, rfl, le_rfl, isRoute_crossLegs d xs true _ _⟩

theorem finalLoc_crossLegs (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    finalLoc (hubOf b) (crossLegs d xs b τ c : List (Leg n t)) =
      hubOf (if Even xs.length then b else !b)
  | [], b, _, _ => by simp [crossLegs]
  | x :: xs, true, τ, c => by
    simp only [crossLegs, finalLoc_cons]
    rw [show (Loc.cg : Loc n) = hubOf false from rfl, finalLoc_crossLegs d xs false]
    by_cases h : Even xs.length <;> simp [h, List.length_cons, Nat.even_add_one]
  | x :: xs, false, τ, c => by
    simp only [crossLegs, finalLoc_cons]
    rw [show (Loc.ci : Loc n) = hubOf true from rfl, finalLoc_crossLegs d xs true]
    by_cases h : Even xs.length <;> simp [h, List.length_cons, Nat.even_add_one]

theorem endTime_crossLegs (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    endTime τ (crossLegs d xs b τ c : List (Leg n t)) = τ + 2 * load d (xs : Multiset (Fin n))
  | [], _, τ, _ => by simp [crossLegs]
  | x :: xs, true, τ, c => by
    simp only [crossLegs, endTime_cons, endTime_crossLegs d xs false, ← Multiset.cons_coe,
      load_cons]
    ring
  | x :: xs, false, τ, c => by
    simp only [crossLegs, endTime_cons, endTime_crossLegs d xs true, ← Multiset.cons_coe,
      load_cons]
    ring

theorem routeLandings_crossLegs (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    routeLandings (crossLegs d xs b τ c : List (Leg n t)) = (xs : Multiset (Fin n))
  | [], _, _, _ => rfl
  | _ :: xs, true, _, _ => by
    simp [crossLegs, routeLandings, routeLandings_crossLegs d xs false]
  | _ :: xs, false, _, _ => by
    simp [crossLegs, routeLandings, routeLandings_crossLegs d xs true]

theorem legs_crossLegs (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((crossLegs d xs b τ c : List (Leg n t)) : Multiset (Leg n t)) =
        ((crossUnits d xs b τ c).map (PaxUnit.legs d)).sum + E
  | [], _, _, _ => ⟨0, by simp, by simp [crossLegs, crossUnits]⟩
  | x :: xs, true, τ, c => by
    obtain ⟨E, hE, h⟩ := legs_crossLegs d xs false (τ + d x + d x) (c + 1)
    refine ⟨E, hE, ?_⟩
    simp only [crossLegs, crossUnits, List.map_cons, List.sum_cons, ← Multiset.cons_coe, h,
      PaxUnit.legs]
    simp [Multiset.cons_add, Multiset.singleton_add]
  | x :: xs, false, τ, c => by
    obtain ⟨E, hE, h⟩ := legs_crossLegs d xs true (τ + d x + d x) c
    refine ⟨⟨.cg, .city x, τ, τ + d x, none⟩ ::ₘ ⟨.city x, .ci, τ + d x, τ + d x + d x, none⟩ ::ₘ E,
      fun ℓ hℓ => ?_, ?_⟩
    · simp only [Multiset.mem_cons] at hℓ
      rcases hℓ with rfl | rfl | hℓ
      · rfl
      · rfl
      · exact hE ℓ hℓ
    · simp only [crossLegs, crossUnits, ← Multiset.cons_coe, h]
      simp [Multiset.add_cons]

theorem crossUnits_ids (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    (crossUnits d xs b τ c).map PaxUnit.j =
      List.range' c (if b then (xs.length + 1) / 2 else xs.length / 2)
  | [], b, _, _ => by cases b <;> simp [crossUnits]
  | x :: xs, true, τ, c => by
    simp only [crossUnits, List.map_cons, crossUnits_ids d xs false, Bool.false_eq_true,
      ↓reduceIte, List.length_cons]
    rw [show (xs.length + 1 + 1) / 2 = xs.length / 2 + 1 by omega, List.range'_succ]
  | x :: xs, false, τ, c => by
    simp only [crossUnits, crossUnits_ids d xs true, Bool.false_eq_true, ↓reduceIte,
      List.length_cons]

theorem crossUnits_time (d : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ c : ℕ),
    ∀ u ∈ crossUnits d xs b τ c, u.e + d u.x ≤ u.e'
  | [], _, _, _ => by simp [crossUnits]
  | x :: xs, true, τ, c => by
    intro u hu
    simp only [crossUnits, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_rfl
    · exact crossUnits_time d xs false _ _ u hu
  | x :: xs, false, τ, c => fun u hu => crossUnits_time d xs true _ _ u hu

/-! ### Drop-offs and pick-ups -/

theorem LKids.card_labels : ∀ K : LKids n, K.labels.card = K.count
  | .nil => rfl
  | .cons _ _ rest => by simp [LKids.labels, LKids.count, LKids.card_labels rest]

theorem flies_dropLegs {N : Network n} : ∀ (K : LKids n) (τ cl : ℕ),
    ∀ ℓ ∈ (K.dropLegs N.d τ cl : List (Leg n t)), Flies N ℓ
  | .nil, _, _ => by simp [LKids.dropLegs]
  | .cons b _ rest, τ, cl => by
    intro ℓ hℓ
    simp only [LKids.dropLegs, List.mem_cons] at hℓ
    rcases hℓ with rfl | rfl | hℓ
    · exact flies_ci_city b τ _
    · exact flies_city_ci b _ _
    · exact flies_dropLegs rest _ _ ℓ hℓ

theorem isRoute_dropLegs (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    IsRoute .ci τ (K.dropLegs d τ cl : List (Leg n t))
  | .nil, _, _ => trivial
  | .cons _ _ rest, _, _ => ⟨rfl, le_rfl, rfl, le_rfl, isRoute_dropLegs d rest _ _⟩

theorem finalLoc_dropLegs (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    finalLoc .ci (K.dropLegs d τ cl : List (Leg n t)) = .ci
  | .nil, _, _ => rfl
  | .cons _ _ rest, _, _ => finalLoc_dropLegs d rest _ _

theorem endTime_dropLegs (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    endTime τ (K.dropLegs d τ cl : List (Leg n t)) = τ + 2 * load d K.labels
  | .nil, τ, _ => by simp [LKids.dropLegs, LKids.labels]
  | .cons b _ rest, τ, cl => by
    simp only [LKids.dropLegs, endTime_cons, endTime_dropLegs d rest, LKids.labels, load_cons]
    ring

theorem routeLandings_dropLegs (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    routeLandings (K.dropLegs d τ cl : List (Leg n t)) = K.labels
  | .nil, _, _ => rfl
  | .cons _ _ rest, _, _ => by
    simp [LKids.dropLegs, routeLandings, routeLandings_dropLegs d rest, LKids.labels]

theorem cons_cons_add_eq {α : Type*} {a e q : α} {R C S E : Multiset α} (h : R + C = S + E) :
    a ::ₘ e ::ₘ R + ({q} + C) = a ::ₘ {q} + S + e ::ₘ E := by
  simp only [← Multiset.singleton_add]
  calc {a} + ({e} + R) + ({q} + C) = {a} + {q} + {e} + (R + C) := by abel
    _ = {a} + {q} + {e} + (S + E) := by rw [h]
    _ = {a} + {q} + S + ({e} + E) := by abel

theorem legs_dropLegs (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((K.dropLegs d τ cl : List (Leg n t)) : Multiset (Leg n t)) + K.childPicks d τ cl =
        ((K.linkUnits d τ cl).map (PaxUnit.legs d)).sum + E
  | .nil, _, _ => ⟨0, by simp, by simp [LKids.dropLegs, LKids.childPicks, LKids.linkUnits]⟩
  | .cons b child rest, τ, cl => by
    obtain ⟨E, hE, h⟩ := legs_dropLegs d rest (τ + d b + d b) (cl + 1)
    refine ⟨⟨.city b, .ci, τ + d b, τ + d b + d b, none⟩ ::ₘ E, fun ℓ hℓ => ?_, ?_⟩
    · rcases Multiset.mem_cons.mp hℓ with rfl | hℓ
      · rfl
      · exact hE ℓ hℓ
    · simp only [LKids.dropLegs, LKids.childPicks, LKids.linkUnits, List.map_cons, List.sum_cons,
        ← Multiset.cons_coe, pickCarry, PaxUnit.legs]
      exact cons_cons_add_eq h

theorem linkUnits_ids (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    (K.linkUnits d τ cl).map PaxUnit.j = List.range' cl K.count
  | .nil, _, _ => rfl
  | .cons _ _ rest, _, cl => by
    simp only [LKids.linkUnits, List.map_cons, linkUnits_ids d rest, LKids.count]
    rw [List.range'_succ]

theorem linkUnits_time (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl : ℕ),
    ∀ u ∈ K.linkUnits d τ cl, u.e + d u.x ≤ u.e'
  | .nil, _, _ => by simp [LKids.linkUnits]
  | .cons b child rest, τ, cl => by
    intro u hu
    simp only [LKids.linkUnits, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_max_right _ _
    · exact linkUnits_time d rest _ _ u hu

theorem flies_pickLegs {N : Network n} (hS : N.dbar = N.d) (τ : ℕ) : ∀ par : ParentLink n,
    ∀ ℓ ∈ (pickLegs N.d τ par : List (Leg n t)), Flies N ℓ
  | none => by simp [pickLegs]
  | some (i, a, j) => by
    intro ℓ hℓ
    simp only [pickLegs, List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl
    · exact flies_cg_city hS i τ _
    · exact flies_city_cg hS i _ _

theorem isRoute_pickLegs (d : Fin n → ℕ) (τ : ℕ) : ∀ par : ParentLink n,
    IsRoute .cg τ (pickLegs d τ par : List (Leg n t))
  | none => trivial
  | some (_, _, _) => ⟨rfl, le_rfl, rfl, le_max_left _ _, trivial⟩

theorem finalLoc_pickLegs (d : Fin n → ℕ) (τ : ℕ) : ∀ par : ParentLink n,
    finalLoc .cg (pickLegs d τ par : List (Leg n t)) = .cg
  | none => rfl
  | some _ => rfl

theorem endTime_pickLegs_none (d : Fin n → ℕ) (τ τ' : ℕ) :
    endTime τ' (pickLegs d τ none : List (Leg n t)) = τ' := rfl

theorem endTime_pickLegs_some (d : Fin n → ℕ) (τ τ' : ℕ) (i : Fin n) (a j : ℕ) :
    endTime τ' (pickLegs d τ (some (i, a, j)) : List (Leg n t)) = max (τ + d i) a + d i := rfl

theorem load_singleton (d : Fin n → ℕ) (i : Fin n) : load d {i} = d i := by simp [load]

theorem routeLandings_pickLegs (d : Fin n → ℕ) (τ : ℕ) : ∀ par : ParentLink n,
    routeLandings (pickLegs d τ par : List (Leg n t)) = extraOf par
  | none => rfl
  | some (i, a, j) => by simp [pickLegs, routeLandings, extraOf]

theorem legs_pickLegs (d : Fin n → ℕ) (τ : ℕ) : ∀ par : ParentLink n,
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((pickLegs d τ par : List (Leg n t)) : Multiset (Leg n t)) = pickCarry d τ par + E
  | none => ⟨0, by simp, rfl⟩
  | some (i, a, j) => ⟨{⟨.cg, .city i, τ, τ + d i, none⟩}, by simp, by
      simp only [pickLegs, pickCarry, Multiset.singleton_add, ← Multiset.cons_coe]
      exact Multiset.cons_swap _ _ _⟩

/-! ### The routes of a tree -/

theorem routeLandings_append : ∀ L M : List (Leg n t),
    routeLandings (L ++ M) = routeLandings L + routeLandings M
  | [], M => by simp [routeLandings]
  | ⟨src, dst, dep, arr, pax⟩ :: L, M => by
    cases dst <;> simp [routeLandings, routeLandings_append L M, Multiset.cons_add]

mutual
/-- The planes of a tree land exactly at their groups. -/
theorem LTree.landings_routes (d : Fin n → ℕ) : ∀ (T : LTree n) (par : ParentLink n) (c : ℕ),
    (((T.routes d par c : List (List (Leg n t))).map routeLandings : List (Multiset (Fin n))) :
      Multiset (Multiset (Fin n))) = T.groups (extraOf par)
  | .node free kids, par, c => by
    simp only [LTree.routes, LTree.groups, List.map_cons, ← Multiset.cons_coe]
    rw [LKids.landings_routes d kids 0 c _, routeLandings_append, routeLandings_append,
      routeLandings_dropLegs, routeLandings_crossLegs, routeLandings_pickLegs, Multiset.coe_toList,
      add_comm kids.labels free]
/-- The planes of the subtrees of child items land exactly at their groups. -/
theorem LKids.landings_routes (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl cs : ℕ),
    (((K.routes d τ cl cs : List (List (Leg n t))).map routeLandings : List (Multiset (Fin n))) :
      Multiset (Multiset (Fin n))) = K.groups
  | .nil, _, _, _ => rfl
  | .cons b child rest, τ, cl, cs => by
    simp only [LKids.routes, LKids.groups, List.map_append, ← Multiset.coe_add]
    rw [LTree.landings_routes d child, LKids.landings_routes d rest]
    rfl
end

mutual
/-- The passengers of a tree are numbered `c, c + 1, …`. -/
theorem LTree.units_ids (d : Fin n → ℕ) : ∀ (T : LTree n) (c : ℕ),
    (T.units d c).map PaxUnit.j = List.range' c T.nUnits
  | .node free kids, c => by
    simp only [LTree.units, LTree.nUnits, List.map_append, linkUnits_ids, crossUnits_ids,
      LKids.units_ids d kids, ↓reduceIte, Multiset.length_toList, List.range'_append_1]
    rw [show c + kids.count + (free.card + 1) / 2 = c + (kids.count + (free.card + 1) / 2) by omega,
      List.range'_append_1]
/-- The passengers of the subtrees of child items are numbered `cs, cs + 1, …`. -/
theorem LKids.units_ids (d : Fin n → ℕ) : ∀ (K : LKids n) (cs : ℕ),
    (K.units d cs).map PaxUnit.j = List.range' cs K.nUnits
  | .nil, _ => rfl
  | .cons _ child rest, cs => by
    simp only [LKids.units, LKids.nUnits, List.map_append, LTree.units_ids d child,
      LKids.units_ids d rest, List.range'_append_1]
end

mutual
/-- Every journey of a tree leaves its city after arriving there. -/
theorem LTree.units_time (d : Fin n → ℕ) : ∀ (T : LTree n) (c : ℕ),
    ∀ u ∈ T.units d c, u.e + d u.x ≤ u.e'
  | .node free kids, c => by
    intro u hu
    simp only [LTree.units, List.mem_append] at hu
    rcases hu with (hu | hu) | hu
    · exact linkUnits_time d kids _ _ u hu
    · exact crossUnits_time d _ _ _ _ u hu
    · exact LKids.units_time d kids _ u hu
/-- Every journey of the subtrees of child items leaves its city after arriving there. -/
theorem LKids.units_time (d : Fin n → ℕ) : ∀ (K : LKids n) (cs : ℕ),
    ∀ u ∈ K.units d cs, u.e + d u.x ≤ u.e'
  | .nil, _ => by simp [LKids.units]
  | .cons _ child rest, cs => by
    intro u hu
    simp only [LKids.units, List.mem_append] at hu
    rcases hu with hu | hu
    · exact LTree.units_time d child _ u hu
    · exact LKids.units_time d rest _ u hu
end

mutual
/-- Counting the passengers of a tree: twice their number, plus the parent link, is
`Σ (|X_k| + 1)` over its planes. -/
theorem LTree.two_mul_nUnits : ∀ (T : LTree n) (extra : Multiset (Fin n)), T.WF →
    2 * T.nUnits + extra.card = ((T.groups extra).map fun g => g.card + 1).sum
  | .node free kids, extra, hwf => by
    obtain ⟨⟨m, hm⟩, hk⟩ := hwf
    have ih := LKids.two_mul_nUnits kids hk
    simp only [LTree.nUnits, LTree.groups, Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_add, LKids.card_labels] at ih ⊢
    omega
/-- Counting the passengers of the subtrees of child items. -/
theorem LKids.two_mul_nUnits : ∀ K : LKids n, K.WF →
    2 * K.nUnits + K.count = (K.groups.map fun g => g.card + 1).sum
  | .nil, _ => by simp [LKids.nUnits, LKids.count, LKids.groups]
  | .cons b child rest, hwf => by
    obtain ⟨hc, hr⟩ := hwf
    have h₁ := LTree.two_mul_nUnits child {b} hc
    have h₂ := LKids.two_mul_nUnits rest hr
    simp only [LKids.nUnits, LKids.count, LKids.groups, Multiset.map_add, Multiset.sum_add,
      Multiset.card_singleton] at h₁ h₂ ⊢
    omega
end

theorem add_shuffle {M : Type*} [AddCommMonoid M] {Dr Cp Lu E₁ Cu E₂ Pc E₃ Ku E₄ : M}
    (h : Dr + Cp = Lu + E₁) :
    Dr + (Cu + E₂) + (Pc + E₃) + (Ku + Cp + E₄) = Lu + Cu + Ku + Pc + (E₁ + E₂ + E₃ + E₄) := by
  calc Dr + (Cu + E₂) + (Pc + E₃) + (Ku + Cp + E₄)
      = (Dr + Cp) + Cu + Ku + Pc + (E₂ + E₃ + E₄) := by abel
    _ = (Lu + E₁) + Cu + Ku + Pc + (E₂ + E₃ + E₄) := by rw [h]
    _ = Lu + Cu + Ku + Pc + (E₁ + E₂ + E₃ + E₄) := by abel

theorem pax_none_add {E₁ E₂ : Multiset (Leg n t)} (h₁ : ∀ ℓ ∈ E₁, ℓ.pax = none)
    (h₂ : ∀ ℓ ∈ E₂, ℓ.pax = none) : ∀ ℓ ∈ E₁ + E₂, ℓ.pax = none := fun ℓ hℓ =>
  (Multiset.mem_add.mp hℓ).elim (h₁ ℓ) (h₂ ℓ)

mutual
/-- The legs of the planes of a tree: the legs of its journeys, the carrying leg of its pick-up,
and empty legs. -/
theorem LTree.legs_routes (d : Fin n → ℕ) : ∀ (T : LTree n) (par : ParentLink n) (c : ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      (((T.routes d par c : List (List (Leg n t))).flatten : List (Leg n t)) : Multiset (Leg n t)) =
        ((T.units d c).map (PaxUnit.legs d)).sum + pickCarry d (T.crossEnd d) par + E
  | .node free kids, par, c => by
    obtain ⟨E₁, hE₁, h₁⟩ := legs_dropLegs (t := t) d kids 0 c
    obtain ⟨E₂, hE₂, h₂⟩ := legs_crossLegs (t := t) d free.toList true (2 * load d kids.labels)
      (c + kids.count)
    obtain ⟨E₃, hE₃, h₃⟩ := legs_pickLegs (t := t) d (2 * load d kids.labels + 2 * load d free) par
    obtain ⟨E₄, hE₄, h₄⟩ := LKids.legs_routes d kids 0 c (c + kids.count + (free.card + 1) / 2)
    refine ⟨E₁ + E₂ + E₃ + E₄, pax_none_add (pax_none_add (pax_none_add hE₁ hE₂) hE₃) hE₄, ?_⟩
    simp only [LTree.routes, LTree.units, LTree.crossEnd, List.flatten_cons, ← Multiset.coe_add,
      List.map_append, List.sum_append, h₂, h₃, h₄]
    exact add_shuffle h₁
/-- The legs of the planes of the subtrees of child items: the legs of their journeys, the
carrying legs of the children's pick-ups, and empty legs. -/
theorem LKids.legs_routes (d : Fin n → ℕ) : ∀ (K : LKids n) (τ cl cs : ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      (((K.routes d τ cl cs : List (List (Leg n t))).flatten : List (Leg n t)) :
        Multiset (Leg n t)) = ((K.units d cs).map (PaxUnit.legs d)).sum + K.childPicks d τ cl + E
  | .nil, _, _, _ => ⟨0, by simp, by simp [LKids.routes, LKids.units, LKids.childPicks]⟩
  | .cons b child rest, τ, cl, cs => by
    obtain ⟨E₁, hE₁, h₁⟩ := LTree.legs_routes d child (some (b, τ + d b, cl)) cs
    obtain ⟨E₂, hE₂, h₂⟩ := LKids.legs_routes d rest (τ + d b + d b) (cl + 1) (cs + child.nUnits)
    refine ⟨E₁ + E₂, pax_none_add hE₁ hE₂, ?_⟩
    simp only [LKids.routes, LKids.units, LKids.childPicks, List.flatten_append,
      ← Multiset.coe_add, List.map_append, List.sum_append, h₁, h₂]
    abel
end

/-- The route of the root of a tree: it is a feasible plane, it flies at least twice the load of
its landings, and it ends no later than `B` when its group's load and its parent's drop-off
allow it. -/
theorem rootRoute_spec {N : Network n} (hS : N.dbar = N.d) {B : ℕ} (free : Multiset (Fin n))
    (kids : LKids n) (par : ParentLink n) (c : ℕ) (hodd : Odd free.card)
    (hg : 2 * load N.d (free + kids.labels + extraOf par) ≤ B)
    (hpar : ∀ i a j, par = some (i, a, j) → a + N.d i ≤ B) :
    let R : List (Leg n t) := kids.dropLegs N.d 0 c ++
      crossLegs N.d free.toList true (2 * load N.d kids.labels) (c + kids.count) ++
      pickLegs N.d (2 * load N.d kids.labels + 2 * load N.d free) par
    PlaneFeasible N R ∧ 2 * load N.d (routeLandings R) ≤ endTime 0 R ∧ endTime 0 R ≤ B := by
  intro R
  have hlen : ¬ Even free.toList.length := by
    rw [Multiset.length_toList]
    exact Nat.not_even_iff_odd.mpr hodd
  have hcross := finalLoc_crossLegs (t := t) N.d free.toList true (2 * load N.d kids.labels)
    (c + kids.count)
  simp only [hlen, ↓reduceIte, Bool.not_true] at hcross
  have hroute : IsRoute .ci 0 R := by
    refine (isRoute_append _ _).mpr ⟨(isRoute_append _ _).mpr ⟨isRoute_dropLegs _ _ _ _, ?_⟩, ?_⟩
    · rw [finalLoc_dropLegs, endTime_dropLegs, zero_add]
      exact isRoute_crossLegs _ _ true _ _
    · rw [finalLoc_append, finalLoc_dropLegs, endTime_append, endTime_dropLegs, zero_add,
        endTime_crossLegs, Multiset.coe_toList]
      exact hcross ▸ isRoute_pickLegs _ _ _
  have hend : finalLoc .ci R = .cg := by
    rw [finalLoc_append, finalLoc_append, finalLoc_dropLegs]
    exact hcross ▸ finalLoc_pickLegs _ _ _
  have hflies : ∀ ℓ ∈ R, Flies N ℓ := by
    intro ℓ hℓ
    simp only [R, List.mem_append] at hℓ
    rcases hℓ with (hℓ | hℓ) | hℓ
    · exact flies_dropLegs _ _ _ ℓ hℓ
    · exact flies_crossLegs hS _ _ _ _ ℓ hℓ
    · exact flies_pickLegs hS _ _ ℓ hℓ
  have htime : endTime 0 R = endTime (2 * load N.d kids.labels + 2 * load N.d free)
      (pickLegs N.d (2 * load N.d kids.labels + 2 * load N.d free) par : List (Leg n t)) := by
    rw [endTime_append, endTime_append, endTime_dropLegs, zero_add, endTime_crossLegs,
      Multiset.coe_toList]
  have hland : routeLandings R = kids.labels + free + extraOf par := by
    rw [routeLandings_append, routeLandings_append, routeLandings_dropLegs,
      routeLandings_crossLegs, routeLandings_pickLegs, Multiset.coe_toList]
  refine ⟨⟨hflies, hroute, hend⟩, ?_⟩
  rw [htime, hland]
  rw [add_comm kids.labels free] at *
  rcases par with _ | ⟨i, a, j⟩
  · simp only [extraOf, add_zero, load_add, endTime_pickLegs_none] at hg ⊢
    omega
  · have := hpar i a j rfl
    simp only [extraOf, load_add, load_singleton, endTime_pickLegs_some] at hg ⊢
    omega

mutual
/-- Every plane of a tree is feasible, flies at least twice its load, and ends by `B`. -/
theorem LTree.feasible_routes {N : Network n} (hS : N.dbar = N.d) {B : ℕ} :
    ∀ (T : LTree n) (par : ParentLink n) (c : ℕ), T.WF →
      (∀ g ∈ T.groups (extraOf par), 2 * load N.d g ≤ B) →
      (∀ i a j, par = some (i, a, j) → a + N.d i ≤ B) →
      ∀ R ∈ (T.routes N.d par c : List (List (Leg n t))),
        PlaneFeasible N R ∧ 2 * load N.d (routeLandings R) ≤ endTime 0 R ∧ endTime 0 R ≤ B
  | .node free kids, par, c, hwf, hg, hpar => by
    obtain ⟨hodd, hk⟩ := hwf
    have hroot : 2 * load N.d (free + kids.labels + extraOf par) ≤ B :=
      hg _ (Multiset.mem_cons_self _ _)
    intro R hR
    simp only [LTree.routes, List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact rootRoute_spec hS free kids par c hodd hroot hpar
    · refine LKids.feasible_routes hS kids 0 c _ hk
        (fun g hg' => hg g (Multiset.mem_cons_of_mem hg')) ?_ R hR
      simp only [load_add] at hroot
      omega
/-- Every plane of the subtrees of child items is feasible, flies at least twice its load, and
ends by `B`. -/
theorem LKids.feasible_routes {N : Network n} (hS : N.dbar = N.d) {B : ℕ} :
    ∀ (K : LKids n) (τ cl cs : ℕ), K.WF → (∀ g ∈ K.groups, 2 * load N.d g ≤ B) →
      τ + 2 * load N.d K.labels ≤ B →
      ∀ R ∈ (K.routes N.d τ cl cs : List (List (Leg n t))),
        PlaneFeasible N R ∧ 2 * load N.d (routeLandings R) ≤ endTime 0 R ∧ endTime 0 R ≤ B
  | .nil, _, _, _, _, _, _ => by simp [LKids.routes]
  | .cons b child rest, τ, cl, cs, hwf, hg, hτ => by
    obtain ⟨hc, hr⟩ := hwf
    simp only [LKids.labels, load_cons] at hτ
    intro R hR
    simp only [LKids.routes, List.mem_append] at hR
    rcases hR with hR | hR
    · refine LTree.feasible_routes hS child (some (b, τ + N.d b, cl)) cs hc
        (fun g hg' => hg g (Multiset.mem_add.mpr (Or.inl hg'))) (fun i a j h => ?_) R hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      omega
    · exact LKids.feasible_routes hS rest _ _ _ hr
        (fun g hg' => hg g (Multiset.mem_add.mpr (Or.inr hg'))) (by omega) R hR
end

/-! ### Forests -/

theorem forestGroups_cons (T : LTree n) (F : List (LTree n)) :
    forestGroups (T :: F) = T.groups 0 + forestGroups F := by
  simp [forestGroups]

theorem forest_landings (d : Fin n → ℕ) : ∀ (F : List (LTree n)) (c : ℕ),
    (((forestRoutes d F c : List (List (Leg n t))).map routeLandings : List (Multiset (Fin n))) :
      Multiset (Multiset (Fin n))) = forestGroups F
  | [], _ => rfl
  | T :: F, c => by
    simp only [forestRoutes, List.map_append, ← Multiset.coe_add, forestGroups_cons,
      forest_landings d F]
    rw [LTree.landings_routes d T none c]
    rfl

theorem forest_feasible {N : Network n} (hS : N.dbar = N.d) {B : ℕ} :
    ∀ (F : List (LTree n)) (c : ℕ), (∀ T ∈ F, T.WF) → (∀ g ∈ forestGroups F, 2 * load N.d g ≤ B) →
      ∀ R ∈ (forestRoutes N.d F c : List (List (Leg n t))),
        PlaneFeasible N R ∧ 2 * load N.d (routeLandings R) ≤ endTime 0 R ∧ endTime 0 R ≤ B
  | [], _, _, _ => by simp [forestRoutes]
  | T :: F, c, hwf, hg => by
    rw [forestGroups_cons] at hg
    intro R hR
    simp only [forestRoutes, List.mem_append] at hR
    rcases hR with hR | hR
    · exact LTree.feasible_routes hS T none c (hwf T List.mem_cons_self)
        (fun g hg' => hg g (Multiset.mem_add.mpr (Or.inl hg'))) (fun _ _ _ h => by cases h) R hR
    · exact forest_feasible hS F _ (fun T' hT' => hwf T' (List.mem_cons_of_mem _ hT'))
        (fun g hg' => hg g (Multiset.mem_add.mpr (Or.inr hg'))) R hR

theorem forest_legs (d : Fin n → ℕ) : ∀ (F : List (LTree n)) (c : ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      (((forestRoutes d F c : List (List (Leg n t))).flatten : List (Leg n t)) :
        Multiset (Leg n t)) = ((forestUnits d F c).map (PaxUnit.legs d)).sum + E
  | [], _ => ⟨0, by simp, by simp [forestRoutes, forestUnits]⟩
  | T :: F, c => by
    obtain ⟨E₁, hE₁, h₁⟩ := LTree.legs_routes (t := t) d T none c
    obtain ⟨E₂, hE₂, h₂⟩ := forest_legs d F (c + T.nUnits)
    refine ⟨E₁ + E₂, pax_none_add hE₁ hE₂, ?_⟩
    simp only [forestRoutes, forestUnits, List.flatten_append, ← Multiset.coe_add,
      List.map_append, List.sum_append, h₁, h₂, pickCarry, add_zero]
    abel

theorem forest_ids (d : Fin n → ℕ) : ∀ (F : List (LTree n)) (c : ℕ),
    (forestUnits d F c).map PaxUnit.j = List.range' c (forestCount F)
  | [], _ => rfl
  | T :: F, c => by
    simp only [forestUnits, forestCount, List.map_append, LTree.units_ids, forest_ids d F,
      List.range'_append_1]

theorem forest_time (d : Fin n → ℕ) : ∀ (F : List (LTree n)) (c : ℕ),
    ∀ u ∈ forestUnits d F c, u.e + d u.x ≤ u.e'
  | [], _ => by simp [forestUnits]
  | T :: F, c => by
    intro u hu
    simp only [forestUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · exact LTree.units_time d T c u hu
    · exact forest_time d F _ u hu

theorem forest_two_mul_count : ∀ F : List (LTree n), (∀ T ∈ F, T.WF) →
    2 * forestCount F = ((forestGroups F).map fun g => g.card + 1).sum
  | [], _ => by simp [forestCount, forestGroups]
  | T :: F, hwf => by
    have h₁ := LTree.two_mul_nUnits T 0 (hwf T List.mem_cons_self)
    have h₂ := forest_two_mul_count F fun T' hT' => hwf T' (List.mem_cons_of_mem _ hT')
    simp only [Multiset.card_zero, add_zero] at h₁
    rw [forestGroups_cons, Multiset.map_add, Multiset.sum_add, ← h₁, ← h₂, forestCount]
    ring

/-! ### Passengers -/

theorem PaxUnit.filter_legs (d : Fin n → ℕ) (π : Fin t) (u : PaxUnit n) (hu : u.j < t) :
    (u.legs d : Multiset (Leg n t)).filter (fun ℓ => ℓ.pax = some π) =
      if u.j = π.val then u.legs d else 0 := by
  have hpid : pid t u.j = some ⟨u.j, hu⟩ := by simp [pid, hu]
  unfold PaxUnit.legs
  rw [hpid]
  by_cases h : u.j = π.val
  · have : (⟨u.j, hu⟩ : Fin t) = π := Fin.ext h
    rw [this]
    simp [h]
  · have : (⟨u.j, hu⟩ : Fin t) ≠ π := fun h' => h (congrArg Fin.val h')
    simp [this, h]

theorem filter_sum_legs (d : Fin n → ℕ) (π : Fin t) : ∀ U : List (PaxUnit n), (∀ u ∈ U, u.j < t) →
    ((U.map (PaxUnit.legs d)).sum : Multiset (Leg n t)).filter (fun ℓ => ℓ.pax = some π) =
      ((U.filter fun u => u.j = π.val).map (PaxUnit.legs d)).sum
  | [], _ => by simp
  | u :: U, hU => by
    have ih := filter_sum_legs d π U fun u' hu' => hU u' (List.mem_cons_of_mem _ hu')
    rw [List.map_cons, List.sum_cons, Multiset.filter_add, ih,
      PaxUnit.filter_legs d π u (hU u List.mem_cons_self), List.filter_cons]
    by_cases h : u.j = π.val <;> simp [h]

/-! ### Theorem 4.1 -/

theorem map_finRange_getD {α : Type*} (L : List α) (a : α) {p : ℕ} (h : L.length = p) :
    (List.finRange p).map (fun k : Fin p => L.getD k a) = L := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  simp [List.getElem?_eq_getElem h₂]

/-- **Theorem 4.1 (achievability).** Under (S), with `p ≤ t`, every admissible partition `X` of
`2t − p` landings is achieved by a feasible plan whose planes land exactly at the groups of `X`
(up to relabelling the planes), so of cost `c(X)`, and whose makespan is `max_k 2 δ(X_k)`. The
plan flies no central flight, so nothing is assumed on them. -/
theorem Admissible.exists_plan {N : Network n} (hS : N.dbar = N.d) {p : ℕ} (hpt : p ≤ t)
    (c : Fin n → ℕ) {X : Groups n p} (hX : Admissible X) (hsize : size X = 2 * t - p) :
    ∃ P : Plan n t p, Feasible N P ∧
      univ.val.map (fun k => routeLandings (P k)) = univ.val.map X ∧
      planCost c P = totalCost c X ∧ planMakespan P = 2 * maxLoad N.d X := by
  classical
  obtain ⟨F, hF, hFg⟩ := hX.exists_linkForest
  set L : List (List (Leg n t)) := forestRoutes N.d F 0 with hL
  set U : List (PaxUnit n) := forestUnits N.d F 0 with hU
  have hland : ((L.map routeLandings : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
      univ.val.map X := (forest_landings N.d F 0).trans hFg
  have hlen : L.length = p := by
    have := congrArg Multiset.card hland
    simpa using this
  have hcount : forestCount F = t := by
    have h := forest_two_mul_count F hF
    rw [hFg, Multiset.map_map] at h
    have h' : (univ.val.map ((fun g : Multiset (Fin n) => g.card + 1) ∘ X)).sum = size X + p := by
      rw [← Finset.sum_eq_multiset_sum]
      simp [size, Finset.sum_add_distrib]
    omega
  have hgB : ∀ g ∈ forestGroups F, 2 * load N.d g ≤ 2 * maxLoad N.d X := by
    intro g hg
    rw [hFg] at hg
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hg
    exact Nat.mul_le_mul_left 2 (load_le_maxLoad _ _ _)
  have hfeas := forest_feasible (t := t) hS F 0 hF hgB
  obtain ⟨E, hE, hlegs⟩ := forest_legs (t := t) N.d F 0
  have hids : U.map PaxUnit.j = List.range t := by
    rw [hU, forest_ids, hcount, List.range_eq_range']
  have htime := forest_time N.d F 0
  have hUlt : ∀ u ∈ U, u.j < t := fun u hu => by
    have : u.j ∈ U.map PaxUnit.j := List.mem_map_of_mem hu
    rwa [hids, List.mem_range] at this
  -- The plan: the routes, plane by plane.
  set P : Plan n t p := fun k => L.getD k [] with hP
  have hPL : (List.finRange p).map P = L := map_finRange_getD L [] hlen
  have hmemP : ∀ k, P k ∈ L := fun k => by
    rw [← hPL]
    exact List.mem_map_of_mem (List.mem_finRange k)
  have hmemL : ∀ R ∈ L, ∃ k, P k = R := fun R hR => by
    rw [← hPL] at hR
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hR
    exact ⟨k, hk⟩
  have hall : allLegs P = L.flatten := by rw [allLegs, List.flatMap_def, hPL]
  have hmap : ∀ {β : Type} (f : List (Leg n t) → β),
      univ.val.map (fun k => f (P k)) = ((L.map f : List β) : Multiset β) := by
    intro β f
    rw [Fin.univ_val_map, List.ofFn_eq_map, ← hPL, List.map_map]
    rfl
  refine ⟨P, ⟨fun k => (hfeas _ (hmemP k)).1, fun π => ?_⟩, ?_, ?_, ?_⟩
  · -- Passenger `π` rides the two legs of its journey.
    have hfilter : (U.filter fun u => u.j = π.val).map PaxUnit.j = [π.val] := by
      rw [show (fun u : PaxUnit n => decide (u.j = π.val)) =
          (fun m => decide (m = π.val)) ∘ PaxUnit.j from rfl, ← List.filter_map, hids,
        List.filter_eq, List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr π.isLt)]
      rfl
    obtain ⟨u, hu1, hu2⟩ := List.map_eq_singleton_iff.mp hfilter
    have huU : u ∈ U := by
      have : u ∈ U.filter fun u => u.j = π.val := by
        rw [hu1]
        exact List.mem_singleton_self u
      exact (List.mem_filter.mp this).1
    have hpid : pid t u.j = some π := by
      rw [hu2]
      simp [pid]
    refine ⟨[⟨.ci, .city u.x, u.e, u.e + N.d u.x, some π⟩,
      ⟨.city u.x, .cg, u.e', u.e' + N.d u.x, some π⟩], ?_,
      ⟨rfl, Nat.zero_le _, rfl, htime u huU, trivial⟩, rfl⟩
    rw [← Multiset.coe_eq_coe]
    calc _ = (u.legs N.d : Multiset (Leg n t)) := by
          simp only [PaxUnit.legs, hpid]
          rfl
      _ = ((U.filter fun u => u.j = π.val).map (PaxUnit.legs N.d)).sum := by rw [hu1]; simp
      _ = ((U.map (PaxUnit.legs N.d)).sum : Multiset (Leg n t)).filter
            (fun ℓ => ℓ.pax = some π) := (filter_sum_legs N.d π U hUlt).symm
      _ = ((L.flatten : List (Leg n t)) : Multiset (Leg n t)).filter
            (fun ℓ => ℓ.pax = some π) := by
          rw [hlegs, Multiset.filter_add,
            show Multiset.filter (fun ℓ : Leg n t => ℓ.pax = some π) E = 0 from
              Multiset.filter_eq_nil.mpr fun ℓ hℓ h => by rw [hE ℓ hℓ] at h; cases h]
          simp only [add_zero]
          rfl
      _ = _ := by rw [paxLegs, hall, Multiset.filter_coe]
  · rw [hmap routeLandings]
    exact hland
  · have h₁ : planCost c P = ((L.map fun R => cost c (routeLandings R) : List ℕ) :
        Multiset ℕ).sum := by
      rw [planCost, Finset.sum_eq_multiset_sum,
        show (fun k => ((P k).map (landCost c)).sum) = fun k => cost c (routeLandings (P k)) from
          funext fun k => landCostSum_eq_cost c (P k),
        hmap fun R => cost c (routeLandings R)]
    have h₂ : totalCost c X = ((univ.val.map X).map (cost c)).sum := by
      rw [totalCost, Finset.sum_eq_multiset_sum, Multiset.map_map]
      rfl
    rw [h₁, h₂, ← hland, Multiset.map_coe, List.map_map]
    rfl
  · apply le_antisymm
    · exact Finset.sup_le fun k _ => (hfeas _ (hmemP k)).2.2
    · have hk : ∀ k, 2 * load N.d (X k) ≤ planMakespan P := by
        intro k
        have hk : X k ∈ ((L.map routeLandings : List (Multiset (Fin n))) :
            Multiset (Multiset (Fin n))) := by
          rw [hland]
          exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
        obtain ⟨R, hR, hRk⟩ := List.mem_map.mp (Multiset.mem_coe.mp hk)
        obtain ⟨k', rfl⟩ := hmemL R hR
        rw [← hRk]
        exact (hfeas _ hR).2.1.trans (endTime_le_planMakespan P k')
      have : maxLoad N.d X ≤ planMakespan P / 2 :=
        (maxLoad_le_iff _ _ _).mpr fun k => by have := hk k; omega
      omega

/-- **Theorem 4.1**, as the hypothesis of `minimal_achievable_iff_anywhere`. -/
theorem admissibleAchievable {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ) {p : ℕ}
    (hpt : p ≤ t) : AdmissibleAchievable N c t p := fun _ hX hsize => by
  obtain ⟨P, hP, -, hc, hm⟩ := hX.exists_plan hS hpt c hsize
  exact ⟨P, hP, hc.le, hm.le⟩

/-! ### Fronts -/

/-- **Theorem 4.9 (bridge B3).** Under (S) and (A1), with `p ≤ t`, the feasible plans and the
plans whose planes end anywhere have the same minimal (cost, makespan) pairs. -/
theorem minimal_achievable_iff_anywhere_of_A1 {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    (c : Fin n → ℕ) {p : ℕ} (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ achievableAnywhere N c t p) x :=
  minimal_achievable_iff_anywhere hS hA1 (admissibleAchievable hS c hpt) hpt x

/-- If every point of `A` is weakly dominated by a point of `B`, minimal points of `A` are minimal
points of `B` as soon as every point of `B` is also weakly dominated by a point of `A`. -/
theorem minimal_of_dominated {α : Type*} [PartialOrder α] {A B : Set α}
    (hAB : ∀ y ∈ A, ∃ x ∈ B, x ≤ y) (hBA : ∀ y ∈ B, ∃ x ∈ A, x ≤ y) {x : α}
    (hx : Minimal (· ∈ A) x) : Minimal (· ∈ B) x := by
  obtain ⟨hxA, hmin⟩ := hx
  obtain ⟨z, hzB, hzx⟩ := hAB x hxA
  obtain ⟨w, hwA, hwz⟩ := hBA z hzB
  have hxw := hmin hwA (hwz.trans hzx)
  have hzx' : z = x := le_antisymm hzx (hxw.trans hwz)
  subst hzx'
  refine ⟨hzB, fun y hyB hyz => ?_⟩
  obtain ⟨w', hw'A, hw'y⟩ := hBA y hyB
  exact (hmin hw'A (hw'y.trans hyz)).trans hw'y

/-- Two sets that weakly dominate each other have the same minimal points. -/
theorem minimal_iff_of_dominated {α : Type*} [PartialOrder α] {A B : Set α}
    (hAB : ∀ y ∈ A, ∃ x ∈ B, x ≤ y) (hBA : ∀ y ∈ B, ∃ x ∈ A, x ≤ y) (x : α) :
    Minimal (· ∈ A) x ↔ Minimal (· ∈ B) x :=
  ⟨minimal_of_dominated hAB hBA, minimal_of_dominated hBA hAB⟩

/-- The points of the admissible partitions of `2t − p` landings: `(c(X), 2 max_k δ(X_k))`. -/
def admissiblePoints (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
    (totalCost c X, 2 * maxLoad N.d X) = x}

/-- Under (S), every admissible point is the point of a feasible plan (Theorem 4.1). -/
theorem admissiblePoints_subset_achievable {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ)
    {p : ℕ} (hpt : p ≤ t) : admissiblePoints N c t p ⊆ achievable N c t p := by
  rintro x ⟨X, hX, hsize, rfl⟩
  obtain ⟨P, hP, -, hc, hm⟩ := hX.exists_plan hS hpt c hsize
  exact ⟨P, hP, by rw [hc, hm]⟩

/-- A plan whose groups `X` have `2 δ(X_k) ≤ M` and cost at most `C` gives an admissible point
below `(C, M)`. -/
theorem admissiblePoint_le {N : Network n} {c : Fin n → ℕ} {p : ℕ} {X : Groups n p}
    (hX : Admissible X) (hsize : size X = 2 * t - p) {C M : ℕ}
    (hload : ∀ k, 2 * load N.d (X k) ≤ M) (hcost : totalCost c X ≤ C) :
    ∃ x ∈ admissiblePoints N c t p, x ≤ (C, M) := by
  refine ⟨_, ⟨X, hX, hsize, rfl⟩, Prod.le_def.mpr ⟨hcost, ?_⟩⟩
  have : maxLoad N.d X ≤ M / 2 := (maxLoad_le_iff _ _ _).mpr fun k => by have := hload k; omega
  change 2 * maxLoad N.d X ≤ M
  omega

/-- **Corollary 4.8 (front characterisation), partition form.** Under (S) and (A1), with
`p ≤ t`, the front of the feasible plans is the set of minimal admissible points. -/
theorem minimal_achievable_iff_admissiblePoints {N : Network n} (hS : N.dbar = N.d)
    (hA1 : N.A1) (c : Fin n → ℕ) {p : ℕ} (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ admissiblePoints N c t p) x := by
  refine minimal_iff_of_dominated (fun y hy => ?_)
    (fun y hy => ⟨y, admissiblePoints_subset_achievable hS c hpt hy, le_rfl⟩) x
  obtain ⟨P, hP, rfl⟩ := hy
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible hS hA1 c hpt
  exact admissiblePoint_le hX hsize hload hcost

/-- **Corollary 4.8 for planes ending anywhere.** Under (S) and (A1), with `p ≤ t`, the front of
the plans whose planes end anywhere is the set of minimal admissible points. -/
theorem minimal_achievableAnywhere_iff_admissiblePoints {N : Network n} (hS : N.dbar = N.d)
    (hA1 : N.A1) (c : Fin n → ℕ) {p : ℕ} (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievableAnywhere N c t p) x ↔ Minimal (· ∈ admissiblePoints N c t p) x :=
  (minimal_achievable_iff_anywhere_of_A1 hS hA1 c hpt x).symm.trans
    (minimal_achievable_iff_admissiblePoints hS hA1 c hpt x)

/-- `M(Y)`: the least `2 max_k δ(X_k)` over the admissible partitions `X` of the multiset `Y`
(`0` if there is none). -/
noncomputable def minMakespan (d : Fin n → ℕ) (p : ℕ) (Y : Multiset (Fin n)) : ℕ :=
  sInf {m | ∃ X : Groups n p, Admissible X ∧ landings X = Y ∧ 2 * maxLoad d X = m}

/-- The note's `𝒳`: the points `(c(Y), M(Y))` of the multisets `Y` of `2t − p` landings that
have an admissible partition into `p` groups. -/
def multisetPoints (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ Y : Multiset (Fin n), Y.card = 2 * t - p ∧
    (∃ X : Groups n p, Admissible X ∧ landings X = Y) ∧ (cost c Y, minMakespan N.d p Y) = x}

/-- The note's `𝒳` and the admissible points have the same minimal points: a multiset's point
is the point of a partition reaching `M(Y)`, and a partition's point is weakly dominated by its
multiset's point. -/
theorem minimal_admissiblePoints_iff_multisetPoints (N : Network n) (c : Fin n → ℕ) {p : ℕ}
    (x : ℕ × ℕ) :
    Minimal (· ∈ admissiblePoints N c t p) x ↔ Minimal (· ∈ multisetPoints N c t p) x := by
  refine minimal_iff_of_dominated (fun y hy => ?_) (fun y hy => ?_) x
  · obtain ⟨X, hX, hsize, rfl⟩ := hy
    refine ⟨_, ⟨landings X, by rw [← size_eq_card_landings, hsize], ⟨X, hX, rfl⟩, rfl⟩,
      Prod.le_def.mpr ⟨(totalCost_eq_cost_landings c X).ge, Nat.sInf_le ⟨X, hX, rfl, rfl⟩⟩⟩
  · obtain ⟨Y, hcard, hne, rfl⟩ := hy
    obtain ⟨X, hX, hXY, hXm⟩ := Nat.sInf_mem (s := {m | ∃ X : Groups n p, Admissible X ∧
      landings X = Y ∧ 2 * maxLoad N.d X = m}) (by
        obtain ⟨X, hX, hXY⟩ := hne
        exact ⟨_, X, hX, hXY, rfl⟩)
    refine ⟨_, ⟨X, hX, by rw [size_eq_card_landings, hXY, hcard], rfl⟩, Prod.le_def.mpr ⟨?_, ?_⟩⟩
    · rw [totalCost_eq_cost_landings, hXY]
    · exact hXm.le

/-- **Corollary 4.8 (front characterisation), as in the note.** Under (S) and (A1), with
`p ≤ t`, the front is `Min 𝒳`, with `𝒳` the points `(c(Y), M(Y))` of the multisets of `2t − p`
landings that have an admissible partition. -/
theorem minimal_achievable_iff_multisetPoints {N : Network n} (hS : N.dbar = N.d)
    (hA1 : N.A1) (c : Fin n → ℕ) {p : ℕ} (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ multisetPoints N c t p) x :=
  (minimal_achievable_iff_admissiblePoints hS hA1 c hpt x).trans
    (minimal_admissiblePoints_iff_multisetPoints N c x)

end ZenoFront
