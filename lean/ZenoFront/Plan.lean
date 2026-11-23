/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Model
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.Lattice

/-!
# Plans and their feasibility

The plan semantics of certificate format v1 (`doc/certificate-format.md`), generalised so that a
theorem about *every* plan is meaningful:

* locations are `C_I`, the central cities and `C_G`;
* a plan gives every plane a list of legs `(from, to, depart, arrive, passenger)`, with at most
  one passenger per leg (capacity one, by construction);
* a leg is a flight of the network: hub–central legs last `d` (via `C_I`) or `d̄` (via `C_G`),
  and, unlike format v1, central–central legs are allowed with an **arbitrary** duration table
  `dc`; there is no flight between two hubs;
* every plane starts in `C_I` at time `≥ 0`, each leg leaves where the previous one arrived and no
  earlier, and the plane ends in `C_G`;
* every passenger starts in `C_I` at time `0`, and the legs that carry it, in some order, form a
  chain of the same kind that ends in `C_G`.

Times are natural numbers (format v1 has integer times). The cost is the sum of the landing costs
of the legs that land in a central city; the makespan is the latest arrival of a plane.
-/

@[expose] public section

namespace ZenoFront

/-- Locations: the initial hub `C_I`, the central cities, and the goal hub `C_G`. -/
inductive Loc (n : ℕ) where
  | ci : Loc n
  | city (i : Fin n) : Loc n
  | cg : Loc n
  deriving DecidableEq, Repr

namespace Loc

variable {n : ℕ}

/-- `C_I` and `C_G` are the hubs. -/
def isHub : Loc n → Bool
  | city _ => false
  | _ => true

/-- Whether the location is `C_I`. -/
def isCI : Loc n → Bool
  | ci => true
  | _ => false

/-- Whether the location is `C_G`. -/
def isCG : Loc n → Bool
  | cg => true
  | _ => false

@[simp] theorem isHub_ci : (ci : Loc n).isHub = true := rfl
@[simp] theorem isHub_cg : (cg : Loc n).isHub = true := rfl
@[simp] theorem isHub_city (i : Fin n) : (city i).isHub = false := rfl
@[simp] theorem isCI_ci : (ci : Loc n).isCI = true := rfl
@[simp] theorem isCI_cg : (cg : Loc n).isCI = false := rfl
@[simp] theorem isCI_city (i : Fin n) : (city i).isCI = false := rfl
@[simp] theorem isCG_ci : (ci : Loc n).isCG = false := rfl
@[simp] theorem isCG_cg : (cg : Loc n).isCG = true := rfl
@[simp] theorem isCG_city (i : Fin n) : (city i).isCG = false := rfl

end Loc

/-- A leg: a flight of one plane from `src` to `dst`, leaving at `dep` and arriving at `arr`,
carrying passenger `pax` (or none). -/
structure Leg (n t : ℕ) where
  src : Loc n
  dst : Loc n
  dep : ℕ
  arr : ℕ
  pax : Option (Fin t)
  deriving DecidableEq, Repr

/-- A plan: the legs of every plane, in flight order. -/
abbrev Plan (n t p : ℕ) := Fin p → List (Leg n t)

/-- The flight network: durations between `C_I` and each city (`d`), between `C_G` and each city
(`dbar`), and between central cities (`dc`, arbitrary). -/
structure Network (n : ℕ) where
  d : Fin n → ℕ
  dbar : Fin n → ℕ
  dc : Fin n → Fin n → ℕ

variable {n t p : ℕ}

/-- The duration of the flight between two locations, if there is one. There is no flight
between two hubs. -/
def Network.duration (N : Network n) : Loc n → Loc n → Option ℕ
  | .ci, .city i => some (N.d i)
  | .city i, .ci => some (N.d i)
  | .cg, .city i => some (N.dbar i)
  | .city i, .cg => some (N.dbar i)
  | .city i, .city j => some (N.dc i j)
  | _, _ => none

/-- A leg is a flight of the network, and lasts exactly the flight's duration. -/
def Flies (N : Network n) (ℓ : Leg n t) : Prop :=
  ∃ τ, N.duration ℓ.src ℓ.dst = some τ ∧ ℓ.arr = ℓ.dep + τ

/-- `IsRoute x τ legs`: starting at `x` at time `τ`, each leg leaves where the previous one
arrived (or `x`), no earlier than that arrival (or `τ`). Waiting is allowed. -/
def IsRoute : Loc n → ℕ → List (Leg n t) → Prop
  | _, _, [] => True
  | x, τ, ℓ :: rest => ℓ.src = x ∧ τ ≤ ℓ.dep ∧ IsRoute ℓ.dst ℓ.arr rest

/-- Where a route starting at `x` ends. -/
def finalLoc : Loc n → List (Leg n t) → Loc n
  | x, [] => x
  | _, ℓ :: rest => finalLoc ℓ.dst rest

/-- When a route starting at time `τ` ends: its last arrival, or `τ`. -/
def endTime : ℕ → List (Leg n t) → ℕ
  | τ, [] => τ
  | _, ℓ :: rest => endTime ℓ.arr rest

@[simp] theorem isRoute_nil (x : Loc n) (τ : ℕ) : IsRoute x τ ([] : List (Leg n t)) := trivial

@[simp] theorem isRoute_cons (x : Loc n) (τ : ℕ) (ℓ : Leg n t) (rest : List (Leg n t)) :
    IsRoute x τ (ℓ :: rest) ↔ ℓ.src = x ∧ τ ≤ ℓ.dep ∧ IsRoute ℓ.dst ℓ.arr rest := Iff.rfl

@[simp] theorem finalLoc_nil (x : Loc n) : finalLoc x ([] : List (Leg n t)) = x := rfl

@[simp] theorem finalLoc_cons (x : Loc n) (ℓ : Leg n t) (rest : List (Leg n t)) :
    finalLoc x (ℓ :: rest) = finalLoc ℓ.dst rest := rfl

@[simp] theorem endTime_nil (τ : ℕ) : endTime τ ([] : List (Leg n t)) = τ := rfl

@[simp] theorem endTime_cons (τ : ℕ) (ℓ : Leg n t) (rest : List (Leg n t)) :
    endTime τ (ℓ :: rest) = endTime ℓ.arr rest := rfl

/-- A feasible plane: its legs are flights, they form a route from `C_I` at time `0`, and the
plane ends in `C_G`. -/
structure PlaneFeasible (N : Network n) (legs : List (Leg n t)) : Prop where
  flies : ∀ ℓ ∈ legs, Flies N ℓ
  route : IsRoute .ci 0 legs
  ends : finalLoc .ci legs = .cg

/-- All legs of a plan, plane by plane. -/
def allLegs (P : Plan n t p) : List (Leg n t) := (List.finRange p).flatMap P

/-- The legs carrying passenger `π`, plane by plane. -/
def paxLegs (P : Plan n t p) (π : Fin t) : List (Leg n t) :=
  (allLegs P).filter fun ℓ => decide (ℓ.pax = some π)

/-- A feasible plan: every plane is feasible, and the legs carrying each passenger form, in some
order, a route from `C_I` at time `0` that ends in `C_G`. -/
structure Feasible (N : Network n) (P : Plan n t p) : Prop where
  planes : ∀ k, PlaneFeasible N (P k)
  pax : ∀ π, ∃ route : List (Leg n t), route.Perm (paxLegs P π) ∧ IsRoute .ci 0 route ∧
    finalLoc .ci route = .cg

/-- The landing cost of a leg: `c i` if it lands in central city `i`, `0` at a hub. -/
def landCost (c : Fin n → ℕ) (ℓ : Leg n t) : ℕ :=
  match ℓ.dst with
  | .city i => c i
  | _ => 0

/-- The cost of a plan: the landing costs of all its legs. -/
def planCost (c : Fin n → ℕ) (P : Plan n t p) : ℕ := ∑ k, ((P k).map (landCost c)).sum

/-- The makespan of a plan: the latest time a plane ends its route. -/
def planMakespan (P : Plan n t p) : ℕ := Finset.univ.sup fun k => endTime 0 (P k)

theorem endTime_le_planMakespan (P : Plan n t p) (k : Fin p) :
    endTime 0 (P k) ≤ planMakespan P :=
  Finset.le_sup (f := fun k => endTime 0 (P k)) (Finset.mem_univ k)

end ZenoFront
