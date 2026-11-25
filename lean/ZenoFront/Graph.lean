/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Checker

/-!
# Flight graphs

The model of §6.6 of the theory note. A *flight graph* is a duration table on the locations `C_I`,
the central vertices and `C_G`, with `none` where there is no flight. Plans, feasibility, cost and
makespan are those of `Plan.lean`, with the table's flights: legs (`Leg`), routes (`IsRoute`),
plans (`Plan`) and costs are reused as they are.

`GFeasible U P` repeats the two conditions of `Feasible` with `U.dur` in place of
`Network.duration`. It is a copy, not a generalisation: changing `Feasible` would touch every
module that uses it. `feasible_iff_gFeasible` proves that the two agree on the table of a network,
so nothing is lost.

`cliqueGraph d d̄` is the clique instance without central flights. Its plans are plans of every
network with the same hub durations (`GFeasible.feasible_of_clique`), so a certificate checked for
the network bounds them.

`planOKDur` simulates a plan on any duration table, central flights included. The simulator of
format v1, `planOK`, accepts hub flights only. `planOKDur` is sound (`gFeasible_of_planOKDur`), so
a concrete plan with central legs is proved feasible by `decide`.

The reduction of arXiv:2304.14659, §2.4, is defined for every flight graph. `vcities U` has one
virtual city for each central vertex `i`, simple path `w` from `C_I` to `i` and simple path `e`
from `i` to `C_G` (the paths may pass through a hub). `Reduced.graph U` is the clique instance of
these cities, with `d = φ(w)`, `d̄ = φ(e)` (flight times) and no central flight, and `Reduced.c U c`
gives them the costs `ω(w) + ω(e)` (the landings after the first vertex).

## Main results

* `ZenoFront.FlightGraph`, `ZenoFront.GFeasible`, `ZenoFront.gAchievable`: the model.
* `ZenoFront.feasible_iff_gFeasible`: a network's plans are the plans of its flight graph.
* `ZenoFront.GFeasible.mono`: a plan stays feasible when flights are added.
* `ZenoFront.GFeasible.feasible_of_clique`: a plan of a clique instance without central flights is
  a plan of every network with its hub durations.
* `ZenoFront.gFeasible_of_planOKDur`: the simulator is sound.
* `ZenoFront.vcities`, `ZenoFront.Reduced.graph`, `ZenoFront.Reduced.c`: the reduction `f`.
-/

@[expose] public section

namespace ZenoFront

variable {n t p : ℕ}

/-- A flight graph on `n` central vertices: the duration of the flight between two locations, if
there is one. -/
structure FlightGraph (n : ℕ) where
  /-- The duration of the flight from one location to another, `none` if there is none. -/
  dur : Loc n → Loc n → Option ℕ

namespace FlightGraph

/-- The flights are undirected: each one has the same duration both ways. -/
def Undirected (U : FlightGraph n) : Prop := ∀ a b, U.dur a b = U.dur b a

/-- There is no flight between the two hubs. -/
def NoHubFlight (U : FlightGraph n) : Prop := U.dur .ci .cg = none ∧ U.dur .cg .ci = none

end FlightGraph

/-- The flight graph of a network: a complete table of central flights, every hub flight, and no
flight between the hubs. -/
def Network.toGraph (N : Network n) : FlightGraph n := ⟨N.duration⟩

/-- A leg is a flight of the graph, and lasts exactly the flight's duration. -/
def GFlies (U : FlightGraph n) (ℓ : Leg n t) : Prop :=
  ∃ τ, U.dur ℓ.src ℓ.dst = some τ ∧ ℓ.arr = ℓ.dep + τ

/-- A feasible plane of a flight graph: its legs are flights, they form a route from `C_I` at
time `0`, and the plane ends in `C_G` (as `PlaneFeasible`). -/
structure GPlaneFeasible (U : FlightGraph n) (legs : List (Leg n t)) : Prop where
  flies : ∀ ℓ ∈ legs, GFlies U ℓ
  route : IsRoute .ci 0 legs
  ends : finalLoc .ci legs = .cg

/-- A feasible plan of a flight graph: every plane is feasible, and the legs carrying each
passenger form, in some order, a route from `C_I` at time `0` that ends in `C_G` (as
`Feasible`). -/
structure GFeasible (U : FlightGraph n) (P : Plan n t p) : Prop where
  planes : ∀ k, GPlaneFeasible U (P k)
  pax : ∀ π, ∃ route : List (Leg n t), route.Perm (paxLegs P π) ∧ IsRoute .ci 0 route ∧
    finalLoc .ci route = .cg

/-- The (cost, makespan) points of the feasible plans of a flight graph. -/
def gAchievable (U : FlightGraph n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ P : Plan n t p, GFeasible U P ∧ (planCost c P, planMakespan P) = x}

/-- **A network's feasible plans are the feasible plans of its flight graph.** -/
theorem feasible_iff_gFeasible (N : Network n) (P : Plan n t p) :
    Feasible N P ↔ GFeasible N.toGraph P :=
  ⟨fun h => ⟨fun k => ⟨(h.planes k).flies, (h.planes k).route, (h.planes k).ends⟩, h.pax⟩,
    fun h => ⟨fun k => ⟨(h.planes k).flies, (h.planes k).route, (h.planes k).ends⟩, h.pax⟩⟩

/-- A network's points are the points of its flight graph. -/
theorem achievable_eq_gAchievable (N : Network n) (c : Fin n → ℕ) (t p : ℕ) :
    achievable N c t p = gAchievable N.toGraph c t p := by
  ext x
  exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, (feasible_iff_gFeasible N P).mp hP, hx⟩,
    fun ⟨P, hP, hx⟩ => ⟨P, (feasible_iff_gFeasible N P).mpr hP, hx⟩⟩

/-- **Adding flights keeps a plan feasible**: if every flight of `U` is a flight of `V` with the
same duration, every feasible plan of `U` is a feasible plan of `V`. -/
theorem GFeasible.mono {U V : FlightGraph n}
    (hUV : ∀ a b τ, U.dur a b = some τ → V.dur a b = some τ) {P : Plan n t p}
    (h : GFeasible U P) : GFeasible V P :=
  ⟨fun k => ⟨fun ℓ hℓ => by
      obtain ⟨τ, hτ, harr⟩ := (h.planes k).flies ℓ hℓ
      exact ⟨τ, hUV _ _ _ hτ, harr⟩, (h.planes k).route, (h.planes k).ends⟩, h.pax⟩

/-! ### Clique instances without central flights -/

/-- The clique instance with hub durations `d` (to `C_I`) and `d̄` (to `C_G`) and no central
flight. -/
def cliqueGraph {m : ℕ} (d dbar : Fin m → ℕ) : FlightGraph m :=
  ⟨fun a b => match a, b with
    | .ci, .city v => some (d v)
    | .city v, .ci => some (d v)
    | .cg, .city v => some (dbar v)
    | .city v, .cg => some (dbar v)
    | _, _ => none⟩

/-- The flights of a clique instance without central flights are flights of every network with the
same hub durations, whatever its central flights. -/
theorem cliqueGraph_le_toGraph {m : ℕ} (d dbar : Fin m → ℕ) (dc : Fin m → Fin m → ℕ) :
    ∀ a b τ, (cliqueGraph d dbar).dur a b = some τ →
      (Network.toGraph ⟨d, dbar, dc⟩).dur a b = some τ := by
  intro a b τ h
  cases a <;> cases b <;>
    first
    | (simp [cliqueGraph] at h; done)
    | simpa [cliqueGraph, Network.toGraph, Network.duration] using h

/-- So every feasible plan of a clique instance without central flights is feasible in every
network with the same hub durations. -/
theorem GFeasible.feasible_of_clique {m t p : ℕ} {d dbar : Fin m → ℕ} {P : Plan m t p}
    (h : GFeasible (cliqueGraph d dbar) P) (dc : Fin m → Fin m → ℕ) :
    Feasible ⟨d, dbar, dc⟩ P :=
  (feasible_iff_gFeasible _ _).mpr (h.mono (cliqueGraph_le_toGraph d dbar dc))

/-! ### Simulation on a duration table -/

/-- A leg is a flight of the table, of the right duration. -/
def legOKDur (U : FlightGraph n) (ℓ : Leg n t) : Bool :=
  match U.dur ℓ.src ℓ.dst with
  | some τ => ℓ.arr == ℓ.dep + τ
  | none => false

theorem gFlies_of_legOKDur {U : FlightGraph n} {ℓ : Leg n t} (h : legOKDur U ℓ = true) :
    GFlies U ℓ := by
  unfold legOKDur at h
  split at h
  · rename_i τ hτ
    exact ⟨τ, hτ, by simpa using h⟩
  · exact absurd h (by simp)

/-- A plane is feasible on the table. -/
def planeOKDur (U : FlightGraph n) (legs : List (Leg n t)) : Bool :=
  legs.all (legOKDur U) && routeOK .ci 0 legs && decide (finalLoc .ci legs = .cg)

/-- The plan is feasible on the table: every plane, then every passenger (followed greedily, as
in `planOK`). -/
def planOKDur (U : FlightGraph n) (P : Plan n t p) : Bool :=
  (List.finRange p).all (fun k => planeOKDur U (P k)) &&
    (let all := allLegs P
     (List.finRange t).all (paxOKIn all))

/-- **The simulation is sound**: a plan it accepts is feasible on the table. -/
theorem gFeasible_of_planOKDur {U : FlightGraph n} {P : Plan n t p}
    (h : planOKDur U P = true) : GFeasible U P := by
  simp only [planOKDur, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine ⟨fun k => ?_, fun π => ?_⟩
  · have hk := h.1 k
    simp only [planeOKDur, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
    exact ⟨fun ℓ hℓ => gFlies_of_legOKDur (hk.1.1 ℓ hℓ), isRoute_of_routeOK hk.1.2, hk.2⟩
  · have := h.2 π
    simp only [paxOKIn, decide_eq_true_eq] at this
    exact follow_sound _ _ _ _ _ rfl this

/-- A plan the simulation accepts on a network's table is feasible in the network, central legs
included. -/
theorem feasible_of_planOKDur {N : Network n} {P : Plan n t p}
    (h : planOKDur N.toGraph P = true) : Feasible N P :=
  (feasible_iff_gFeasible N P).mpr (gFeasible_of_planOKDur h)

/-! ### The reduction of arXiv §2.4 -/

/-- The locations, in order: `C_I`, the central vertices, `C_G`. -/
def allLocs (n : ℕ) : List (Loc n) := .ci :: (List.finRange n).map .city ++ [.cg]

theorem mem_allLocs : ∀ x : Loc n, x ∈ allLocs n
  | .ci => by simp [allLocs]
  | .city i => by simp [allLocs]
  | .cg => by simp [allLocs]

/-- The simple paths from `x` to `b`, as vertex lists, that avoid the vertices `seen`; `fuel`
bounds their number of vertices. A path stops at its first visit of `b`. -/
def simplePathsFrom (U : FlightGraph n) (b : Loc n) : ℕ → List (Loc n) → Loc n → List (List (Loc n))
  | 0, _, _ => []
  | f + 1, seen, x =>
    if x = b then [[x]]
    else (allLocs n).flatMap fun y =>
      if (U.dur x y).isSome ∧ y ∉ x :: seen then
        (simplePathsFrom U b f (x :: seen) y).map (x :: ·)
      else []

/-- The simple paths from `a` to `b` (a simple path has at most `n + 2` vertices). -/
def simplePaths (U : FlightGraph n) (a b : Loc n) : List (List (Loc n)) :=
  simplePathsFrom U b (n + 2) [] a

/-- The flight time `φ` of a walk: the sum of its flight durations. -/
def pathDur (U : FlightGraph n) : List (Loc n) → ℕ
  | x :: y :: rest => (U.dur x y).getD 0 + pathDur U (y :: rest)
  | _ => 0

/-- The landing cost of a location: `c i` at central vertex `i`, `0` at a hub. -/
def locCost (c : Fin n → ℕ) : Loc n → ℕ
  | .city i => c i
  | _ => 0

/-- The landing cost `ω` of a walk: its vertices after the first. -/
def pathCost (c : Fin n → ℕ) : List (Loc n) → ℕ
  | [] => 0
  | _ :: rest => (rest.map (locCost c)).sum

/-- A virtual city of the reduction: a central vertex `i`, a simple path `w` from `C_I` to `i`
and a simple path `e` from `i` to `C_G`. -/
structure VCity (n : ℕ) where
  i : Fin n
  w : List (Loc n)
  e : List (Loc n)
  deriving DecidableEq, Repr

/-- **The reduction f of arXiv §2.4** (as in Example 6.11 of the note): one virtual city for every
central vertex `i`, every simple path `w` from `C_I` to `i` and every simple path `e` from `i` to
`C_G`. -/
def vcities (U : FlightGraph n) : List (VCity n) :=
  (List.finRange n).flatMap fun i =>
    (simplePaths U .ci (.city i)).flatMap fun w =>
      (simplePaths U (.city i) .cg).map fun e => ⟨i, w, e⟩

namespace Reduced

/-- The number of cities of `f(U)`. -/
def m (U : FlightGraph n) : ℕ := (vcities U).length

/-- The city `v` of `f(U)`. -/
def city (U : FlightGraph n) (v : Fin (m U)) : VCity n := (vcities U)[v]

/-- `d_v = φ(w)`. -/
def d (U : FlightGraph n) (v : Fin (m U)) : ℕ := pathDur U (city U v).w

/-- `d̄_v = φ(e)`. -/
def dbar (U : FlightGraph n) (v : Fin (m U)) : ℕ := pathDur U (city U v).e

/-- `c_v = ω(w) + ω(e)`: the landings of `w` followed by `e`, `c_i` counted once. -/
def c (U : FlightGraph n) (c : Fin n → ℕ) (v : Fin (m U)) : ℕ :=
  pathCost c (city U v).w + pathCost c (city U v).e

/-- **`f(U)`**: the clique instance of the virtual cities, without central flights. -/
def graph (U : FlightGraph n) : FlightGraph (m U) := cliqueGraph (d U) (dbar U)

end Reduced

end ZenoFront
