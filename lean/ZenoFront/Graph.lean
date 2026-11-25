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

## Main results

* `ZenoFront.FlightGraph`, `ZenoFront.GFeasible`, `ZenoFront.gAchievable`: the model.
* `ZenoFront.feasible_iff_gFeasible`: a network's plans are the plans of its flight graph.
* `ZenoFront.GFeasible.mono`: a plan stays feasible when flights are added.
* `ZenoFront.GFeasible.feasible_of_clique`: a plan of a clique instance without central flights is
  a plan of every network with its hub durations.
* `ZenoFront.gFeasible_of_planOKDur`: the simulator is sound.
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

end ZenoFront
