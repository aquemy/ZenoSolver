/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Plan

/-!
# Simulating a plan

A computable feasibility check for the plans of certificate format v1, mirroring
`checkPlan` in `src/zeno/plan.cpp`:

* every leg is a hub–central flight of exactly the right duration (format v1 has no
  central–central legs);
* every plane's legs form a route from `C_I` at time `0` ending in `C_G`;
* every passenger is followed greedily: from where it is, the earliest leg (by departure, then
  arrival; the first one in plan order on a tie) that carries it out of that location no earlier
  than it got there. All its legs must be used, and it must end in `C_G`.

`planOK_feasible` proves that an accepted plan is feasible for **every** table of central
flight durations `dc`.
-/

@[expose] public section

namespace ZenoFront

variable {n t p : ℕ}

/-- A leg is a hub–central flight of the right duration (`d` via `C_I`, `dbar` via `C_G`). -/
def legOK (d dbar : Fin n → ℕ) (ℓ : Leg n t) : Bool :=
  match ℓ.src, ℓ.dst with
  | .ci, .city i => ℓ.arr == ℓ.dep + d i
  | .city i, .ci => ℓ.arr == ℓ.dep + d i
  | .cg, .city i => ℓ.arr == ℓ.dep + dbar i
  | .city i, .cg => ℓ.arr == ℓ.dep + dbar i
  | _, _ => false

theorem flies_of_legOK {d dbar : Fin n → ℕ} (dc : Fin n → Fin n → ℕ) {ℓ : Leg n t}
    (h : legOK d dbar ℓ = true) : Flies ⟨d, dbar, dc⟩ ℓ := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases src <;> cases dst <;> simp [legOK] at h <;> exact ⟨_, rfl, h⟩

/-- The legs form a route from `x` at time `τ`. -/
def routeOK : Loc n → ℕ → List (Leg n t) → Bool
  | _, _, [] => true
  | x, τ, ℓ :: rest => decide (ℓ.src = x) && decide (τ ≤ ℓ.dep) && routeOK ℓ.dst ℓ.arr rest

theorem isRoute_of_routeOK : ∀ {x : Loc n} {τ : ℕ} {l : List (Leg n t)},
    routeOK x τ l = true → IsRoute x τ l
  | _, _, [], _ => trivial
  | x, τ, ℓ :: rest, h => by
    simp only [routeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, isRoute_of_routeOK h.2⟩

/-- A plane is feasible (format v1 legs). -/
def planeOK (d dbar : Fin n → ℕ) (legs : List (Leg n t)) : Bool :=
  legs.all (legOK d dbar) && routeOK .ci 0 legs && decide (finalLoc .ci legs = .cg)

theorem planeFeasible_of_planeOK {d dbar : Fin n → ℕ} (dc : Fin n → Fin n → ℕ)
    {legs : List (Leg n t)} (h : planeOK d dbar legs = true) :
    PlaneFeasible ⟨d, dbar, dc⟩ legs := by
  simp only [planeOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun ℓ hℓ => flies_of_legOK dc (h.1.1 ℓ hℓ), isRoute_of_routeOK h.1.2, h.2⟩

/-- `a` leaves strictly before `b`, by departure and then arrival. -/
def Leg.before (a b : Leg n t) : Bool := a.dep < b.dep || (a.dep == b.dep && a.arr < b.arr)

/-- The earliest leg (by departure, then arrival; the first one on a tie) leaving `x` no
earlier than `τ`. -/
def pickLeg (x : Loc n) (τ : ℕ) : List (Leg n t) → Option (Leg n t)
  | [] => none
  | ℓ :: rest =>
    if ℓ.src = x ∧ τ ≤ ℓ.dep then
      match pickLeg x τ rest with
      | some b => if b.before ℓ then some b else some ℓ
      | none => some ℓ
    else pickLeg x τ rest

theorem pickLeg_spec {x : Loc n} {τ : ℕ} : ∀ {l : List (Leg n t)} {ℓ : Leg n t},
    pickLeg x τ l = some ℓ → ℓ ∈ l ∧ ℓ.src = x ∧ τ ≤ ℓ.dep
  | [], _, h => by simp [pickLeg] at h
  | m :: rest, ℓ, h => by
    unfold pickLeg at h
    split_ifs at h with hm
    · split at h
      · rename_i b hb
        split_ifs at h
        · cases h
          obtain ⟨h₁, h₂⟩ := pickLeg_spec hb
          exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩
        · cases h
          exact ⟨List.mem_cons_self, hm⟩
      · cases h
        exact ⟨List.mem_cons_self, hm⟩
    · obtain ⟨h₁, h₂⟩ := pickLeg_spec h
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩

/-- Follow a passenger for `k` legs from `x` at time `τ`, each time taking `pickLeg` among the
legs not used yet; returns where it ends. -/
def follow : ℕ → List (Leg n t) → Loc n → ℕ → Option (Loc n)
  | 0, _, x, _ => some x
  | k + 1, legs, x, τ =>
    match pickLeg x τ legs with
    | none => none
    | some ℓ => follow k (legs.erase ℓ) ℓ.dst ℓ.arr

/-- A successful run of `follow` through all the legs orders them into a route. -/
theorem follow_sound : ∀ (k : ℕ) (legs : List (Leg n t)) (x : Loc n) (τ : ℕ) (y : Loc n),
    legs.length = k → follow k legs x τ = some y →
    ∃ route : List (Leg n t), route.Perm legs ∧ IsRoute x τ route ∧ finalLoc x route = y
  | 0, legs, x, τ, y, hlen, h => by
    simp only [follow, Option.some.injEq] at h
    subst h
    exact ⟨[], by rw [List.length_eq_zero_iff.mp hlen], trivial, rfl⟩
  | k + 1, legs, x, τ, y, hlen, h => by
    simp only [follow] at h
    split at h
    · exact absurd h (by simp)
    · rename_i ℓ hpick
      obtain ⟨hmem, hsrc, hdep⟩ := pickLeg_spec hpick
      have hlen' : (legs.erase ℓ).length = k := by
        rw [List.length_erase_of_mem hmem]
        omega
      obtain ⟨route, hperm, hroute, hfin⟩ := follow_sound k (legs.erase ℓ) ℓ.dst ℓ.arr y hlen' h
      exact ⟨ℓ :: route, (hperm.cons ℓ).trans (List.perm_cons_erase hmem).symm,
        ⟨hsrc, hdep, hroute⟩, hfin⟩

/-- Passenger `π` reaches `C_G` along all its legs among `all` (the plan's legs). -/
def paxOKIn (all : List (Leg n t)) (π : Fin t) : Bool :=
  let legs := all.filter fun ℓ => decide (ℓ.pax = some π)
  decide (follow legs.length legs .ci 0 = some .cg)

/-- Passenger `π` reaches `C_G` along all its legs. -/
def paxOK (P : Plan n t p) (π : Fin t) : Bool := paxOKIn (allLegs P) π

/-- The plan is feasible (format v1): every plane, then every passenger (the plan's legs are
gathered once). -/
def planOK (d dbar : Fin n → ℕ) (P : Plan n t p) : Bool :=
  (List.finRange p).all (fun k => planeOK d dbar (P k)) &&
    (let all := allLegs P
     (List.finRange t).all (paxOKIn all))

/-- **The simulation is sound.** A plan the simulation accepts is feasible, whatever the
central flight durations `dc`. -/
theorem planOK_feasible {d dbar : Fin n → ℕ} (dc : Fin n → Fin n → ℕ) {P : Plan n t p}
    (h : planOK d dbar P = true) : Feasible ⟨d, dbar, dc⟩ P := by
  simp only [planOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  refine ⟨fun k => planeFeasible_of_planeOK dc (h.1 k), fun π => ?_⟩
  have := h.2 π
  simp only [paxOKIn, decide_eq_true_eq] at this
  exact follow_sound _ _ _ _ _ rfl this

end ZenoFront
