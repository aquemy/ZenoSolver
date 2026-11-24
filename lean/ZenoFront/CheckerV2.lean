/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Checker
public import ZenoFront.RoleBound

/-!
# The checker for certificate format v2 (non-symmetric instances)

Format v2 (`doc/certificate-format.md`, "Version 2") certifies fronts of instances whose
durations to `C_I` (`d`) and to `C_G` (`d̄`) may differ. Levels are full loads in units of the gcd
`g` of the weights, and a line `fastest <kind>` names the bound that rules out plans faster than
the first point.

This file verifies:

* `relaxed` (gaps and fastest point), with **no assumption**: Lemma R with the weight
  `2 min(d_i, d̄_i)` per landing (`Feasible.exists_relaxation_emin`); a segment starts and ends
  with hub flights, each lasting at least `min(d, d̄)` of its city;
* `roles` (gaps and fastest point), under (A1-NS), which the certificate must list: Theorem 6.1
  (`Feasible.exists_roleConfig_ns`) and the role relaxation (`rolesBoundAt_le_totalCost`), at
  levels `⌊(M − 1)/g⌋` for the gcd `g` of all durations;
* `fastest closed` for symmetric durations, as in v1.

The other v2 kinds (`lagrangian`, `balanced`, `search`, `forest`) are parsed but given no bound,
so a certificate that uses one is rejected.

## Main results

* `ZenoFront.Cert2.check`: the checker.
* `ZenoFront.Cert2.relaxedWith_le`: the relaxed bound is a lower bound on the cost of every
  feasible plan faster than the gap's upper point, for any durations and central flights.
* `ZenoFront.Cert2.check_sound`: if `check` accepts, the listed points are exactly the Pareto
  front, for **every** table of central flight durations.
-/

@[expose] public section

namespace ZenoFront

open Finset

/-- The bound kinds of format v2: for the fastest point (`closed`, `relaxed`, `roles`,
`balanced`, `search`) and for the gaps (`relaxed`, `forest`, `roles`, `lagrangian` with one
multiplier per city, `balanced`, `search`). -/
inductive Kind2 where
  | closed
  | relaxed
  | forest
  | roles
  | lagrangian (mu : List ℤ)
  | balanced
  | search
  deriving DecidableEq, Repr

/-- The name of a kind, as in the file. -/
def Kind2.name : Kind2 → String
  | .closed => "closed"
  | .relaxed => "relaxed"
  | .forest => "forest"
  | .roles => "roles"
  | .lagrangian _ => "lagrangian"
  | .balanced => "balanced"
  | .search => "search"

/-- A parsed certificate of format v2. -/
structure Cert2 where
  n : ℕ
  t : ℕ
  p : ℕ
  d : Fin n → ℕ
  dbar : Fin n → ℕ
  c : Fin n → ℕ
  assumptions : List String
  front : List (ℕ × ℕ)
  fastest : Kind2
  plans : List (Plan n t p)
  gaps : List Kind2

namespace Cert2

variable (C : Cert2)

/-- The number of landings of a front plan, `s = 2t − p`. -/
def s : ℕ := 2 * C.t - C.p

/-- The instance's flight network, with central flight durations `dc`. -/
def network (dc : Fin C.n → Fin C.n → ℕ) : Network C.n := ⟨C.d, C.dbar, dc⟩

/-- The weight of a landing in the relaxation: `2 min(d_i, d̄_i)`. -/
def weight (i : Fin C.n) : ℕ := 2 * min (C.d i) (C.dbar i)

/-- Whether the durations are symmetric. -/
def symmetric : Bool := decide (∀ i, C.d i = C.dbar i)

/-- The header: `1 ≤ n`, `1 ≤ p ≤ t`, and assumption `S` listed only for symmetric durations. -/
def headerOK : Bool :=
  decide (1 ≤ C.n) && decide (1 ≤ C.p) && decide (C.p ≤ C.t) &&
    (!C.assumptions.contains "S" || C.symmetric)

/-- Obligation 1: one plan per point, each feasible with the point's cost and makespan. -/
def plansOK : Bool :=
  decide (C.plans.length = C.front.length) &&
    (C.plans.zip C.front).all fun x => planOK C.d C.dbar x.1 &&
      decide (planCost C.c x.1 = x.2.1) && decide (planMakespan x.1 = x.2.2)

/-- Obligation 4: the last cost is `s · c_min`. -/
def lastOK : Bool :=
  match C.front.getLast? with
  | some x => decide (x.1 = C.s * minOf C.c)
  | none => false

/-- The relaxed bound below a point of makespan `M`: level `⌊(M − 1)/g⌋`, read from `table`. -/
def relaxedWith (scale Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (M : ℕ) : WithTop ℕ :=
  relaxedBoundAt C.p C.s Tmax table ((M - 1) / scale)

/-- The highest level of the certificate, for the scale `g`. -/
def maxLevel (scale : ℕ) : ℕ := (C.front.map fun x => (x.2 - 1) / scale).foldr max 0

/-- The scale of the role bounds: the gcd of all durations `d` and `d̄`. -/
def rolesScale : ℕ := durationScale fun i => Nat.gcd (C.d i) (C.dbar i)

/-- The `roles` bound below a point of makespan `M`, on durations scaled by `g = rolesScale`
(`dR`, `dbR`), at level `⌊(M − 1)/g⌋`; `0` (no bound) unless assumption `A1-NS` is listed. -/
def rolesWith (dR dbR : Fin C.n → ℕ) : ℕ → WithTop ℕ :=
  if C.assumptions.contains "A1-NS" then
    let TmaxR := C.maxLevel C.rolesScale
    let L := roleLayers dR dbR C.c TmaxR C.s
    let F := oneplaneTable (fillW dR dbR) C.c (C.p * TmaxR) C.s
    fun M => rolesBoundAt C.p C.s TmaxR L F ((M - 1) / C.rolesScale)
  else fun _ => 0

/-- The bound named by a kind; `0` (no bound) for the kinds this checker does not verify. -/
def boundWith (scale Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (rolesB : ℕ → WithTop ℕ) :
    Kind2 → ℕ → WithTop ℕ
  | .relaxed => C.relaxedWith scale Tmax table
  | .roles => rolesB
  | _ => fun _ => 0

/-- Obligation 2: nothing is faster than the first point. `closed` is v1's closed form
(symmetric durations only); `relaxed` requires the relaxed bound at the first point's level to be
infinite. -/
def fastestOK (bound : Kind2 → ℕ → WithTop ℕ) : Bool :=
  match C.front.head? with
  | none => false
  | some x =>
    match C.fastest with
    | .closed => C.symmetric && decide (x.2 = 2 * minOf C.d * ((C.s + C.p - 1) / C.p))
    | .relaxed => decide (bound .relaxed x.2 = ⊤)
    | .roles => decide (bound .roles x.2 = ⊤)
    | _ => false

/-- Obligations 2 and 3, with the scale, the top level and the one-plane table computed once. -/
def boundsCheck : Bool :=
  let scale := durationScale C.weight
  let Tmax := C.maxLevel scale
  let wArr := Array.ofFn (n := C.n) fun i => C.weight i / scale
  let wS : Fin C.n → ℕ := fun i => wArr.getD i 0
  let gR := C.rolesScale
  let dArr := Array.ofFn (n := C.n) fun i => C.d i / gR
  let dbArr := Array.ofFn (n := C.n) fun i => C.dbar i / gR
  let bound := C.boundWith scale Tmax (oneplaneTable wS C.c Tmax C.s)
    (C.rolesWith (fun i => dArr.getD i 0) (fun i => dbArr.getD i 0))
  C.fastestOK bound && gapsOK bound C.front C.gaps

/-- The bounds of the checker, as specified. -/
def bound : Kind2 → ℕ → WithTop ℕ :=
  C.boundWith (durationScale C.weight) (C.maxLevel (durationScale C.weight))
    (oneplaneTable (scaledDurations C.weight) C.c (C.maxLevel (durationScale C.weight)) C.s)
    (C.rolesWith (fun i => C.d i / C.rolesScale) (fun i => C.dbar i / C.rolesScale))

theorem boundsCheck_eq : C.boundsCheck = (C.fastestOK C.bound && gapsOK C.bound C.front C.gaps) := by
  have hwS : (fun i : Fin C.n => (Array.ofFn (n := C.n) fun i =>
      C.weight i / durationScale C.weight).getD i 0) = scaledDurations C.weight := by
    funext i
    simp [Array.getD_eq_getD_getElem?, scaledDurations]
  have hd : (fun i : Fin C.n => (Array.ofFn (n := C.n) fun i =>
      C.d i / C.rolesScale).getD i 0) = fun i => C.d i / C.rolesScale := by
    funext i
    simp [Array.getD_eq_getD_getElem?]
  have hdb : (fun i : Fin C.n => (Array.ofFn (n := C.n) fun i =>
      C.dbar i / C.rolesScale).getD i 0) = fun i => C.dbar i / C.rolesScale := by
    funext i
    simp [Array.getD_eq_getD_getElem?]
  simp only [boundsCheck]
  rw [hwS, hd, hdb]
  rfl

/-- **The v2 checker.** -/
def check : Bool :=
  C.headerOK && strictlyMonotone C.front && C.plansOK && C.lastOK && C.boundsCheck

theorem load_weight (dc : Fin C.n → Fin C.n → ℕ) (Y : Multiset (Fin C.n)) :
    load C.weight Y = 2 * load (C.network dc).emin Y := by
  simp only [load]
  rw [← Multiset.sum_map_mul_left]
  rfl

/-- **The relaxed bound is a lower bound**, for any durations and any central flights: a
feasible plan with makespan below `M` costs at least the relaxed bound at the level of `M`. -/
theorem relaxedWith_le {dc : Fin C.n → Fin C.n → ℕ} (hpt : C.p ≤ C.t) (Tmax : ℕ)
    {P : Plan C.n C.t C.p} (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.relaxedWith (durationScale C.weight) Tmax
      (oneplaneTable (scaledDurations C.weight) C.c Tmax C.s) M ≤ (planCost C.c P : WithTop ℕ) := by
  obtain ⟨Y, hpos, hsize, hload, hcost⟩ := hP.exists_relaxation_emin C.c hpt
  refine (relaxedBoundAt_le_totalCost (scaledDurations C.weight) C.c Y hpos hsize
    fun k => ?_).trans (WithTop.coe_le_coe.mpr hcost)
  apply load_scaled_le_of_load_le
  rw [C.load_weight dc]
  have := hload k
  omega

theorem load_eq_mul_of_dvd {f : Fin C.n → ℕ} {g : ℕ} (hg : ∀ i, g ∣ f i)
    (Y : Multiset (Fin C.n)) : load f Y = g * load (fun i => f i / g) Y := by
  simp only [load]
  rw [← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun i _ => (Nat.mul_div_cancel' (hg i)).symm

theorem rolesScale_dvd_d (i : Fin C.n) : C.rolesScale ∣ C.d i :=
  (durationScale_dvd _ i).trans (Nat.gcd_dvd_left _ _)

theorem rolesScale_dvd_dbar (i : Fin C.n) : C.rolesScale ∣ C.dbar i :=
  (durationScale_dvd _ i).trans (Nat.gcd_dvd_right _ _)

/-- **The `roles` bound is a lower bound** under (A1-NS): a feasible plan with makespan below `M`
costs at least the bound at the level of `M`. -/
theorem rolesWith_le {dc : Fin C.n → Fin C.n → ℕ} (hA : C.assumptions.contains "A1-NS" = true →
    (C.network dc).A1NS) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.rolesWith (fun i => C.d i / C.rolesScale) (fun i => C.dbar i / C.rolesScale) M ≤
      (planCost C.c P : WithTop ℕ) := by
  unfold rolesWith
  split_ifs with hlist
  · obtain ⟨cfg, hsize, hcost, hload⟩ := hP.exists_roleConfig_ns (hA hlist) C.c hpt
    refine (rolesBoundAt_le_totalCost _ _ C.c dc cfg hsize fun k => ?_).trans
      (WithTop.coe_le_coe.mpr hcost)
    have hg : 0 < C.rolesScale := durationScale_pos _
    have hk := hload k
    have e : cfg.roleLoad (C.network dc) k = C.rolesScale *
        cfg.roleLoad ⟨fun i => C.d i / C.rolesScale, fun i => C.dbar i / C.rolesScale, dc⟩ k := by
      unfold RoleConfig.roleLoad
      simp only [network]
      rw [C.load_eq_mul_of_dvd C.rolesScale_dvd_d, C.load_eq_mul_of_dvd C.rolesScale_dvd_dbar,
        C.load_eq_mul_of_dvd C.rolesScale_dvd_d (Y := cfg.cross k),
        C.load_eq_mul_of_dvd C.rolesScale_dvd_dbar (Y := cfg.cross k)]
      ring
    rw [Nat.le_div_iff_mul_le hg, mul_comm, ← e]
    omega
  · exact zero_le

/-- **Soundness of the v2 checker.** If `check` accepts a certificate, its points are exactly the
Pareto front of the instance, for every table `dc` of central flight durations that satisfies
(A1-NS) if the certificate lists it, and for **every** table otherwise. The `relaxed` bounds
need no assumption, the `roles` bounds (A1-NS), and `fastest closed` (S), which the checker
tests. -/
theorem check_sound (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : C.assumptions.contains "A1-NS" = true → (C.network dc).A1NS) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hhead, hmono⟩, hplans⟩, hlast⟩, hbounds⟩ := h
  rw [boundsCheck_eq, Bool.and_eq_true] at hbounds
  obtain ⟨hfast, hgaps⟩ := hbounds
  simp only [headerOK, Bool.and_eq_true, decide_eq_true_eq] at hhead
  obtain ⟨⟨⟨-, hp⟩, hpt⟩, -⟩ := hhead
  simp only [plansOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hplans
  -- Every bound named in the certificate is a lower bound.
  have hbound : ∀ g : Kind2, ∀ {P : Plan C.n C.t C.p}, Feasible (C.network dc) P →
      ∀ M, planMakespan P < M → C.bound g M ≤ (planCost C.c P : WithTop ℕ) := by
    intro g P hP M hM
    cases g with
    | relaxed => exact C.relaxedWith_le hpt _ hP hM
    | roles => exact C.rolesWith_le hA hpt hP hM
    | _ => exact bot_le
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
  · -- 1. Every point is achieved by its plan.
    obtain ⟨P, hPx⟩ := exists_mem_zip_of_mem hplans.1 hx
    obtain ⟨⟨hok, hcost⟩, hmk⟩ := hplans.2 _ hPx
    exact ⟨P, planOK_feasible dc hok, Prod.ext hcost hmk⟩
  · -- 2–4. Every feasible plan is weakly dominated.
    obtain ⟨P, hP, rfl⟩ := hy
    refine exists_le_of_gapsOK C.bound _ C.front C.gaps
      (fun g _ M hM => hbound g hP M hM) hgaps (fun x hx => ?_) (fun x hx => ?_)
    · rw [Option.mem_def] at hx
      simp only [fastestOK, hx] at hfast
      cases hk : C.fastest with
      | closed =>
        rw [hk] at hfast
        simp only [Bool.and_eq_true, decide_eq_true_eq, symmetric] at hfast
        have hS : (C.network dc).dbar = (C.network dc).d := funext fun i => (hfast.1 i).symm
        rw [hfast.2]
        exact hP.minOf_le_makespan hS C.c hp hpt
      | relaxed =>
        rw [hk] at hfast
        simp only [decide_eq_true_eq] at hfast
        by_contra hlt
        push Not at hlt
        have := hbound .relaxed hP x.2 hlt
        rw [hfast] at this
        exact absurd this (by simp)
      | roles =>
        rw [hk] at hfast
        simp only [decide_eq_true_eq] at hfast
        by_contra hlt
        push Not at hlt
        have := hbound .roles hP x.2 hlt
        rw [hfast] at this
        exact absurd this (by simp)
      | _ => rw [hk] at hfast; simp at hfast
    · simp only [lastOK] at hlast
      rw [Option.mem_def] at hx
      rw [hx] at hlast
      simp only [decide_eq_true_eq] at hlast
      rw [hlast]
      exact hP.minOf_le_cost_emin C.c hpt
  · -- The points are pairwise incomparable.
    refine (pairwise_of_strictlyMonotone hmono).imp fun {a b} hab => ⟨fun hle => ?_, fun hle => ?_⟩
    · exact absurd (Prod.le_def.mp hle).1 (not_le.mpr hab.2)
    · exact absurd (Prod.le_def.mp hle).2 (not_le.mpr hab.1)

/-- **Soundness under (A1-NS).** -/
theorem check_sound_A1NS (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : (C.network dc).A1NS) : IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound h dc fun _ => hA

/-- **Soundness without assumption**, when the certificate does not list (A1-NS). -/
theorem check_sound_of_not_A1NS (h : C.check = true)
    (hno : C.assumptions.contains "A1-NS" = false) (dc : Fin C.n → Fin C.n → ℕ) :
    IsParetoFront (achievable (C.network dc) C.c C.t C.p) C.front :=
  C.check_sound h dc fun h' => absurd (hno ▸ h') (by decide)

/-- **Soundness, minimal-elements form.** -/
theorem check_sound_minimal (h : C.check = true) (dc : Fin C.n → Fin C.n → ℕ)
    (hA : C.assumptions.contains "A1-NS" = true → (C.network dc).A1NS) (x : ℕ × ℕ) :
    x ∈ C.front ↔ Minimal (· ∈ achievable (C.network dc) C.c C.t C.p) x :=
  (C.check_sound h dc hA).mem_iff_minimal x

end Cert2

end ZenoFront
