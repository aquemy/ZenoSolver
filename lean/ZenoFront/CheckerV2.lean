/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Checker
public import ZenoFront.BalancedBound
public import ZenoFront.SearchGap

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
* `lagrangian μ` gaps, under (A1-NS): the decoupled per-plane bound at the listed multipliers
  (`LagData.value_le_totalCost`), over the representatives of the cities (`domRep3`);
* `balanced` (gaps and fastest point), under (A1-NS): the exact program over balanced role
  configurations (`BalData.value_le_totalCost`), rerun at the gap's level;
* `fastest closed` for symmetric durations, as in v1.

The other v2 kinds (`search`, `forest`) are parsed but given no bound, so a certificate that uses
one is rejected.

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

/-- The representatives of the cities (`domRep3`): among the cities the C++ reduction keeps. -/
def reps3 : List (Fin C.n) := repList3 C.d C.dbar C.c

/-- The scale of the role bounds: the gcd of the durations `d` and `d̄` of the representatives,
as in the C++ checker. -/
def rolesScale : ℕ :=
  durationScale fun i => if i ∈ C.reps3 then Nat.gcd (C.d i) (C.dbar i) else 0

/-- A weight above every budget of the role tables, for the cities that are not
representatives: they never fit. -/
def bigW : ℕ := C.p * C.maxLevel C.rolesScale + 1

/-- The scaled `d` of a representative, `bigW` for the other cities. -/
def dR (i : Fin C.n) : ℕ := if i ∈ C.reps3 then C.d i / C.rolesScale else C.bigW

/-- The scaled `d̄` of a representative, `bigW` for the other cities. -/
def dbR (i : Fin C.n) : ℕ := if i ∈ C.reps3 then C.dbar i / C.rolesScale else C.bigW

/-- The `roles` bound below a point of makespan `M`, on durations scaled by `g = rolesScale`
(`dR`, `dbR`), at level `⌊(M − 1)/g⌋`; `0` (no bound) unless assumption `A1-NS` is listed. -/
def rolesWith (dR dbR : Fin C.n → ℕ) : ℕ → WithTop ℕ :=
  if C.assumptions.contains "A1-NS" then
    let TmaxR := C.maxLevel C.rolesScale
    let L := roleLayers dR dbR C.c TmaxR C.s
    let F := oneplaneTable (fillW dR dbR) C.c (C.p * TmaxR) C.s
    fun M => rolesBoundAt C.p C.s TmaxR L F ((M - 1) / C.rolesScale)
  else fun _ => 0

/-- The Lagrangian data at the level of `M`, on scaled durations `dR`, `dbR`, for multipliers
`mu` (one per city). -/
def lagData (dR dbR : Fin C.n → ℕ) (mu : List ℤ) (M : ℕ) : LagData C.n :=
  ⟨fillW dR dbR, fun i => 2 * dR i, fun i => 2 * dbR i, C.c, fun i => mu.getD i 0,
    repList3 C.d C.dbar C.c, (M - 1) / C.rolesScale⟩

/-- The `lagrangian` bound below a point of makespan `M`; `0` (no bound) unless assumption
`A1-NS` is listed. -/
def lagWith (dR dbR : Fin C.n → ℕ) (mu : List ℤ) (M : ℕ) : WithTop ℕ :=
  if C.assumptions.contains "A1-NS" then toNatTop ((C.lagData dR dbR mu M).value C.p C.s)
  else 0

/-- The `balanced` program at the level of `M`, on scaled durations `dR`, `dbR`, with the crossing
table `F` (columns `0, …, p · TmaxR`). -/
def balData (dR dbR : Fin C.n → ℕ) (F : Array (Array (WithTop ℕ))) (M : ℕ) : BalData C.n :=
  ⟨fun i => 2 * dR i, fun i => 2 * dbR i, C.c, fun r τ => (F.getD r #[]).getD τ ⊤,
    (M - 1) / C.rolesScale, C.t - C.p, C.s⟩

/-- The `balanced` bound below a point of makespan `M`; `0` (no bound) unless assumption `A1-NS`
is listed, or above the highest level. -/
def balWith (dR dbR : Fin C.n → ℕ) : ℕ → WithTop ℕ :=
  if C.assumptions.contains "A1-NS" then
    let TmaxR := C.maxLevel C.rolesScale
    let F := oneplaneTable (fillW dR dbR) C.c (C.p * TmaxR) C.s
    fun M => if (M - 1) / C.rolesScale ≤ TmaxR then (C.balData dR dbR F M).value C.p else 0
  else fun _ => 0

/-- The exhaustive search of a `search` gap (or of `fastest search`, with no cost bound) below a
point of makespan `M`, on the representatives' scaled durations. `SearchData.closed_sound`
proves its enumeration complete; the checker does not use it until Theorem 6.9
(`SchedulableDomination`) is proved, so `search` gaps are still rejected. -/
def searchData (cost : WithTop ℕ) (M : ℕ) : SearchData C.n :=
  ⟨C.dR, C.dbR, C.c, C.p, C.s, (M - 1) / C.rolesScale, cost⟩

/-- The bound named by a kind; `0` (no bound) for the kinds this checker does not verify. -/
def boundWith (scale Tmax : ℕ) (table : Array (Array (WithTop ℕ))) (rolesB : ℕ → WithTop ℕ)
    (lagB : List ℤ → ℕ → WithTop ℕ) (balB : ℕ → WithTop ℕ) : Kind2 → ℕ → WithTop ℕ
  | .relaxed => C.relaxedWith scale Tmax table
  | .roles => rolesB
  | .lagrangian mu => lagB mu
  | .balanced => balB
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
    | .balanced => decide (bound .balanced x.2 = ⊤)
    | _ => false

/-- Obligations 2 and 3, with the scale, the top level and the one-plane table computed once. -/
def boundsCheck : Bool :=
  let scale := durationScale C.weight
  let Tmax := C.maxLevel scale
  let wArr := Array.ofFn (n := C.n) fun i => C.weight i / scale
  let wS : Fin C.n → ℕ := fun i => wArr.getD i 0
  let dArr := Array.ofFn (n := C.n) C.dR
  let dbArr := Array.ofFn (n := C.n) C.dbR
  let bound := C.boundWith scale Tmax (oneplaneTable wS C.c Tmax C.s)
    (C.rolesWith (fun i => dArr.getD i 0) (fun i => dbArr.getD i 0))
    (C.lagWith (fun i => dArr.getD i 0) (fun i => dbArr.getD i 0))
    (C.balWith (fun i => dArr.getD i 0) (fun i => dbArr.getD i 0))
  C.fastestOK bound && gapsOK bound C.front C.gaps

/-- The bounds of the checker, as specified. -/
def bound : Kind2 → ℕ → WithTop ℕ :=
  C.boundWith (durationScale C.weight) (C.maxLevel (durationScale C.weight))
    (oneplaneTable (scaledDurations C.weight) C.c (C.maxLevel (durationScale C.weight)) C.s)
    (C.rolesWith C.dR C.dbR) (C.lagWith C.dR C.dbR) (C.balWith C.dR C.dbR)

theorem boundsCheck_eq : C.boundsCheck = (C.fastestOK C.bound && gapsOK C.bound C.front C.gaps) := by
  have hwS : (fun i : Fin C.n => (Array.ofFn (n := C.n) fun i =>
      C.weight i / durationScale C.weight).getD i 0) = scaledDurations C.weight := by
    funext i
    simp [Array.getD_eq_getD_getElem?, scaledDurations]
  have hd : (fun i : Fin C.n => (Array.ofFn (n := C.n) C.dR).getD i 0) = C.dR := by
    funext i
    simp [Array.getD_eq_getD_getElem?]
  have hdb : (fun i : Fin C.n => (Array.ofFn (n := C.n) C.dbR).getD i 0) = C.dbR := by
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

theorem load_eq_mul_of_mem {f f' : Fin C.n → ℕ} {g : ℕ} {Y : Multiset (Fin C.n)}
    (h : ∀ i ∈ Y, f i = g * f' i) : load f Y = g * load f' Y := by
  simp only [load]
  rw [← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl h

theorem rolesScale_pos : 0 < C.rolesScale := durationScale_pos _

theorem rolesScale_dvd_gcd {i : Fin C.n} (hi : i ∈ C.reps3) :
    C.rolesScale ∣ Nat.gcd (C.d i) (C.dbar i) := by
  have := durationScale_dvd (fun i => if i ∈ C.reps3 then Nat.gcd (C.d i) (C.dbar i) else 0) i
  simp only [hi, ite_true] at this
  exact this

theorem d_eq_mul {i : Fin C.n} (hi : i ∈ C.reps3) : C.d i = C.rolesScale * C.dR i := by
  rw [dR, ite_eq_left hi, Nat.mul_div_cancel' ((C.rolesScale_dvd_gcd hi).trans (Nat.gcd_dvd_left _ _))]

theorem dbar_eq_mul {i : Fin C.n} (hi : i ∈ C.reps3) : C.dbar i = C.rolesScale * C.dbR i := by
  rw [dbR, ite_eq_left hi,
    Nat.mul_div_cancel' ((C.rolesScale_dvd_gcd hi).trans (Nat.gcd_dvd_right _ _))]

/-- The role load in units of `rolesScale`, for a configuration on representatives. -/
theorem roleLoad_scaled {dc : Fin C.n → Fin C.n → ℕ} (cfg : RoleConfig C.n C.p)
    (hcfg : ∀ k, ∀ i ∈ cfg.groups k, i ∈ C.reps3) (k : Fin C.p) :
    cfg.roleLoad (C.network dc) k = C.rolesScale * cfg.roleLoad ⟨C.dR, C.dbR, dc⟩ k := by
  have hmem : ∀ i ∈ cfg.drop k + cfg.pick k + cfg.cross k, i ∈ C.reps3 := hcfg k
  unfold RoleConfig.roleLoad
  simp only [network]
  rw [C.load_eq_mul_of_mem (f' := C.dR) (g := C.rolesScale) (Y := cfg.drop k)
      fun i hi => C.d_eq_mul (hmem i (by simp [hi])),
    C.load_eq_mul_of_mem (f' := C.dbR) (g := C.rolesScale) (Y := cfg.pick k)
      fun i hi => C.dbar_eq_mul (hmem i (by simp [hi])),
    C.load_eq_mul_of_mem (f' := C.dR) (g := C.rolesScale) (Y := cfg.cross k)
      fun i hi => C.d_eq_mul (hmem i (by simp [hi])),
    C.load_eq_mul_of_mem (f' := C.dbR) (g := C.rolesScale) (Y := cfg.cross k)
      fun i hi => C.dbar_eq_mul (hmem i (by simp [hi]))]
  ring

/-- Theorem 6.1, then the configuration mapped to representatives, with role loads in units of
`rolesScale` at most the level of `M`. -/
theorem exists_repConfig {dc : Fin C.n → Fin C.n → ℕ} (hA : (C.network dc).A1NS)
    (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p} (hP : Feasible (C.network dc) P) {M : ℕ}
    (hM : planMakespan P < M) :
    ∃ cfg : RoleConfig C.n C.p, size cfg.groups = C.s ∧
      totalCost C.c cfg.groups ≤ planCost C.c P ∧
      (∀ k, ∀ i ∈ cfg.groups k, i ∈ C.reps3) ∧
      ∀ k, cfg.roleLoad ⟨C.dR, C.dbR, dc⟩ k ≤ (M - 1) / C.rolesScale := by
  obtain ⟨cfg, hsize, hcost, hload⟩ := hP.exists_roleConfig_ns hA C.c hpt
  have hrep := domRep3_le C.d C.dbar C.c
  have hcfg : ∀ k, ∀ i ∈ (cfg.map (domRep3 C.d C.dbar C.c)).groups k, i ∈ C.reps3 :=
    fun k i hi => by
      obtain ⟨j, rfl⟩ := cfg.mem_map_groups _ hi
      exact domRep3_mem C.d C.dbar C.c j
  refine ⟨cfg.map (domRep3 C.d C.dbar C.c), by rw [RoleConfig.size_map, hsize]; rfl,
    (cfg.totalCost_map_le C.c fun i => (hrep i).2.2).trans hcost, hcfg, fun k => ?_⟩
  have h₁ := cfg.roleLoad_map_le (C.network dc) (rep := domRep3 C.d C.dbar C.c)
    (fun i => (hrep i).1) (fun i => (hrep i).2.1) k
  have e := C.roleLoad_scaled (dc := dc) _ hcfg k
  rw [Nat.le_div_iff_mul_le C.rolesScale_pos, mul_comm]
  have := hload k
  omega

/-- **The `roles` bound is a lower bound** under (A1-NS): a feasible plan with makespan below `M`
costs at least the bound at the level of `M`. -/
theorem rolesWith_le {dc : Fin C.n → Fin C.n → ℕ} (hA : C.assumptions.contains "A1-NS" = true →
    (C.network dc).A1NS) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.rolesWith C.dR C.dbR M ≤ (planCost C.c P : WithTop ℕ) := by
  unfold rolesWith
  split_ifs with hlist
  · obtain ⟨cfg, hsize, hcost, -, hload⟩ := C.exists_repConfig (hA hlist) hpt hP hM
    exact (rolesBoundAt_le_totalCost _ _ C.c dc cfg hsize hload).trans
      (WithTop.coe_le_coe.mpr hcost)
  · exact zero_le

/-- **The `lagrangian` bound is a lower bound** under (A1-NS), for every multiplier. -/
theorem lagWith_le {dc : Fin C.n → Fin C.n → ℕ} (hA : C.assumptions.contains "A1-NS" = true →
    (C.network dc).A1NS) (hpt : C.p ≤ C.t) (mu : List ℤ) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.lagWith C.dR C.dbR mu M ≤ (planCost C.c P : WithTop ℕ) := by
  unfold lagWith
  split_ifs with hlist
  · obtain ⟨cfg, hsize, hcost, hcfg, hload⟩ := C.exists_repConfig (hA hlist) hpt hP hM
    have hv := (C.lagData C.dR C.dbR mu M).value_le_totalCost cfg (fun k i hi => hcfg k i hi)
      (fun k => by
        have := hload k
        simp only [lagData, RoleConfig.roleLoad] at this ⊢
        have e₀ : load (fillW C.dR C.dbR) (cfg.cross k) =
            load C.dR (cfg.cross k) + load C.dbR (cfg.cross k) := load_add_fun _ _ _
        have e₁ : load (fun i => 2 * C.dR i) (cfg.drop k) = 2 * load C.dR (cfg.drop k) := by
          simp only [load]; rw [Multiset.sum_map_mul_left]
        have e₂ : load (fun i => 2 * C.dbR i) (cfg.pick k) = 2 * load C.dbR (cfg.pick k) := by
          simp only [load]; rw [Multiset.sum_map_mul_left]
        omega)
    rw [hsize] at hv
    exact (toNatTop_le hv).trans (WithTop.coe_le_coe.mpr hcost)
  · exact zero_le

/-- **The `balanced` bound is a lower bound** under (A1-NS). -/
theorem balWith_le {dc : Fin C.n → Fin C.n → ℕ} (hA : C.assumptions.contains "A1-NS" = true →
    (C.network dc).A1NS) (hp : 1 ≤ C.p) (hpt : C.p ≤ C.t) {P : Plan C.n C.t C.p}
    (hP : Feasible (C.network dc) P) {M : ℕ} (hM : planMakespan P < M) :
    C.balWith C.dR C.dbR M ≤ (planCost C.c P : WithTop ℕ) := by
  unfold balWith
  split_ifs with hlist
  · dsimp only
    split_ifs with hT
    · obtain ⟨cfg, hsize, hcost, -, hload⟩ := C.exists_repConfig (hA hlist) hpt hP hM
      have hTmax : C.maxLevel C.rolesScale ≤ C.p * C.maxLevel C.rolesScale :=
        Nat.le_mul_of_pos_left _ hp
      refine ((C.balData C.dR C.dbR _ M).value_le_totalCost C.dR C.dbR dc rfl rfl
        (by simp only [balData, s]; omega) (fun r τ Y hY hr hτ hYl => ?_) cfg hsize hload).trans
        (WithTop.coe_le_coe.mpr hcost)
      simp only [balData] at hr hτ ⊢
      rw [oneplaneTable_getD (fillW C.dR C.dbR) C.c hr (by omega)]
      exact oneplane_le_cost hY hYl
    · exact zero_le
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
    | lagrangian mu => exact C.lagWith_le hA hpt mu hP hM
    | balanced => exact C.balWith_le hA hp hpt hP hM
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
      | balanced =>
        rw [hk] at hfast
        simp only [decide_eq_true_eq] at hfast
        by_contra hlt
        push Not at hlt
        have := hbound .balanced hP x.2 hlt
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
