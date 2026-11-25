/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Template
public import ZenoFront.DominationAll

/-!
# The non-symmetric front for all plans (Corollary 6.10)

**Corollary 6.10.** Under (A1-NS), with `p ≤ t`, the front of the feasible plans is the set of
minimal points `(c(S), M_tmpl(S))` over the valid scheduled configurations `S` with `2t − p`
landings: role configurations with passenger count `t`, together with orders of their drop-offs
and pick-ups and a link matching. The two halves:

* every such point is the point of a feasible plan, the template (Lemma 6.3,
  `Sched.tmplPlan_spec`);
* every feasible plan is weakly dominated by such a point (Theorem 6.9,
  `schedulableDomination_all`).

No event order and no hypothesis on zero durations is needed. Forgetting orders and matchings,
the front is also `Min 𝒦` for the note's `𝒦`, the points `(c(cfg), m(cfg))` of the role
configurations, `m(cfg)` their least makespan: every role configuration has an order and a
matching (`RoleConfig.exists_sched`), so `m(cfg)` is attained.

## Main results

* `schedPoints`: the points `(c(S), M_tmpl(S))`.
* `minimal_achievable_iff_schedPoints` (**Corollary 6.10**): the minimal achievable points are
  the minimal points of `schedPoints`.
* `isParetoFront_achievable_iff_schedPoints`: a list is the Pareto front of the feasible plans
  iff it is the Pareto front of `schedPoints`.
* `configPoints`, `RoleConfig.leastTmpl`: the note's `𝒦` and `m(cfg)`.
* `minimal_achievable_iff_configPoints` (**Corollary 6.10, as in the note**): the front is
  `Min 𝒦`.
* `schedulableDomination_template` (**Theorem 6.9, as in the note**): every feasible plan is
  weakly dominated by a scheduled configuration whose template plan is no later.
* `Feasible.exists_roleConfig_of_domination`: Theorem 6.1 in the form of
  `Feasible.exists_roleConfig_ns` (role loads at most the makespan), as a corollary of
  Theorem 6.9, since every role load is at most `M_tmpl` (`Sched.load_le_tmpl`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- If `A ⊆ A′` and every point of `A′` is weakly dominated by a point of `A`, a list is the
Pareto front of `A` iff it is the Pareto front of `A′`. -/
theorem isParetoFront_iff_of_subset_of_dominated {α : Type*} [PartialOrder α] {A A' : Set α}
    (hsub : A ⊆ A') (hdom : ∀ y ∈ A', ∃ x ∈ A, x ≤ y) (F : List α) :
    IsParetoFront A F ↔ IsParetoFront A' F := by
  constructor
  · intro h
    refine ⟨fun x hx => hsub (h.achieved x hx), fun y hy => ?_, h.antichain⟩
    obtain ⟨z, hz, hzy⟩ := hdom y hy
    obtain ⟨x, hx, hxz⟩ := h.dominates z hz
    exact ⟨x, hx, hxz.trans hzy⟩
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => h.dominates y (hsub hy), h.antichain⟩
    exact ((minimal_iff_of_subset_of_dominated hsub hdom x).mpr
      ((h.mem_iff_minimal x).mp hx)).1

/-- The note's `𝒦`, per schedule: the points `(c(S), M_tmpl(S))` of the valid scheduled
configurations with `2t − p` landings. -/
def schedPoints (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧ (S.cost c, S.tmpl N.d N.dbar) = x}

/-- Every point of `schedPoints` is the point of a feasible plan, its template (Lemma 6.3). -/
theorem schedPoints_subset_achievable (N : Network n) (c : Fin n → ℕ) :
    schedPoints N c t p ⊆ achievable N c t p := by
  rintro x ⟨S, hv, hsize, rfl⟩
  obtain ⟨hP, hc, hm⟩ := S.tmplPlan_spec (t := t) (N := N) c hv hsize
  exact ⟨_, hP, by rw [hc, hm]⟩

/-- Under (A1-NS), with `p ≤ t`, every feasible plan is weakly dominated by a point of
`schedPoints` (Theorem 6.9). -/
theorem achievable_dominated_schedPoints {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    (hpt : p ≤ t) : ∀ y ∈ achievable N c t p, ∃ x ∈ schedPoints N c t p, x ≤ y := by
  rintro y ⟨P, hP, rfl⟩
  obtain ⟨S, hv, hsize, hcost, htmpl⟩ := schedulableDomination_all c hpt hA hP
  exact ⟨_, ⟨S, hv, hsize, rfl⟩, Prod.le_def.mpr ⟨hcost, htmpl⟩⟩

/-- **Corollary 6.10 (non-symmetric front), for all plans.** Under (A1-NS), with `p ≤ t`, the
minimal (cost, makespan) points of the feasible plans are the minimal points
`(c(S), M_tmpl(S))` of the valid scheduled configurations with `2t − p` landings. -/
theorem minimal_achievable_iff_schedPoints {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ schedPoints N c t p) x :=
  (minimal_iff_of_subset_of_dominated (schedPoints_subset_achievable N c)
    (achievable_dominated_schedPoints hA c hpt) x).symm

/-- **Corollary 6.10, Pareto-front form.** Under (A1-NS), with `p ≤ t`, a list of points is the
Pareto front of the feasible plans iff it is the Pareto front of `schedPoints`. -/
theorem isParetoFront_achievable_iff_schedPoints {N : Network n} (hA : N.A1NS)
    (c : Fin n → ℕ) (hpt : p ≤ t) (F : List (ℕ × ℕ)) :
    IsParetoFront (achievable N c t p) F ↔ IsParetoFront (schedPoints N c t p) F :=
  (isParetoFront_iff_of_subset_of_dominated (schedPoints_subset_achievable N c)
    (achievable_dominated_schedPoints hA c hpt) F).symm

namespace Sched

variable {S : Sched n p}

/-! ### The role configuration of a scheduled configuration -/

theorem _root_.ZenoFront.coe_eq_sum_getElem {α : Type*} (l : List α) :
    (l : Multiset α) = ∑ j : Fin l.length, {l[j]} := by
  rw [sum_singleton_eq_map, Fin.univ_val_map]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

/-- A valid scheduled configuration has as many drop-offs as pick-ups at every city. -/
theorem Valid.sum_drops_eq (hv : S.Valid) :
    ∑ k, (S.drops k : Multiset (Fin n)) = ∑ k, (S.picks k : Multiset (Fin n)) := by
  calc ∑ k, (S.drops k : Multiset (Fin n))
      = ∑ k, ∑ j : Fin (S.drops k).length, {(S.drops k)[j]} :=
        Finset.sum_congr rfl fun k _ => coe_eq_sum_getElem _
    _ = ∑ ds : S.DSlot, {(S.drops ds.1)[ds.2]} :=
        (Fintype.sum_sigma fun ds : S.DSlot => ({(S.drops ds.1)[ds.2]} : Multiset (Fin n))).symm
    _ = ∑ ps : S.PSlot, {(S.picks ps.1)[ps.2]} :=
        (Fintype.sum_equiv (Equiv.ofBijective _ hv.slot_bijective)
          (fun ps : S.PSlot => ({(S.picks ps.1)[ps.2]} : Multiset (Fin n)))
          (fun ds : S.DSlot => ({(S.drops ds.1)[ds.2]} : Multiset (Fin n))) fun ps =>
          congrArg (fun x => ({x} : Multiset (Fin n))) (hv.mate_city ps.1 ps.2).symm).symm
    _ = ∑ k, ∑ l : Fin (S.picks k).length, {(S.picks k)[l]} :=
        Fintype.sum_sigma fun ps : S.PSlot => ({(S.picks ps.1)[ps.2]} : Multiset (Fin n))
    _ = ∑ k, (S.picks k : Multiset (Fin n)) :=
        Finset.sum_congr rfl fun k _ => (coe_eq_sum_getElem _).symm

/-- The role configuration of a valid scheduled configuration: its orders and matching
forgotten. -/
def toRoleConfig (S : Sched n p) (hv : S.Valid) : RoleConfig n p :=
  ⟨fun k => S.drops k, fun k => S.picks k, S.cross, hv.odd, hv.sum_drops_eq⟩

/-- `S` schedules the role configuration `R`: every plane has the drop-offs, pick-ups and
crossings of `R`, in some order. -/
def Schedules (S : Sched n p) (R : RoleConfig n p) : Prop :=
  ∀ k, (S.drops k : Multiset (Fin n)) = R.drop k ∧ (S.picks k : Multiset (Fin n)) = R.pick k ∧
    S.cross k = R.cross k

theorem schedules_toRoleConfig (hv : S.Valid) : S.Schedules (S.toRoleConfig hv) :=
  fun _ => ⟨rfl, rfl, rfl⟩

theorem Schedules.size_eq {R : RoleConfig n p} (h : S.Schedules R) :
    S.size = ZenoFront.size R.groups := by
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨h₁, h₂, h₃⟩ := h k
  rw [R.card_groups, ← h₁, ← h₂, ← h₃, Multiset.coe_card, Multiset.coe_card]

theorem Schedules.cost_eq {R : RoleConfig n p} (h : S.Schedules R) (c : Fin n → ℕ) :
    S.cost c = totalCost c R.groups := by
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨h₁, h₂, h₃⟩ := h k
  simp only [RoleConfig.groups, ← h₁, ← h₂, ← h₃, ZenoFront.cost, Multiset.map_add,
    Multiset.sum_add, Multiset.map_coe, Multiset.sum_coe]

theorem Schedules.load_eq {R : RoleConfig n p} (h : S.Schedules R) (N : Network n) (k : Fin p) :
    S.load N.d N.dbar k = R.roleLoad N k := by
  obtain ⟨h₁, h₂, h₃⟩ := h k
  simp only [load, RoleConfig.roleLoad, ← h₁, ← h₂, ← h₃, ZenoFront.load, Multiset.map_coe,
    Multiset.sum_coe]

end Sched

/-! ### Every role configuration can be scheduled -/

theorem card_fiber_eq_count {ι α : Type*} [Fintype ι] [DecidableEq α] (f : ι → α) (x : α) :
    Fintype.card {a // f a = x} = Multiset.count x (∑ a, {f a}) := by
  rw [Fintype.card_subtype, Finset.card_filter, Multiset.count_sum']
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Multiset.count_singleton]
  by_cases h : f a = x
  · simp [h]
  · simp [h, Ne.symm h]

theorem sigma_fin_ext {m : ℕ} {f : Fin m → ℕ} {x y : (k : Fin m) × Fin (f k)} (h₁ : x.1 = y.1)
    (h₂ : (x.2 : ℕ) = y.2) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  dsimp only at h₁ h₂
  subst h₁
  exact congrArg _ (Fin.ext h₂)

/-- Every role configuration has orders of its drop-offs and pick-ups and a link matching: it is
scheduled by a valid scheduled configuration. -/
theorem RoleConfig.exists_sched (R : RoleConfig n p) :
    ∃ S : Sched n p, S.Valid ∧ S.Schedules R := by
  classical
  let dr : Fin p → List (Fin n) := fun k => (R.drop k).toList
  let pk : Fin p → List (Fin n) := fun k => (R.pick k).toList
  let cD : ((k : Fin p) × Fin (dr k).length) → Fin n := fun ds => (dr ds.1)[ds.2]
  let cP : ((k : Fin p) × Fin (pk k).length) → Fin n := fun ps => (pk ps.1)[ps.2]
  have hD : ∑ ds, ({cD ds} : Multiset (Fin n)) = ∑ k, R.drop k := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← coe_eq_sum_getElem]
    exact Multiset.coe_toList _
  have hP : ∑ ps, ({cP ps} : Multiset (Fin n)) = ∑ k, R.pick k := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← coe_eq_sum_getElem]
    exact Multiset.coe_toList _
  have hfib : ∀ x, Fintype.card {ps // cP ps = x} = Fintype.card {ds // cD ds = x} := fun x => by
    rw [card_fiber_eq_count, card_fiber_eq_count, hD, hP, R.sum_drop_eq_sum_pick]
  let eqv : ((k : Fin p) × Fin (pk k).length) ≃ ((k : Fin p) × Fin (dr k).length) :=
    Equiv.ofFiberEquiv fun x => Fintype.equivOfCardEq (hfib x)
  have heqv : ∀ ps, cD (eqv ps) = cP ps := Equiv.ofFiberEquiv_map _
  let mate : Fin p → ℕ → Fin p × ℕ := fun v l =>
    if h : l < (pk v).length then ((eqv ⟨v, ⟨l, h⟩⟩).1, (eqv ⟨v, ⟨l, h⟩⟩).2) else (v, 0)
  refine ⟨⟨dr, pk, R.cross, mate⟩,
    ⟨R.odd_card_cross, fun v l hl => ?_, fun v l v' l' hl hl' h => ?_, ?_⟩,
    fun k => ⟨Multiset.coe_toList _, Multiset.coe_toList _, rfl⟩⟩
  · simp only [mate, hl, ↓reduceDIte]
    rw [List.getElem?_eq_getElem (eqv ⟨v, ⟨l, hl⟩⟩).2.isLt, List.getElem?_eq_getElem hl]
    exact congrArg some (heqv ⟨v, ⟨l, hl⟩⟩)
  · simp only [mate, hl, hl', ↓reduceDIte, Prod.mk.injEq] at h
    have h' := eqv.injective (sigma_fin_ext h.1 h.2)
    exact ⟨congrArg Sigma.fst h',
      congrArg (fun s : (k : Fin p) × Fin (pk k).length => (s.2 : ℕ)) h'⟩
  · have h := congrArg Multiset.card R.sum_drop_eq_sum_pick
    simp only [Multiset.card_sum] at h
    simpa [dr, pk, Multiset.length_toList] using h


/-! ### Role configurations and their least makespans -/

/-- The least makespan `m(cfg)` of a role configuration (§6.2 of the note): the least `M_tmpl`
over the orders of its drop-offs and pick-ups and its link matchings. There is at least one
(`RoleConfig.exists_sched`), and the least one is attained (`RoleConfig.exists_leastTmpl`). -/
noncomputable def RoleConfig.leastTmpl (N : Network n) (R : RoleConfig n p) : ℕ :=
  sInf {m | ∃ S : Sched n p, S.Valid ∧ S.Schedules R ∧ S.tmpl N.d N.dbar = m}

theorem RoleConfig.exists_leastTmpl (N : Network n) (R : RoleConfig n p) :
    ∃ S : Sched n p, S.Valid ∧ S.Schedules R ∧ S.tmpl N.d N.dbar = R.leastTmpl N := by
  obtain ⟨S, hv, hS⟩ := R.exists_sched
  exact Nat.sInf_mem (s := {m | ∃ S : Sched n p, S.Valid ∧ S.Schedules R ∧
    S.tmpl N.d N.dbar = m}) ⟨_, S, hv, hS, rfl⟩

theorem RoleConfig.leastTmpl_le (N : Network n) {R : RoleConfig n p} {S : Sched n p}
    (hv : S.Valid) (hS : S.Schedules R) : R.leastTmpl N ≤ S.tmpl N.d N.dbar :=
  Nat.sInf_le ⟨S, hv, hS, rfl⟩

/-- The note's `𝒦`: the points `(c(cfg), m(cfg))` of the role configurations on the `p` planes
with `2t − p` landings (passenger count `t`). -/
def configPoints (N : Network n) (c : Fin n → ℕ) (t p : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ R : RoleConfig n p, size R.groups = 2 * t - p ∧ (totalCost c R.groups, R.leastTmpl N) = x}

/-- `𝒦` and the points of the scheduled configurations have the same minimal points: a role
configuration's point is the point of a schedule reaching `m(cfg)`, and a schedule's point is
weakly dominated by its configuration's point. -/
theorem minimal_schedPoints_iff_configPoints (N : Network n) (c : Fin n → ℕ) (x : ℕ × ℕ) :
    Minimal (· ∈ schedPoints N c t p) x ↔ Minimal (· ∈ configPoints N c t p) x := by
  refine minimal_iff_of_dominated (fun y hy => ?_) (fun y hy => ?_) x
  · obtain ⟨S, hv, hsize, rfl⟩ := hy
    have hS := Sched.schedules_toRoleConfig hv
    refine ⟨_, ⟨S.toRoleConfig hv, by rw [← hS.size_eq, hsize], rfl⟩,
      Prod.le_def.mpr ⟨(hS.cost_eq c).ge, RoleConfig.leastTmpl_le N hv hS⟩⟩
  · obtain ⟨R, hsize, rfl⟩ := hy
    obtain ⟨S, hv, hS, hm⟩ := R.exists_leastTmpl N
    exact ⟨_, ⟨S, hv, by rw [hS.size_eq, hsize], rfl⟩,
      Prod.le_def.mpr ⟨(hS.cost_eq c).le, hm.le⟩⟩

/-- **Corollary 6.10 (non-symmetric front), as in the note.** Under (A1-NS), with `p ≤ t`, the
front of the feasible plans is `Min 𝒦`, with `𝒦` the points `(c(cfg), m(cfg))` of the role
configurations on the `p` planes with passenger count `t`, `m(cfg)` the least `M_tmpl` over
their orders and link matchings. -/
theorem minimal_achievable_iff_configPoints {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    (hpt : p ≤ t) (x : ℕ × ℕ) :
    Minimal (· ∈ achievable N c t p) x ↔ Minimal (· ∈ configPoints N c t p) x :=
  (minimal_achievable_iff_schedPoints hA c hpt x).trans (minimal_schedPoints_iff_configPoints N c x)

/-! ### Theorem 6.1 from Theorem 6.9 -/

/-- Every role load is at most the closed form. -/
theorem Sched.load_le_tmpl (S : Sched n p) (d db : Fin n → ℕ) (k : Fin p) :
    S.load d db k ≤ S.tmpl d db :=
  (Finset.le_sup (f := fun k => S.load d db k) (Finset.mem_univ k)).trans (le_max_left _ _)

/-- **Theorem 6.1 as a corollary of Theorem 6.9.** Under (A1-NS), with `p ≤ t`, every feasible
plan gives a role configuration on the `p` planes with `2t − p` landings, cost at most the
plan's, and every role load at most the makespan: the role configuration of the scheduled
configuration of `schedulableDomination_all`, whose role loads are at most its closed form.
This is the statement of `Feasible.exists_roleConfig_ns`. -/
theorem Feasible.exists_roleConfig_of_domination {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ cfg : RoleConfig n p, size cfg.groups = 2 * t - p ∧
      totalCost c cfg.groups ≤ planCost c P ∧ ∀ k, cfg.roleLoad N k ≤ planMakespan P := by
  obtain ⟨S, hv, hsize, hcost, htmpl⟩ := schedulableDomination_all c hpt hA hP
  have hS := Sched.schedules_toRoleConfig hv
  refine ⟨S.toRoleConfig hv, by rw [← hS.size_eq, hsize], by rw [← hS.cost_eq c]; exact hcost,
    fun k => ?_⟩
  rw [← hS.load_eq N k]
  exact (S.load_le_tmpl N.d N.dbar k).trans htmpl

/-! ### Theorem 6.9 with the template plan -/

/-- **Theorem 6.9 (schedulable domination), as in the note.** Under (A1-NS), with `p ≤ t`, every
feasible plan is weakly dominated by a valid scheduled configuration with `2t − p` landings
(a role configuration with passenger count `t`, orders of its drop-offs and pick-ups and a link
matching) of cost at most the plan's, whose template is a feasible plan of the same cost and of
makespan at most the plan's: `schedulableDomination_all` bounds the closed form by the
makespan, and the template's makespan is the closed form (Lemma 6.3). -/
theorem schedulableDomination_template {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    (hpt : p ≤ t) {P : Plan n t p} (hP : Feasible N P) :
    ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧ S.cost c ≤ planCost c P ∧
      Feasible N (S.tmplPlan (t := t) N.d N.dbar) ∧
      planCost c (S.tmplPlan (t := t) N.d N.dbar) = S.cost c ∧
      planMakespan (S.tmplPlan (t := t) N.d N.dbar) ≤ planMakespan P := by
  obtain ⟨S, hv, hsize, hcost, htmpl⟩ := schedulableDomination_all c hpt hA hP
  obtain ⟨hT, hc, hm⟩ := S.tmplPlan_spec (t := t) (N := N) c hv hsize
  exact ⟨S, hv, hsize, hcost, hT, hc, hm ▸ htmpl⟩

end ZenoFront
