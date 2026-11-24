/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Plan
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Lower bounds on every feasible plan

This file proves the lower bounds behind certificate obligations 2, 3 (`relaxed` gaps) and 4,
for **every** feasible plan, whatever the central flights (`dc` is arbitrary), under symmetric
durations (S), `d̄ = d`.

* **Counting** (Lemma 3.2 of the note, leg-counting proof). Along a plane's route from `C_I` to
  `C_G`, `#departures from C_I + #arrivals at C_G = #hub arrivals + 1`. Every passenger leaves
  `C_I` on a leg and reaches `C_G` on a leg, and a leg carries one passenger, so summed over the
  planes, `#hub arrivals ≥ 2t − p = s`.
* **Segments.** Cut a route at its hub arrivals: each piece (segment) lands at least once, and
  it lasts at least `e_a + e_b ≥ 2 min(e_a, e_b)`, `a` and `b` being its first and last landings
  and `e = min(d, d̄)` (`Network.emin`): its first and last flights are hub flights. Keeping one
  landing per segment (the one with the smaller `e`) gives a multiset `Z_k` per plane with
  `|Z_k| = #segments`, `2 e(Z_k) ≤` flight time `≤` makespan, and `c(Z_k) ≤` the plane's
  landing cost. Under (S), `e = d`.
* **Lemma R** (`Feasible.exists_relaxation`). Trimming the `Z_k` gives `p` non-empty groups of
  total size exactly `s`, with `2 δ(Y_k) ≤ M` and `Σ c(Y_k) ≤ C`.

## Main results

* `ZenoFront.ciDepartures_add_cgArrivals`: the counting identity along a route.
* `ZenoFront.Feasible.le_sum_hubArrivals`: `2t ≤ Σ_k #hub arrivals_k + p`.
* `ZenoFront.PlaneFeasible.exists_segments`: one landing per segment.
* `ZenoFront.exists_trim`: trimming groups to a given total size.
* `ZenoFront.Feasible.exists_relaxation_emin`: **Lemma R**, for any durations (the weight of a
  landing is `2 min(d, d̄)`).
* `ZenoFront.Feasible.exists_relaxation`: **Lemma R** under (S).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Counting -/

/-- Number of legs arriving at a hub: the number of segments of a route. -/
def hubArrivals (legs : List (Leg n t)) : ℕ := legs.countP fun ℓ => ℓ.dst.isHub

/-- Number of legs leaving `C_I`. -/
def ciDepartures (legs : List (Leg n t)) : ℕ := legs.countP fun ℓ => ℓ.src.isCI

/-- Number of legs arriving at `C_G`. -/
def cgArrivals (legs : List (Leg n t)) : ℕ := legs.countP fun ℓ => ℓ.dst.isCG

/-- The counting identity along a route from `x`:
`#departures from C_I + #arrivals at C_G + [ends at C_I] = #hub arrivals + [starts at C_I]`
(`Bool.toNat` is the indicator). -/
theorem ciDepartures_add_cgArrivals : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ),
    IsRoute x τ legs →
    ciDepartures legs + cgArrivals legs + (finalLoc x legs).isCI.toNat =
      hubArrivals legs + x.isCI.toNat
  | [], x, τ, _ => by simp [ciDepartures, cgArrivals, hubArrivals]
  | ⟨src, dst, dep, arr, pax⟩ :: rest, x, τ, h => by
    obtain ⟨hsrc, -, hrest⟩ := h
    have ih := ciDepartures_add_cgArrivals rest dst arr hrest
    simp only [ciDepartures, cgArrivals, hubArrivals, List.countP_cons, finalLoc_cons] at ih ⊢
    subst hsrc
    cases src <;> cases dst <;> simp at ih ⊢ <;> omega

/-- For a plane: `#departures from C_I + #arrivals at C_G = #hub arrivals + 1`. -/
theorem PlaneFeasible.ciDepartures_add_cgArrivals {N : Network n} {legs : List (Leg n t)}
    (h : PlaneFeasible N legs) :
    ciDepartures legs + cgArrivals legs = hubArrivals legs + 1 := by
  have := ZenoFront.ciDepartures_add_cgArrivals legs .ci 0 h.route
  simpa [h.ends] using this

theorem isRoute_ne_nil_of_finalLoc_ne {x y : Loc n} {l : List (Leg n t)}
    (h : finalLoc x l = y) (hxy : x ≠ y) : l ≠ [] := by
  rintro rfl
  exact hxy h

theorem exists_mem_src_of_isRoute {x : Loc n} {τ : ℕ} {l : List (Leg n t)}
    (h : IsRoute x τ l) (hne : l ≠ []) : ∃ ℓ ∈ l, ℓ.src = x := by
  cases l with
  | nil => exact absurd rfl hne
  | cons ℓ rest => exact ⟨ℓ, List.mem_cons_self, h.1⟩

theorem exists_mem_dst_finalLoc : ∀ (x : Loc n) (l : List (Leg n t)), l ≠ [] →
    ∃ ℓ ∈ l, ℓ.dst = finalLoc x l
  | _, [], hne => absurd rfl hne
  | _, [ℓ], _ => ⟨ℓ, List.mem_cons_self, rfl⟩
  | _, ℓ :: ℓ' :: rest, _ => by
    obtain ⟨m, hm, hdst⟩ := exists_mem_dst_finalLoc ℓ.dst (ℓ' :: rest) (List.cons_ne_nil _ _)
    exact ⟨m, List.mem_cons_of_mem _ hm, hdst⟩

theorem countP_allLegs (P : Plan n t p) (q : Leg n t → Bool) :
    (allLegs P).countP q = ∑ k, (P k).countP q := by
  rw [allLegs, List.countP_flatMap, Fin.sum_univ_def]
  rfl

theorem mem_allLegs_of_mem_paxLegs {P : Plan n t p} {π : Fin t} {ℓ : Leg n t}
    (h : ℓ ∈ paxLegs P π) : ℓ ∈ allLegs P ∧ ℓ.pax = some π := by
  simpa [paxLegs] using h

/-- `t` distinct legs, all in `l` and satisfying `q`, give `t ≤ #{ℓ ∈ l | q ℓ}`. -/
private theorem le_countP_of_injective (l : List (Leg n t)) (q : Leg n t → Bool)
    (f : Fin t → Leg n t) (hf : Function.Injective f) (hmem : ∀ π, f π ∈ l)
    (hq : ∀ π, q (f π) = true) : t ≤ l.countP q := by
  classical
  calc t = (univ.image f).card := by rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
    _ ≤ (l.filter q).toFinset.card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨π, -, rfl⟩ := mem_image.mp hx
        simpa [List.mem_toFinset, List.mem_filter] using ⟨hmem π, hq π⟩
    _ ≤ (l.filter q).length := List.toFinset_card_le _
    _ = l.countP q := List.countP_eq_length_filter.symm

/-- Every passenger leaves `C_I` on its own leg: `t ≤ #departures from C_I`. -/
theorem Feasible.le_ciDepartures {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    t ≤ ciDepartures (allLegs P) := by
  choose route hperm hroute hfin using hP.pax
  have hne : ∀ π, route π ≠ [] := fun π => isRoute_ne_nil_of_finalLoc_ne (hfin π) (by simp)
  choose f hfmem hfsrc using fun π => exists_mem_src_of_isRoute (hroute π) (hne π)
  have hpax : ∀ π, f π ∈ allLegs P ∧ (f π).pax = some π := fun π =>
    mem_allLegs_of_mem_paxLegs ((hperm π).mem_iff.mp (hfmem π))
  refine le_countP_of_injective _ _ f (fun π π' h => ?_) (fun π => (hpax π).1) (fun π => ?_)
  · have := (hpax π).2
    rw [h, (hpax π').2] at this
    exact (Option.some_injective _ this).symm
  · simp [hfsrc π]

/-- Every passenger reaches `C_G` on its own leg: `t ≤ #arrivals at C_G`. -/
theorem Feasible.le_cgArrivals {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    t ≤ cgArrivals (allLegs P) := by
  choose route hperm hroute hfin using hP.pax
  have hne : ∀ π, route π ≠ [] := fun π => isRoute_ne_nil_of_finalLoc_ne (hfin π) (by simp)
  choose f hfmem hfdst using fun π => exists_mem_dst_finalLoc .ci (route π) (hne π)
  have hpax : ∀ π, f π ∈ allLegs P ∧ (f π).pax = some π := fun π =>
    mem_allLegs_of_mem_paxLegs ((hperm π).mem_iff.mp (hfmem π))
  refine le_countP_of_injective _ _ f (fun π π' h => ?_) (fun π => (hpax π).1) (fun π => ?_)
  · have := (hpax π).2
    rw [h, (hpax π').2] at this
    exact (Option.some_injective _ this).symm
  · simp [hfdst π, hfin π]

/-- **Counting.** A feasible plan has at least `2t − p` segments: `2t ≤ Σ_k #hub arrivals + p`. -/
theorem Feasible.le_sum_hubArrivals {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    2 * t ≤ ∑ k, hubArrivals (P k) + p := by
  have h₁ := hP.le_ciDepartures
  have h₂ := hP.le_cgArrivals
  rw [ciDepartures, countP_allLegs] at h₁
  rw [cgArrivals, countP_allLegs] at h₂
  have h₃ : ∑ k, ((P k).countP (fun ℓ => ℓ.src.isCI) + (P k).countP (fun ℓ => ℓ.dst.isCG)) =
      ∑ k, (hubArrivals (P k) + 1) :=
    Finset.sum_congr rfl fun k _ => (hP.planes k).ciDepartures_add_cgArrivals
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h₃
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h₃
  omega

/-! ### Segments -/

/-- Total flight time of a list of legs. -/
def durSum (legs : List (Leg n t)) : ℕ := (legs.map fun ℓ => ℓ.arr - ℓ.dep).sum

/-- Total landing cost of a list of legs. -/
def landCostSum (c : Fin n → ℕ) (legs : List (Leg n t)) : ℕ := (legs.map (landCost c)).sum

/-- Waiting only adds time: a route from time `τ` ends no earlier than `τ` plus its flight time. -/
theorem add_durSum_le_endTime : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ),
    IsRoute x τ legs → (∀ ℓ ∈ legs, ℓ.dep ≤ ℓ.arr) → τ + durSum legs ≤ endTime τ legs
  | [], _, _, _, _ => by simp [durSum]
  | ℓ :: rest, x, τ, h, hdep => by
    have ih := add_durSum_le_endTime rest ℓ.dst ℓ.arr h.2.2 fun m hm => hdep m (List.mem_cons_of_mem _ hm)
    have h₁ := h.2.1
    have h₂ := hdep ℓ List.mem_cons_self
    simp only [durSum, List.map_cons, List.sum_cons, endTime_cons] at ih ⊢
    omega

/-- The shorter hub flight of city `i`: `min(d_i, d̄_i)`. Every flight between a hub and `i`
lasts at least this long. -/
def Network.emin (N : Network n) (i : Fin n) : ℕ := min (N.d i) (N.dbar i)

theorem Network.emin_le_d (N : Network n) (i : Fin n) : N.emin i ≤ N.d i := min_le_left _ _

theorem Network.emin_le_dbar (N : Network n) (i : Fin n) : N.emin i ≤ N.dbar i :=
  min_le_right _ _

theorem Network.emin_eq_of_sym {N : Network n} (hS : N.dbar = N.d) : N.emin = N.d := by
  funext i
  simp [Network.emin, hS]

/-- **Segments.** Along a route ending at a hub, keep one landing per segment, the one of smaller
`min(d, d̄)` among the segment's first and last landings. This gives a multiset with one
element per hub arrival, twice its load at most the flight time, and its cost at most the landing
cost. The second part is the invariant in the middle of a segment: the current city is `w`, the
segment's first landing was `f` (its incoming hub leg, `d f`, is already paid), and the landing
costs of `f` and `w` are available. -/
theorem exists_segments_aux (N : Network n) (c : Fin n → ℕ) :
    ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs → (∀ ℓ ∈ legs, Flies N ℓ) →
      (finalLoc x legs).isHub = true →
      (x.isHub = true → ∃ Z : Multiset (Fin n), Z.card = hubArrivals legs ∧
          2 * load N.emin Z ≤ durSum legs ∧ cost c Z ≤ landCostSum c legs) ∧
      (∀ w f : Fin n, x = .city w → ∃ Z : Multiset (Fin n), Z.card = hubArrivals legs ∧
          2 * load N.emin Z ≤ durSum legs + N.emin f ∧
          cost c Z ≤ landCostSum c legs + max (c f) (c w))
  | [], x, _, _, _, hend => by
    refine ⟨fun _ => ⟨0, by simp [hubArrivals], by simp, by simp⟩, fun w f hx => ?_⟩
    subst hx
    simp [] at hend
  | ⟨src, dst, dep, arr, pax⟩ :: rest, x, τ, hroute, hflies, hend => by
    obtain ⟨hsrc, -, hrest⟩ := hroute
    simp only at hsrc
    subst hsrc
    have hfl : Flies N ⟨src, dst, dep, arr, pax⟩ := hflies _ List.mem_cons_self
    obtain ⟨τ', hdur, harr⟩ := hfl
    simp only at hdur harr
    have ih := exists_segments_aux N c rest dst arr hrest
      (fun m hm => hflies m (List.mem_cons_of_mem _ hm)) hend
    have hdur' : arr - dep = τ' := by omega
    simp only [hubArrivals, durSum, landCostSum, List.countP_cons, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [hdur']
    cases src with
    | ci =>
      refine ⟨fun _ => ?_, fun w f hx => absurd hx (by simp)⟩
      cases dst with
      | ci => simp [Network.duration] at hdur
      | cg => simp [Network.duration] at hdur
      | city w' =>
        simp only [Network.duration, Option.some.injEq] at hdur
        have he := N.emin_le_d w'
        obtain ⟨Z, hcard, hload, hcost⟩ := ih.2 w' w' rfl
        refine ⟨Z, by simp [hcard], by omega, ?_⟩
        simp only [landCost, max_self] at hcost ⊢
        omega
    | cg =>
      refine ⟨fun _ => ?_, fun w f hx => absurd hx (by simp)⟩
      cases dst with
      | ci => simp [Network.duration] at hdur
      | cg => simp [Network.duration] at hdur
      | city w' =>
        simp only [Network.duration, Option.some.injEq] at hdur
        have he := N.emin_le_dbar w'
        obtain ⟨Z, hcard, hload, hcost⟩ := ih.2 w' w' rfl
        refine ⟨Z, by simp [hcard], by omega, ?_⟩
        simp only [landCost, max_self] at hcost ⊢
        omega
    | city w =>
      refine ⟨fun h => by simp [] at h, fun w₀ f hx => ?_⟩
      simp only [Loc.city.injEq] at hx
      subst hx
      cases dst with
      | city w'' =>
        obtain ⟨Z, hcard, hload, hcost⟩ := ih.2 w'' f rfl
        refine ⟨Z, by simp [hcard], by omega, ?_⟩
        simp only [landCost] at hcost ⊢
        omega
      | ci =>
        simp only [Network.duration, Option.some.injEq] at hdur
        have he := N.emin_le_d w
        obtain ⟨Z, hcard, hload, hcost⟩ := ih.1 rfl
        refine ⟨(if N.emin f ≤ N.emin w then f else w) ::ₘ Z, by simp [hcard], ?_, ?_⟩
        · split_ifs with hfw <;> simp only [load_cons] <;> omega
        · simp only [landCost] at hcost ⊢
          split_ifs with hfw <;> simp only [cost_cons] <;> omega
      | cg =>
        simp only [Network.duration, Option.some.injEq] at hdur
        have he := N.emin_le_dbar w
        obtain ⟨Z, hcard, hload, hcost⟩ := ih.1 rfl
        refine ⟨(if N.emin f ≤ N.emin w then f else w) ::ₘ Z, by simp [hcard], ?_, ?_⟩
        · split_ifs with hfw <;> simp only [load_cons] <;> omega
        · simp only [landCost] at hcost ⊢
          split_ifs with hfw <;> simp only [cost_cons] <;> omega

theorem Flies.dep_le_arr {N : Network n} {ℓ : Leg n t} (h : Flies N ℓ) : ℓ.dep ≤ ℓ.arr := by
  obtain ⟨τ, -, h⟩ := h
  omega

/-- **Segments of a plane.** A feasible plane yields a multiset `Z` with one landing per
segment (`|Z| = #hub arrivals`), `2 δ(Z) ≤` the plane's end time for the durations
`min(d, d̄)`, and `c(Z) ≤` the plane's landing cost. -/
theorem PlaneFeasible.exists_segments_emin {N : Network n} (c : Fin n → ℕ)
    {legs : List (Leg n t)} (h : PlaneFeasible N legs) :
    ∃ Z : Multiset (Fin n), Z.card = hubArrivals legs ∧ 2 * load N.emin Z ≤ endTime 0 legs ∧
      cost c Z ≤ landCostSum c legs := by
  obtain ⟨Z, hcard, hload, hcost⟩ :=
    (exists_segments_aux N c legs .ci 0 h.route h.flies (by simp [h.ends])).1 rfl
  have := add_durSum_le_endTime legs .ci 0 h.route fun ℓ hℓ => (h.flies ℓ hℓ).dep_le_arr
  exact ⟨Z, hcard, by omega, hcost⟩

/-! ### Trimming -/

/-- Trimming: from groups that are all non-empty with total size at least `s ≥ p`, remove
landings to reach total size exactly `s`, keeping every group non-empty. -/
theorem exists_trim {α : Type*} [DecidableEq α] (s : ℕ) (hps : p ≤ s) :
    ∀ (N : ℕ) (Z : Fin p → Multiset α), (∀ k, 1 ≤ (Z k).card) →
      ∑ k, (Z k).card = s + N →
      ∃ Y : Fin p → Multiset α, (∀ k, Y k ≤ Z k) ∧ (∀ k, 1 ≤ (Y k).card) ∧
        ∑ k, (Y k).card = s
  | 0, Z, hpos, hsum => ⟨Z, fun _ => le_rfl, hpos, hsum⟩
  | N + 1, Z, hpos, hsum => by
    -- Some group has at least two landings.
    have hbig : ∃ k₀, 2 ≤ (Z k₀).card := by
      by_contra hall
      push Not at hall
      have : ∑ k, (Z k).card ≤ ∑ _k : Fin p, 1 :=
        Finset.sum_le_sum fun k _ => by have := hall k; omega
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one] at this
      omega
    obtain ⟨k₀, hk₀⟩ := hbig
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (Z k₀).card)
    classical
    set Z' := Function.update Z k₀ ((Z k₀).erase a) with hZ'
    have hcard' : ((Z k₀).erase a).card = (Z k₀).card - 1 := by
      rw [Multiset.card_erase_of_mem ha]
      rfl
    have hpos' : ∀ k, 1 ≤ (Z' k).card := by
      intro k
      by_cases hk : k = k₀
      · subst hk
        simp only [hZ', Function.update_self]
        omega
      · simp only [hZ', Function.update_of_ne hk]
        exact hpos k
    have hsum' : ∑ k, (Z' k).card = s + N := by
      have h₁ := Finset.sum_update_of_mem (Finset.mem_univ k₀) (fun k => (Z k).card)
        ((Z k₀).erase a).card
      have h₂ := Finset.add_sum_erase (Finset.univ : Finset (Fin p)) (fun k => (Z k).card)
        (Finset.mem_univ k₀)
      have h₃ : ∑ k, (Z' k).card = ∑ k, Function.update (fun k => (Z k).card) k₀
          ((Z k₀).erase a).card k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = k₀
        · subst hk; simp [hZ']
        · simp [hZ', Function.update_of_ne hk]
      rw [h₃, h₁, hcard', ← Finset.sdiff_singleton_eq_erase] at *
      rw [Finset.sdiff_singleton_eq_erase] at h₁
      omega
    obtain ⟨Y, hle, hYpos, hYsum⟩ := exists_trim s hps N Z' hpos' hsum'
    refine ⟨Y, fun k => (hle k).trans ?_, hYpos, hYsum⟩
    by_cases hk : k = k₀
    · subst hk
      simp only [hZ', Function.update_self]
      exact Multiset.erase_le _ _
    · simp [hZ', Function.update_of_ne hk]

/-! ### Lemma R -/

/-- **Lemma R** (relaxation), non-symmetric form. Whatever the durations and the central
flights, a feasible plan with `1 ≤ p ≤ t` yields `p` non-empty groups of landings, of total size
`s = 2t − p`, with `2 δ(Y_k) ≤` the makespan for the durations `min(d, d̄)`, and total cost at most
the plan's cost. -/
theorem Feasible.exists_relaxation_emin {N : Network n} (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ Y : Groups n p, (∀ k, 1 ≤ (Y k).card) ∧ size Y = 2 * t - p ∧
      (∀ k, 2 * load N.emin (Y k) ≤ planMakespan P) ∧ totalCost c Y ≤ planCost c P := by
  choose Z hcard hload hcost using fun k => (hP.planes k).exists_segments_emin c
  have hpos : ∀ k, 1 ≤ (Z k).card := by
    intro k
    rw [hcard k]
    have h := (hP.planes k).ciDepartures_add_cgArrivals
    -- the last leg of the plane arrives at `C_G`, a hub
    have hne := isRoute_ne_nil_of_finalLoc_ne (hP.planes k).ends (by simp)
    obtain ⟨ℓ, hℓ, hdst⟩ := exists_mem_dst_finalLoc .ci (P k) hne
    rw [(hP.planes k).ends] at hdst
    have : 0 < hubArrivals (P k) := List.countP_pos_iff.mpr ⟨ℓ, hℓ, by simp [hdst]⟩
    omega
  have hcount := hP.le_sum_hubArrivals
  have hsum : ∑ k, (Z k).card = (2 * t - p) + (∑ k, (Z k).card - (2 * t - p)) := by
    simp only [hcard] at hcount ⊢
    omega
  obtain ⟨Y, hle, hYpos, hYsum⟩ := exists_trim (2 * t - p) (by omega) _ Z hpos hsum
  refine ⟨Y, hYpos, hYsum, fun k => ?_, ?_⟩
  · exact (Nat.mul_le_mul_left 2 (load_mono _ (hle k))).trans
      ((hload k).trans (endTime_le_planMakespan P k))
  · calc totalCost c Y ≤ ∑ k, cost c (Z k) :=
          Finset.sum_le_sum fun k _ => cost_mono c (hle k)
      _ ≤ ∑ k, landCostSum c (P k) := Finset.sum_le_sum fun k _ => hcost k
      _ = planCost c P := rfl

/-- **Segments of a plane**, under (S): `2 δ(Z) ≤` the plane's end time. -/
theorem PlaneFeasible.exists_segments {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ)
    {legs : List (Leg n t)} (h : PlaneFeasible N legs) :
    ∃ Z : Multiset (Fin n), Z.card = hubArrivals legs ∧ 2 * load N.d Z ≤ endTime 0 legs ∧
      cost c Z ≤ landCostSum c legs := by
  simpa [Network.emin_eq_of_sym hS] using h.exists_segments_emin c

/-- **Lemma R** (relaxation). Under (S), whatever the central flights, a feasible plan with
`1 ≤ p ≤ t` yields `p` non-empty groups of landings, of total size `s = 2t − p`, with
`2 δ(Y_k) ≤` the makespan for every plane and total cost at most the plan's cost. -/
theorem Feasible.exists_relaxation {N : Network n} (hS : N.dbar = N.d) (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ Y : Groups n p, (∀ k, 1 ≤ (Y k).card) ∧ size Y = 2 * t - p ∧
      (∀ k, 2 * load N.d (Y k) ≤ planMakespan P) ∧ totalCost c Y ≤ planCost c P := by
  simpa [Network.emin_eq_of_sym hS] using hP.exists_relaxation_emin c hpt

end ZenoFront
