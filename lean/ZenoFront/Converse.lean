/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.PlanBounds
public import ZenoFront.Shrink

/-!
# The converse under (S) and (A1) (Theorem 4.7)

**Theorem 4.7.** Under symmetric durations (S) and useless central flights (A1,
`dc i j ≥ d i + d j`), every feasible plan with cost `C` and makespan `M` is weakly dominated by
an admissible partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = s = 2t − p`,
`c(X) ≤ C` and `2 δ(X_k) ≤ M` for every plane (`Feasible.exists_admissible`).

The proof follows the note's Steps 1–3, in a form that needs no surgery on the plan:

* **Step 1 (removing central flights).** Under (S) and (A1), a central flight `a → b` lasts at
  least `d_a + d_b`, as long as `a → C_G → b`. So every leg lasts at least the weights of its
  central endpoints, and a route from `C_I` to `C_G` flies at least `2 δ(L_k)`, `L_k` being all
  its central landings (`PlaneFeasible.two_mul_load_landings_le`). The segment *types* of the
  plan after Step 1 are read off directly: a landing's entry hub is `C_I` iff its incoming leg
  leaves `C_I`, and its exit hub is `C_I` iff its outgoing leg arrives at `C_I` (a central
  outgoing leg counts as going through `C_G`) (`landingRecs`).
* **Step 2 (cleaning).** For each passenger, take its last departure from `C_I`, a leg
  `C_I → x`, and the next leg, which leaves `x` and does not arrive at `C_I`
  (`exists_transfer`). They are the two flights of its clean journey after Step 1.
* **Step 3 (direct selection, then PAR).** Every passenger transferring at `x` gives a distinct
  landing at `x` entered from `C_I` (type `A` or `B`) and a distinct landing at `x` left towards
  `C_G` (type `A` or `B̄`). So the passengers at `x` number at most
  `#A_x + min(#B_x, #B̄_x)`. Taking all `A` and `Ā` landings as crossings (an odd number per
  plane, as `#A = #Ā + 1`) and `min(#B_x, #B̄_x)` drop-offs and pick-ups at every city gives a
  role configuration with at least `t` passengers. PAR (`RoleConfig.admissible_groups`) makes its
  groups admissible, with at least `s` landings, and shrinking (`Admissible.exists_shrink`)
  brings them to exactly `s`.

Every group is a sub-multiset of its plane's central landings, so the cost is at most `C` and,
by Step 1, `2 δ(X_k) ≤ M`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- Assumption (A1): central flights are useless, `dc i j ≥ d i + d j` (under (S)). -/
def Network.A1 (N : Network n) : Prop := ∀ i j, N.d i + N.d j ≤ N.dc i j

namespace Loc

/-- The duration weight of a location: `d i` for a central city `i`, `0` for a hub. -/
def weight (d : Fin n → ℕ) : Loc n → ℕ
  | city i => d i
  | _ => 0

/-- Whether the location is a central city satisfying `q`. -/
def isCityWith (q : Fin n → Bool) : Loc n → Bool
  | city i => q i
  | _ => false

@[simp] theorem weight_ci (d : Fin n → ℕ) : (ci : Loc n).weight d = 0 := rfl
@[simp] theorem weight_cg (d : Fin n → ℕ) : (cg : Loc n).weight d = 0 := rfl
@[simp] theorem weight_city (d : Fin n → ℕ) (i : Fin n) : (city i).weight d = d i := rfl
@[simp] theorem isCityWith_ci (q : Fin n → Bool) : (ci : Loc n).isCityWith q = false := rfl
@[simp] theorem isCityWith_cg (q : Fin n → Bool) : (cg : Loc n).isCityWith q = false := rfl
@[simp] theorem isCityWith_city (q : Fin n → Bool) (i : Fin n) :
    (city i).isCityWith q = q i := rfl

end Loc

/-! ### Landings and Step 1 -/

/-- The central landings of a list of legs. -/
def routeLandings : List (Leg n t) → Multiset (Fin n)
  | [] => 0
  | ℓ :: rest =>
    match ℓ.dst with
    | .city i => i ::ₘ routeLandings rest
    | _ => routeLandings rest

theorem landCostSum_eq_cost (c : Fin n → ℕ) : ∀ legs : List (Leg n t),
    landCostSum c legs = cost c (routeLandings legs)
  | [] => by simp [landCostSum, routeLandings]
  | ⟨src, dst, dep, arr, pax⟩ :: rest => by
    have ih := landCostSum_eq_cost c rest
    simp only [landCostSum, List.map_cons, List.sum_cons] at ih ⊢
    cases dst <;> simp [routeLandings, landCost, ih]

theorem Flies.duration_ge {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1) {ℓ : Leg n t}
    (h : Flies N ℓ) : ℓ.src.weight N.d + ℓ.dst.weight N.d ≤ ℓ.arr - ℓ.dep := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, harr⟩ := h
  simp only at hdur harr ⊢
  have : arr - dep = τ := by omega
  rw [this]
  cases src <;> cases dst <;> simp [Network.duration, hS] at hdur ⊢ <;> try omega
  rename_i i j
  rw [← hdur]
  exact hA1 i j

/-- **Step 1.** Under (S) and (A1), a route flies at least twice the load of its central
landings (with the endpoints' weights as boundary terms). -/
theorem two_mul_load_landings_le {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1) :
    ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs →
      (∀ ℓ ∈ legs, Flies N ℓ) →
      2 * load N.d (routeLandings legs) + x.weight N.d ≤
        durSum legs + (finalLoc x legs).weight N.d
  | [], x, _, _, _ => by simp [routeLandings, durSum]
  | ⟨src, dst, dep, arr, pax⟩ :: rest, x, τ, hroute, hflies => by
    obtain ⟨hsrc, -, hrest⟩ := hroute
    simp only at hsrc
    subst hsrc
    have hfl := (hflies _ List.mem_cons_self).duration_ge hS hA1
    have ih := two_mul_load_landings_le hS hA1 rest dst arr hrest
      fun m hm => hflies m (List.mem_cons_of_mem _ hm)
    simp only [durSum, List.map_cons, List.sum_cons, finalLoc_cons] at ih hfl ⊢
    cases dst with
    | city i =>
      simp only [routeLandings, load_cons, Loc.weight_city] at ih hfl ⊢
      omega
    | ci =>
      simp only [routeLandings, Loc.weight_ci] at ih hfl ⊢
      omega
    | cg =>
      simp only [routeLandings, Loc.weight_cg] at ih hfl ⊢
      omega

/-- **Step 1 for a plane.** Under (S) and (A1), `2 δ(L_k)` is at most the plane's end time. -/
theorem PlaneFeasible.two_mul_load_landings_le {N : Network n} (hS : N.dbar = N.d)
    (hA1 : N.A1) {legs : List (Leg n t)} (h : PlaneFeasible N legs) :
    2 * load N.d (routeLandings legs) ≤ endTime 0 legs := by
  have h₁ := ZenoFront.two_mul_load_landings_le hS hA1 legs .ci 0 h.route h.flies
  have h₂ := add_durSum_le_endTime legs .ci 0 h.route fun ℓ hℓ => (h.flies ℓ hℓ).dep_le_arr
  rw [h.ends] at h₁
  simp only [Loc.weight_ci, Loc.weight_cg, add_zero] at h₁
  omega

/-! ### Landing records: segment types after Step 1 -/

/-- The central landings of a route with, for each, whether its incoming leg leaves `C_I`
(entry hub `C_I`) and whether its outgoing leg arrives at `C_I` (exit hub `C_I`; a central
outgoing leg counts as exiting through `C_G`). The last leg yields no record. -/
def landingRecs : List (Leg n t) → List (Fin n × Bool × Bool)
  | ℓ :: ℓ' :: rest =>
    match ℓ.dst with
    | .city x => (x, ℓ.src.isCI, ℓ'.dst.isCI) :: landingRecs (ℓ' :: rest)
    | _ => landingRecs (ℓ' :: rest)
  | _ => []

theorem landingRecs_map_fst_le : ∀ legs : List (Leg n t),
    (((landingRecs legs).map Prod.fst : List (Fin n)) : Multiset (Fin n)) ≤ routeLandings legs
  | [] => by simp [landingRecs, routeLandings]
  | [_] => by simp [landingRecs]
  | ⟨src, dst, dep, arr, pax⟩ :: ℓ' :: rest => by
    have ih := landingRecs_map_fst_le (ℓ' :: rest)
    cases dst with
    | city x =>
      simp only [landingRecs, routeLandings, List.map_cons, ← Multiset.cons_coe]
      exact Multiset.cons_le_cons x ih
    | ci => simpa [landingRecs, routeLandings] using ih
    | cg => simpa [landingRecs, routeLandings] using ih

/-- Records entered from `C_I` are the legs leaving `C_I` (towards a city satisfying `q`), when
the route ends at a hub. -/
theorem countP_landingRecs_entry (q : Fin n → Bool) : ∀ (legs : List (Leg n t)) (y : Loc n),
    (finalLoc y legs).isHub = true →
    (landingRecs legs).countP (fun r => q r.1 && r.2.1) =
      legs.countP fun ℓ => ℓ.src.isCI && ℓ.dst.isCityWith q
  | [], _, _ => by simp [landingRecs]
  | [⟨src, dst, dep, arr, pax⟩], y, h => by
    simp only [finalLoc_cons, finalLoc_nil] at h
    cases dst <;> simp_all [landingRecs]
  | ⟨src, dst, dep, arr, pax⟩ :: ℓ' :: rest, y, h => by
    have ih := countP_landingRecs_entry q (ℓ' :: rest) dst h
    cases dst with
    | city x =>
      simp only [landingRecs, List.countP_cons, ih]
      simp [and_comm]
    | ci => simp only [landingRecs, List.countP_cons, ih]; simp
    | cg => simp only [landingRecs, List.countP_cons, ih]; simp

/-- Records by exit hub: for a route from `y` with first leg `ℓ`, a record's exit flag `f`
(applied to "exits to `C_I`") counts the legs leaving a city satisfying `q`, except `ℓ` itself,
which leaves `y`. -/
theorem countP_landingRecs_exit (q : Fin n → Bool) (f : Bool → Bool) :
    ∀ (rest : List (Leg n t)) (ℓ : Leg n t) (y : Loc n) (τ : ℕ), IsRoute y τ (ℓ :: rest) →
      (landingRecs (ℓ :: rest)).countP (fun r => q r.1 && f r.2.2) +
        (if (f ℓ.dst.isCI && y.isCityWith q) = true then 1 else 0) =
      (ℓ :: rest).countP fun ℓ => f ℓ.dst.isCI && ℓ.src.isCityWith q
  | [], ℓ, y, τ, h => by
    obtain ⟨hsrc, -⟩ := h
    simp [landingRecs, List.countP_cons, hsrc]
  | ℓ' :: rest, ⟨src, dst, dep, arr, pax⟩, y, τ, h => by
    obtain ⟨hsrc, -, hrest⟩ := h
    simp only at hsrc hrest
    subst hsrc
    have ih := countP_landingRecs_exit q f rest ℓ' dst arr hrest
    have hsrc' : ℓ'.src = dst := hrest.1
    rw [List.countP_cons, ← ih]
    cases dst with
    | city x =>
      simp only [landingRecs, List.countP_cons, Loc.isCityWith_city, Bool.and_comm (q x)]
      rfl
    | ci => simp [landingRecs]
    | cg => simp [landingRecs]

/-! ### Counting the four segment types -/

/-- Records of type `A` (entry `C_I`, exit `C_G`) at cities satisfying `q`. -/
def cntA (q : Fin n → Bool) (R : List (Fin n × Bool × Bool)) : ℕ :=
  R.countP fun r => q r.1 && (r.2.1 && !r.2.2)

/-- Records of type `Ā` (entry `C_G`, exit `C_I`). -/
def cntAbar (q : Fin n → Bool) (R : List (Fin n × Bool × Bool)) : ℕ :=
  R.countP fun r => q r.1 && (!r.2.1 && r.2.2)

/-- Records of type `B` (entry and exit `C_I`: a drop-off). -/
def cntB (q : Fin n → Bool) (R : List (Fin n × Bool × Bool)) : ℕ :=
  R.countP fun r => q r.1 && (r.2.1 && r.2.2)

/-- Records of type `B̄` (entry and exit `C_G`: a pick-up). -/
def cntBbar (q : Fin n → Bool) (R : List (Fin n × Bool × Bool)) : ℕ :=
  R.countP fun r => q r.1 && (!r.2.1 && !r.2.2)

theorem countP_entry_eq (q : Fin n → Bool) : ∀ R : List (Fin n × Bool × Bool),
    R.countP (fun r => q r.1 && r.2.1) = cntA q R + cntB q R
  | [] => rfl
  | ⟨x, a, b⟩ :: R => by
    have := countP_entry_eq q R
    simp only [cntA, cntB, List.countP_cons] at this ⊢
    cases q x <;> cases a <;> cases b <;> simp <;> omega

theorem countP_exitI_eq (q : Fin n → Bool) : ∀ R : List (Fin n × Bool × Bool),
    R.countP (fun r => q r.1 && r.2.2) = cntAbar q R + cntB q R
  | [] => rfl
  | ⟨x, a, b⟩ :: R => by
    have := countP_exitI_eq q R
    simp only [cntAbar, cntB, List.countP_cons] at this ⊢
    cases q x <;> cases a <;> cases b <;> simp <;> omega

theorem countP_exitG_eq (q : Fin n → Bool) : ∀ R : List (Fin n × Bool × Bool),
    R.countP (fun r => q r.1 && !r.2.2) = cntA q R + cntBbar q R
  | [] => rfl
  | ⟨x, a, b⟩ :: R => by
    have := countP_exitG_eq q R
    simp only [cntA, cntBbar, List.countP_cons] at this ⊢
    cases q x <;> cases a <;> cases b <;> simp <;> omega

/-- Summing a per-city count over all cities. -/
theorem sum_countP_city (g : Fin n × Bool × Bool → Bool) : ∀ R : List (Fin n × Bool × Bool),
    ∑ x, R.countP (fun r => decide (r.1 = x) && g r) = R.countP g
  | [] => by simp
  | r :: R => by
    simp only [List.countP_cons, Finset.sum_add_distrib, sum_countP_city g R]
    congr 1
    by_cases hg : g r = true
    · simp [hg]
    · simp [hg]

/-- The cities of the records satisfying `g`. -/
def recCities (g : Fin n × Bool × Bool → Bool) (R : List (Fin n × Bool × Bool)) :
    Multiset (Fin n) :=
  ((R.filter g).map Prod.fst : List (Fin n))

theorem count_recCities (g : Fin n × Bool × Bool → Bool) (x : Fin n) :
    ∀ R : List (Fin n × Bool × Bool),
      (recCities g R).count x = R.countP fun r => decide (r.1 = x) && g r
  | [] => rfl
  | r :: R => by
    have := count_recCities g x R
    simp only [recCities, Multiset.coe_count] at this ⊢
    by_cases hg : g r = true
    · by_cases hx : r.1 = x
      · simp [hg, hx, this]
      · simp [hg, hx, this]
    · simp [hg, this]

theorem card_recCities (g : Fin n × Bool × Bool → Bool) (R : List (Fin n × Bool × Bool)) :
    (recCities g R).card = R.countP g := by
  simp [recCities, List.countP_eq_length_filter]

theorem recCities_cons (g : Fin n × Bool × Bool → Bool) (r : Fin n × Bool × Bool)
    (R : List (Fin n × Bool × Bool)) :
    recCities g (r :: R) = if g r = true then r.1 ::ₘ recCities g R else recCities g R := by
  unfold recCities
  by_cases hg : g r = true <;> simp [hg]

/-- The records of types `B`, `B̄`, and `A` or `Ā`, together, are all the records. -/
theorem recCities_split : ∀ R : List (Fin n × Bool × Bool),
    recCities (fun r => r.2.1 && r.2.2) R + recCities (fun r => !r.2.1 && !r.2.2) R +
      recCities (fun r => r.2.1 != r.2.2) R = ((R.map Prod.fst : List (Fin n)) : Multiset (Fin n))
  | [] => rfl
  | ⟨x, a, b⟩ :: R => by
    have ih := recCities_split R
    rw [recCities_cons, recCities_cons, recCities_cons, List.map_cons, ← Multiset.cons_coe, ← ih]
    cases a <;> cases b <;> simp [Multiset.cons_add, Multiset.add_cons]

/-! ### Plane-level counts -/

/-- Number of legs arriving at `C_I`. -/
def ciArrivals (legs : List (Leg n t)) : ℕ := legs.countP fun ℓ => ℓ.dst.isCI

theorem hubArrivals_eq (legs : List (Leg n t)) :
    hubArrivals legs = ciArrivals legs + cgArrivals legs := by
  induction legs with
  | nil => rfl
  | cons ℓ rest ih =>
    simp only [hubArrivals, ciArrivals, cgArrivals, List.countP_cons] at ih ⊢
    cases ℓ.dst <;> simp <;> omega

theorem Flies.dst_city_of_src_isHub {N : Network n} {ℓ : Leg n t} (h : Flies N ℓ)
    (hs : ℓ.src.isHub = true) : ∃ x, ℓ.dst = .city x := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, -⟩ := h
  simp only at hdur hs ⊢
  cases src <;> cases dst <;> simp_all [Network.duration]

theorem Flies.src_city_of_dst_isHub {N : Network n} {ℓ : Leg n t} (h : Flies N ℓ)
    (hd : ℓ.dst.isHub = true) : ∃ x, ℓ.src = .city x := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ, hdur, -⟩ := h
  simp only at hdur hd ⊢
  cases src <;> cases dst <;> simp_all [Network.duration]

theorem Loc.isCityWith_true_of_city {x : Loc n} (h : ∃ i, x = .city i) :
    x.isCityWith (fun _ => true) = true := by
  obtain ⟨i, rfl⟩ := h
  rfl

namespace PlaneFeasible

variable {N : Network n} {legs : List (Leg n t)}

theorem entry_total (h : PlaneFeasible N legs) :
    cntA (fun _ => true) (landingRecs legs) + cntB (fun _ => true) (landingRecs legs) =
      ciDepartures legs := by
  rw [← countP_entry_eq]
  refine (countP_landingRecs_entry (fun _ => true) legs .ci (by simp [h.ends])).trans ?_
  rw [ciDepartures]
  refine List.countP_congr fun ℓ hℓ => ?_
  by_cases hs : ℓ.src.isCI = true
  · have : ℓ.src.isHub = true := by
      obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
      cases src <;> simp_all
    simp [hs, Loc.isCityWith_true_of_city ((h.flies ℓ hℓ).dst_city_of_src_isHub this)]
  · simp [hs]

theorem exitI_total (h : PlaneFeasible N legs) :
    cntAbar (fun _ => true) (landingRecs legs) + cntB (fun _ => true) (landingRecs legs) =
      ciArrivals legs := by
  rw [← countP_exitI_eq]
  cases legs with
  | nil => rfl
  | cons ℓ rest =>
    have := countP_landingRecs_exit (fun _ => true) id rest ℓ .ci 0 h.route
    simp only [Loc.isCityWith_ci, Bool.and_false] at this
    rw [show (if (false : Bool) = true then 1 else 0) = 0 from rfl, add_zero] at this
    simp only [id] at this
    rw [this, ciArrivals]
    refine List.countP_congr fun m hm => ?_
    by_cases hd : m.dst.isCI = true
    · have : m.dst.isHub = true := by
        obtain ⟨src, dst, dep, arr, pax⟩ := m
        cases dst <;> simp_all
      simp [hd, Loc.isCityWith_true_of_city ((h.flies m hm).src_city_of_dst_isHub this)]
    · simp [hd]

/-- `#A = #Ā + 1` for every plane (Lemma 2.1 after Step 1). -/
theorem cntA_eq (h : PlaneFeasible N legs) :
    cntA (fun _ => true) (landingRecs legs) = cntAbar (fun _ => true) (landingRecs legs) + 1 := by
  have h₁ := h.entry_total
  have h₂ := h.exitI_total
  have h₃ := h.ciDepartures_add_cgArrivals
  rw [hubArrivals_eq] at h₃
  omega

/-- Per city: the records at `x` entered from `C_I` are the legs `C_I → x`. -/
theorem entry_city (h : PlaneFeasible N legs) (x : Fin n) :
    cntA (fun y => decide (y = x)) (landingRecs legs) + cntB (fun y => decide (y = x))
      (landingRecs legs) = legs.countP fun ℓ => ℓ.src.isCI && ℓ.dst.isCityWith (fun y => decide (y = x)) := by
  rw [← countP_entry_eq]
  exact countP_landingRecs_entry (fun y => decide (y = x)) legs .ci (by simp [h.ends])

/-- Per city: the records at `x` exiting towards `C_G` are the legs leaving `x` not towards
`C_I`. -/
theorem exitG_city (h : PlaneFeasible N legs) (x : Fin n) :
    cntA (fun y => decide (y = x)) (landingRecs legs) + cntBbar (fun y => decide (y = x))
      (landingRecs legs) = legs.countP fun ℓ => !ℓ.dst.isCI && ℓ.src.isCityWith (fun y => decide (y = x)) := by
  rw [← countP_exitG_eq]
  cases legs with
  | nil => rfl
  | cons ℓ rest =>
    have := countP_landingRecs_exit (fun y => decide (y = x)) (fun b => !b) rest ℓ .ci 0 h.route
    simp only [Loc.isCityWith_ci, Bool.and_false] at this
    rw [show (if (false : Bool) = true then 1 else 0) = 0 from rfl, add_zero] at this
    exact this

end PlaneFeasible

/-! ### Passengers: Step 2 (cleaning) -/

/-- **Step 2.** A route from `C_I` to `C_G` has a leg `C_I → x` followed, later, by a leg leaving
`x` that does not arrive at `C_I`: the last departure from `C_I` and the next leg. -/
theorem exists_transfer {N : Network n} : ∀ (l : List (Leg n t)) (τ : ℕ), IsRoute .ci τ l →
    (∀ ℓ ∈ l, Flies N ℓ) → finalLoc .ci l = .cg →
    ∃ x : Fin n, ∃ ℓo ∈ l, ∃ ℓn ∈ l, ℓo.src = .ci ∧ ℓo.dst = .city x ∧ ℓn.src = .city x ∧
      ℓn.dst ≠ .ci
  | [], _, _, _, h => by simp at h
  | [ℓ], _, hr, hf, h => by
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).dst_city_of_src_isHub (by simp [hr.1])
    simp [hx] at h
  | ℓ :: ℓ' :: rest, τ, hr, hf, h => by
    obtain ⟨hsrc, -, hrest⟩ := hr
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).dst_city_of_src_isHub (by simp [hsrc])
    have hsrc' : ℓ'.src = .city x := by rw [hrest.1, hx]
    by_cases hd : ℓ'.dst = .ci
    · obtain ⟨-, -, hrest'⟩ := hrest
      rw [hd] at hrest'
      have hfin : finalLoc .ci rest = .cg := by
        simpa [finalLoc_cons, hd] using h
      obtain ⟨y, ℓo, hℓo, ℓn, hℓn, h₁, h₂, h₃, h₄⟩ := exists_transfer rest ℓ'.arr hrest'
        (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) hfin
      exact ⟨y, ℓo, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓo), ℓn,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓn), h₁, h₂, h₃, h₄⟩
    · exact ⟨x, ℓ, List.mem_cons_self, ℓ', List.mem_cons_of_mem _ List.mem_cons_self, hsrc, hx,
        hsrc', hd⟩

theorem Feasible.flies_of_mem_allLegs {N : Network n} {P : Plan n t p} (hP : Feasible N P)
    {ℓ : Leg n t} (h : ℓ ∈ allLegs P) : Flies N ℓ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact (hP.planes k).flies ℓ hk

/-- Distinct elements of `l` satisfying `q`, indexed by a set of passengers. -/
theorem card_le_countP_of_injective {α : Type*} [DecidableEq α] (S : Finset (Fin t))
    (l : List α) (q : α → Bool) (f : Fin t → α) (hf : Function.Injective f)
    (hmem : ∀ π ∈ S, f π ∈ l ∧ q (f π) = true) : S.card ≤ l.countP q := by
  calc S.card = (S.image f).card := (card_image_of_injective _ hf).symm
    _ ≤ (l.filter q).toFinset.card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨π, hπ, rfl⟩ := mem_image.mp hx
        simpa [List.mem_toFinset, List.mem_filter] using hmem π hπ
    _ ≤ (l.filter q).length := List.toFinset_card_le _
    _ = l.countP q := List.countP_eq_length_filter.symm

/-! ### Step 3: selection, PAR, shrinking -/

/-- Choosing counts below `a` with a given total `μ ≤ Σ a`. -/
theorem exists_le_sum_eq (a : Fin p → ℕ) : ∀ μ : ℕ, μ ≤ ∑ k, a k →
    ∃ b : Fin p → ℕ, (∀ k, b k ≤ a k) ∧ ∑ k, b k = μ
  | 0, _ => ⟨0, fun _ => Nat.zero_le _, by simp⟩
  | μ + 1, h => by
    classical
    obtain ⟨b, hb, hsum⟩ := exists_le_sum_eq a μ (by omega)
    obtain ⟨k₀, hk₀⟩ : ∃ k, b k < a k := by
      by_contra hall
      push Not at hall
      have : ∑ k, a k ≤ ∑ k, b k := Finset.sum_le_sum fun k _ => hall k
      omega
    refine ⟨Function.update b k₀ (b k₀ + 1), fun k => ?_, ?_⟩
    · by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hk]; exact hb k
    · rw [Finset.sum_update_of_mem (Finset.mem_univ k₀), Finset.sdiff_singleton_eq_erase]
      have := Finset.add_sum_erase (univ : Finset (Fin p)) b (Finset.mem_univ k₀)
      omega

theorem countP_cross_eq : ∀ R : List (Fin n × Bool × Bool),
    R.countP (fun r => r.2.1 != r.2.2) = cntA (fun _ => true) R + cntAbar (fun _ => true) R
  | [] => rfl
  | ⟨x, a, b⟩ :: R => by
    have := countP_cross_eq R
    simp only [cntA, cntAbar, List.countP_cons, Bool.true_and] at this ⊢
    cases a <;> cases b <;> simp <;> omega

theorem sum_cntA (R : List (Fin n × Bool × Bool)) :
    ∑ x, cntA (fun y => decide (y = x)) R = cntA (fun _ => true) R := by
  simp only [cntA]
  rw [sum_countP_city (fun r => r.2.1 && !r.2.2) R]
  exact List.countP_congr fun r _ => by simp

/-- A multiset given by its counts. -/
def ofCounts (v : Fin n → ℕ) : Multiset (Fin n) := ∑ x, Multiset.replicate (v x) x

theorem count_ofCounts (v : Fin n → ℕ) (y : Fin n) : (ofCounts v).count y = v y := by
  classical
  simp only [ofCounts, Multiset.count_sum', Multiset.count_replicate]
  simp

theorem card_ofCounts (v : Fin n → ℕ) : (ofCounts v).card = ∑ x, v x := by
  simp [ofCounts, Multiset.card_sum]

theorem Loc.isCI_eq_false_of_ne {x : Loc n} (h : x ≠ .ci) : x.isCI = false := by
  cases x <;> simp_all

/-- **Direct selection on landing records (Lemma 4.3(b)).** Every feasible plan with `p ≤ t`
gives a role configuration whose drop-offs, pick-ups and crossings are the cities of landing
records of type `B`, `B̄`, and `A` or `Ā` of their plane, and whose groups have at least
`2t − p` landings. No assumption on durations is needed; under (S) and (A1), or on a plan
without central flights, the records' types are those of the segments. -/
theorem Feasible.exists_roleConfig_records {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    ∃ cfg : RoleConfig n p,
      (∀ k, cfg.drop k ≤ recCities (fun r => r.2.1 && r.2.2) (landingRecs (P k))) ∧
      (∀ k, cfg.pick k ≤ recCities (fun r => !r.2.1 && !r.2.2) (landingRecs (P k))) ∧
      (∀ k, cfg.cross k = recCities (fun r => r.2.1 != r.2.2) (landingRecs (P k))) ∧
      2 * t - p ≤ size cfg.groups := by
  classical
  set R : Fin p → List (Fin n × Bool × Bool) := fun k => landingRecs (P k) with hR
  -- Step 2: every passenger's transfer.
  have htr : ∀ π : Fin t, ∃ x : Fin n, ∃ ℓo ∈ paxLegs P π, ∃ ℓn ∈ paxLegs P π,
      ℓo.src = .ci ∧ ℓo.dst = .city x ∧ ℓn.src = .city x ∧ ℓn.dst ≠ .ci := by
    intro π
    obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    obtain ⟨x, ℓo, hℓo, ℓn, hℓn, h⟩ := exists_transfer route 0 hroute
      (fun ℓ hℓ => hP.flies_of_mem_allLegs
        (mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)).1) hfin
    exact ⟨x, ℓo, hperm.mem_iff.mp hℓo, ℓn, hperm.mem_iff.mp hℓn, h⟩
  choose xπ ℓo hℓo ℓn hℓn hsrc_o hdst_o hsrc_n hdst_n using htr
  have hpax_o : ∀ π, (ℓo π).pax = some π := fun π => (mem_allLegs_of_mem_paxLegs (hℓo π)).2
  have hpax_n : ∀ π, (ℓn π).pax = some π := fun π => (mem_allLegs_of_mem_paxLegs (hℓn π)).2
  have hinj : ∀ f : Fin t → Leg n t, (∀ π, (f π).pax = some π) → Function.Injective f :=
    fun f hf π π' h => by
      have := hf π
      rw [h, hf π'] at this
      exact (Option.some_injective _ this).symm
  -- Step 3: counts at each city.
  set b : Fin n → ℕ := fun x => ∑ k, cntB (fun y => decide (y = x)) (R k) with hb
  set bb : Fin n → ℕ := fun x => ∑ k, cntBbar (fun y => decide (y = x)) (R k) with hbb
  set A : Fin n → ℕ := fun x => ∑ k, cntA (fun y => decide (y = x)) (R k) with hA
  have hpass : ∀ x, #{π | xπ π = x} ≤ A x + min (b x) (bb x) := by
    intro x
    have h₁ : #{π | xπ π = x} ≤ A x + b x := by
      have := card_le_countP_of_injective {π | xπ π = x} (allLegs P)
        (fun ℓ => ℓ.src.isCI && ℓ.dst.isCityWith (fun y => decide (y = x))) ℓo
        (hinj ℓo hpax_o) fun π hπ => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
          refine ⟨(mem_allLegs_of_mem_paxLegs (hℓo π)).1, ?_⟩
          simp [hsrc_o π, hdst_o π, hπ]
      rw [countP_allLegs] at this
      refine this.trans (le_of_eq ?_)
      rw [hA, hb, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => ((hP.planes k).entry_city x).symm
    have h₂ : #{π | xπ π = x} ≤ A x + bb x := by
      have := card_le_countP_of_injective {π | xπ π = x} (allLegs P)
        (fun ℓ => !ℓ.dst.isCI && ℓ.src.isCityWith (fun y => decide (y = x))) ℓn
        (hinj ℓn hpax_n) fun π hπ => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
          refine ⟨(mem_allLegs_of_mem_paxLegs (hℓn π)).1, ?_⟩
          simp [hsrc_n π, Loc.isCI_eq_false_of_ne (hdst_n π), hπ]
      rw [countP_allLegs] at this
      refine this.trans (le_of_eq ?_)
      rw [hA, hbb, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => ((hP.planes k).exitG_city x).symm
    omega
  have ht : t = ∑ x, #{π | xπ π = x} := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := xπ) (t := univ) fun π _ => Finset.mem_univ _]
    simp
  have hsumA : ∑ x, A x = ∑ k, cntA (fun _ => true) (R k) := by
    rw [hA, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cntA (R k)
  -- Selection: `min(#B_x, #B̄_x)` drop-offs and pick-ups at every city.
  have hdr : ∀ x, ∃ v : Fin p → ℕ, (∀ k, v k ≤ cntB (fun y => decide (y = x)) (R k)) ∧
      ∑ k, v k = min (b x) (bb x) := fun x => exists_le_sum_eq _ _ (min_le_left _ _)
  choose dr hdr_le hdr_sum using hdr
  have hpk : ∀ x, ∃ v : Fin p → ℕ, (∀ k, v k ≤ cntBbar (fun y => decide (y = x)) (R k)) ∧
      ∑ k, v k = min (b x) (bb x) := fun x => exists_le_sum_eq _ _ (min_le_right _ _)
  choose pk hpk_le hpk_sum using hpk
  set Dr : Fin p → Multiset (Fin n) := fun k => ofCounts fun x => dr x k with hDr
  set Pk : Fin p → Multiset (Fin n) := fun k => ofCounts fun x => pk x k with hPk
  set Cr : Fin p → Multiset (Fin n) := fun k => recCities (fun r => r.2.1 != r.2.2) (R k)
    with hCr
  have hcr : ∀ k, (Cr k).card = 2 * cntAbar (fun _ => true) (R k) + 1 := by
    intro k
    have h₁ := (hP.planes k).cntA_eq
    have h₂ := countP_cross_eq (landingRecs (P k))
    show (recCities (fun r => r.2.1 != r.2.2) (landingRecs (P k))).card =
      2 * cntAbar (fun _ => true) (landingRecs (P k)) + 1
    rw [card_recCities]
    omega
  let cfg : RoleConfig n p :=
    { drop := Dr
      pick := Pk
      cross := Cr
      odd_card_cross := fun k => ⟨cntAbar (fun _ => true) (R k), hcr k⟩
      sum_drop_eq_sum_pick := by
        ext y
        rw [Multiset.count_sum', Multiset.count_sum']
        simp only [hDr, hPk, count_ofCounts, hdr_sum, hpk_sum] }
  -- Size: at least `2t − p`.
  have hsize : 2 * t - p ≤ size cfg.groups := by
    have hk : ∀ k, (cfg.groups k).card + 1 =
        ∑ x, dr x k + ∑ x, pk x k + 2 * cntA (fun _ => true) (R k) := by
      intro k
      have h₁ := RoleConfig.card_groups cfg k
      have h₂ : (cfg.drop k).card = ∑ x, dr x k := card_ofCounts _
      have h₃ : (cfg.pick k).card = ∑ x, pk x k := card_ofCounts _
      have h₄ : (cfg.cross k).card = 2 * cntAbar (fun _ => true) (R k) + 1 := hcr k
      have h₅ : cntA (fun _ => true) (R k) = cntAbar (fun _ => true) (R k) + 1 :=
        (hP.planes k).cntA_eq
      omega
    have h₁ : size cfg.groups + p = ∑ k, ((cfg.groups k).card + 1) := by
      rw [size, Finset.sum_add_distrib]
      simp
    have h₂ : ∑ k, ((cfg.groups k).card + 1) = ∑ x, min (b x) (bb x) +
        ∑ x, min (b x) (bb x) + 2 * ∑ k, cntA (fun _ => true) (R k) := by
      rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_comm (f := fun k x => dr x k),
        Finset.sum_comm (f := fun k x => pk x k)]
      simp only [hdr_sum, hpk_sum]
    have h₃ : t ≤ ∑ x, (A x + min (b x) (bb x)) := ht ▸ Finset.sum_le_sum fun x _ => hpass x
    rw [Finset.sum_add_distrib, hsumA] at h₃
    omega
  refine ⟨cfg, fun k => ?_, fun k => ?_, fun k => rfl, hsize⟩
  · refine Multiset.le_iff_count.mpr fun y => ?_
    rw [count_ofCounts, count_recCities]
    exact hdr_le y k
  · refine Multiset.le_iff_count.mpr fun y => ?_
    rw [count_ofCounts, count_recCities]
    exact hpk_le y k

/-- **Theorem 4.7 (converse).** Under (S) and (A1), with `p ≤ t`, every feasible plan is weakly
dominated by an admissible partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤` the makespan for every plane, and total cost at most the plan's cost. -/
theorem Feasible.exists_admissible {N : Network n} (hS : N.dbar = N.d) (hA1 : N.A1)
    (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P := by
  obtain ⟨cfg, hdr, hpk, hcr, hsize⟩ := hP.exists_roleConfig_records
  -- The groups are sub-multisets of the planes' landings.
  have hsub : ∀ k, cfg.groups k ≤ routeLandings (P k) := by
    intro k
    refine le_trans ?_ (landingRecs_map_fst_le (P k))
    rw [← recCities_split]
    exact add_le_add (add_le_add (hdr k) (hpk k)) (le_of_eq (hcr k))
  -- PAR, then shrinking to exactly `2t − p` landings.
  obtain ⟨X, hX, hle, hXsize⟩ := cfg.admissible_groups.exists_shrink (s := 2 * t - p)
    (by omega) (by omega) hsize
  refine ⟨X, hX, hXsize, fun k => ?_, ?_⟩
  · calc 2 * load N.d (X k) ≤ 2 * load N.d (routeLandings (P k)) :=
          Nat.mul_le_mul_left 2 (load_mono _ ((hle k).trans (hsub k)))
      _ ≤ endTime 0 (P k) := (hP.planes k).two_mul_load_landings_le hS hA1
      _ ≤ planMakespan P := endTime_le_planMakespan P k
  · calc totalCost c X ≤ ∑ k, cost c (routeLandings (P k)) :=
          Finset.sum_le_sum fun k _ => cost_mono c ((hle k).trans (hsub k))
      _ = ∑ k, landCostSum c (P k) :=
          Finset.sum_congr rfl fun k _ => (landCostSum_eq_cost c (P k)).symm
      _ = planCost c P := rfl

end ZenoFront
