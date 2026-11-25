/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SearchGap
public import ZenoFront.Achievability

/-!
# Template plans (Lemma 6.3, achievability)

The *template* of a scheduled configuration `S` (§6.2 of the note, `runTemplate` in
`src/zeno/ns_search.cpp`) is the plan in which every plane `k`, from time `0`,

1. flies its drop-offs in order, `C_I → x → C_I`, the first leg carrying a new passenger
   (`Sched.dropPart`); the `j`-th one reaches `x` at `Pre_k(j) + d_x`;
2. flies its crossings (sorted), `C_I → x → C_G` carrying a new passenger and `C_G → x → C_I`
   empty, alternately (`tCrossLegs`); there is an odd number of them, so the plane is now in
   `C_G`;
3. flies its pick-ups in order, `C_G → y → C_G`, leaving `y` once the passenger dropped by the
   linked drop-off has arrived, and carrying it (`Sched.pickPart`).

Passengers are numbered by their slot: the drop-off slots, then the crossing passengers
(`Sched.labelEquiv`). The plan is computable (`Sched.tmplPlan`).

The proof follows the note. Every block of a route starts where and when the previous one ends
(`chain_flatMap_finRange`). With `φ_k(l)` the time plane `k` leaves `C_G` for its `l`-th
pick-up, `φ_k(l + 1) + Suf_k(l) = max(φ_k(l) + Suf_k(l − 1), term of the link into (k, l))`
(`Sched.slack_succ`), so the plane ends at `max(λ_k, max_l term)` (`Sched.pickTime_length_eq`).
The matching is a bijection from the pick-up slots onto the drop-off slots
(`Sched.Valid.slot_bijective`), so the legs of the plan are the two legs `C_I → x → C_G` of one
journey per passenger, plus empty legs (`pax_of_units`).

## Main results

* `Sched.tmplPlan_spec` (**Lemma 6.3, achievability**): for every valid scheduled configuration
  with `2t − p` landings, the template is a feasible plan of cost `c(S)` and makespan exactly
  `M_tmpl = S.tmpl d d̄`. No assumption on the durations (zero durations included) and none on
  central flights (the template flies none) is needed; `p ≤ t` follows from the hypotheses
  (`Sched.Valid.count_eq`).
* `Sched.exists_plan`: the same, as an existence statement.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Crossings, non-symmetric -/

/-- Crossings at the cities `xs`, from the hub `hubOf b` at time `τ`: `C_I → x → C_G` carrying
passenger `ls.head` (none once `ls` is exhausted), and `C_G → x → C_I` empty, alternately. A
crossing at `x` lasts `d x + db x`. -/
def tCrossLegs (d db : Fin n → ℕ) : List (Fin n) → Bool → ℕ → List ℕ → List (Leg n t)
  | [], _, _, _ => []
  | x :: xs, true, τ, ls =>
    ⟨.ci, .city x, τ, τ + d x, pid t (ls.headD t)⟩ ::
      ⟨.city x, .cg, τ + d x, τ + d x + db x, pid t (ls.headD t)⟩ ::
      tCrossLegs d db xs false (τ + d x + db x) ls.tail
  | x :: xs, false, τ, ls =>
    ⟨.cg, .city x, τ, τ + db x, none⟩ :: ⟨.city x, .ci, τ + db x, τ + db x + d x, none⟩ ::
      tCrossLegs d db xs true (τ + db x + d x) ls

namespace Sched

variable (S : Sched n p) (d db : Fin n → ℕ)

/-! ### Slots and passenger labels -/

/-- The drop-off slots `(u, j)`. -/
abbrev DSlot := (k : Fin p) × Fin (S.drops k).length

/-- The pick-up slots `(v, l)`. -/
abbrev PSlot := (k : Fin p) × Fin (S.picks k).length

/-- The crossings of a plane, sorted. -/
def crossList (k : Fin p) : List (Fin n) := (S.cross k).sort (· ≤ ·)

/-- The number of passengers a plane carries across, `(|Cr_k| + 1) / 2`. -/
def nCarry (k : Fin p) : ℕ := ((S.cross k).card + 1) / 2

/-- The crossing passengers `(k, i)`. -/
abbrev XSlot := (k : Fin p) × Fin (S.nCarry k)

/-- The passengers of the template: one per drop-off slot, and the crossing passengers. -/
abbrev Slot := S.DSlot ⊕ S.XSlot

/-- The number of drop-offs. -/
def nDrops : ℕ := ∑ k, (S.drops k).length

/-- The number of crossing passengers. -/
def nCross : ℕ := ∑ k, S.nCarry k

/-- The numbering of the passengers: the drop-off slots plane by plane, then the crossing
passengers. -/
def labelEquiv : S.Slot ≃ Fin (S.nDrops + S.nCross) :=
  (Equiv.sumCongr finSigmaFinEquiv finSigmaFinEquiv).trans finSumFinEquiv

/-- The label of the passenger dropped at slot `(u, j)` (out of range if there is no such
slot). -/
def dropLab (u : Fin p) (j : ℕ) : ℕ :=
  if h : j < (S.drops u).length then S.labelEquiv (.inl ⟨u, ⟨j, h⟩⟩) else S.nDrops + S.nCross

/-- The labels of the passengers plane `k` carries across. -/
def xLabs (k : Fin p) : List ℕ := List.ofFn fun i : Fin (S.nCarry k) => S.labelEquiv (.inr ⟨k, i⟩)

/-! ### The template -/

/-- The carrying leg of the `j`-th drop-off of plane `k`: `C_I → x` from time `Pre_k(j)`. -/
def dropCarryLeg (k : Fin p) (j : Fin (S.drops k).length) : Leg n t :=
  ⟨.ci, .city (S.drops k)[j], S.pre d k j, S.pre d k j + d (S.drops k)[j], pid t (S.dropLab k j)⟩

/-- The `j`-th drop-off of plane `k`: `C_I → x → C_I` from time `Pre_k(j)`, carrying its
passenger to `x`. -/
def dropBlock (k : Fin p) (j : Fin (S.drops k).length) : List (Leg n t) :=
  [S.dropCarryLeg d k j,
    ⟨.city (S.drops k)[j], .ci, S.pre d k j + d (S.drops k)[j],
      S.pre d k j + d (S.drops k)[j] + d (S.drops k)[j], none⟩]

/-- The drop-offs of plane `k`, in order, from time `0`. -/
def dropPart (k : Fin p) : List (Leg n t) :=
  (List.finRange (S.drops k).length).flatMap (S.dropBlock d k)

/-- When plane `k` reaches `C_G` after its drop-offs and crossings. -/
def crossEnd (k : Fin p) : ℕ :=
  2 * ((S.drops k).map d).sum + ((S.crossList k).map fun x => d x + db x).sum

/-- The crossings of plane `k`, after its drop-offs. -/
def crossPart (k : Fin p) : List (Leg n t) :=
  tCrossLegs d db (S.crossList k) true (2 * ((S.drops k).map d).sum) (S.xLabs k)

/-- The duration `d̄_y` of the `l`-th pick-up of plane `k` (`0` if there is none). -/
def pickDur (k : Fin p) (l : ℕ) : ℕ := ((S.picks k)[l]?.map db).getD 0

/-- When the passenger of the `l`-th pick-up of plane `k` reaches its city: the linked drop-off
`(u, j)` arrives at `Pre_u(j) + d_y`. -/
def pickAvail (k : Fin p) (l : ℕ) : ℕ :=
  if h : l < (S.picks k).length then S.pre d (S.mate k l).1 (S.mate k l).2 + d (S.picks k)[l]
  else 0

/-- When plane `k` leaves `C_G` for its `l`-th pick-up (`φ_k(l)` of the note). -/
def pickTime (k : Fin p) : ℕ → ℕ
  | 0 => S.crossEnd d db k
  | l + 1 => max (pickTime k l + S.pickDur db k l) (S.pickAvail d k l) + S.pickDur db k l

/-- When plane `k` leaves the city of its `l`-th pick-up: on arrival, or once the linked
passenger is there. -/
def pickLeave (k : Fin p) (l : Fin (S.picks k).length) : ℕ :=
  max (S.pickTime d db k l + db (S.picks k)[l]) (S.pickAvail d k l)

/-- The carrying leg of the `l`-th pick-up of plane `k`: `y → C_G`, with the linked passenger. -/
def pickCarryLeg (k : Fin p) (l : Fin (S.picks k).length) : Leg n t :=
  ⟨.city (S.picks k)[l], .cg, S.pickLeave d db k l, S.pickLeave d db k l + db (S.picks k)[l],
    pid t (S.dropLab (S.mate k l).1 (S.mate k l).2)⟩

/-- The `l`-th pick-up of plane `k`: `C_G → y`, then `y → C_G` once the linked passenger is
there, carrying it. -/
def pickBlock (k : Fin p) (l : Fin (S.picks k).length) : List (Leg n t) :=
  [⟨.cg, .city (S.picks k)[l], S.pickTime d db k l, S.pickTime d db k l + db (S.picks k)[l], none⟩,
    S.pickCarryLeg d db k l]

/-- The pick-ups of plane `k`, in order, after its crossings. -/
def pickPart (k : Fin p) : List (Leg n t) :=
  (List.finRange (S.picks k).length).flatMap (S.pickBlock d db k)

/-- **The template plan** of a scheduled configuration (§6.2 of the note). -/
def tmplPlan : Plan n t p := fun k => S.dropPart d k ++ S.crossPart d db k ++ S.pickPart d db k

end Sched

/-! ### Routes made of blocks -/

/-- A list of blocks, each a route from where and when the previous one ends, is a route. -/
theorem chain_flatMap_finRange : ∀ (m : ℕ) (loc : ℕ → Loc n) (tm : ℕ → ℕ)
    (f : Fin m → List (Leg n t)),
    (∀ j : Fin m, IsRoute (loc j) (tm j) (f j) ∧ finalLoc (loc j) (f j) = loc (j + 1) ∧
      endTime (tm j) (f j) = tm (j + 1)) →
    IsRoute (loc 0) (tm 0) ((List.finRange m).flatMap f) ∧
      finalLoc (loc 0) ((List.finRange m).flatMap f) = loc m ∧
      endTime (tm 0) ((List.finRange m).flatMap f) = tm m
  | 0, _, _, _, _ => by simp
  | m + 1, loc, tm, f, h => by
    have ih := chain_flatMap_finRange m (fun j => loc (j + 1)) (fun j => tm (j + 1))
      (fun j => f j.succ) (fun j => by simpa using h j.succ)
    obtain ⟨h₁, h₂, h₃⟩ := h 0
    simp only [Fin.val_zero, zero_add] at h₁ h₂ h₃
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    refine ⟨(isRoute_append _ _).mpr ⟨h₁, ?_⟩, ?_, ?_⟩
    · rw [h₂, h₃]
      exact ih.1
    · rw [finalLoc_append, h₂]
      exact ih.2.1
    · rw [endTime_append, h₃]
      exact ih.2.2

theorem coe_flatMap_finRange {α : Type*} : ∀ (m : ℕ) (f : Fin m → List α),
    (((List.finRange m).flatMap f : List α) : Multiset α) = ∑ j, (f j : Multiset α)
  | 0, _ => by simp
  | m + 1, f => by
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, ← Multiset.coe_add,
      coe_flatMap_finRange m, Fin.sum_univ_succ]

theorem sum_map_flatMap_finRange {α : Type*} (g : α → ℕ) : ∀ (m : ℕ) (f : Fin m → List α),
    (((List.finRange m).flatMap f).map g).sum = ∑ j, ((f j).map g).sum
  | 0, _ => by simp
  | m + 1, f => by
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.map_append, List.sum_append,
      sum_map_flatMap_finRange g m, Fin.sum_univ_succ]

theorem sum_getElem_eq {α : Type*} {M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ j : Fin l.length, g l[j] = (l.map g).sum := by
  rw [← List.sum_ofFn]
  simp [List.ofFn_getElem_eq_map]

theorem map_finset_sum {ι α β : Type*} [Fintype ι] (s : ι → Multiset α) (g : α → β) :
    (∑ i, s i).map g = ∑ i, (s i).map g :=
  map_sum (Multiset.mapAddMonoidHom g) s univ

theorem sum_singleton_eq_map {ι α : Type*} [Fintype ι] (f : ι → α) :
    ∑ i, ({f i} : Multiset α) = univ.val.map f := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (univ.val.map f), Multiset.map_map]
  rfl

theorem univ_val_map_val (m : ℕ) : (univ : Finset (Fin m)).val.map Fin.val = Multiset.range m := by
  rw [Fin.univ_val_map]
  simp [List.ofFn_eq_map]
  rfl

theorem flies_cg_city' {N : Network n} (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.cg, .city i, e, e + N.dbar i, π⟩ : Leg n t) := ⟨_, rfl, rfl⟩

theorem flies_city_cg' {N : Network n} (i : Fin n) (e : ℕ) (π : Option (Fin t)) :
    Flies N (⟨.city i, .cg, e, e + N.dbar i, π⟩ : Leg n t) := ⟨_, rfl, rfl⟩

/-! ### Journeys `C_I → x → C_G` -/

/-- A passenger's journey `C_I → x → C_G`: its label `j`, its city `x`, and the departure
times `e` of `C_I → x` and `e'` of `x → C_G`. -/
structure TUnit (n : ℕ) where
  j : ℕ
  x : Fin n
  e : ℕ
  e' : ℕ

/-- The two legs of a journey. -/
def TUnit.legs (d db : Fin n → ℕ) (u : TUnit n) : Multiset (Leg n t) :=
  (⟨.ci, .city u.x, u.e, u.e + d u.x, pid t u.j⟩ : Leg n t) ::ₘ
    {(⟨.city u.x, .cg, u.e', u.e' + db u.x, pid t u.j⟩ : Leg n t)}

theorem TUnit.filter_legs (d db : Fin n → ℕ) (π : Fin t) (u : TUnit n) (hu : u.j < t) :
    (u.legs d db : Multiset (Leg n t)).filter (fun ℓ => ℓ.pax = some π) =
      if u.j = π.val then u.legs d db else 0 := by
  have hpid : pid t u.j = some ⟨u.j, hu⟩ := by simp [pid, hu]
  unfold TUnit.legs
  rw [hpid]
  by_cases h : u.j = π.val
  · have : (⟨u.j, hu⟩ : Fin t) = π := Fin.ext h
    rw [this]
    simp [h]
  · have : (⟨u.j, hu⟩ : Fin t) ≠ π := fun h' => h (congrArg Fin.val h')
    simp [this, h]

theorem TUnit.filter_sum_legs (d db : Fin n → ℕ) (π : Fin t) (U : Multiset (TUnit n))
    (hU : ∀ u ∈ U, u.j < t) :
    ((U.map (TUnit.legs d db)).sum : Multiset (Leg n t)).filter (fun ℓ => ℓ.pax = some π) =
      ((U.filter fun u => u.j = π.val).map (TUnit.legs d db)).sum := by
  induction U using Multiset.induction_on with
  | empty => simp
  | cons u U ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_add,
      ih fun u' hu' => hU u' (Multiset.mem_cons_of_mem hu'),
      TUnit.filter_legs d db π u (hU u (Multiset.mem_cons_self _ _)), Multiset.filter_cons]
    by_cases h : u.j = π.val <;> simp [h]

/-- **Every passenger rides its journey.** If the legs of a plan are the legs of journeys
`C_I → x → C_G` (each leaving `x` after arriving there), labelled `0, …, t − 1` once each, plus
empty legs, every passenger's legs form a route from `C_I` to `C_G`. -/
theorem pax_of_units {P : Plan n t p} (d db : Fin n → ℕ) (U : Multiset (TUnit n))
    (E : Multiset (Leg n t)) (hE : ∀ ℓ ∈ E, ℓ.pax = none)
    (hlegs : ((allLegs P : List (Leg n t)) : Multiset (Leg n t)) =
      (U.map (TUnit.legs d db)).sum + E)
    (hids : U.map TUnit.j = Multiset.range t) (htime : ∀ u ∈ U, u.e + d u.x ≤ u.e') (π : Fin t) :
    ∃ route : List (Leg n t), route.Perm (paxLegs P π) ∧ IsRoute .ci 0 route ∧
      finalLoc .ci route = .cg := by
  classical
  have hUlt : ∀ u ∈ U, u.j < t := fun u hu => by
    have : u.j ∈ U.map TUnit.j := Multiset.mem_map_of_mem _ hu
    rwa [hids, Multiset.mem_range] at this
  have hfilter : (U.filter fun u => u.j = π.val).map TUnit.j = {π.val} := by
    rw [show (U.filter fun u => u.j = π.val) = U.filter ((· = π.val) ∘ TUnit.j) from rfl,
      ← Multiset.filter_map, hids, Multiset.filter_eq',
      Multiset.count_eq_one_of_mem (Multiset.nodup_range t) (Multiset.mem_range.mpr π.isLt)]
    rfl
  obtain ⟨u, hu1, hu2⟩ := Multiset.map_eq_singleton.mp hfilter
  have huU : u ∈ U := by
    have : u ∈ U.filter fun u => u.j = π.val := by
      rw [hu1]
      exact Multiset.mem_singleton_self u
    exact (Multiset.mem_filter.mp this).1
  have hpid : pid t u.j = some π := by
    rw [hu2]
    simp [pid]
  refine ⟨[⟨.ci, .city u.x, u.e, u.e + d u.x, some π⟩,
      ⟨.city u.x, .cg, u.e', u.e' + db u.x, some π⟩],
    ?_, ⟨rfl, Nat.zero_le _, rfl, htime u huU, trivial⟩, rfl⟩
  rw [← Multiset.coe_eq_coe]
  calc _ = (u.legs d db : Multiset (Leg n t)) := by
        simp only [TUnit.legs, hpid]
        rfl
    _ = ((U.filter fun u => u.j = π.val).map (TUnit.legs d db)).sum := by rw [hu1]; simp
    _ = ((U.map (TUnit.legs d db)).sum : Multiset (Leg n t)).filter
          (fun ℓ => ℓ.pax = some π) := (TUnit.filter_sum_legs d db π U hUlt).symm
    _ = ((allLegs P : List (Leg n t)) : Multiset (Leg n t)).filter (fun ℓ => ℓ.pax = some π) := by
        rw [hlegs, Multiset.filter_add,
          show Multiset.filter (fun ℓ : Leg n t => ℓ.pax = some π) E = 0 from
            Multiset.filter_eq_nil.mpr fun ℓ hℓ h => by rw [hE ℓ hℓ] at h; cases h]
        simp only [add_zero]
    _ = _ := by rw [paxLegs, Multiset.filter_coe]

/-! ### Crossings -/

/-- The journeys of the passengers of `tCrossLegs`. -/
def tCrossUnits (t : ℕ) (d db : Fin n → ℕ) : List (Fin n) → Bool → ℕ → List ℕ → List (TUnit n)
  | [], _, _, _ => []
  | x :: xs, true, τ, ls =>
    ⟨ls.headD t, x, τ, τ + d x⟩ :: tCrossUnits t d db xs false (τ + d x + db x) ls.tail
  | x :: xs, false, τ, ls => tCrossUnits t d db xs true (τ + db x + d x) ls

section Cross

variable (d db : Fin n → ℕ)

theorem isRoute_tCrossLegs : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    IsRoute (hubOf b) τ (tCrossLegs (t := t) d db xs b τ ls)
  | [], _, _, _ => trivial
  | _ :: xs, true, _, _ => ⟨rfl, le_rfl, rfl, le_rfl, isRoute_tCrossLegs xs false _ _⟩
  | _ :: xs, false, _, _ => ⟨rfl, le_rfl, rfl, le_rfl, isRoute_tCrossLegs xs true _ _⟩

theorem finalLoc_tCrossLegs : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    finalLoc (hubOf b) (tCrossLegs (t := t) d db xs b τ ls) =
      hubOf (if Even xs.length then b else !b)
  | [], b, _, _ => by simp [tCrossLegs]
  | x :: xs, true, τ, ls => by
    simp only [tCrossLegs, finalLoc_cons]
    rw [show (Loc.cg : Loc n) = hubOf false from rfl, finalLoc_tCrossLegs xs false]
    by_cases h : Even xs.length <;> simp [h, List.length_cons, Nat.even_add_one]
  | x :: xs, false, τ, ls => by
    simp only [tCrossLegs, finalLoc_cons]
    rw [show (Loc.ci : Loc n) = hubOf true from rfl, finalLoc_tCrossLegs xs true]
    by_cases h : Even xs.length <;> simp [h, List.length_cons, Nat.even_add_one]

theorem endTime_tCrossLegs : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    endTime τ (tCrossLegs (t := t) d db xs b τ ls) = τ + (xs.map fun x => d x + db x).sum
  | [], _, τ, _ => by simp [tCrossLegs]
  | x :: xs, true, τ, ls => by
    simp only [tCrossLegs, endTime_cons, endTime_tCrossLegs xs false, List.map_cons, List.sum_cons]
    ring
  | x :: xs, false, τ, ls => by
    simp only [tCrossLegs, endTime_cons, endTime_tCrossLegs xs true, List.map_cons, List.sum_cons]
    ring

theorem landCost_tCrossLegs (c : Fin n → ℕ) : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ)
    (ls : List ℕ), ((tCrossLegs (t := t) d db xs b τ ls).map (landCost c)).sum = (xs.map c).sum
  | [], _, _, _ => rfl
  | x :: xs, true, τ, ls => by
    simp [tCrossLegs, landCost, landCost_tCrossLegs c xs false]
  | x :: xs, false, τ, ls => by
    simp [tCrossLegs, landCost, landCost_tCrossLegs c xs true]

theorem legs_tCrossLegs : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((tCrossLegs (t := t) d db xs b τ ls : List (Leg n t)) : Multiset (Leg n t)) =
        ((tCrossUnits t d db xs b τ ls).map (TUnit.legs d db)).sum + E
  | [], _, _, _ => ⟨0, by simp, by simp [tCrossLegs, tCrossUnits]⟩
  | x :: xs, true, τ, ls => by
    obtain ⟨E, hE, h⟩ := legs_tCrossLegs xs false (τ + d x + db x) ls.tail
    refine ⟨E, hE, ?_⟩
    simp only [tCrossLegs, tCrossUnits, List.map_cons, List.sum_cons, ← Multiset.cons_coe, h,
      TUnit.legs]
    simp [Multiset.cons_add, Multiset.singleton_add]
  | x :: xs, false, τ, ls => by
    obtain ⟨E, hE, h⟩ := legs_tCrossLegs xs true (τ + db x + d x) ls
    refine ⟨⟨.cg, .city x, τ, τ + db x, none⟩ ::ₘ
      ⟨.city x, .ci, τ + db x, τ + db x + d x, none⟩ ::ₘ E,
      fun ℓ hℓ => ?_, ?_⟩
    · simp only [Multiset.mem_cons] at hℓ
      rcases hℓ with rfl | rfl | hℓ
      · rfl
      · rfl
      · exact hE ℓ hℓ
    · simp only [tCrossLegs, tCrossUnits, ← Multiset.cons_coe, h]
      simp [Multiset.add_cons]

theorem tCrossUnits_ids : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    ls.length = (if b then (xs.length + 1) / 2 else xs.length / 2) →
    (tCrossUnits t d db xs b τ ls).map TUnit.j = ls
  | [], b, _, ls, h => by
    cases b <;> simp_all [tCrossUnits]
  | x :: xs, true, τ, ls, h => by
    obtain ⟨l, ls', rfl⟩ : ∃ l ls', ls = l :: ls' :=
      List.exists_cons_of_length_pos (by simp at h; omega)
    simp only [tCrossUnits, List.map_cons, List.headD_cons, List.tail_cons]
    rw [tCrossUnits_ids xs false _ ls' (by simp at h ⊢; omega)]
  | x :: xs, false, τ, ls, h => by
    simp only [tCrossUnits]
    exact tCrossUnits_ids xs true _ ls (by simp at h ⊢; omega)

theorem tCrossUnits_time : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    ∀ u ∈ tCrossUnits t d db xs b τ ls, u.e + d u.x ≤ u.e'
  | [], _, _, _ => by simp [tCrossUnits]
  | x :: xs, true, τ, ls => by
    intro u hu
    simp only [tCrossUnits, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_rfl
    · exact tCrossUnits_time xs false _ _ u hu
  | x :: xs, false, τ, ls => fun u hu => tCrossUnits_time xs true _ _ u hu

end Cross

theorem flies_tCrossLegs {N : Network n} : ∀ (xs : List (Fin n)) (b : Bool) (τ : ℕ) (ls : List ℕ),
    ∀ ℓ ∈ (tCrossLegs (t := t) N.d N.dbar xs b τ ls), Flies N ℓ
  | [], _, _, _ => by simp [tCrossLegs]
  | x :: xs, true, τ, ls => by
    intro ℓ hℓ
    simp only [tCrossLegs, List.mem_cons] at hℓ
    rcases hℓ with rfl | rfl | hℓ
    · exact flies_ci_city x τ _
    · exact flies_city_cg' x _ _
    · exact flies_tCrossLegs xs false _ _ ℓ hℓ
  | x :: xs, false, τ, ls => by
    intro ℓ hℓ
    simp only [tCrossLegs, List.mem_cons] at hℓ
    rcases hℓ with rfl | rfl | hℓ
    · exact flies_cg_city' x τ _
    · exact flies_city_ci x _ _
    · exact flies_tCrossLegs xs true _ _ ℓ hℓ

namespace Sched

variable (S : Sched n p) (d db : Fin n → ℕ)

/-! ### Drop-offs -/

theorem pre_zero (k : Fin p) : S.pre d k 0 = 0 := by simp [pre]

theorem pre_succ (k : Fin p) (j : ℕ) (hj : j < (S.drops k).length) :
    S.pre d k (j + 1) = S.pre d k j + d (S.drops k)[j] + d (S.drops k)[j] := by
  simp only [pre, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem pre_length (k : Fin p) : S.pre d k (S.drops k).length = 2 * ((S.drops k).map d).sum := by
  simp [pre]

theorem dropPart_chain (k : Fin p) :
    IsRoute .ci 0 (S.dropPart (t := t) d k) ∧ finalLoc .ci (S.dropPart (t := t) d k) = .ci ∧
      endTime 0 (S.dropPart (t := t) d k) = 2 * ((S.drops k).map d).sum := by
  have h := chain_flatMap_finRange _ (fun _ => (.ci : Loc n)) (S.pre d k) (S.dropBlock (t := t) d k)
    fun j => ⟨⟨rfl, le_rfl, rfl, le_rfl, trivial⟩, rfl, by
      simp only [dropBlock, dropCarryLeg, endTime_cons, endTime_nil, Fin.getElem_fin]
      rw [S.pre_succ d k j j.isLt]⟩
  rw [S.pre_zero, S.pre_length] at h
  exact h

theorem flies_dropPart {N : Network n} (k : Fin p) :
    ∀ ℓ ∈ (S.dropPart (t := t) N.d k), Flies N ℓ := by
  intro ℓ hℓ
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hℓ
  simp only [dropBlock, dropCarryLeg, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact flies_ci_city _ _ _
  · exact flies_city_ci _ _ _

theorem landCost_dropPart (c : Fin n → ℕ) (k : Fin p) :
    ((S.dropPart (t := t) d k).map (landCost c)).sum = ((S.drops k).map c).sum := by
  rw [dropPart, sum_map_flatMap_finRange, ← sum_getElem_eq]
  simp [dropBlock, dropCarryLeg, landCost]

theorem coe_dropPart (k : Fin p) :
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((S.dropPart (t := t) d k : List (Leg n t)) : Multiset (Leg n t)) =
        ∑ j, {S.dropCarryLeg d k j} + E := by
  refine ⟨∑ j : Fin (S.drops k).length,
      {(⟨.city (S.drops k)[j], .ci, S.pre d k j + d (S.drops k)[j],
        S.pre d k j + d (S.drops k)[j] + d (S.drops k)[j], none⟩ : Leg n t)},
    fun ℓ hℓ => ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Multiset.mem_sum.mp hℓ
    rw [Multiset.mem_singleton] at hj
    rw [hj]
  · rw [dropPart, coe_flatMap_finRange, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dropBlock, ← Multiset.cons_coe, Multiset.singleton_add]
    rfl

/-! ### Crossings -/

theorem length_crossList (k : Fin p) : (S.crossList k).length = (S.cross k).card := by
  simp [crossList]

theorem sum_crossList (f : Fin n → ℕ) (k : Fin p) :
    ((S.crossList k).map f).sum = ((S.cross k).map f).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, crossList, Multiset.sort_eq]

theorem length_xLabs (k : Fin p) : (S.xLabs k).length = S.nCarry k := by simp [xLabs]

/-! ### Pick-ups -/

theorem pickDur_eq (k : Fin p) (l : ℕ) (hl : l < (S.picks k).length) :
    S.pickDur db k l = db (S.picks k)[l] := by
  simp [pickDur, List.getElem?_eq_getElem hl]

theorem pickPart_chain (k : Fin p) :
    IsRoute .cg (S.crossEnd d db k) (S.pickPart (t := t) d db k) ∧
      finalLoc .cg (S.pickPart (t := t) d db k) = .cg ∧
      endTime (S.crossEnd d db k) (S.pickPart (t := t) d db k) =
        S.pickTime d db k (S.picks k).length :=
  chain_flatMap_finRange _ (fun _ => (.cg : Loc n)) (S.pickTime d db k)
    (S.pickBlock (t := t) d db k)
    fun l => ⟨⟨rfl, le_rfl, rfl, le_max_left _ _, trivial⟩, rfl, by
      simp only [pickBlock, pickCarryLeg, pickLeave, endTime_cons, endTime_nil, pickTime,
        S.pickDur_eq db k l l.isLt, Fin.getElem_fin]⟩

theorem flies_pickPart {N : Network n} (k : Fin p) :
    ∀ ℓ ∈ (S.pickPart (t := t) N.d N.dbar k), Flies N ℓ := by
  intro ℓ hℓ
  obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hℓ
  simp only [pickBlock, pickCarryLeg, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact flies_cg_city' _ _ _
  · exact flies_city_cg' _ _ _

theorem landCost_pickPart (c : Fin n → ℕ) (k : Fin p) :
    ((S.pickPart (t := t) d db k).map (landCost c)).sum = ((S.picks k).map c).sum := by
  rw [pickPart, sum_map_flatMap_finRange, ← sum_getElem_eq]
  simp [pickBlock, pickCarryLeg, landCost]

theorem coe_pickPart (k : Fin p) :
    ∃ E : Multiset (Leg n t), (∀ ℓ ∈ E, ℓ.pax = none) ∧
      ((S.pickPart (t := t) d db k : List (Leg n t)) : Multiset (Leg n t)) =
        ∑ l, {S.pickCarryLeg d db k l} + E := by
  refine ⟨∑ l : Fin (S.picks k).length, {(⟨.cg, .city (S.picks k)[l], S.pickTime d db k l,
      S.pickTime d db k l + db (S.picks k)[l], none⟩ : Leg n t)}, fun ℓ hℓ => ?_, ?_⟩
  · obtain ⟨l, -, hl⟩ := Multiset.mem_sum.mp hℓ
    rw [Multiset.mem_singleton] at hl
    rw [hl]
  · rw [pickPart, coe_flatMap_finRange, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [pickBlock, ← Multiset.cons_coe, Multiset.singleton_add]
    exact Multiset.cons_swap _ _ _

/-! ### The makespan of a plane -/

/-- `φ_k(l) + Suf_k(l − 1)`: when plane `k` would finish if it never waited after its `l`-th
pick-up. -/
def slack (k : Fin p) (l : ℕ) : ℕ :=
  S.pickTime d db k l + 2 * (((S.picks k).drop l).map db).sum

theorem slack_zero (k : Fin p) : S.slack d db k 0 = S.load d db k := by
  simp only [slack, pickTime, crossEnd, List.drop_zero, load, S.sum_crossList, Multiset.sum_map_add]
  simp only [ZenoFront.load]
  ring

theorem slack_length (k : Fin p) :
    S.slack d db k (S.picks k).length = S.pickTime d db k (S.picks k).length := by
  simp [slack]

/-- `φ_k(l + 1) + Suf_k(l) = max(φ_k(l) + Suf_k(l − 1), term of the link into (k, l))`. -/
theorem slack_succ (k : Fin p) (l : ℕ) (hl : l < (S.picks k).length) :
    S.slack d db k (l + 1) = max (S.slack d db k l) (S.term d db k ⟨l, hl⟩) := by
  simp only [slack, term, suf, pickTime, S.pickDur_eq db k l hl, pickAvail, hl, ↓reduceDIte,
    List.drop_eq_getElem_cons hl, List.map_cons, List.sum_cons, Fin.getElem_fin]
  simp only [max_def]
  split_ifs <;> omega

theorem slack_mono (k : Fin p) : ∀ (m i : ℕ), m + i ≤ (S.picks k).length →
    S.slack d db k m ≤ S.slack d db k (m + i)
  | _, 0, _ => le_rfl
  | m, i + 1, h => by
    rw [← add_assoc, S.slack_succ d db k (m + i) (by omega)]
    exact (slack_mono k m i (by omega)).trans (le_max_left _ _)

theorem pickTime_length_eq (k : Fin p) :
    S.pickTime d db k (S.picks k).length =
      max (S.load d db k) (univ.sup fun l => S.term d db k l) := by
  apply le_antisymm
  · rw [← S.slack_length]
    have : ∀ m ≤ (S.picks k).length,
        S.slack d db k m ≤ max (S.load d db k) (univ.sup fun l => S.term d db k l) := by
      intro m
      induction m with
      | zero => intro _; rw [S.slack_zero]; exact le_max_left _ _
      | succ m ih =>
        intro hm
        rw [S.slack_succ d db k m (by omega)]
        exact max_le (ih (by omega)) ((Finset.le_sup (f := fun l => S.term d db k l)
          (Finset.mem_univ ⟨m, by omega⟩)).trans (le_max_right _ _))
    exact this _ le_rfl
  · rw [← S.slack_length]
    refine max_le ?_ (Finset.sup_le fun l _ => ?_)
    · rw [← S.slack_zero]
      simpa using S.slack_mono d db k 0 (S.picks k).length (by omega)
    · have h₁ : S.term d db k l ≤ S.slack d db k (l + 1) := by
        rw [S.slack_succ d db k l l.isLt]
        exact le_max_right _ _
      exact h₁.trans (by
        simpa [show (l : ℕ) + 1 + ((S.picks k).length - (l + 1)) = (S.picks k).length by omega]
          using S.slack_mono d db k (l + 1) ((S.picks k).length - (l + 1)) (by omega))

/-! ### Planes -/

theorem tmplPlan_chain (k : Fin p) (hodd : Odd (S.cross k).card) :
    IsRoute .ci 0 (S.tmplPlan (t := t) d db k) ∧ finalLoc .ci (S.tmplPlan (t := t) d db k) = .cg ∧
      endTime 0 (S.tmplPlan (t := t) d db k) = S.pickTime d db k (S.picks k).length := by
  obtain ⟨hd₁, hd₂, hd₃⟩ := S.dropPart_chain (t := t) d k
  obtain ⟨hp₁, hp₂, hp₃⟩ := S.pickPart_chain (t := t) d db k
  have hlen : ¬ Even (S.crossList k).length := by
    rw [S.length_crossList]
    exact Nat.not_even_iff_odd.mpr hodd
  have hc₂ := finalLoc_tCrossLegs (t := t) d db (S.crossList k) true
    (2 * ((S.drops k).map d).sum) (S.xLabs k)
  simp only [hlen, ↓reduceIte, Bool.not_true] at hc₂
  have hc₃ := endTime_tCrossLegs (t := t) d db (S.crossList k) true
    (2 * ((S.drops k).map d).sum) (S.xLabs k)
  have hAB₂ : finalLoc .ci (S.dropPart (t := t) d k ++ S.crossPart (t := t) d db k) = .cg := by
    rw [finalLoc_append, hd₂]
    exact hc₂
  have hAB₃ : endTime 0 (S.dropPart (t := t) d k ++ S.crossPart (t := t) d db k) =
      S.crossEnd d db k := by
    rw [endTime_append, hd₃]
    exact hc₃
  refine ⟨(isRoute_append _ _).mpr ⟨(isRoute_append _ _).mpr ⟨hd₁, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [hd₂, hd₃]
    exact isRoute_tCrossLegs d db _ true _ _
  · rw [hAB₂, hAB₃]
    exact hp₁
  · simp only [tmplPlan]
    rw [finalLoc_append, hAB₂]
    exact hp₂
  · simp only [tmplPlan]
    rw [endTime_append, hAB₃]
    exact hp₃

theorem landCost_tmplPlan (c : Fin n → ℕ) (k : Fin p) :
    ((S.tmplPlan (t := t) d db k).map (landCost c)).sum =
      ((S.drops k).map c).sum + ((S.picks k).map c).sum + ZenoFront.cost c (S.cross k) := by
  simp only [tmplPlan, crossPart, List.map_append, List.sum_append, S.landCost_dropPart,
    S.landCost_pickPart, landCost_tCrossLegs, S.sum_crossList, ZenoFront.cost]
  ring

/-! ### Lemma 6.3 -/

variable {S}

theorem Valid.two_mul_nCarry (hv : S.Valid) (k : Fin p) :
    2 * S.nCarry k = (S.cross k).card + 1 := by
  obtain ⟨m, hm⟩ := hv.odd k
  simp only [nCarry, hm]
  omega

/-- A valid configuration with `2t − p` landings carries exactly `t` passengers, and `p ≤ t`. -/
theorem Valid.count_eq (hv : S.Valid) (hsize : S.size = 2 * t - p) :
    S.nDrops + S.nCross = t ∧ p ≤ t := by
  have h₁ : 2 * S.nCross = ∑ k, (S.cross k).card + p := by
    simp only [nCross, Finset.mul_sum, hv.two_mul_nCarry, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have h₂ : p ≤ S.nCross := by
    calc p = ∑ _k : Fin p, 1 := by simp
      _ ≤ S.nCross := Finset.sum_le_sum fun k _ => by have := hv.two_mul_nCarry k; omega
  have h₃ : S.size = 2 * S.nDrops + ∑ k, (S.cross k).card := by
    simp only [size, Finset.sum_add_distrib, nDrops]
    rw [← hv.count]
    ring
  omega

theorem Valid.mate_lt (hv : S.Valid) (v : Fin p) (l : Fin (S.picks v).length) :
    (S.mate v l).2 < (S.drops (S.mate v l).1).length := by
  have h := hv.city v l l.isLt
  rw [List.getElem?_eq_getElem l.isLt] at h
  exact (List.getElem?_eq_some_iff.mp h).1

theorem Valid.mate_city (hv : S.Valid) (v : Fin p) (l : Fin (S.picks v).length) :
    (S.drops (S.mate v l).1)[(S.mate v l).2]'(hv.mate_lt v l) = (S.picks v)[l] := by
  have h := hv.city v l l.isLt
  rw [List.getElem?_eq_getElem l.isLt, List.getElem?_eq_getElem (hv.mate_lt v l)] at h
  exact Option.some.inj h

/-- The matching of a valid configuration, from the pick-up slots to the drop-off slots. -/
def Valid.slot (hv : S.Valid) (ps : S.PSlot) : S.DSlot :=
  ⟨(S.mate ps.1 ps.2).1, ⟨(S.mate ps.1 ps.2).2, hv.mate_lt ps.1 ps.2⟩⟩

/-- The matching is a bijection from the pick-up slots onto the drop-off slots. -/
theorem Valid.slot_bijective (hv : S.Valid) : Function.Bijective hv.slot := by
  refine (Fintype.bijective_iff_injective_and_card hv.slot).mpr ⟨?_, ?_⟩
  · rintro ⟨v, l⟩ ⟨v', l'⟩ h
    have h₁ : (S.mate v l).1 = (S.mate v' l').1 := congrArg Sigma.fst h
    have h₂ : (S.mate v l).2 = (S.mate v' l').2 := congrArg (fun s : S.DSlot => (s.2 : ℕ)) h
    obtain ⟨rfl, hl⟩ := hv.inj v l v' l' l.isLt l'.isLt (Prod.ext h₁ h₂)
    obtain rfl : l = l' := Fin.ext hl
    rfl
  · simp only [Fintype.card_sigma, Fintype.card_fin]
    exact hv.count.symm

/-- **Lemma 6.3 (template), achievability.** For every valid scheduled configuration with
`2t − p` landings, the template is a feasible plan whose cost is the configuration's and whose
makespan is the closed form `M_tmpl`. Nothing is assumed on the durations (zero durations
included) or on the central flights, which the template does not use. -/
theorem tmplPlan_spec {N : Network n} (c : Fin n → ℕ) (hv : S.Valid)
    (hsize : S.size = 2 * t - p) :
    Feasible N (S.tmplPlan (t := t) N.d N.dbar) ∧
      planCost c (S.tmplPlan (t := t) N.d N.dbar) = S.cost c ∧
      planMakespan (S.tmplPlan (t := t) N.d N.dbar) = S.tmpl N.d N.dbar := by
  classical
  obtain ⟨hcount, -⟩ := hv.count_eq hsize
  set P : Plan n t p := S.tmplPlan N.d N.dbar with hP
  have hchain := fun k => S.tmplPlan_chain (t := t) N.d N.dbar k (hv.odd k)
  -- The matching, as a bijection from the pick-up slots onto the drop-off slots.
  let e : S.PSlot → S.DSlot := hv.slot
  have hcity := hv.mate_city
  let eqv := Equiv.ofBijective e hv.slot_bijective
  -- The journeys: one per link, and the crossing passengers.
  let link : S.PSlot → TUnit n := fun ps =>
    ⟨S.dropLab (e ps).1 (e ps).2, (S.drops (e ps).1)[(e ps).2], S.pre N.d (e ps).1 (e ps).2,
      S.pickLeave N.d N.dbar ps.1 ps.2⟩
  let cu : Fin p → List (TUnit n) := fun k =>
    tCrossUnits t N.d N.dbar (S.crossList k) true (2 * ((S.drops k).map N.d).sum) (S.xLabs k)
  let U : Multiset (TUnit n) := ∑ ps, {link ps} + ∑ k, (cu k : Multiset (TUnit n))
  have hlink : ∀ ps, ((link ps).legs N.d N.dbar : Multiset (Leg n t)) =
      {S.dropCarryLeg N.d (e ps).1 (e ps).2} + {S.pickCarryLeg N.d N.dbar ps.1 ps.2} := by
    rintro ⟨v, l⟩
    have hc := hcity v l
    simp only [TUnit.legs, link, e, Valid.slot, dropCarryLeg, pickCarryLeg, Multiset.singleton_add,
      Fin.getElem_fin]
    rw [hc]
    rfl
  -- The legs of each plane.
  choose Ed hEd hd using fun k => S.coe_dropPart (t := t) N.d k
  choose Ex hEx hx using fun k => legs_tCrossLegs (t := t) N.d N.dbar (S.crossList k) true
    (2 * ((S.drops k).map N.d).sum) (S.xLabs k)
  choose Ep hEp hpk using fun k => S.coe_pickPart (t := t) N.d N.dbar k
  have hlegs : ((allLegs P : List (Leg n t)) : Multiset (Leg n t)) =
      (U.map (TUnit.legs N.d N.dbar)).sum + ∑ k, (Ed k + Ex k + Ep k) := by
    have hA : ∑ ps : S.PSlot, ({S.dropCarryLeg N.d (e ps).1 (e ps).2} : Multiset (Leg n t)) =
        ∑ k, ∑ j, {S.dropCarryLeg N.d k j} :=
      (Fintype.sum_equiv eqv _ (fun ds => {S.dropCarryLeg N.d ds.1 ds.2}) fun _ => rfl).trans
        (Fintype.sum_sigma fun ds : S.DSlot => ({S.dropCarryLeg N.d ds.1 ds.2} : Multiset _))
    have hB : ∑ ps : S.PSlot, ({S.pickCarryLeg N.d N.dbar ps.1 ps.2} : Multiset (Leg n t)) =
        ∑ k, ∑ l, {S.pickCarryLeg N.d N.dbar k l} :=
      Fintype.sum_sigma fun ps : S.PSlot => ({S.pickCarryLeg N.d N.dbar ps.1 ps.2} : Multiset _)
    have hU : (U.map (TUnit.legs N.d N.dbar)).sum = ∑ ps, ((link ps).legs N.d N.dbar) +
        ∑ k, (((cu k).map (TUnit.legs N.d N.dbar)).sum : Multiset (Leg n t)) := by
      simp only [U, Multiset.map_add, map_finset_sum, Multiset.map_singleton, Multiset.sum_add,
        Multiset.sum_sum, Multiset.sum_singleton, Multiset.map_coe, Multiset.sum_coe]
    rw [hU, Finset.sum_congr rfl fun ps _ => hlink ps, Finset.sum_add_distrib, hA, hB,
      show allLegs P = (List.finRange p).flatMap P from rfl, coe_flatMap_finRange]
    have hk : ∀ k, ((P k : List (Leg n t)) : Multiset (Leg n t)) =
        (∑ j, {S.dropCarryLeg N.d k j} + Ed k) +
          ((((cu k).map (TUnit.legs N.d N.dbar)).sum : Multiset (Leg n t)) + Ex k) +
          (∑ l, {S.pickCarryLeg N.d N.dbar k l} + Ep k) := fun k => by
      rw [← hd k, ← hx k, ← hpk k]
      simp only [hP, tmplPlan, crossPart, ← Multiset.coe_add]
    simp only [hk, Finset.sum_add_distrib]
    abel
  have hids : U.map TUnit.j = Multiset.range t := by
    have hcu : ∀ k, (cu k).map TUnit.j = S.xLabs k := fun k =>
      tCrossUnits_ids N.d N.dbar _ true _ _ (by
        simp only [S.length_xLabs, S.length_crossList, nCarry, ↓reduceIte])
    have hL : ∀ ps, (link ps).j = (S.labelEquiv (.inl (e ps)) : ℕ) := fun ps => by
      simp only [link, dropLab, (e ps).2.isLt, ↓reduceDIte]
    have hX : ∀ k, ((S.xLabs k : List ℕ) : Multiset ℕ) =
        ∑ i : Fin (S.nCarry k), {(S.labelEquiv (.inr ⟨k, i⟩) : ℕ)} := fun k => by
      rw [sum_singleton_eq_map, Fin.univ_val_map]
      rfl
    have h₁ : ∑ ps, ({(S.labelEquiv (.inl (e ps)) : ℕ)} : Multiset ℕ) =
        ∑ ds, {(S.labelEquiv (.inl ds) : ℕ)} :=
      Fintype.sum_equiv eqv _ (fun ds => {(S.labelEquiv (.inl ds) : ℕ)}) fun _ => rfl
    have h₂ : ∑ k, ∑ i : Fin (S.nCarry k), ({(S.labelEquiv (.inr ⟨k, i⟩) : ℕ)} : Multiset ℕ) =
        ∑ xs, {(S.labelEquiv (.inr xs) : ℕ)} :=
      (Fintype.sum_sigma fun xs : S.XSlot => ({(S.labelEquiv (.inr xs) : ℕ)} : Multiset ℕ)).symm
    simp only [U, Multiset.map_add, map_finset_sum, Multiset.map_singleton, Multiset.map_coe, hcu,
      hL, hX]
    rw [h₁, h₂, ← Fintype.sum_sum_type (fun s => ({(S.labelEquiv s : ℕ)} : Multiset ℕ)),
      sum_singleton_eq_map,
      show (fun s => (S.labelEquiv s : ℕ)) = Fin.val ∘ S.labelEquiv from rfl,
      ← Multiset.map_map Fin.val, Multiset.map_univ_val_equiv, univ_val_map_val, hcount]
  have htime : ∀ u ∈ U, u.e + N.d u.x ≤ u.e' := by
    intro u hu
    rcases Multiset.mem_add.mp hu with hu | hu
    · obtain ⟨⟨v, l⟩, -, hl⟩ := Multiset.mem_sum.mp hu
      rw [Multiset.mem_singleton] at hl
      subst hl
      have hc := hcity v l
      simp only [link, e, Valid.slot, pickLeave, pickAvail, l.isLt, ↓reduceDIte,
        Fin.getElem_fin] at hc ⊢
      rw [hc]
      exact le_max_right _ _
    · obtain ⟨k, -, hk⟩ := Multiset.mem_sum.mp hu
      exact tCrossUnits_time N.d N.dbar _ _ _ _ u (Multiset.mem_coe.mp hk)
  refine ⟨⟨fun k => ⟨fun ℓ hℓ => ?_, (hchain k).1, (hchain k).2.1⟩, fun π =>
    pax_of_units N.d N.dbar U _ (fun ℓ hℓ => ?_) hlegs hids htime π⟩, ?_, ?_⟩
  · simp only [hP, tmplPlan, crossPart, List.mem_append] at hℓ
    rcases hℓ with (hℓ | hℓ) | hℓ
    · exact S.flies_dropPart k ℓ hℓ
    · exact flies_tCrossLegs _ _ _ _ ℓ hℓ
    · exact S.flies_pickPart k ℓ hℓ
  · obtain ⟨k, -, hk⟩ := Multiset.mem_sum.mp hℓ
    rcases Multiset.mem_add.mp hk with hk | hk
    · rcases Multiset.mem_add.mp hk with hk | hk
      · exact hEd k ℓ hk
      · exact hEx k ℓ hk
    · exact hEp k ℓ hk
  · simp only [planCost, hP, landCost_tmplPlan, Sched.cost]
  · have hend : ∀ k, endTime 0 (P k) = max (S.load N.d N.dbar k)
        (univ.sup fun l => S.term N.d N.dbar k l) := fun k => by
      rw [hP, (hchain k).2.2, S.pickTime_length_eq]
    simp only [planMakespan, hend, tmpl]
    exact Finset.sup_sup (f := fun k => S.load N.d N.dbar k)
      (g := fun v => univ.sup fun l => S.term N.d N.dbar v l)

/-- **Lemma 6.3, existence form.** Every valid scheduled configuration with `2t − p` landings
has a feasible plan of the same cost whose makespan is `M_tmpl`. -/
theorem exists_plan {N : Network n} (c : Fin n → ℕ) (hv : S.Valid) (hsize : S.size = 2 * t - p) :
    ∃ P : Plan n t p, Feasible N P ∧ planCost c P = S.cost c ∧
      planMakespan P = S.tmpl N.d N.dbar :=
  ⟨_, tmplPlan_spec c hv hsize⟩

end Sched

end ZenoFront
