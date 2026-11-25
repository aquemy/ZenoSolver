/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SchedBuild

/-!
# Step 2 of Theorem 5.3: exchanges, cuts and splices

Step 2 of Theorem 5.3 rearranges the visits of the planes until every hand-off is ordered in time.
Exchanging futures alone does not suffice: a passenger can be handed backwards on one plane, but
only at an instant and at a city with `d = d̄ = 0` (the route and the journey squeeze every leg
between its two flights to one time). This file proves Step 2 for every plan (§5 of the note),
with routes ordered by time only (`TRoute`) and *loops*: closed chains of visits whose legs all
depart and arrive at one time `τ` (`TLoop`).

Three moves, each carrying one more passenger through (`tThrough` grows, `tVisits` is kept):

* `tExchange_step`: a hand-off between two planes overlaps in time; they exchange futures.
* `tCut_step`: a hand-off goes backwards on one route; the closed zero-time walk between its two
  flights is cut out as a loop, and the passenger rides through its visit `(ℓα π, ℓβ π)`.
* `tSplice_step`: a hand-off between a loop at time `τ` and a route visit `δ` with
  `a(δ) ≤ τ ≤ e(δ)`; the loop is spliced into the route at `δ`, so the passenger rides through.

**Step 2** (`exists_rewired`): routes and loops with the legs of the plan in which every passenger
is carried through, or every visit entered by its first flight is left no later than every visit
left by its second flight is entered.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ} {K : Type}

/-! ### Chains of visits, by time only -/

/-- The state of a plane, by time only: its hub, and the time it is free. -/
abbrev TState (n : ℕ) := Loc n × ℕ

/-- The state after a visit. -/
def Visit.tnext (v : Visit n t K) : TState n := (v.2.leg.dst, v.2.leg.arr)

/-- A visit can be flown from state `s`. -/
structure TOK (N : Network n) (s : TState n) (v : Visit n t K) : Prop where
  src : v.1.leg.src = s.1
  time : s.2 ≤ v.1.leg.dep
  loc : LocOK N v

/-- A chain of visits from state `s`, by time only. -/
def TChain (N : Network n) : TState n → List (Visit n t K) → Prop
  | _, [] => True
  | s, v :: rest => TOK N s v ∧ TChain N v.tnext rest

/-- The state at the end of a chain. -/
def tEnd : TState n → List (Visit n t K) → TState n
  | s, [] => s
  | _, v :: rest => tEnd v.tnext rest

/-- A route by time only: a chain from `C_I` at time `0` that ends in `C_G`. -/
def TRoute (N : Network n) (L : List (Visit n t K)) : Prop :=
  TChain N (.ci, 0) L ∧ (tEnd (.ci, 0) L).1 = .cg

/-- Every leg of a visit departs and arrives at time `τ`. -/
def Visit.AtTime (τ : ℕ) (v : Visit n t K) : Prop :=
  v.1.leg.dep = τ ∧ v.1.leg.arr = τ ∧ v.2.leg.dep = τ ∧ v.2.leg.arr = τ

/-- A loop: a non-empty closed chain of visits all at time `τ`. -/
def TLoop (N : Network n) (τ : ℕ) (L : List (Visit n t K)) : Prop :=
  L ≠ [] ∧ (∀ v ∈ L, v.AtTime τ) ∧ ∃ h, TChain N (h, τ) L ∧ (tEnd (h, τ) L).1 = h

@[simp] theorem tChain_nil (N : Network n) (s : TState n) :
    TChain N s ([] : List (Visit n t K)) := trivial

@[simp] theorem tChain_cons (N : Network n) (s : TState n) (v : Visit n t K)
    (rest : List (Visit n t K)) : TChain N s (v :: rest) ↔ TOK N s v ∧ TChain N v.tnext rest :=
  Iff.rfl

@[simp] theorem tEnd_nil (s : TState n) : tEnd s ([] : List (Visit n t K)) = s := rfl

@[simp] theorem tEnd_cons (s : TState n) (v : Visit n t K) (rest : List (Visit n t K)) :
    tEnd s (v :: rest) = tEnd v.tnext rest := rfl

theorem tChain_append (N : Network n) : ∀ (s : TState n) (A B : List (Visit n t K)),
    TChain N s (A ++ B) ↔ TChain N s A ∧ TChain N (tEnd s A) B
  | _, [], _ => by simp
  | s, v :: A, B => by
    simp only [List.cons_append, tChain_cons, tEnd_cons, tChain_append N v.tnext A B]
    tauto

theorem tEnd_append : ∀ (s : TState n) (A B : List (Visit n t K)),
    tEnd s (A ++ B) = tEnd (tEnd s A) B
  | _, [], _ => rfl
  | _, v :: A, B => tEnd_append v.tnext A B

theorem TChain.loc {N : Network n} : ∀ {s : TState n} {L : List (Visit n t K)}, TChain N s L →
    ∀ v ∈ L, LocOK N v
  | _, [], _, _, h => absurd h List.not_mem_nil
  | _, w :: L, ⟨hw, hL⟩, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw.loc
    · exact hL.loc v hv

theorem LocOK.dep_le_arr₁ {N : Network n} {v : Visit n t K} (h : LocOK N v) :
    v.1.leg.dep ≤ v.1.leg.arr := h.flies₁.dep_le_arr

theorem LocOK.dep_le_arr₂ {N : Network n} {v : Visit n t K} (h : LocOK N v) :
    v.2.leg.dep ≤ v.2.leg.arr := h.flies₂.dep_le_arr

/-- Along a chain, every visit comes after the state. -/
theorem TChain.le_of_mem {N : Network n} : ∀ {s : TState n} {L : List (Visit n t K)},
    TChain N s L → ∀ v ∈ L, s.2 ≤ v.1.leg.dep
  | _, [], _, _, h => absurd h List.not_mem_nil
  | _, w :: L, ⟨hw, hL⟩, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw.time
    · have h₁ := hL.le_of_mem v hv
      simp only [Visit.tnext] at h₁
      exact hw.time.trans (hw.loc.dep_le_arr₁.trans (hw.loc.wait.trans
        (hw.loc.dep_le_arr₂.trans h₁)))

/-- Along a chain, an earlier visit is left before a later one is entered. -/
theorem TChain.le_of_lt {N : Network n} {s : TState n} {L : List (Visit n t K)}
    (h : TChain N s L) {i j : ℕ} (hij : i < j) (hj : j < L.length) :
    L[i].2.leg.arr ≤ L[j].1.leg.dep := by
  have hL : L = L.take (i + 1) ++ L.drop (i + 1) := (List.take_append_drop _ _).symm
  rw [hL, tChain_append] at h
  have hend : tEnd s (L.take (i + 1)) = L[i].tnext := by
    have : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem (by omega)
    rw [this, tEnd_append]
    rfl
  have hmem : L[j] ∈ L.drop (i + 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨j - (i + 1), by simp; omega, by simp; congr 1; omega⟩
  rw [hend] at h
  exact h.2.le_of_mem _ hmem

/-- The time of the end of a chain of visits at time `τ`. -/
theorem tEnd_snd_of_atTime : ∀ {s : TState n} {τ : ℕ} {L : List (Visit n t K)}, s.2 = τ →
    (∀ v ∈ L, v.AtTime τ) → (tEnd s L).2 = τ
  | _, _, [], hs, _ => hs
  | _, _, v :: L, _, hL => tEnd_snd_of_atTime (s := v.tnext) (L := L) (hL v List.mem_cons_self).2.2.2
      fun w hw => hL w (List.mem_cons_of_mem _ hw)

/-! ### Routes and loops -/

/-- All legs of routes `R` and loops `Q`. -/
def tLegs (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K))) :
    Multiset (KLeg n t K) :=
  allK R + (Q.map fun q => (legsOf q.2 : Multiset (KLeg n t K))).sum

/-- The number of visits of routes and loops. -/
def tVisits (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K))) : ℕ :=
  visitCount R + (Q.map fun q => q.2.length).sum

/-- A visit of a route or of a loop. -/
def InV (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K)))
    (w : Visit n t K) : Prop :=
  (∃ k, w ∈ R k) ∨ ∃ q ∈ Q, w ∈ q.2

variable [LinearOrder K]

/-- The number of visits of routes and loops that carry their passenger through. -/
def tThrough (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) : ℕ :=
  throughCount ℓα ℓβ R + (Q.map fun q => q.2.countP (isThrough ℓα ℓβ)).sum

theorem tThrough_le (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) : tThrough ℓα ℓβ R Q ≤ tVisits R Q := by
  have h₁ := throughCount_le ℓα ℓβ R
  have h₂ : (Q.map fun q => q.2.countP (isThrough ℓα ℓβ)).sum ≤ (Q.map fun q => q.2.length).sum :=
    List.sum_le_sum fun q _ => List.countP_le_length
  unfold tThrough tVisits
  omega

/-- Passenger `π` is carried through: `(ℓα π, ℓβ π)` is a visit of a route or a loop. -/
def Carried (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) (π : Fin t) : Prop :=
  InV R Q (ℓα π, ℓβ π)

/-- The two flights of every passenger, without keys, among the legs of routes and loops. -/
structure TPax (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K)))
    (ℓα ℓβ : Fin t → KLeg n t K) : Prop where
  memα : ∀ π, ℓα π ∈ tLegs R Q
  memβ : ∀ π, ℓβ π ∈ tLegs R Q
  ends : PaxEnds ℓα ℓβ
  time : ∀ π, (ℓα π).leg.arr ≤ (ℓβ π).leg.dep

omit [LinearOrder K] in
theorem TPax.of_tLegs_eq {R R' : Fin p → List (Visit n t K)} {Q Q' : List (ℕ × List (Visit n t K))}
    {ℓα ℓβ : Fin t → KLeg n t K} (h : TPax R Q ℓα ℓβ) (he : tLegs R' Q' = tLegs R Q) :
    TPax R' Q' ℓα ℓβ :=
  ⟨fun π => he ▸ h.memα π, fun π => he ▸ h.memβ π, h.ends, h.time⟩

theorem isThrough_false {ℓα ℓβ : Fin t → KLeg n t K} (hpax : PaxEnds ℓα ℓβ) {π : Fin t}
    {v : Visit n t K} (hv : v.1 = ℓα π ∨ v.2 = ℓβ π) (hne : v ≠ (ℓα π, ℓβ π)) :
    isThrough ℓα ℓβ v = false := by
  simp only [isThrough, decide_eq_false_iff_not, not_exists]
  intro π' he
  rcases hv with h | h
  · rw [he] at h
    have := hpax.injα h
    subst this
    exact hne he
  · rw [he] at h
    have := hpax.injβ h
    subst this
    exact hne he

theorem isThrough_true {ℓα ℓβ : Fin t → KLeg n t K} (π : Fin t) :
    isThrough ℓα ℓβ (ℓα π, ℓβ π) = true := by
  simp only [isThrough, decide_eq_true_eq]
  exact ⟨π, rfl⟩

theorem multiset_sum_map_append {α β : Type*} [AddCommMonoid β] (f : α → β) (A B : List α) :
    ((A ++ B).map f).sum = (A.map f).sum + (B.map f).sum := by
  simp

/-! ### The three moves -/

omit [LinearOrder K] in
/-- Updating one coordinate, in a sum. -/
theorem sum_update_one {M : Type*} [AddCommMonoid M] {α : Type*} (R : Fin p → α) (f : α → M)
    (u : Fin p) (a : α) :
    ∑ k, f (Function.update R u a k) + f (R u) = ∑ k, f (R k) + f a := by
  classical
  have h₁ := Finset.add_sum_erase univ (fun k => f (Function.update R u a k)) (Finset.mem_univ u)
  have h₂ := Finset.add_sum_erase univ (fun k => f (R k)) (Finset.mem_univ u)
  have h₃ : ∑ k ∈ univ.erase u, f (Function.update R u a k) = ∑ k ∈ univ.erase u, f (R k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  simp only [Function.update_self] at h₁
  rw [← h₁, ← h₂, h₃]
  ac_rfl

omit [LinearOrder K] in
/-- Every leg of a chain lies between the start and the end of the chain, in time. -/
theorem TChain.bounds {N : Network n} : ∀ {s : TState n} {L : List (Visit n t K)}, TChain N s L →
    s.2 ≤ (tEnd s L).2 ∧ ∀ v ∈ L, s.2 ≤ v.1.leg.dep ∧ v.1.leg.dep ≤ v.1.leg.arr ∧
      v.1.leg.arr ≤ v.2.leg.dep ∧ v.2.leg.dep ≤ v.2.leg.arr ∧ v.2.leg.arr ≤ (tEnd s L).2
  | _, [], _ => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | s, w :: L, ⟨hw, hL⟩ => by
    obtain ⟨h₁, h₂⟩ := hL.bounds
    simp only [Visit.tnext, tEnd_cons] at h₁ h₂ ⊢
    have := hw.time; have := hw.loc.dep_le_arr₁; have := hw.loc.wait; have := hw.loc.dep_le_arr₂
    refine ⟨by omega, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨by omega, by omega, by omega, by omega, h₁⟩
    · obtain ⟨g₁, g₂, g₃, g₄, g₅⟩ := h₂ v hv
      exact ⟨by omega, g₂, g₃, g₄, g₅⟩

/-- **Exchange.** Plane `u` enters `x` with `ℓα π` and leaves with `β'`, plane `v ≠ u` enters
with `α'` and leaves with `ℓβ π`, and `v` is in `x` before `u` leaves: they exchange futures. -/
theorem tExchange_step {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, TRoute N (R k)) (hpax : PaxEnds ℓα ℓβ) {π : Fin t}
    (htime : (ℓα π).leg.arr ≤ (ℓβ π).leg.dep) {u v : Fin p} (huv : u ≠ v)
    {A B C D : List (Visit n t K)} {α' β' : KLeg n t K} (hu : R u = A ++ (ℓα π, β') :: B)
    (hv : R v = C ++ (α', ℓβ π) :: D) (hov : α'.leg.arr ≤ β'.leg.dep)
    (hnot : ∀ k, (ℓα π, ℓβ π) ∉ R k) :
    ∃ R' : Fin p → List (Visit n t K), (∀ k, TRoute N (R' k)) ∧ allK R' = allK R ∧
      visitCount R' = visitCount R ∧ throughCount ℓα ℓβ R < throughCount ℓα ℓβ R' := by
  set R' := Function.update (Function.update R u (A ++ (ℓα π, ℓβ π) :: D)) v
      (C ++ (α', β') :: B) with hR'
  refine ⟨R', ?_⟩
  have hRu := hR u
  have hRv := hR v
  rw [hu] at hRu
  rw [hv] at hRv
  obtain ⟨hcu, heu⟩ := hRu
  obtain ⟨hcv, hev⟩ := hRv
  rw [tChain_append, tChain_cons] at hcu hcv
  rw [tEnd_append, tEnd_cons] at heu hev
  obtain ⟨hA, hαβ', hB⟩ := hcu
  obtain ⟨hC, hα'β, hD⟩ := hcv
  obtain ⟨x, hx₁, hx₂⟩ := hpax.city π
  have hnew₁ : TOK N (tEnd (.ci, 0) A) (ℓα π, ℓβ π) :=
    ⟨hαβ'.src, hαβ'.time, ⟨hαβ'.loc.hub, hαβ'.loc.flies₁, hα'β.loc.flies₂, ⟨x, hx₁, hx₂⟩,
      htime, hα'β.loc.exit⟩⟩
  have hnew₂ : TOK N (tEnd (.ci, 0) C) (α', β') := by
    obtain ⟨y, hy₁, hy₂⟩ := hα'β.loc.city
    obtain ⟨z, hz₁, hz₂⟩ := hαβ'.loc.city
    have hyx : y = x := by rw [hx₂] at hy₂; exact (Loc.city.inj hy₂).symm
    have hzx : z = x := by rw [hx₁] at hz₁; exact (Loc.city.inj hz₁).symm
    exact ⟨hα'β.src, hα'β.time, ⟨hα'β.loc.hub, hα'β.loc.flies₁, hαβ'.loc.flies₂,
      ⟨x, hyx ▸ hy₁, hzx ▸ hz₂⟩, hov, hαβ'.loc.exit⟩⟩
  have hR'u : R' u = A ++ (ℓα π, ℓβ π) :: D := by
    simp only [R', Function.update_of_ne huv, Function.update_self]
  have hR'v : R' v = C ++ (α', β') :: B := by simp only [R', Function.update_self]
  refine ⟨fun k => ?_, ?_, ?_, ?_⟩
  · by_cases hkv : k = v
    · subst hkv
      rw [hR'v]
      refine ⟨?_, ?_⟩
      · rw [tChain_append, tChain_cons]
        exact ⟨hC, hnew₂, hB⟩
      · rw [tEnd_append, tEnd_cons]
        exact heu
    · by_cases hku : k = u
      · subst hku
        rw [hR'u]
        refine ⟨?_, ?_⟩
        · rw [tChain_append, tChain_cons]
          exact ⟨hA, hnew₁, hD⟩
        · rw [tEnd_append, tEnd_cons]
          exact hev
      · simp only [R', Function.update_of_ne hkv, Function.update_of_ne hku]
        exact hR k
  · have h : allK R' + (legsOf (R u) : Multiset (KLeg n t K)) + (legsOf (R v) : Multiset _) =
        allK R + (legsOf (A ++ (ℓα π, ℓβ π) :: D) : Multiset _) +
          (legsOf (C ++ (α', β') :: B) : Multiset _) :=
      sum_update_update R (fun L => (legsOf L : Multiset (KLeg n t K))) huv _ _
    have e : ((legsOf (A ++ (ℓα π, ℓβ π) :: D) : Multiset (KLeg n t K)) +
        (legsOf (C ++ (α', β') :: B) : Multiset (KLeg n t K))) =
        (legsOf (R u) : Multiset (KLeg n t K)) + (legsOf (R v) : Multiset (KLeg n t K)) := by
      rw [hu, hv]
      simp only [legsOf_append, legsOf_cons, ← Multiset.coe_add, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      ac_rfl
    rw [add_assoc, add_assoc, ← e] at h
    exact add_right_cancel h
  · have h : visitCount R' + (R u).length + (R v).length =
        visitCount R + (A ++ (ℓα π, ℓβ π) :: D).length + (C ++ (α', β') :: B).length :=
      sum_update_update R (fun L => L.length) huv _ _
    simp only [hu, hv, List.length_append, List.length_cons] at h
    omega
  · have h : throughCount ℓα ℓβ R' + (R u).countP (isThrough ℓα ℓβ) +
        (R v).countP (isThrough ℓα ℓβ) = throughCount ℓα ℓβ R +
          (A ++ (ℓα π, ℓβ π) :: D).countP (isThrough ℓα ℓβ) +
          (C ++ (α', β') :: B).countP (isThrough ℓα ℓβ) :=
      sum_update_update R (fun L => L.countP (isThrough ℓα ℓβ)) huv _ _
    have h₂ := isThrough_false hpax (v := (ℓα π, β')) (Or.inl rfl)
      fun he => hnot u (by rw [hu, ← he]; simp)
    have h₃ := isThrough_false hpax (v := (α', ℓβ π)) (Or.inr rfl)
      fun he => hnot v (by rw [hv, ← he]; simp)
    simp only [hu, hv, List.countP_append, List.countP_cons, isThrough_true, h₂, h₃] at h
    simp only [ite_true, ite_false, Bool.false_eq_true] at h
    omega

/-- **Cut.** A hand-off goes backwards on one route: plane `u` leaves `x` with `ℓβ π`, flies `Z`,
and enters `x` with `ℓα π`. All of it happens at the time `τ` of `ℓβ π`, and the walk becomes a
loop `(ℓα π, ℓβ π) :: Z`; the route keeps `(α', β'')`. -/
theorem tCut_step {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, TRoute N (R k)) (hpax : PaxEnds ℓα ℓβ) {π : Fin t}
    (htime : (ℓα π).leg.arr ≤ (ℓβ π).leg.dep) {u : Fin p} {A Z B : List (Visit n t K)}
    {α' β'' : KLeg n t K} (hu : R u = A ++ (α', ℓβ π) :: Z ++ (ℓα π, β'') :: B)
    (hnot : (ℓα π, ℓβ π) ∉ R u) :
    (∀ k, TRoute N (Function.update R u (A ++ (α', β'') :: B) k)) ∧
      TLoop N (ℓβ π).leg.dep ((ℓα π, ℓβ π) :: Z) ∧
      allK (Function.update R u (A ++ (α', β'') :: B)) +
        (legsOf ((ℓα π, ℓβ π) :: Z) : Multiset _) = allK R ∧
      visitCount (Function.update R u (A ++ (α', β'') :: B)) + ((ℓα π, ℓβ π) :: Z).length =
        visitCount R ∧
      throughCount ℓα ℓβ R < throughCount ℓα ℓβ (Function.update R u (A ++ (α', β'') :: B)) +
        ((ℓα π, ℓβ π) :: Z).countP (isThrough ℓα ℓβ) := by
  set τ := (ℓβ π).leg.dep with hτ
  have hRu := hR u
  rw [hu] at hRu
  obtain ⟨hc, he⟩ := hRu
  rw [List.append_assoc, tChain_append, List.cons_append, tChain_cons, tChain_append,
    tChain_cons] at hc
  rw [List.append_assoc, tEnd_append, List.cons_append, tEnd_cons, tEnd_append,
    tEnd_cons] at he
  obtain ⟨hA, hα'β, hZ, hαβ'', hB⟩ := hc
  obtain ⟨x, hx₁, hx₂⟩ := hpax.city π
  -- Everything between the two flights happens at `τ`.
  obtain ⟨hZ₀, hZb⟩ := hZ.bounds
  have hβ := hα'β.loc.dep_le_arr₂
  have hα₁ := hαβ''.time
  have hα₂ := hαβ''.loc.dep_le_arr₁
  simp only [Visit.tnext] at hZ₀ hZb hα₁
  have hαt : (ℓα π).leg.dep = τ ∧ (ℓα π).leg.arr = τ := by
    have := htime; simp only [hτ] at *; omega
  have hβt : (ℓβ π).leg.arr = τ := by have := htime; simp only [hτ] at *; omega
  have hZt : ∀ v ∈ Z, v.AtTime τ := fun v hv => by
    obtain ⟨g₁, g₂, g₃, g₄, g₅⟩ := hZb v hv
    have := htime
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hτ] at * <;> omega
  refine ⟨fun k => ?_, ⟨List.cons_ne_nil _ _, fun v hv => ?_, (ℓα π).leg.src, ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases hk : k = u
    · subst hk
      rw [Function.update_self]
      refine ⟨?_, ?_⟩
      · rw [tChain_append, tChain_cons]
        refine ⟨hA, ⟨hα'β.src, hα'β.time, ⟨hα'β.loc.hub, hα'β.loc.flies₁, hαβ''.loc.flies₂, ?_,
          ?_, hαβ''.loc.exit⟩⟩, hB⟩
        · obtain ⟨y, hy₁, hy₂⟩ := hα'β.loc.city
          obtain ⟨z, hz₁, hz₂⟩ := hαβ''.loc.city
          have hyx : y = x := by rw [hx₂] at hy₂; exact (Loc.city.inj hy₂).symm
          have hzx : z = x := by rw [hx₁] at hz₁; exact (Loc.city.inj hz₁).symm
          exact ⟨x, hyx ▸ hy₁, hzx ▸ hz₂⟩
        · have w₁ : α'.leg.arr ≤ (ℓβ π).leg.dep := hα'β.loc.wait
          have w₂ : (ℓα π).leg.arr ≤ β''.leg.dep := hαβ''.loc.wait
          show α'.leg.arr ≤ β''.leg.dep
          have := hαt.2
          omega
      · rw [tEnd_append, tEnd_cons]
        exact he
    · rw [Function.update_of_ne hk]
      exact hR k
  · rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨hαt.1, hαt.2, rfl, hβt⟩
    · exact hZt v hv
  · rw [tChain_cons]
    refine ⟨⟨rfl, hαt.1.symm.le, ⟨hαβ''.loc.hub, hαβ''.loc.flies₁, hα'β.loc.flies₂,
      ⟨x, hx₁, hx₂⟩, htime, hα'β.loc.exit⟩⟩, ?_⟩
    have e : Visit.tnext (ℓα π, ℓβ π) = Visit.tnext (α', ℓβ π) := rfl
    rw [e]
    exact hZ
  · rw [tEnd_cons]
    exact hαβ''.src.symm
  · have h := sum_update_one R (fun L => (legsOf L : Multiset (KLeg n t K))) u
      (A ++ (α', β'') :: B)
    have e : (legsOf (A ++ (α', β'') :: B) : Multiset (KLeg n t K)) +
        (legsOf ((ℓα π, ℓβ π) :: Z) : Multiset _) = (legsOf (R u) : Multiset _) := by
      rw [hu]
      simp only [legsOf_append, legsOf_cons, ← Multiset.coe_add,
        ← Multiset.cons_coe, ← Multiset.singleton_add]
      ac_rfl
    change allK _ + _ = allK R + _ at h
    rw [← e, ← add_assoc, add_right_comm] at h
    exact add_right_cancel h
  · have h : visitCount (Function.update R u (A ++ (α', β'') :: B)) + (R u).length =
        visitCount R + (A ++ (α', β'') :: B).length :=
      sum_update_one R (fun L => L.length) u _
    simp only [hu, List.length_append, List.length_cons] at h ⊢
    omega
  · have h : throughCount ℓα ℓβ (Function.update R u (A ++ (α', β'') :: B)) +
        (R u).countP (isThrough ℓα ℓβ) = throughCount ℓα ℓβ R +
          (A ++ (α', β'') :: B).countP (isThrough ℓα ℓβ) :=
      sum_update_one R (fun L => L.countP (isThrough ℓα ℓβ)) u _
    have h₂ := isThrough_false hpax (v := (α', ℓβ π)) (Or.inr rfl)
      fun he => hnot (by rw [hu, ← he]; simp)
    have h₃ := isThrough_false hpax (v := (ℓα π, β'')) (Or.inl rfl)
      fun he => hnot (by rw [hu, ← he]; simp)
    simp only [hu, List.append_assoc, List.cons_append, List.countP_append, List.countP_cons,
      isThrough_true, h₂, h₃] at h ⊢
    simp only [ite_true, ite_false, Bool.false_eq_true] at h ⊢
    omega

omit [LinearOrder K] in
/-- A loop, read from just after one of its visits `F`, is a chain from the exit hub of `F` back
to its entry hub, at time `τ`. -/
theorem TLoop.rotate {N : Network n} {τ : ℕ} {C D : List (Visit n t K)} {F : Visit n t K}
    (h : TLoop N τ (C ++ F :: D)) :
    LocOK N F ∧ F.AtTime τ ∧ TChain N F.tnext (D ++ C) ∧ tEnd F.tnext (D ++ C) = (F.1.leg.src, τ) ∧
      ∀ v ∈ D ++ C, v.AtTime τ := by
  obtain ⟨-, hat, h₀, hc, he⟩ := h
  rw [tChain_append, tChain_cons] at hc
  rw [tEnd_append, tEnd_cons] at he
  obtain ⟨hC, hF, hD⟩ := hc
  have hatF : F.AtTime τ := hat F (by simp)
  have hatD : ∀ v ∈ D, v.AtTime τ := fun v hv => hat v (by simp [hv])
  have hatC : ∀ v ∈ C, v.AtTime τ := fun v hv => hat v (by simp [hv])
  have hDend : tEnd F.tnext D = (h₀, τ) :=
    Prod.ext he (tEnd_snd_of_atTime (s := F.tnext) hatF.2.2.2 hatD)
  have hCend : (tEnd (h₀, τ) C).2 = τ := tEnd_snd_of_atTime rfl hatC
  refine ⟨hF.loc, hatF, ?_, ?_, fun v hv => ?_⟩
  · rw [tChain_append, hDend]
    exact ⟨hD, hC⟩
  · rw [tEnd_append, hDend]
    exact Prod.ext hF.src.symm hCend
  · rcases List.mem_append.mp hv with hv | hv
    · exact hatD v hv
    · exact hatC v hv

/-- **Splice.** A loop at time `τ` with a visit `F`, and a route visit `δ` at the same city with
`a(δ) ≤ τ ≤ e(δ)`: the loop is inserted in the route at `δ`, which becomes
`(δ.1, F.2)`, the rest of the loop, `(F.1, δ.2)`. -/
theorem tSplice_step {N : Network n} {R : Fin p → List (Visit n t K)} {ℓα ℓβ : Fin t → KLeg n t K}
    (hR : ∀ k, TRoute N (R k))
    {k : Fin p} {A B : List (Visit n t K)} {δ : Visit n t K} (hk : R k = A ++ δ :: B)
    {τ : ℕ} {C D : List (Visit n t K)} {F : Visit n t K} (hL : TLoop N τ (C ++ F :: D))
    (hcity : ∃ x, δ.1.leg.dst = .city x ∧ F.1.leg.dst = .city x)
    (h₁ : δ.1.leg.arr ≤ τ) (h₂ : τ ≤ δ.2.leg.dep) :
    (∀ k', TRoute N (Function.update R k (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B) k')) ∧
      allK (Function.update R k (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B)) =
        allK R + (legsOf (C ++ F :: D) : Multiset _) ∧
      visitCount (Function.update R k (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B)) =
        visitCount R + (C ++ F :: D).length ∧
      ((A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B).countP (isThrough ℓα ℓβ) =
        (A ++ B ++ D ++ C).countP (isThrough ℓα ℓβ) + (if isThrough ℓα ℓβ (δ.1, F.2) then 1 else 0)
          + (if isThrough ℓα ℓβ (F.1, δ.2) then 1 else 0)) := by
  obtain ⟨hFl, hFt, hDC, hDCend, hDCt⟩ := hL.rotate
  obtain ⟨x, hx₁, hx₂⟩ := hcity
  have hRk := hR k
  rw [hk] at hRk
  obtain ⟨hc, he⟩ := hRk
  rw [tChain_append, tChain_cons] at hc
  rw [tEnd_append, tEnd_cons] at he
  obtain ⟨hA, hδ, hB⟩ := hc
  obtain ⟨y, hy₁, hy₂⟩ := hδ.loc.city
  obtain ⟨z, hz₁, hz₂⟩ := hFl.city
  have hyx : y = x := by rw [hx₁] at hy₁; exact (Loc.city.inj hy₁).symm
  have hzx : z = x := by rw [hx₂] at hz₁; exact (Loc.city.inj hz₁).symm
  have hnew₁ : TOK N (tEnd (.ci, 0) A) (δ.1, F.2) :=
    ⟨hδ.src, hδ.time, ⟨hδ.loc.hub, hδ.loc.flies₁, hFl.flies₂, ⟨x, hx₁, hzx ▸ hz₂⟩,
      by rw [hFt.2.2.1]; exact h₁, hFl.exit⟩⟩
  have hnew₂ : TOK N (tEnd (Visit.tnext (δ.1, F.2)) (D ++ C)) (F.1, δ.2) := by
    have e : Visit.tnext (δ.1, F.2) = F.tnext := rfl
    rw [e, hDCend]
    exact ⟨rfl, hFt.1.symm.le, ⟨hFl.hub, hFl.flies₁, hδ.loc.flies₂, ⟨x, hx₂, hyx ▸ hy₂⟩,
      by rw [hFt.2.1]; exact h₂, hδ.loc.exit⟩⟩
  refine ⟨fun k' => ?_, ?_, ?_, ?_⟩
  · by_cases hk' : k' = k
    · subst hk'
      rw [Function.update_self]
      refine ⟨?_, ?_⟩
      · rw [List.append_assoc, tChain_append, List.cons_append, tChain_cons, tChain_append,
          tChain_cons]
        exact ⟨hA, hnew₁, hDC, hnew₂, hB⟩
      · rw [List.append_assoc, tEnd_append, List.cons_append, tEnd_cons, tEnd_append, tEnd_cons]
        exact he
    · rw [Function.update_of_ne hk']
      exact hR k'
  · have h := sum_update_one R (fun L => (legsOf L : Multiset (KLeg n t K))) k
      (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B)
    have e : (legsOf (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B) : Multiset (KLeg n t K)) =
        (legsOf (R k) : Multiset _) + (legsOf (C ++ F :: D) : Multiset _) := by
      rw [hk]
      simp only [legsOf_append, legsOf_cons, ← Multiset.coe_add,
        ← Multiset.cons_coe, ← Multiset.singleton_add]
      ac_rfl
    change allK _ + _ = allK R + _ at h
    rw [e, ← add_assoc] at h
    exact add_right_cancel (h.trans (add_right_comm _ _ _))
  · have h : visitCount (Function.update R k (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B)) +
        (R k).length = visitCount R + (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B).length :=
      sum_update_one R (fun L => L.length) k _
    simp only [hk, List.length_append, List.length_cons] at h ⊢
    omega
  · simp only [List.append_assoc, List.cons_append, List.countP_append, List.countP_cons]
    omega

/-! ### Step 2: rewire while a move applies -/

omit [LinearOrder K] in
theorem split_two {α : Type*} (L : List α) {i j : ℕ} (hji : j < i) (hi : i < L.length) :
    L = L.take j ++ L[j] :: (L.drop (j + 1)).take (i - j - 1) ++ L[i] :: L.drop (i + 1) := by
  have h₁ : L.drop j = L[j] :: L.drop (j + 1) := (List.getElem_cons_drop (h := by omega)).symm
  have h₂ : (L.drop (j + 1)).drop (i - j - 1) = L.drop i := by
    rw [List.drop_drop]; congr 1; omega
  have h₃ : L.drop i = L[i] :: L.drop (i + 1) := (List.getElem_cons_drop (h := hi)).symm
  conv_lhs => rw [← List.take_append_drop j L, h₁, ← List.take_append_drop (i - j - 1)
    (L.drop (j + 1)), h₂, h₃]
  simp

omit [LinearOrder K] in
theorem exists_split_of_mem {Q : List (ℕ × List (Visit n t K))} {q : ℕ × List (Visit n t K)}
    (hq : q ∈ Q) {w : Visit n t K} (hw : w ∈ q.2) :
    ∃ Q₁ Q₂ C D, Q = Q₁ ++ (q.1, C ++ w :: D) :: Q₂ := by
  obtain ⟨Q₁, Q₂, hQ⟩ := List.append_of_mem hq
  obtain ⟨C, D, hCD⟩ := List.append_of_mem hw
  exact ⟨Q₁, Q₂, C, D, by rw [hQ, ← hCD]⟩

/-- An exchange applies. -/
def ExchangeApplies (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) : Prop :=
  ∃ (π : Fin t) (u v : Fin p) (A B C D : List (Visit n t K)) (α' β' : KLeg n t K), u ≠ v ∧
    R u = A ++ (ℓα π, β') :: B ∧ R v = C ++ (α', ℓβ π) :: D ∧ α'.leg.arr ≤ β'.leg.dep ∧
    ¬ Carried ℓα ℓβ R Q π

/-- A cut applies. -/
def CutApplies (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) : Prop :=
  ∃ (π : Fin t) (u : Fin p) (A Z B : List (Visit n t K)) (α' β'' : KLeg n t K),
    R u = A ++ (α', ℓβ π) :: Z ++ (ℓα π, β'') :: B ∧ ¬ Carried ℓα ℓβ R Q π

/-- A splice applies. -/
def SpliceApplies (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K))
    (Q : List (ℕ × List (Visit n t K))) : Prop :=
  ∃ (π : Fin t) (k : Fin p) (A B : List (Visit n t K)) (δ : Visit n t K)
    (Q₁ Q₂ : List (ℕ × List (Visit n t K))) (τ : ℕ) (C D : List (Visit n t K)) (F : Visit n t K),
    R k = A ++ δ :: B ∧ Q = Q₁ ++ (τ, C ++ F :: D) :: Q₂ ∧
    ((F.1 = ℓα π ∧ δ.2 = ℓβ π) ∨ (δ.1 = ℓα π ∧ F.2 = ℓβ π)) ∧ δ.1.leg.arr ≤ τ ∧
    τ ≤ δ.2.leg.dep ∧ ¬ Carried ℓα ℓβ R Q π

omit [LinearOrder K] in
/-- When no move applies, every hand-off is ordered in time. -/
theorem ordered_of_stuck {N : Network n} {R : Fin p → List (Visit n t K)}
    {Q : List (ℕ × List (Visit n t K))} {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, TRoute N (R k))
    (hQ : ∀ q ∈ Q, TLoop N q.1 q.2) (hpax : TPax R Q ℓα ℓβ)
    (hX : ¬ ExchangeApplies ℓα ℓβ R Q) (hC : ¬ CutApplies ℓα ℓβ R Q)
    (hS : ¬ SpliceApplies ℓα ℓβ R Q) (π : Fin t) :
    Carried ℓα ℓβ R Q π ∨ ∀ w₁ w₂, InV R Q w₁ → InV R Q w₂ → w₁.1 = ℓα π → w₂.2 = ℓβ π →
      w₁.2.leg.dep ≤ w₂.1.leg.arr := by
  by_cases hc : Carried ℓα ℓβ R Q π
  · exact Or.inl hc
  refine Or.inr fun w₁ w₂ h₁ h₂ e₁ e₂ => ?_
  have hw₁ : w₁ = (ℓα π, w₁.2) := Prod.ext e₁ rfl
  have hw₂ : w₂ = (w₂.1, ℓβ π) := Prod.ext rfl e₂
  have ht := hpax.time π
  rcases h₁ with ⟨u, hu⟩ | ⟨q₁, hq₁, hw₁q⟩ <;> rcases h₂ with ⟨v, hv⟩ | ⟨q₂, hq₂, hw₂q⟩
  · -- Two routes.
    by_cases huv : u = v
    · subst huv
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      rcases lt_trichotomy i j with hij | rfl | hji
      · have := (hR u).1.le_of_lt hij hj
        have h₃ := ((hR u).1.loc _ (List.getElem_mem hi)).dep_le_arr₂
        have h₄ := ((hR u).1.loc _ (List.getElem_mem hj)).dep_le_arr₁
        omega
      · exact absurd (Or.inl ⟨u, (Prod.ext e₁ e₂ : (R u)[i] = (ℓα π, ℓβ π)) ▸
          List.getElem_mem hi⟩) hc
      · refine absurd ⟨π, u, (R u).take j, ((R u).drop (j + 1)).take (i - j - 1),
          (R u).drop (i + 1), (R u)[j].1, (R u)[i].2, ?_, hc⟩ hC
        rw [← e₂, ← e₁, Prod.mk.eta, Prod.mk.eta]
        exact split_two _ hji hi
    · obtain ⟨A, B, hAB⟩ := List.append_of_mem hu
      obtain ⟨C, D, hCD⟩ := List.append_of_mem hv
      by_contra hlt
      push Not at hlt
      exact hX ⟨π, u, v, A, B, C, D, w₂.1, w₁.2, huv, hw₁ ▸ hAB, hw₂ ▸ hCD, hlt.le, hc⟩
  · -- `ℓα π` on a route, `ℓβ π` in a loop at `τ`: no splice, so the route visit is left before `τ`.
    obtain ⟨-, hat, -⟩ := hQ q₂ hq₂
    obtain ⟨g₁, g₂, g₃, g₄⟩ := hat w₂ hw₂q
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hu
    obtain ⟨Q₁, Q₂, C, D, hQ'⟩ := exists_split_of_mem hq₂ hw₂q
    by_contra hlt
    push Not at hlt
    rw [e₂] at g₃
    have a₁ : w₁.1.leg.arr = (ℓα π).leg.arr := by rw [e₁]
    exact hS ⟨π, u, A, B, w₁, Q₁, Q₂, q₂.1, C, D, w₂, hAB.symm ▸ rfl, hQ',
      Or.inr ⟨e₁, e₂⟩, by omega, by omega, hc⟩
  · -- `ℓα π` in a loop at `τ`, `ℓβ π` on a route: no splice, so the route visit is entered after `τ`.
    obtain ⟨-, hat, -⟩ := hQ q₁ hq₁
    obtain ⟨g₁, g₂, g₃, g₄⟩ := hat w₁ hw₁q
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hv
    obtain ⟨Q₁, Q₂, C, D, hQ'⟩ := exists_split_of_mem hq₁ hw₁q
    by_contra hlt
    push Not at hlt
    rw [e₁] at g₂
    refine hS ⟨π, v, A, B, w₂, Q₁, Q₂, q₁.1, C, D, w₁, hAB.symm ▸ rfl, hQ',
      Or.inl ⟨e₁, e₂⟩, by omega, ?_, hc⟩
    rw [e₂]; omega
  · -- Two loops.
    obtain ⟨-, hat₁, -⟩ := hQ q₁ hq₁
    obtain ⟨-, hat₂, -⟩ := hQ q₂ hq₂
    obtain ⟨-, a₂, a₃, -⟩ := hat₁ w₁ hw₁q
    obtain ⟨-, b₂, b₃, -⟩ := hat₂ w₂ hw₂q
    rw [e₁] at a₂
    rw [e₂] at b₃
    omega

omit [LinearOrder K] in
theorem sum_loops_append {β : Type*} [AddCommMonoid β] (f : ℕ × List (Visit n t K) → β)
    (Q₁ Q₂ : List (ℕ × List (Visit n t K))) (q : ℕ × List (Visit n t K)) :
    ((Q₁ ++ q :: Q₂).map f).sum = (Q₁.map f).sum + f q + (Q₂.map f).sum := by
  simp [add_assoc]

/-- **Step 2 of Theorem 5.3.** From routes and loops, exchanges, cuts and splices give routes and
loops with the same legs in which every passenger is carried through, or every visit entered by
its first flight is left no later than every visit left by its second flight is entered. -/
theorem exists_rewired {N : Network n} {ℓα ℓβ : Fin t → KLeg n t K} :
    ∀ (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K))),
      (∀ k, TRoute N (R k)) → (∀ q ∈ Q, TLoop N q.1 q.2) → TPax R Q ℓα ℓβ →
      ∃ (R' : Fin p → List (Visit n t K)) (Q' : List (ℕ × List (Visit n t K))),
        (∀ k, TRoute N (R' k)) ∧ (∀ q ∈ Q', TLoop N q.1 q.2) ∧ tLegs R' Q' = tLegs R Q ∧
        ∀ π, Carried ℓα ℓβ R' Q' π ∨ ∀ w₁ w₂, InV R' Q' w₁ → InV R' Q' w₂ → w₁.1 = ℓα π →
          w₂.2 = ℓβ π → w₁.2.leg.dep ≤ w₂.1.leg.arr := by
  suffices H : ∀ (μ : ℕ) (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K))),
      tVisits R Q - tThrough ℓα ℓβ R Q = μ → (∀ k, TRoute N (R k)) →
      (∀ q ∈ Q, TLoop N q.1 q.2) → TPax R Q ℓα ℓβ →
      ∃ (R' : Fin p → List (Visit n t K)) (Q' : List (ℕ × List (Visit n t K))),
        (∀ k, TRoute N (R' k)) ∧ (∀ q ∈ Q', TLoop N q.1 q.2) ∧ tLegs R' Q' = tLegs R Q ∧
        ∀ π, Carried ℓα ℓβ R' Q' π ∨ ∀ w₁ w₂, InV R' Q' w₁ → InV R' Q' w₂ → w₁.1 = ℓα π →
          w₂.2 = ℓβ π → w₁.2.leg.dep ≤ w₂.1.leg.arr from fun R Q => H _ R Q rfl
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro R Q hμ hR hQ hpax
    -- Recurse on a state with the same legs and more passengers carried through.
    have next : ∀ (R₁ : Fin p → List (Visit n t K)) (Q₁ : List (ℕ × List (Visit n t K))),
        (∀ k, TRoute N (R₁ k)) → (∀ q ∈ Q₁, TLoop N q.1 q.2) → tLegs R₁ Q₁ = tLegs R Q →
        tVisits R₁ Q₁ = tVisits R Q → tThrough ℓα ℓβ R Q < tThrough ℓα ℓβ R₁ Q₁ →
        ∃ (R' : Fin p → List (Visit n t K)) (Q' : List (ℕ × List (Visit n t K))),
          (∀ k, TRoute N (R' k)) ∧ (∀ q ∈ Q', TLoop N q.1 q.2) ∧ tLegs R' Q' = tLegs R Q ∧
          ∀ π, Carried ℓα ℓβ R' Q' π ∨ ∀ w₁ w₂, InV R' Q' w₁ → InV R' Q' w₂ → w₁.1 = ℓα π →
            w₂.2 = ℓβ π → w₁.2.leg.dep ≤ w₂.1.leg.arr := by
      intro R₁ Q₁ hR₁ hQ₁ hl hv ht
      have hle := tThrough_le ℓα ℓβ R₁ Q₁
      obtain ⟨R', Q', h₁, h₂, h₃, h₄⟩ := ih _ (by omega) R₁ Q₁ rfl hR₁ hQ₁ (hpax.of_tLegs_eq hl)
      exact ⟨R', Q', h₁, h₂, h₃.trans hl, h₄⟩
    have hnotR : ∀ {π : Fin t}, ¬ Carried ℓα ℓβ R Q π → ∀ k, (ℓα π, ℓβ π) ∉ R k :=
      fun hc k h => hc (Or.inl ⟨k, h⟩)
    by_cases hX : ExchangeApplies ℓα ℓβ R Q
    · obtain ⟨π, u, v, A, B, C, D, α', β', huv, hu, hv, hov, hc⟩ := hX
      obtain ⟨R₁, hR₁, hl, hvis, hthr⟩ := tExchange_step hR hpax.ends (hpax.time π) huv hu hv hov
        (hnotR hc)
      refine next R₁ Q hR₁ hQ ?_ ?_ ?_
      · unfold tLegs; rw [hl]
      · unfold tVisits; rw [hvis]
      · unfold tThrough; omega
    by_cases hC : CutApplies ℓα ℓβ R Q
    · obtain ⟨π, u, A, Z, B, α', β'', hu, hc⟩ := hC
      obtain ⟨hR₁, hL, hl, hvis, hthr⟩ := tCut_step hR hpax.ends (hpax.time π) hu (hnotR hc u)
      refine next _ (((ℓβ π).leg.dep, (ℓα π, ℓβ π) :: Z) :: Q) hR₁ ?_ ?_ ?_ ?_
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hL
        · exact hQ q hq
      · unfold tLegs
        simp only [List.map_cons, List.sum_cons]
        rw [← hl]
        ac_rfl
      · unfold tVisits
        simp only [List.map_cons, List.sum_cons]
        omega
      · unfold tThrough
        simp only [List.map_cons, List.sum_cons]
        omega
    by_cases hS : SpliceApplies ℓα ℓβ R Q
    · obtain ⟨π, k, A, B, δ, Q₁, Q₂, τ, C, D, F, hk, hQe, hcase, h₁, h₂, hc⟩ := hS
      have hL : TLoop N τ (C ++ F :: D) := hQ (τ, C ++ F :: D) (by rw [hQe]; simp)
      have hFin : F ∈ C ++ F :: D := by simp
      have hFloc : LocOK N F := hL.2.2.choose_spec.1.loc F hFin
      have hδloc : LocOK N δ := (hR k).1.loc δ (by rw [hk]; simp)
      obtain ⟨x, hx₁, hx₂⟩ := hpax.ends.city π
      have hcity : ∃ x, δ.1.leg.dst = .city x ∧ F.1.leg.dst = .city x := by
        rcases hcase with ⟨hF, hδ⟩ | ⟨hδ, hF⟩
        · obtain ⟨y, hy₁, hy₂⟩ := hδloc.city
          rw [hδ, hx₂] at hy₂
          exact ⟨x, (Loc.city.inj hy₂) ▸ hy₁, hF ▸ hx₁⟩
        · obtain ⟨z, hz₁, hz₂⟩ := hFloc.city
          rw [hF, hx₂] at hz₂
          exact ⟨x, hδ ▸ hx₁, (Loc.city.inj hz₂) ▸ hz₁⟩
      obtain ⟨hR₁, hl, hvis, hcnt⟩ := tSplice_step (ℓα := ℓα) (ℓβ := ℓβ) hR hk hL hcity h₁ h₂
      have hδne : δ ≠ (ℓα π, ℓβ π) := fun he => hc (Or.inl ⟨k, by rw [hk, he]; simp⟩)
      have hFne : F ≠ (ℓα π, ℓβ π) := fun he => hc (Or.inr ⟨(τ, C ++ F :: D),
        by rw [hQe]; simp, by rw [← he]; simp⟩)
      have hδthr := isThrough_false hpax.ends
        (hcase.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)) hδne
      have hFthr := isThrough_false hpax.ends
        (hcase.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)) hFne
      have hnew : (if isThrough ℓα ℓβ (δ.1, F.2) then 1 else 0) +
          (if isThrough ℓα ℓβ (F.1, δ.2) then 1 else 0) ≥ 1 := by
        rcases hcase with ⟨hF, hδ⟩ | ⟨hδ, hF⟩
        · rw [hF, hδ, isThrough_true]; simp
        · rw [hδ, hF, isThrough_true]; simp
      have hupd : throughCount ℓα ℓβ (Function.update R k
          (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B)) + (R k).countP (isThrough ℓα ℓβ) =
          throughCount ℓα ℓβ R + (A ++ (δ.1, F.2) :: (D ++ C) ++ (F.1, δ.2) :: B).countP
            (isThrough ℓα ℓβ) :=
        sum_update_one R (fun L => L.countP (isThrough ℓα ℓβ)) k _
      refine next _ (Q₁ ++ Q₂) hR₁ (fun q hq => hQ q (by rw [hQe]; simp at hq ⊢; tauto)) ?_ ?_ ?_
      · unfold tLegs
        rw [hl, hQe, sum_loops_append]
        simp only [List.map_append, List.sum_append]
        ac_rfl
      · unfold tVisits
        rw [hvis, hQe, sum_loops_append]
        simp only [List.map_append, List.sum_append, List.length_append, List.length_cons]
        omega
      · unfold tThrough
        rw [hQe, sum_loops_append]
        simp only [List.map_append, List.sum_append]
        rw [hk, List.countP_append, List.countP_cons, hδthr] at hupd
        rw [hcnt] at hupd
        simp only [List.countP_append, List.countP_cons, hFthr, Bool.false_eq_true, ite_false]
          at hupd ⊢
        omega
    exact ⟨R, Q, hR, hQ, rfl, ordered_of_stuck hR hQ hpax hX hC hS⟩

/-! ### What Steps 3–6 need, along a route and a loop -/

section RouteFacts

omit [LinearOrder K]

variable {N : Network n}

theorem TChain.time_le_dep : ∀ {s : TState n} {L : List (Visit n t K)}, TChain N s L →
    ∀ (m : ℕ) (hm : m < L.length), s.2 + ((L.take m).map Visit.w).sum ≤ L[m].1.leg.dep
  | _, [], _, m, hm => absurd hm (by simp)
  | s, v :: L, ⟨hv, _⟩, 0, _ => by simpa using hv.time
  | s, v :: L, ⟨hv, hL⟩, m + 1, hm => by
    have ih := hL.time_le_dep m (by simpa using hm)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    simp only [Visit.tnext] at ih
    have h₁ := hv.time
    have h₂ := hv.loc.wait
    have h₃ := hv.loc.dep_le_arr₁
    have h₄ := hv.loc.dep_le_arr₂
    have hw : v.w = (v.1.leg.arr - v.1.leg.dep) + (v.2.leg.arr - v.2.leg.dep) := rfl
    omega

theorem TChain.arr_add_le {M : ℕ} : ∀ {s : TState n} {L : List (Visit n t K)}, TChain N s L →
    (∀ v ∈ L, v.2.leg.arr ≤ M) →
    ∀ (m : ℕ) (hm : m < L.length), L[m].2.leg.arr + ((L.drop (m + 1)).map Visit.w).sum ≤ M
  | _, [], _, _, m, hm => absurd hm (by simp)
  | _, [v], _, hM, 0, _ => by simpa using hM v List.mem_cons_self
  | _, v :: v' :: L, ⟨_, hL⟩, hM, 0, _ => by
    have ih := hL.arr_add_le (fun w hw => hM w (List.mem_cons_of_mem _ hw)) 0 (by simp)
    obtain ⟨hv', -⟩ := hL
    simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, List.map_cons,
      List.sum_cons] at ih ⊢
    have h₁ := hv'.time
    have h₂ := hv'.loc.wait
    have h₃ := hv'.loc.dep_le_arr₁
    have h₄ := hv'.loc.dep_le_arr₂
    simp only [Visit.tnext] at h₁
    unfold Visit.w at ih ⊢
    omega
  | _, v :: L, ⟨_, hL⟩, hM, m + 1, hm => by
    have ih := hL.arr_add_le (fun w hw => hM w (List.mem_cons_of_mem _ hw)) m
      (by simpa using hm)
    simpa using ih

theorem TChain.sum_w_le {M : ℕ} {s : TState n} {L : List (Visit n t K)} (h : TChain N s L)
    (hM : ∀ v ∈ L, v.2.leg.arr ≤ M) : (L.map Visit.w).sum ≤ M := by
  cases L with
  | nil => simp
  | cons v L =>
    have h₁ := h.arr_add_le hM 0 (by simp)
    obtain ⟨hv, -⟩ := h
    have h₂ := hv.loc.wait
    have h₃ := hv.loc.dep_le_arr₁
    have h₄ := hv.loc.dep_le_arr₂
    simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at h₁
    simp only [List.map_cons, List.sum_cons]
    unfold Visit.w at h₁ ⊢
    omega

theorem TChain.countP_isA : ∀ {s : TState n} {L : List (Visit n t K)}, TChain N s L →
    L.countP Visit.isA + (tEnd s L).1.isCI.toNat = L.countP Visit.isAbar + s.1.isCI.toNat
  | _, [], _ => by simp
  | s, v :: L, ⟨hv, hL⟩ => by
    have ih := hL.countP_isA
    have key : (if v.isA = true then 1 else 0) + v.2.leg.dst.isCI.toNat =
        (if v.isAbar = true then 1 else 0) + v.1.leg.src.isCI.toNat := by
      have hub₁ := hv.loc.hub
      have hub₂ := hv.loc.exit
      rcases hs : v.1.leg.src with _ | z | _ <;> rcases hd : v.2.leg.dst with _ | z' | _ <;>
        simp_all [Visit.isA, Visit.isAbar]
    simp only [List.countP_cons, tEnd_cons]
    rw [show v.tnext.1 = v.2.leg.dst from rfl] at ih
    rw [← hv.src]
    omega

theorem TRoute.countP_isA {L : List (Visit n t K)} (h : TRoute N L) :
    L.countP Visit.isA = L.countP Visit.isAbar + 1 := by
  have := h.1.countP_isA
  rw [h.2] at this
  simpa using this

/-- A loop is closed, so it has as many `A` as `Ā` visits. -/
theorem TLoop.countP_isA {τ : ℕ} {L : List (Visit n t K)} (h : TLoop N τ L) :
    L.countP Visit.isA = L.countP Visit.isAbar := by
  obtain ⟨-, -, hh, hc, he⟩ := h
  have := hc.countP_isA
  rw [he] at this
  simpa using this

/-- A visit at one time has flight time `0`. -/
theorem Visit.w_of_atTime {τ : ℕ} {v : Visit n t K} (h : v.AtTime τ) : v.w = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp [Visit.w, h₁, h₂, h₃, h₄]

end RouteFacts

end ZenoFront
