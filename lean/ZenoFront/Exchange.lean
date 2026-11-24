/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.PlanBounds

/-!
# Step 2 of Theorem 6.9: exchanging futures

Theorem 6.9 (schedulable domination) works on a plan without central flights whose legs carry an
*event order*. This file models such a plan by its *visits* and proves Step 2 of the note: while
some hand-off overlaps, two planes can exchange their futures, until every hand-off is ordered in
time.

* A `KLeg` is a leg with a key in a linear order (the event order).
* A `Visit` is a pair of legs: the leg into a central city `x` and the leg out of it.
* `VRoute N L`: the visits `L` form a route of a plane, from `C_I` at time `0` to `C_G`, with keys
  increasing along it (`VChain`, `VOK`).
* `PaxData`: every passenger `π` has a leg `ℓα π : C_I → x` and a later leg `ℓβ π : x → C_G`,
  both carrying it, among the legs of the planes. These are the two flights of its clean journey.

A hand-off of `π` *overlaps* if `ℓα π` is the entry of a visit `(ℓα π, β')` of plane `u`, `ℓβ π`
the exit of a visit `(α', ℓβ π)` of another plane `v`, and `v` is in `x` before `u` leaves:
`α' ≺ β'` and `α'` arrives no later than `β'` departs. Then `u` takes `(ℓα π, ℓβ π)` and the future
of `v`, and `v` takes `(α', β')` and the future of `u` (`exchange_step`). Both routes stay valid,
the multiset of legs is unchanged, and the number of visits carrying their passenger through
increases.

**Step 2** (`exists_ordered_handoffs`): there are routes with the same legs in which, for every
passenger, either `(ℓα π, ℓβ π)` is a visit, or the visit entered by `ℓα π` is left no later than
the visit left by `ℓβ π` is entered (`e(γ) ≤ a(γ')`, Step 3 of the note). This uses that
departure times do not decrease along the keys.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ} {K : Type}

/-- A leg with a key in the event order. -/
structure KLeg (n t : ℕ) (K : Type) where
  leg : Leg n t
  key : K
  deriving DecidableEq

/-- A visit of a central city: the leg into it and the leg out of it. -/
abbrev Visit (n t : ℕ) (K : Type) := KLeg n t K × KLeg n t K

/-- The state of a plane: its hub, the time it is free, and the key of its last leg. -/
abbrev VState (n : ℕ) (K : Type) := Loc n × ℕ × WithBot K

/-- The state after a visit. It only depends on the exit leg. -/
def Visit.next (v : Visit n t K) : VState n K := (v.2.leg.dst, v.2.leg.arr, (v.2.key : WithBot K))

/-- The state at the end of a chain of visits. -/
def vEnd : VState n K → List (Visit n t K) → VState n K
  | s, [] => s
  | _, v :: rest => vEnd v.next rest

/-- The start of every plane: `C_I`, time `0`, no leg yet. -/
def vStart : VState n K := (.ci, 0, ⊥)

@[simp] theorem vEnd_nil (s : VState n K) : vEnd s ([] : List (Visit n t K)) = s := rfl

@[simp] theorem vEnd_cons (s : VState n K) (v : Visit n t K) (rest : List (Visit n t K)) :
    vEnd s (v :: rest) = vEnd v.next rest := rfl

theorem vEnd_append : ∀ (s : VState n K) (A B : List (Visit n t K)),
    vEnd s (A ++ B) = vEnd (vEnd s A) B
  | _, [], _ => rfl
  | _, v :: A, B => vEnd_append v.next A B

/-- The legs of a list of visits. -/
def legsOf (L : List (Visit n t K)) : List (KLeg n t K) := L.flatMap fun v => [v.1, v.2]

@[simp] theorem legsOf_nil : legsOf ([] : List (Visit n t K)) = [] := rfl

@[simp] theorem legsOf_cons (v : Visit n t K) (L : List (Visit n t K)) :
    legsOf (v :: L) = v.1 :: v.2 :: legsOf L := rfl

@[simp] theorem legsOf_append (A B : List (Visit n t K)) :
    legsOf (A ++ B) = legsOf A ++ legsOf B := List.flatMap_append

/-- All legs of the planes, as a multiset. -/
def allK (R : Fin p → List (Visit n t K)) : Multiset (KLeg n t K) :=
  ∑ k, (legsOf (R k) : Multiset (KLeg n t K))

theorem mem_allK {R : Fin p → List (Visit n t K)} {ℓ : KLeg n t K} :
    ℓ ∈ allK R ↔ ∃ k, ∃ v ∈ R k, ℓ = v.1 ∨ ℓ = v.2 := by
  simp only [allK, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_coe, legsOf,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

/-- The number of visits. -/
def visitCount (R : Fin p → List (Visit n t K)) : ℕ := ∑ k, (R k).length

/-- Updating two distinct coordinates, in a sum. -/
theorem sum_update_update {M : Type*} [AddCommMonoid M] {α : Type*} (R : Fin p → α) (f : α → M)
    {u v : Fin p} (huv : u ≠ v) (a b : α) :
    ∑ k, f (Function.update (Function.update R u a) v b k) + f (R u) + f (R v) =
      ∑ k, f (R k) + f a + f b := by
  classical
  have h₁ := Finset.add_sum_erase univ (fun k => f (Function.update (Function.update R u a) v b k))
    (Finset.mem_univ u)
  have h₂ := Finset.add_sum_erase (univ.erase u)
    (fun k => f (Function.update (Function.update R u a) v b k))
    (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
  have h₃ := Finset.add_sum_erase univ (fun k => f (R k)) (Finset.mem_univ u)
  have h₄ := Finset.add_sum_erase (univ.erase u) (fun k => f (R k))
    (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
  have h₅ : ∑ k ∈ (univ.erase u).erase v, f (Function.update (Function.update R u a) v b k) =
      ∑ k ∈ (univ.erase u).erase v, f (R k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkv, hk⟩ := Finset.mem_erase.mp hk
    rw [Function.update_of_ne hkv, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  simp only [Function.update_self, Function.update_of_ne huv] at h₁ h₂
  rw [← h₁, ← h₂, h₅, ← h₃, ← h₄]
  ac_rfl

/-! ### Chains of visits -/

variable [LinearOrder K]

/-- A visit can be flown from state `s`: it leaves the hub of `s`, after its time and key, flies
into a central city and out of it to a hub, the exit after the entry. -/
structure VOK (N : Network n) (s : VState n K) (v : Visit n t K) : Prop where
  src : v.1.leg.src = s.1
  time : s.2.1 ≤ v.1.leg.dep
  key : s.2.2 < (v.1.key : WithBot K)
  hub : v.1.leg.src.isHub = true
  flies₁ : Flies N v.1.leg
  flies₂ : Flies N v.2.leg
  city : ∃ x, v.1.leg.dst = .city x ∧ v.2.leg.src = .city x
  wait : v.1.leg.arr ≤ v.2.leg.dep
  order : v.1.key < v.2.key
  exit : v.2.leg.dst.isHub = true

/-- A chain of visits flown from state `s`. -/
def VChain (N : Network n) : VState n K → List (Visit n t K) → Prop
  | _, [] => True
  | s, v :: rest => VOK N s v ∧ VChain N v.next rest

/-- A route of visits: a chain from `C_I` at time `0` that ends in `C_G`. -/
def VRoute (N : Network n) (L : List (Visit n t K)) : Prop :=
  VChain N vStart L ∧ (vEnd vStart L).1 = .cg

@[simp] theorem vChain_nil (N : Network n) (s : VState n K) : VChain N s ([] : List (Visit n t K)) :=
  trivial

@[simp] theorem vChain_cons (N : Network n) (s : VState n K) (v : Visit n t K)
    (rest : List (Visit n t K)) : VChain N s (v :: rest) ↔ VOK N s v ∧ VChain N v.next rest :=
  Iff.rfl

theorem vChain_append (N : Network n) : ∀ (s : VState n K) (A B : List (Visit n t K)),
    VChain N s (A ++ B) ↔ VChain N s A ∧ VChain N (vEnd s A) B
  | _, [], _ => by simp
  | s, v :: A, B => by
    simp only [List.cons_append, vChain_cons, vEnd_cons, vChain_append N v.next A B]
    tauto

theorem VOK.dep_le_arr₁ {N : Network n} {s : VState n K} {v : Visit n t K} (h : VOK N s v) :
    v.1.leg.dep ≤ v.1.leg.arr := h.flies₁.dep_le_arr

theorem VOK.dep_le_arr₂ {N : Network n} {s : VState n K} {v : Visit n t K} (h : VOK N s v) :
    v.2.leg.dep ≤ v.2.leg.arr := h.flies₂.dep_le_arr

/-- Along a chain, every leg comes after the state, in time and in key. -/
theorem VChain.le_of_mem {N : Network n} : ∀ {s : VState n K} {L : List (Visit n t K)},
    VChain N s L → ∀ v ∈ L, s.2.1 ≤ v.1.leg.dep ∧ s.2.2 < (v.1.key : WithBot K)
  | _, [], _, _, h => absurd h List.not_mem_nil
  | s, w :: L, ⟨hw, hL⟩, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨hw.time, hw.key⟩
    · obtain ⟨h₁, h₂⟩ := hL.le_of_mem v hv
      simp only [Visit.next] at h₁ h₂
      refine ⟨hw.time.trans (hw.dep_le_arr₁.trans (hw.wait.trans (hw.dep_le_arr₂.trans h₁))), ?_⟩
      exact hw.key.trans ((WithBot.coe_lt_coe.mpr hw.order).trans h₂)

/-- Along a chain, an earlier visit is left before a later one is entered, in time and in key. -/
theorem VChain.lt_of_lt {N : Network n} {s : VState n K} {L : List (Visit n t K)}
    (h : VChain N s L) {i j : ℕ} (hij : i < j) (hj : j < L.length) :
    L[i].2.leg.arr ≤ L[j].1.leg.dep ∧ L[i].2.key < L[j].1.key := by
  have hL : L = L.take (i + 1) ++ L.drop (i + 1) := (List.take_append_drop _ _).symm
  rw [hL, vChain_append] at h
  have hend : vEnd s (L.take (i + 1)) = L[i].next := by
    have : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem (by omega)
    rw [this, vEnd_append]
    rfl
  have hmem : L[j] ∈ L.drop (i + 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨j - (i + 1), by simp; omega, by simp; congr 1; omega⟩
  rw [hend] at h
  obtain ⟨h₁, h₂⟩ := h.2.le_of_mem _ hmem
  exact ⟨h₁, WithBot.coe_lt_coe.mp h₂⟩

/-! ### Passengers -/

/-- The two flights of every passenger's clean journey: `ℓα π : C_I → x` and `ℓβ π : x → C_G`,
both carrying `π` and among the legs of the planes, the second after the first in time and in
key. -/
structure PaxData (R : Fin p → List (Visit n t K)) (ℓα ℓβ : Fin t → KLeg n t K) : Prop where
  memα : ∀ π, ℓα π ∈ allK R
  memβ : ∀ π, ℓβ π ∈ allK R
  paxα : ∀ π, (ℓα π).leg.pax = some π
  paxβ : ∀ π, (ℓβ π).leg.pax = some π
  srcα : ∀ π, (ℓα π).leg.src = .ci
  dstβ : ∀ π, (ℓβ π).leg.dst = .cg
  city : ∀ π, ∃ x, (ℓα π).leg.dst = .city x ∧ (ℓβ π).leg.src = .city x
  time : ∀ π, (ℓα π).leg.arr ≤ (ℓβ π).leg.dep
  key : ∀ π, (ℓα π).key < (ℓβ π).key

theorem PaxData.of_allK_eq {R R' : Fin p → List (Visit n t K)} {ℓα ℓβ : Fin t → KLeg n t K}
    (h : PaxData R ℓα ℓβ) (he : allK R' = allK R) : PaxData R' ℓα ℓβ :=
  ⟨fun π => he ▸ h.memα π, fun π => he ▸ h.memβ π, h.paxα, h.paxβ, h.srcα, h.dstβ, h.city,
    h.time, h.key⟩

theorem PaxData.injα {R : Fin p → List (Visit n t K)} {ℓα ℓβ : Fin t → KLeg n t K}
    (h : PaxData R ℓα ℓβ) {π π' : Fin t} (he : ℓα π = ℓα π') : π = π' := by
  have := h.paxα π
  rw [he, h.paxα π'] at this
  exact (Option.some_injective _ this).symm

theorem PaxData.injβ {R : Fin p → List (Visit n t K)} {ℓα ℓβ : Fin t → KLeg n t K}
    (h : PaxData R ℓα ℓβ) {π π' : Fin t} (he : ℓβ π = ℓβ π') : π = π' := by
  have := h.paxβ π
  rw [he, h.paxβ π'] at this
  exact (Option.some_injective _ this).symm

/-- Whether a visit carries its passenger through: it is `(ℓα π, ℓβ π)` for some `π`. -/
def isThrough (ℓα ℓβ : Fin t → KLeg n t K) (v : Visit n t K) : Bool :=
  decide (∃ π, v = (ℓα π, ℓβ π))

/-- The number of visits that carry their passenger through. -/
def throughCount (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K)) : ℕ :=
  ∑ k, (R k).countP (isThrough ℓα ℓβ)

theorem throughCount_le (ℓα ℓβ : Fin t → KLeg n t K) (R : Fin p → List (Visit n t K)) :
    throughCount ℓα ℓβ R ≤ visitCount R :=
  Finset.sum_le_sum fun _ _ => List.countP_le_length

/-! ### One exchange -/

/-- **One exchange of futures.** Plane `u` enters `x` with `ℓα π` and leaves with `β'`, plane
`v ≠ u` enters `x` with `α'` and leaves with `ℓβ π`, and `v` is in `x` before `u` leaves
(`α' ≺ β'`, `α'` arrives no later than `β'` departs). Then `u` takes `(ℓα π, ℓβ π)` and the future
of `v`, `v` takes `(α', β')` and the future of `u`: both are routes, the legs are the same, and
one more visit carries its passenger through. -/
theorem exchange_step {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, VRoute N (R k)) (hpax : PaxData R ℓα ℓβ)
    {π : Fin t} {u v : Fin p} (huv : u ≠ v) {A B C D : List (Visit n t K)}
    {α' β' : KLeg n t K} (hu : R u = A ++ (ℓα π, β') :: B) (hv : R v = C ++ (α', ℓβ π) :: D)
    (hkey : α'.key < β'.key) (htime : α'.leg.arr ≤ β'.leg.dep)
    (hnot : ∀ k, (ℓα π, ℓβ π) ∉ R k) :
    ∃ R' : Fin p → List (Visit n t K), (∀ k, VRoute N (R' k)) ∧ allK R' = allK R ∧
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
  rw [vChain_append, vChain_cons] at hcu hcv
  rw [vEnd_append, vEnd_cons] at heu hev
  obtain ⟨hA, hαβ', hB⟩ := hcu
  obtain ⟨hC, hα'β, hD⟩ := hcv
  obtain ⟨x, hx₁, hx₂⟩ := hpax.city π
  -- The two new visits.
  have hnew₁ : VOK N (vEnd vStart A) (ℓα π, ℓβ π) :=
    ⟨hαβ'.src, hαβ'.time, hαβ'.key, hαβ'.hub, hαβ'.flies₁, hα'β.flies₂, ⟨x, hx₁, hx₂⟩,
      hpax.time π, hpax.key π, hα'β.exit⟩
  have hnew₂ : VOK N (vEnd vStart C) (α', β') := by
    obtain ⟨y, hy₁, hy₂⟩ := hα'β.city
    obtain ⟨z, hz₁, hz₂⟩ := hαβ'.city
    have hyx : y = x := by
      rw [hx₂] at hy₂
      exact (Loc.city.inj hy₂).symm
    have hzx : z = x := by
      rw [hx₁] at hz₁
      exact (Loc.city.inj hz₁).symm
    exact ⟨hα'β.src, hα'β.time, hα'β.key, hα'β.hub, hα'β.flies₁, hαβ'.flies₂,
      ⟨x, hyx ▸ hy₁, hzx ▸ hz₂⟩, htime, hkey, hαβ'.exit⟩
  have hR'u : R' u = A ++ (ℓα π, ℓβ π) :: D := by
    simp only [R', Function.update_of_ne huv, Function.update_self]
  have hR'v : R' v = C ++ (α', β') :: B := by
    simp only [R', Function.update_self]
  refine ⟨fun k => ?_, ?_, ?_, ?_⟩
  · by_cases hkv : k = v
    · subst hkv
      rw [hR'v]
      refine ⟨?_, ?_⟩
      · rw [vChain_append, vChain_cons]
        exact ⟨hC, hnew₂, hB⟩
      · rw [vEnd_append, vEnd_cons]
        exact heu
    · by_cases hku : k = u
      · subst hku
        rw [hR'u]
        refine ⟨?_, ?_⟩
        · rw [vChain_append, vChain_cons]
          exact ⟨hA, hnew₁, hD⟩
        · rw [vEnd_append, vEnd_cons]
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
    have h₁ : isThrough ℓα ℓβ (ℓα π, ℓβ π) = true := by
      simp only [isThrough, decide_eq_true_eq]
      exact ⟨π, rfl⟩
    have h₂ : isThrough ℓα ℓβ (ℓα π, β') = false := by
      simp only [isThrough, decide_eq_false_iff_not, not_exists]
      intro π' he
      simp only [Prod.mk.injEq] at he
      have hπ := hpax.injα he.1
      subst hπ
      exact hnot u (by rw [hu, he.2]; simp)
    have h₃ : isThrough ℓα ℓβ (α', ℓβ π) = false := by
      simp only [isThrough, decide_eq_false_iff_not, not_exists]
      intro π' he
      simp only [Prod.mk.injEq] at he
      have hπ := hpax.injβ he.2
      subst hπ
      exact hnot v (by rw [hv, he.1]; simp)
    simp only [hu, hv, List.countP_append, List.countP_cons, h₁, h₂, h₃] at h
    simp only [ite_true, ite_false, Bool.false_eq_true] at h
    omega

/-! ### Step 2: exchange while some hand-off overlaps -/

theorem VChain.exists_vok {N : Network n} : ∀ {s : VState n K} {L : List (Visit n t K)},
    VChain N s L → ∀ w ∈ L, ∃ s', VOK N s' w
  | _, [], _, _, h => absurd h List.not_mem_nil
  | s, w :: L, ⟨hw, hL⟩, w', hw' => by
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact ⟨s, hw⟩
    · exact hL.exists_vok w' hw'

theorem list_eq_take_cons_drop {α : Type*} (L : List α) (i : ℕ) (hi : i < L.length) :
    L = L.take i ++ L[i] :: L.drop (i + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

/-- Where the two flights of a passenger are: `ℓα π` enters a visit, `ℓβ π` leaves one. -/
theorem PaxData.exists_pos {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, VRoute N (R k)) (hpax : PaxData R ℓα ℓβ) (π : Fin t) :
    (∃ (u : Fin p) (i : Fin (R u).length), (R u)[i].1 = ℓα π) ∧
      ∃ (v : Fin p) (j : Fin (R v).length), (R v)[j].2 = ℓβ π := by
  obtain ⟨u, w, hw, hα⟩ := mem_allK.mp (hpax.memα π)
  obtain ⟨v, w', hw', hβ⟩ := mem_allK.mp (hpax.memβ π)
  obtain ⟨s, hs⟩ := (hR u).1.exists_vok w hw
  obtain ⟨s', hs'⟩ := (hR v).1.exists_vok w' hw'
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    refine ⟨u, ⟨i, hi⟩, ?_⟩
    rcases hα with h | h
    · exact h.symm
    · exfalso
      obtain ⟨x, -, hx⟩ := hs.city
      rw [← h, hpax.srcα π] at hx
      cases hx
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw'
    refine ⟨v, ⟨j, hj⟩, ?_⟩
    rcases hβ with h | h
    · exfalso
      obtain ⟨x, hx, -⟩ := hs'.city
      rw [← h, hpax.dstβ π] at hx
      cases hx
    · exact h.symm

/-- The conclusion of Step 2, for routes where no hand-off overlaps. -/
theorem ordered_of_no_overlap {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, VRoute N (R k)) (hpax : PaxData R ℓα ℓβ)
    (hdep : ∀ ℓ ∈ allK R, ∀ ℓ' ∈ allK R, ℓ.key ≤ ℓ'.key → ℓ.leg.dep ≤ ℓ'.leg.dep)
    (hno : ∀ π, (∃ k, (ℓα π, ℓβ π) ∈ R k) ∨ ∀ (u v : Fin p) (A B C D : List (Visit n t K))
      (α' β' : KLeg n t K), u ≠ v → R u = A ++ (ℓα π, β') :: B → R v = C ++ (α', ℓβ π) :: D →
        ¬ (α'.key < β'.key ∧ α'.leg.arr ≤ β'.leg.dep)) (π : Fin t) :
    ∃ (u : Fin p) (i : Fin (R u).length) (v : Fin p) (j : Fin (R v).length),
      (R u)[i].1 = ℓα π ∧ (R v)[j].2 = ℓβ π ∧
      ((⟨u, i⟩ : (k : Fin p) × Fin (R k).length) ≠ ⟨v, j⟩ →
        (R u)[i].2.leg.dep ≤ (R v)[j].1.leg.arr) := by
  rcases hno π with ⟨k, hk⟩ | hno
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hk
    exact ⟨k, ⟨i, hi⟩, k, ⟨i, hi⟩, by simp [he], by simp [he], fun h => absurd rfl h⟩
  obtain ⟨⟨u, i, hi⟩, ⟨v, j, hj⟩⟩ := hpax.exists_pos hR π
  refine ⟨u, i, v, j, hi, hj, fun hne => ?_⟩
  have hvok : ∀ (k : Fin p) (m : Fin (R k).length), ∃ s, VOK N s (R k)[m] := fun k m =>
    (hR k).1.exists_vok _ (List.getElem_mem _)
  by_cases huv : u = v
  · subst huv
    have hij : i ≠ j := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · obtain ⟨h₁, -⟩ := (hR u).1.lt_of_lt h j.isLt
      obtain ⟨s₁, hs₁⟩ := hvok u i
      obtain ⟨s₂, hs₂⟩ := hvok u j
      have := hs₁.dep_le_arr₂
      have := hs₂.dep_le_arr₁
      exact le_trans (by assumption) (le_trans h₁ (by assumption))
    · obtain ⟨-, h₂⟩ := (hR u).1.lt_of_lt h i.isLt
      simp only [Fin.getElem_fin] at hi hj h₂
      rw [hi, hj] at h₂
      exact absurd (hpax.key π) (not_lt.mpr h₂.le)
  · have hu : R u = (R u).take i ++ (ℓα π, (R u)[i].2) :: (R u).drop (i + 1) := by
      conv_lhs => rw [list_eq_take_cons_drop (R u) i i.isLt]
      rw [← hi]
      rfl
    have hv : R v = (R v).take j ++ ((R v)[j].1, ℓβ π) :: (R v).drop (j + 1) := by
      conv_lhs => rw [list_eq_take_cons_drop (R v) j j.isLt]
      rw [← hj]
      rfl
    have h := hno u v _ _ _ _ _ _ huv hu hv
    have hβ' : (R u)[i].2 ∈ allK R := mem_allK.mpr ⟨u, _, List.getElem_mem _, Or.inr rfl⟩
    have hα' : (R v)[j].1 ∈ allK R := mem_allK.mpr ⟨v, _, List.getElem_mem _, Or.inl rfl⟩
    obtain ⟨s, hs⟩ := hvok v j
    have harr := hs.dep_le_arr₁
    by_cases hk : (R v)[j].1.key < (R u)[i].2.key
    · exact (lt_of_not_ge fun hle => h ⟨hk, hle⟩).le
    · exact (hdep _ hβ' _ hα' (not_lt.mp hk)).trans harr

/-- **Step 2 (exchanges).** Exchanging futures while some hand-off overlaps gives routes with the
same legs in which, for every passenger `π`, the visit `γ` entered by `ℓα π` is left no later
than the visit `γ'` left by `ℓβ π` is entered, `e(γ) ≤ a(γ')`, unless `γ = γ'` is the visit
`(ℓα π, ℓβ π)`. It uses that departure times do not decrease along the keys. -/
theorem exists_ordered_handoffs {N : Network n} {R : Fin p → List (Visit n t K)}
    {ℓα ℓβ : Fin t → KLeg n t K} (hR : ∀ k, VRoute N (R k)) (hpax : PaxData R ℓα ℓβ)
    (hdep : ∀ ℓ ∈ allK R, ∀ ℓ' ∈ allK R, ℓ.key ≤ ℓ'.key → ℓ.leg.dep ≤ ℓ'.leg.dep) :
    ∃ R' : Fin p → List (Visit n t K), (∀ k, VRoute N (R' k)) ∧ allK R' = allK R ∧
      ∀ π, ∃ (u : Fin p) (i : Fin (R' u).length) (v : Fin p) (j : Fin (R' v).length),
        (R' u)[i].1 = ℓα π ∧ (R' v)[j].2 = ℓβ π ∧
        ((⟨u, i⟩ : (k : Fin p) × Fin (R' k).length) ≠ ⟨v, j⟩ →
          (R' u)[i].2.leg.dep ≤ (R' v)[j].1.leg.arr) := by
  suffices H : ∀ (μ : ℕ) (R : Fin p → List (Visit n t K)), visitCount R - throughCount ℓα ℓβ R = μ →
      (∀ k, VRoute N (R k)) → PaxData R ℓα ℓβ →
      (∀ ℓ ∈ allK R, ∀ ℓ' ∈ allK R, ℓ.key ≤ ℓ'.key → ℓ.leg.dep ≤ ℓ'.leg.dep) →
      ∃ R' : Fin p → List (Visit n t K), (∀ k, VRoute N (R' k)) ∧ allK R' = allK R ∧
        ∀ π, ∃ (u : Fin p) (i : Fin (R' u).length) (v : Fin p) (j : Fin (R' v).length),
          (R' u)[i].1 = ℓα π ∧ (R' v)[j].2 = ℓβ π ∧
          ((⟨u, i⟩ : (k : Fin p) × Fin (R' k).length) ≠ ⟨v, j⟩ →
            (R' u)[i].2.leg.dep ≤ (R' v)[j].1.leg.arr) from H _ R rfl hR hpax hdep
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro R hμ hR hpax hdep
    by_cases hex : ∃ (π : Fin t) (u v : Fin p) (A B C D : List (Visit n t K)) (α' β' : KLeg n t K),
        u ≠ v ∧ R u = A ++ (ℓα π, β') :: B ∧ R v = C ++ (α', ℓβ π) :: D ∧ α'.key < β'.key ∧
          α'.leg.arr ≤ β'.leg.dep ∧ ∀ k, (ℓα π, ℓβ π) ∉ R k
    · obtain ⟨π, u, v, A, B, C, D, α', β', huv, hu, hv, hkey, htime, hnot⟩ := hex
      obtain ⟨R₁, hR₁, hall, hvis, hthr⟩ := exchange_step hR hpax huv hu hv hkey htime hnot
      have hle := throughCount_le ℓα ℓβ R₁
      obtain ⟨R', hR', hall', hfin⟩ := ih _ (by omega) R₁ rfl hR₁ (hpax.of_allK_eq hall)
        (by rw [hall]; exact hdep)
      exact ⟨R', hR', hall'.trans hall, hfin⟩
    · refine ⟨R, hR, rfl, ordered_of_no_overlap hR hpax hdep fun π => ?_⟩
      by_cases hthr : ∃ k, (ℓα π, ℓβ π) ∈ R k
      · exact Or.inl hthr
      · refine Or.inr fun u v A B C D α' β' huv hu hv hov => hex ?_
        push Not at hthr
        exact ⟨π, u, v, A, B, C, D, α', β', huv, hu, hv, hov.1, hov.2, hthr⟩

end ZenoFront
