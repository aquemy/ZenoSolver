/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Rewire
public import ZenoFront.NonSymmetric
public import ZenoFront.Bridge

/-!
# Theorem 5.3 for every plan

**Theorem 5.3 (schedulable domination), for every plan.** Under (A1-NS), with `p ≤ t`, every
feasible plan gives a valid scheduled configuration with `2t − p` landings, cost at most the
plan's and closed form (Lemma 5.5) at most its makespan (`schedulableDomination_all`). No event
order and no hypothesis on zero durations is needed, so it covers instances with a city of
`d = d̄ = 0` too.

* Step 1 (`Feasible.split`, `exists_transfer_pw`) gives routes of visits (`TRoute`,
  `tChain_pairs`) and every passenger's two flights: its last departure from `C_I`, a leg
  `C_I → x`, and the next leg, `x → C_G`.
* Step 2 (`exists_rewired`, Rewire.lean) exchanges, cuts and splices until every hand-off is
  ordered in time, keeping loops of zero-time visits on the side.
* Steps 3–6 (`exists_sched_of`, SchedBuild.lean) run on the planes' visits, with every loop
  attached to one plane (`withLoops`): its drop-offs first and its other visits last. They weigh
  nothing, so the drop-offs' prefix bound and the pick-ups' suffix bound hold (`planesOK_withLoops`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ} {K : Type}

/-! ### Step 1: the passengers' two flights -/

/-- **Step 1, the passengers.** In a route from `C_I` to `C_G` without central flights, some leg
`C_I → x` is followed by a leg `x → C_G`: the last departure from `C_I` and the next leg. They
are related by any pairwise relation of the route. -/
theorem exists_transfer_pw {N : Network n} {α : Type*} (f : α → Leg n t) (r : α → α → Prop) :
    ∀ (J : List α) (τ : ℕ), J.Pairwise r → IsRoute .ci τ (J.map f) →
      (∀ a ∈ J, Flies N (f a) ∧ (f a).central = false) → finalLoc .ci (J.map f) = .cg →
      ∃ a ∈ J, ∃ b ∈ J, (f a).src = .ci ∧ (∃ x, (f a).dst = .city x ∧ (f b).src = .city x) ∧
        (f b).dst = .cg ∧ (f a).arr ≤ (f b).dep ∧ r a b
  | [], _, _, _, _, h => by simp at h
  | [a], _, _, hr, hf, h => by
    obtain ⟨x, hx⟩ := (hf a List.mem_cons_self).1.dst_city_of_src_isHub (by simp [hr.1])
    simp [hx] at h
  | a :: b :: rest, τ, hpw, hr, hf, h => by
    simp only [List.map_cons, isRoute_cons] at hr
    obtain ⟨hsrc, -, hsrc', hab, hrest⟩ := hr
    obtain ⟨x, hx⟩ := (hf a List.mem_cons_self).1.dst_city_of_src_isHub (by simp [hsrc])
    have hbsrc : (f b).src = .city x := hsrc'.trans hx
    have hbhub : (f b).dst.isHub = true := by
      have := (hf b (List.mem_cons_of_mem _ List.mem_cons_self)).2
      simpa [Leg.central, hbsrc] using this
    by_cases hd : (f b).dst = .ci
    · rw [hd] at hrest
      have hfin : finalLoc .ci (rest.map f) = .cg := by
        simpa [finalLoc_cons, hd] using h
      obtain ⟨a', ha', b', hb', h'⟩ := exists_transfer_pw f r rest (f b).arr
        (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).2 hrest
        (fun a ha => hf a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))) hfin
      exact ⟨a', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha'), b',
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb'), h'⟩
    · have hcg : (f b).dst = .cg := by
        rcases hdst : (f b).dst with _ | z | _
        · exact absurd hdst hd
        · rw [hdst] at hbhub; simp at hbhub
        · rfl
      exact ⟨a, List.mem_cons_self, b, List.mem_cons_of_mem _ List.mem_cons_self, hsrc,
        ⟨x, hx, hbsrc⟩, hcg, hab, (List.pairwise_cons.mp hpw).1 b List.mem_cons_self⟩

/-- Consecutive elements, two by two. -/
def pairs {α : Type*} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

theorem sum_map_sum_coe {α : Type*} (L : Fin p → List α) (f : α → ℕ) :
    ((∑ k, (L k : Multiset α)).map f).sum = ∑ k, ((L k).map f).sum :=
  map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom f))
    (fun k => (L k : Multiset α)) univ

/-- The empty configuration, on no plane. -/
def Sched.empty : Sched n 0 := ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

theorem Sched.empty_spec (c d db : Fin n → ℕ) :
    (Sched.empty (n := n)).Valid ∧ (Sched.empty (n := n)).size = 0 ∧
      (Sched.empty (n := n)).cost c = 0 ∧ (Sched.empty (n := n)).tmpl d db = 0 := by
  refine ⟨⟨fun k => k.elim0, fun v => v.elim0, fun v => v.elim0, by simp⟩, by simp [Sched.size],
    by simp [Sched.cost], ?_⟩
  simp only [Sched.tmpl, Finset.univ_eq_empty, Finset.sup_empty]
  rfl

/-! ### Prefix and suffix bounds, through concatenation -/

/-- A drop-off `C_I → x → C_I`. -/
def Visit.isB (v : Visit n t K) : Bool := v.1.leg.src.isCI && v.2.leg.dst.isCI

/-- The drop-offs' prefix bound of a list of visits. -/
def PreOK (L : List (Visit n t K)) : Prop :=
  ∀ (m : ℕ) (hm : m < L.length), L[m].1.leg.src = .ci → L[m].2.leg.dst = .ci →
    ((L.take m).map Visit.w).sum ≤ L[m].1.leg.dep

/-- The pick-ups' suffix bound of a list of visits. -/
def SufOK (M : ℕ) (L : List (Visit n t K)) : Prop :=
  ∀ (m : ℕ) (hm : m < L.length), L[m].1.leg.src = .cg → L[m].2.leg.dst = .cg →
    L[m].2.leg.arr + ((L.drop (m + 1)).map Visit.w).sum ≤ M

theorem sum_w_eq_zero {L : List (Visit n t K)} (h : ∀ v ∈ L, v.w = 0) : (L.map Visit.w).sum = 0 :=
  List.sum_eq_zero fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact h v hv

theorem PreOK.zero_append {X L : List (Visit n t K)} (hX : ∀ v ∈ X, v.w = 0) (hL : PreOK L) :
    PreOK (X ++ L) := by
  intro m hm hs hd
  by_cases h : m < X.length
  · rw [List.take_append_of_le_length h.le,
      sum_w_eq_zero fun v hv => hX v (List.mem_of_mem_take hv)]
    exact Nat.zero_le _
  · push Not at h
    have hm' : m - X.length < L.length := by simp at hm; omega
    rw [List.getElem_append_right h] at hs hd ⊢
    rw [List.take_append, List.take_of_length_le h, List.map_append, List.sum_append,
      sum_w_eq_zero hX, zero_add]
    exact hL _ hm' hs hd

theorem PreOK.append_nonB {L Y : List (Visit n t K)} (hL : PreOK L)
    (hY : ∀ v ∈ Y, ¬ (v.1.leg.src = .ci ∧ v.2.leg.dst = .ci)) : PreOK (L ++ Y) := by
  intro m hm hs hd
  by_cases h : m < L.length
  · rw [List.getElem_append_left h] at hs hd ⊢
    rw [List.take_append_of_le_length h.le]
    exact hL m h hs hd
  · push Not at h
    have hm' : m - L.length < Y.length := by simp at hm; omega
    rw [List.getElem_append_right h] at hs hd
    exact absurd ⟨hs, hd⟩ (hY _ (List.getElem_mem hm'))

theorem SufOK.nonBbar_append {M : ℕ} {X L : List (Visit n t K)}
    (hX : ∀ v ∈ X, ¬ (v.1.leg.src = .cg ∧ v.2.leg.dst = .cg)) (hL : SufOK M L) :
    SufOK M (X ++ L) := by
  intro m hm hs hd
  by_cases h : m < X.length
  · rw [List.getElem_append_left h] at hs hd
    exact absurd ⟨hs, hd⟩ (hX _ (List.getElem_mem h))
  · push Not at h
    have hm' : m - X.length < L.length := by simp at hm; omega
    rw [List.getElem_append_right h, List.drop_append,
      List.drop_eq_nil_of_le (by omega : X.length ≤ m + 1), List.nil_append,
      show m + 1 - X.length = m - X.length + 1 by omega]
    rw [List.getElem_append_right h] at hs hd
    exact hL _ hm' hs hd

theorem SufOK.append_zero {M : ℕ} {L Y : List (Visit n t K)} (hL : SufOK M L)
    (hYw : ∀ v ∈ Y, v.w = 0) (hYM : ∀ v ∈ Y, v.2.leg.arr ≤ M) : SufOK M (L ++ Y) := by
  intro m hm hs hd
  by_cases h : m < L.length
  · rw [List.getElem_append_left h] at hs hd ⊢
    rw [List.drop_append, List.map_append, List.sum_append, sum_w_eq_zero fun v hv =>
      hYw v (List.mem_of_mem_drop hv), add_zero]
    exact hL m h hs hd
  · push Not at h
    have hm' : m - L.length < Y.length := by simp at hm; omega
    rw [List.getElem_append_right h, List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, sum_w_eq_zero fun v hv => hYw v (List.mem_of_mem_drop hv), add_zero]
    exact hYM _ (List.getElem_mem hm')

/-! ### Loops attached to one plane -/

/-- The visits of all loops. -/
def loopVisits (Q : List (ℕ × List (Visit n t K))) : List (Visit n t K) := Q.flatMap (·.2)

/-- The planes' visits for Steps 3–6: the routes, with the visits of every loop attached to plane
`k₀`, its drop-offs before the route and its other visits after it. -/
def withLoops (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K))) (k₀ : Fin p) :
    Fin p → List (Visit n t K) :=
  Function.update R k₀
    ((loopVisits Q).filter Visit.isB ++ R k₀ ++ (loopVisits Q).filter fun v => !v.isB)

theorem mem_loopVisits {Q : List (ℕ × List (Visit n t K))} {v : Visit n t K} :
    v ∈ loopVisits Q ↔ ∃ q ∈ Q, v ∈ q.2 := by
  simp [loopVisits]

theorem legsOf_loopVisits : ∀ Q : List (ℕ × List (Visit n t K)),
    (legsOf (loopVisits Q) : Multiset (KLeg n t K)) =
      (Q.map fun q => (legsOf q.2 : Multiset (KLeg n t K))).sum
  | [] => rfl
  | q :: Q => by
    simp only [loopVisits, List.flatMap_cons, legsOf_append, ← Multiset.coe_add, List.map_cons,
      List.sum_cons]
    rw [← legsOf_loopVisits Q]
    rfl

theorem allK_withLoops (R : Fin p → List (Visit n t K)) (Q : List (ℕ × List (Visit n t K)))
    (k₀ : Fin p) : allK (withLoops R Q k₀) = tLegs R Q := by
  have h := sum_update_one R (fun L => (legsOf L : Multiset (KLeg n t K))) k₀
    ((loopVisits Q).filter Visit.isB ++ R k₀ ++ (loopVisits Q).filter fun v => !v.isB)
  have hperm : ((loopVisits Q).filter Visit.isB ++ (loopVisits Q).filter fun v => !v.isB).Perm
      (loopVisits Q) := List.filter_append_perm _ _
  have e : (legsOf ((loopVisits Q).filter Visit.isB ++ R k₀ ++
      (loopVisits Q).filter fun v => !v.isB) : Multiset (KLeg n t K)) =
      (legsOf (R k₀) : Multiset _) + (legsOf (loopVisits Q) : Multiset _) := by
    have hp : (legsOf ((loopVisits Q).filter Visit.isB ++ (loopVisits Q).filter fun v => !v.isB) :
        Multiset (KLeg n t K)) = legsOf (loopVisits Q) :=
      Multiset.coe_eq_coe.mpr (by unfold legsOf; exact hperm.flatMap_right _)
    simp only [legsOf_append, ← Multiset.coe_add] at hp ⊢
    rw [← hp]
    ac_rfl
  change allK (withLoops R Q k₀) + _ = allK R + _ at h
  rw [e, ← add_assoc, legsOf_loopVisits] at h
  unfold tLegs
  exact add_right_cancel (h.trans (add_right_comm _ _ _))

theorem inV_iff_withLoops {R : Fin p → List (Visit n t K)} {Q : List (ℕ × List (Visit n t K))}
    {k₀ : Fin p} {w : Visit n t K} : InV R Q w ↔ ∃ k, w ∈ withLoops R Q k₀ k := by
  constructor
  · rintro (⟨k, hk⟩ | ⟨q, hq, hw⟩)
    · by_cases h : k = k₀
      · subst h
        exact ⟨k, by simp [withLoops, hk]⟩
      · exact ⟨k, by rw [withLoops, Function.update_of_ne h]; exact hk⟩
    · have hl : w ∈ loopVisits Q := mem_loopVisits.mpr ⟨q, hq, hw⟩
      refine ⟨k₀, ?_⟩
      simp only [withLoops, Function.update_self, List.mem_append, List.mem_filter]
      by_cases hb : w.isB = true
      · exact Or.inl (Or.inl ⟨hl, hb⟩)
      · exact Or.inr ⟨hl, by simpa using hb⟩
  · rintro ⟨k, hk⟩
    by_cases h : k = k₀
    · subst h
      simp only [withLoops, Function.update_self, List.mem_append, List.mem_filter] at hk
      rcases hk with (⟨hl, -⟩ | hk) | ⟨hl, -⟩
      · exact Or.inr (mem_loopVisits.mp hl)
      · exact Or.inl ⟨k, hk⟩
      · exact Or.inr (mem_loopVisits.mp hl)
    · rw [withLoops, Function.update_of_ne h] at hk
      exact Or.inl ⟨k, hk⟩

theorem countP_isA_loopVisits {N : Network n} : ∀ {Q : List (ℕ × List (Visit n t K))},
    (∀ q ∈ Q, TLoop N q.1 q.2) →
    (loopVisits Q).countP Visit.isA = (loopVisits Q).countP Visit.isAbar
  | [], _ => rfl
  | q :: Q, hQ => by
    have h₁ := (hQ q List.mem_cons_self).countP_isA
    have h₂ := countP_isA_loopVisits (Q := Q) fun q' hq' => hQ q' (List.mem_cons_of_mem _ hq')
    simp only [loopVisits, List.flatMap_cons, List.countP_append] at h₂ ⊢
    omega

/-- **The planes' visits satisfy what Steps 3–6 need.** -/
theorem planesOK_withLoops {N : Network n} {R : Fin p → List (Visit n t K)}
    {Q : List (ℕ × List (Visit n t K))} (hR : ∀ k, TRoute N (R k)) (hQ : ∀ q ∈ Q, TLoop N q.1 q.2)
    {M : ℕ} (hM : ∀ ℓ ∈ tLegs R Q, ℓ.leg.arr ≤ M) (k₀ : Fin p) :
    PlanesOK N M (withLoops R Q k₀) := by
  have hloop : ∀ v ∈ loopVisits Q, LocOK N v ∧ v.w = 0 ∧ v.2.leg.arr ≤ M := fun v hv => by
    obtain ⟨q, hq, hvq⟩ := mem_loopVisits.mp hv
    obtain ⟨-, hat, h, hc, -⟩ := hQ q hq
    refine ⟨hc.loc v hvq, Visit.w_of_atTime (hat v hvq), hM _ ?_⟩
    unfold tLegs
    rw [← legsOf_loopVisits]
    refine Multiset.mem_add.mpr (Or.inr ?_)
    simp only [Multiset.mem_coe, legsOf, List.mem_flatMap]
    exact ⟨v, hv, by simp⟩
  have hexit : ∀ k, ∀ v ∈ R k, v.2.leg.arr ≤ M := fun k v hv =>
    hM _ (Multiset.mem_add.mpr (Or.inl (mem_allK.mpr ⟨k, v, hv, Or.inr rfl⟩)))
  have hpre : ∀ k, PreOK (R k) := fun k m hm _ _ => by
    simpa using (hR k).1.time_le_dep m hm
  have hsuf : ∀ k, SufOK M (R k) := fun k m hm _ _ => (hR k).1.arr_add_le (hexit k) m hm
  set X := (loopVisits Q).filter Visit.isB
  set Y := (loopVisits Q).filter fun v => !v.isB
  have hX : ∀ v ∈ X, v ∈ loopVisits Q ∧ v.isB = true := fun v hv => List.mem_filter.mp hv
  have hY : ∀ v ∈ Y, v ∈ loopVisits Q ∧ v.isB = false := fun v hv => by
    simpa using List.mem_filter.mp hv
  have hk₀ : withLoops R Q k₀ k₀ = X ++ R k₀ ++ Y := by simp [withLoops, X, Y]
  have hk : ∀ k, k ≠ k₀ → withLoops R Q k₀ k = R k := fun k h => by
    rw [withLoops, Function.update_of_ne h]
  refine ⟨fun k v hv => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · by_cases h : k = k₀
    · subst h
      rw [hk₀] at hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact (hloop v (hX v hv).1).1
        · exact (hR k).1.loc v hv
      · exact (hloop v (hY v hv).1).1
    · rw [hk k h] at hv
      exact (hR k).1.loc v hv
  · by_cases h : k = k₀
    · subst h
      rw [hk₀]
      refine (PreOK.zero_append (fun v hv => (hloop v (hX v hv).1).2.1) (hpre k)).append_nonB
        fun v hv hci => ?_
      have := (hY v hv).2
      simp [Visit.isB, hci.1, hci.2] at this
    · rw [hk k h]
      exact hpre k
  · by_cases h : k = k₀
    · subst h
      rw [hk₀]
      refine (SufOK.nonBbar_append (fun v hv hcg => ?_) (hsuf k)).append_zero
        (fun v hv => (hloop v (hY v hv).1).2.1) (fun v hv => (hloop v (hY v hv).1).2.2)
      have := (hX v hv).2
      simp [Visit.isB, hcg.1] at this
    · rw [hk k h]
      exact hsuf k
  · by_cases h : k = k₀
    · subst h
      rw [hk₀, List.map_append, List.map_append, List.sum_append, List.sum_append,
        sum_w_eq_zero fun v hv => (hloop v (hX v hv).1).2.1,
        sum_w_eq_zero fun v hv => (hloop v (hY v hv).1).2.1]
      simpa using (hR k).1.sum_w_le (hexit k)
    · rw [hk k h]
      exact (hR k).1.sum_w_le (hexit k)
  · by_cases h : k = k₀
    · subst h
      rw [hk₀]
      have hl := countP_isA_loopVisits hQ
      have hr := (hR k).countP_isA
      have hXA : X.countP Visit.isA = 0 := List.countP_eq_zero.mpr fun v hv => by
        have := (hX v hv).2
        simp only [Visit.isB, Bool.and_eq_true] at this
        simp [Visit.isA, this.2]
      have hXAb : X.countP Visit.isAbar = 0 := List.countP_eq_zero.mpr fun v hv => by
        have := (hX v hv).2
        simp only [Visit.isB, Bool.and_eq_true] at this
        simp [Visit.isAbar, this.1]
      have hYA : Y.countP Visit.isA = (loopVisits Q).countP Visit.isA := by
        rw [List.countP_filter]
        refine List.countP_congr fun v _ => ?_
        simp only [Visit.isA, Visit.isB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          have := h.2
          simp_all
      have hYAb : Y.countP Visit.isAbar = (loopVisits Q).countP Visit.isAbar := by
        rw [List.countP_filter]
        refine List.countP_congr fun v _ => ?_
        simp only [Visit.isAbar, Visit.isB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          have := h.1
          simp_all
      simp only [List.countP_append]
      omega
    · rw [hk k h]
      exact (hR k).countP_isA

theorem mem_tLegs {R : Fin p → List (Visit n t K)} {Q : List (ℕ × List (Visit n t K))}
    {ℓ : KLeg n t K} (h : ℓ ∈ tLegs R Q) : ∃ w, InV R Q w ∧ (ℓ = w.1 ∨ ℓ = w.2) := by
  unfold tLegs at h
  rw [← legsOf_loopVisits] at h
  rcases Multiset.mem_add.mp h with h | h
  · obtain ⟨k, w, hw, he⟩ := mem_allK.mp h
    exact ⟨w, Or.inl ⟨k, hw⟩, he⟩
  · simp only [Multiset.mem_coe, legsOf, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨w, hw, he⟩ := h
    exact ⟨w, Or.inr (mem_loopVisits.mp hw), he⟩

theorem InV.loc {N : Network n} {R : Fin p → List (Visit n t K)}
    {Q : List (ℕ × List (Visit n t K))} (hR : ∀ k, TRoute N (R k)) (hQ : ∀ q ∈ Q, TLoop N q.1 q.2)
    {w : Visit n t K} (h : InV R Q w) : LocOK N w := by
  rcases h with ⟨k, hk⟩ | ⟨q, hq, hw⟩
  · exact (hR k).1.loc w hk
  · obtain ⟨-, -, h, hc, -⟩ := hQ q hq
    exact hc.loc w hw

/-- A route of legs without central flights, from a hub to a hub, is a chain of visits by time. -/
theorem tChain_pairs {N : Network n} : ∀ (L : List (KLeg n t K)) (s : TState n),
    s.1.isHub = true → IsRoute s.1 s.2 (L.map KLeg.leg) →
    (∀ ℓ ∈ L, Flies N ℓ.leg ∧ ℓ.leg.central = false) →
    (finalLoc s.1 (L.map KLeg.leg)).isHub = true →
    TChain N s (pairs L) ∧ (tEnd s (pairs L)).1 = finalLoc s.1 (L.map KLeg.leg) ∧
      legsOf (pairs L) = L
  | [], _, _, _, _, _ => by simp [pairs]
  | [ℓ], s, hs, hr, hf, hfin => by
    exfalso
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).1.dst_city_of_src_isHub (by
      simp only [List.map_cons, List.map_nil, isRoute_cons] at hr
      rw [hr.1]
      exact hs)
    simp [hx] at hfin
  | ℓ :: ℓ' :: rest, s, hs, hr, hf, hfin => by
    simp only [List.map_cons, isRoute_cons] at hr
    obtain ⟨hsrc, hτ, hsrc', hτ', hrest⟩ := hr
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).1.dst_city_of_src_isHub (by rw [hsrc]; exact hs)
    have hf' := hf ℓ' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hsrcx : ℓ'.leg.src = .city x := hsrc'.trans hx
    have hhub : ℓ'.leg.dst.isHub = true := by
      have := hf'.2
      simpa [Leg.central, hsrcx] using this
    have hvok : TOK N s (ℓ, ℓ') :=
      ⟨hsrc, hτ, ⟨by rw [hsrc]; exact hs, (hf ℓ List.mem_cons_self).1, hf'.1, ⟨x, hx, hsrcx⟩,
        hτ', hhub⟩⟩
    obtain ⟨h₁, h₂, h₃⟩ := tChain_pairs rest (ℓ'.leg.dst, ℓ'.leg.arr) hhub hrest
      (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) (by simpa using hfin)
    exact ⟨⟨hvok, h₁⟩, h₂, by simp [pairs, h₃]⟩

/-- **Theorem 5.3 (schedulable domination), for every plan.** Under (A1-NS), with `p ≤ t`, every
feasible plan gives a valid scheduled configuration with `2t − p` landings, cost at most the
plan's and closed form at most its makespan. No event order and no hypothesis on zero durations
is needed. -/
theorem schedulableDomination_all {N : Network n} (c : Fin n → ℕ) (hpt : p ≤ t) (hA : N.A1NS)
    {P : Plan n t p} (hP : Feasible N P) :
    ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧ S.cost c ≤ planCost c P ∧
      S.tmpl N.d N.dbar ≤ planMakespan P := by
  obtain ⟨hP', hcost, hmk, hcentral⟩ := hP.split hA
  suffices H : ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧
      S.cost c ≤ planCost c (splitPlan N P) ∧ S.tmpl N.d N.dbar ≤ planMakespan (splitPlan N P) by
    obtain ⟨S, h₁, h₂, h₃, h₄⟩ := H
    exact ⟨S, h₁, h₂, h₃.trans (hcost c).le, h₄.trans hmk⟩
  set P' := splitPlan N P with hP'def
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    obtain rfl : p = 0 := by omega
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Sched.empty_spec (n := n) c N.d N.dbar
    exact ⟨Sched.empty, h₁, h₂, by omega, by omega⟩
  -- The legs, as visits without keys.
  set KL : Fin p → List (KLeg n t Unit) := fun k => (P' k).map fun ℓ => ⟨ℓ, ()⟩ with hKLdef
  have hKL : ∀ k, (KL k).map KLeg.leg = P' k := fun k => by
    simp only [KL, List.map_map]
    exact List.map_id' _
  set R : Fin p → List (Visit n t Unit) := fun k => pairs (KL k) with hRdef
  have hRk : ∀ k, TRoute N (R k) ∧ legsOf (R k) = KL k := fun k => by
    have hf : ∀ ℓ ∈ KL k, Flies N ℓ.leg ∧ ℓ.leg.central = false := fun ℓ hℓ => by
      have hm : ℓ.leg ∈ P' k := hKL k ▸ List.mem_map_of_mem hℓ
      exact ⟨(hP'.planes k).flies _ hm, hcentral k _ hm⟩
    obtain ⟨h₁, h₂, h₃⟩ := tChain_pairs (N := N) (KL k) (.ci, 0) rfl
      (by rw [hKL k]; exact (hP'.planes k).route) hf
      (by rw [hKL k, (hP'.planes k).ends]; rfl)
    refine ⟨⟨h₁, ?_⟩, h₃⟩
    rw [h₂, hKL k]
    exact (hP'.planes k).ends
  have hall : allK R = ∑ k, (KL k : Multiset (KLeg n t Unit)) :=
    Finset.sum_congr rfl fun k _ => by rw [(hRk k).2]
  have hmemKL : ∀ ℓ, ℓ ∈ allK R ↔ ∃ k, ℓ ∈ KL k := fun ℓ => by
    rw [hall]
    simp [Multiset.mem_sum]
  -- Every passenger's two flights (Step 1).
  have htr : ∀ π, ∃ a b : Leg n t, a ∈ allLegs P' ∧ b ∈ allLegs P' ∧ a.pax = some π ∧
      b.pax = some π ∧ a.src = .ci ∧ b.dst = .cg ∧ (∃ x, a.dst = .city x ∧ b.src = .city x) ∧
      a.arr ≤ b.dep := by
    intro π
    obtain ⟨route, hperm, hr, hfin⟩ := hP'.pax π
    have hmem : ∀ ℓ ∈ route, ℓ ∈ allLegs P' ∧ ℓ.pax = some π := fun ℓ hℓ =>
      mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)
    have hcent : ∀ ℓ ∈ allLegs P', ℓ.central = false := fun ℓ hℓ => by
      obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hℓ
      exact hcentral k ℓ hk
    obtain ⟨a, ha, b, hb, hsrc, hcity, hdst, htime, -⟩ :=
      exists_transfer_pw (N := N) id (fun _ _ : Leg n t => True) route 0
        (List.pairwise_of_forall fun _ _ => trivial) (by simpa using hr)
        (fun ℓ hℓ => ⟨hP'.flies_of_mem_allLegs (hmem ℓ hℓ).1, hcent ℓ (hmem ℓ hℓ).1⟩)
        (by simpa using hfin)
    exact ⟨a, b, (hmem a ha).1, (hmem b hb).1, (hmem a ha).2, (hmem b hb).2, hsrc, hdst, hcity,
      htime⟩
  choose a b ha hb hpa hpb hsa hdb hcy htm using htr
  set ℓα : Fin t → KLeg n t Unit := fun π => ⟨a π, ()⟩ with hℓα
  set ℓβ : Fin t → KLeg n t Unit := fun π => ⟨b π, ()⟩ with hℓβ
  have hinKL : ∀ ℓ : Leg n t, ℓ ∈ allLegs P' → (⟨ℓ, ()⟩ : KLeg n t Unit) ∈ allK R := fun ℓ hℓ => by
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hℓ
    exact (hmemKL _).mpr ⟨k, List.mem_map_of_mem hk⟩
  have hends : PaxEnds ℓα ℓβ := ⟨hpa, hpb, hsa, hdb, hcy⟩
  have hpax : TPax R [] ℓα ℓβ :=
    ⟨fun π => by simpa [tLegs] using hinKL _ (ha π), fun π => by simpa [tLegs] using hinKL _ (hb π),
      hends, htm⟩
  -- Step 2.
  obtain ⟨R', Q', hR', hQ', hlegs, hfin⟩ := exists_rewired R [] (fun k => (hRk k).1)
    (by simp) hpax
  have hlegs' : tLegs R' Q' = allK R := by rw [hlegs]; simp [tLegs]
  have hM : ∀ ℓ ∈ tLegs R' Q', ℓ.leg.arr ≤ planMakespan P' := fun ℓ hℓ => by
    rw [hlegs'] at hℓ
    obtain ⟨k, hk⟩ := (hmemKL ℓ).mp hℓ
    have hm : ℓ.leg ∈ P' k := hKL k ▸ List.mem_map_of_mem hk
    exact (arr_le_endTime (P' k) .ci 0 (hP'.planes k).route
      (fun m hm => ((hP'.planes k).flies m hm).dep_le_arr) _ hm).trans
      (endTime_le_planMakespan P' k)
  -- A plane and a city to attach the loops and to stand for nothing.
  obtain ⟨k₀, -, -⟩ := List.mem_flatMap.mp (ha ⟨0, ht⟩)
  obtain ⟨x₀, -, -⟩ := hcy ⟨0, ht⟩
  have hplanes := planesOK_withLoops hR' hQ' hM k₀
  have hpax' := hpax.of_tLegs_eq hlegs
  -- Steps 3–6.
  have hord : ∀ π, ∃ (u : Fin p) (i : Fin (withLoops R' Q' k₀ u).length) (v : Fin p)
      (j : Fin (withLoops R' Q' k₀ v).length),
      (withLoops R' Q' k₀ u)[i].1 = ℓα π ∧ (withLoops R' Q' k₀ v)[j].2 = ℓβ π ∧
      ((⟨u, i⟩ : (k : Fin p) × Fin (withLoops R' Q' k₀ k).length) ≠ ⟨v, j⟩ →
        (withLoops R' Q' k₀ u)[i].2.leg.dep ≤ (withLoops R' Q' k₀ v)[j].1.leg.arr) := by
    intro π
    rcases hfin π with hc | hle
    · obtain ⟨u, hu⟩ := (inV_iff_withLoops (k₀ := k₀)).mp hc
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hu
      exact ⟨u, ⟨i, hi⟩, u, ⟨i, hi⟩, by simp [he], by simp [he], fun h => absurd rfl h⟩
    · obtain ⟨w₁, hw₁, he₁⟩ := mem_tLegs (hpax'.memα π)
      obtain ⟨w₂, hw₂, he₂⟩ := mem_tLegs (hpax'.memβ π)
      have e₁ : w₁.1 = ℓα π := by
        rcases he₁ with h | h
        · exact h.symm
        · exfalso
          obtain ⟨x, -, hx⟩ := (hw₁.loc hR' hQ').city
          rw [← h] at hx
          have := hsa π
          simp only [ℓα] at hx
          rw [this] at hx
          cases hx
      have e₂ : w₂.2 = ℓβ π := by
        rcases he₂ with h | h
        · exfalso
          obtain ⟨x, hx, -⟩ := (hw₂.loc hR' hQ').city
          rw [← h] at hx
          have := hdb π
          simp only [ℓβ] at hx
          rw [this] at hx
          cases hx
        · exact h.symm
      have hlt := hle w₁ w₂ hw₁ hw₂ e₁ e₂
      obtain ⟨u, hu⟩ := (inV_iff_withLoops (k₀ := k₀)).mp hw₁
      obtain ⟨v, hv⟩ := (inV_iff_withLoops (k₀ := k₀)).mp hw₂
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
      exact ⟨u, ⟨i, hi⟩, v, ⟨j, hj⟩, e₁, e₂, fun _ => hlt⟩
  obtain ⟨S, hS, hsize, hScost, htmpl⟩ := exists_sched_of hplanes hends hord hpt x₀ c
  refine ⟨S, hS, hsize, hScost.trans (le_of_eq ?_), htmpl⟩
  rw [allK_withLoops, hlegs', hall, sum_map_sum_coe]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [KL, List.map_map]
  rfl

end ZenoFront
