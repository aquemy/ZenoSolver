/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SchedBuild
public import ZenoFront.NonSymmetric
public import ZenoFront.Bridge

/-!
# Theorem 6.9 (schedulable domination)

**Theorem 6.9.** Under (A1-NS), with `p ≤ t`, every feasible plan that is event-ordered, or any
feasible plan if no city has `d = d̄ = 0`, gives a valid scheduled configuration with `2t − p`
landings, cost at most the plan's and closed form (Lemma 6.3) at most its makespan
(`schedulableDomination`).

The proof follows the note.

* **Step 1** (`Feasible.split`, NonSymmetric.lean): central flights are replaced by detours
  through a hub. Every passenger's journey then contains a leg `C_I → x` followed by a leg
  `x → C_G` (`exists_transfer_pw`); these are its two flights after cleaning.
* **Event order.** The legs of the split plan get keys `(departure, ·, ·)` in `ℕ ×ₗ ℕ ×ₗ ℕ` that
  increase along routes and from the first to the second flight of every passenger:
  `(departure, old rank, part)` for an event-ordered plan (`eoKeys`, the two halves of a split leg
  taking its rank), `(departure, arrival, position)` when no city has `d = d̄ = 0` (`nzKeys`). In
  the second case a passenger's two flights depart at the same time only if `d_x = 0`, and then
  the second arrives later, since `d̄_x > 0`. This replaces Lemma 6.8(a)(b) of the note.
* The keyed routes, paired into visits (`vChain_pairs`), are the input of Step 2 (exchanges,
  `exists_ordered_handoffs`) and of Steps 3–6 (`exists_sched`).

**Scope.** The statement needs `p ≤ t`, which the model assumes (§1.1 of the note) and the checker
tests: a valid configuration has an odd number of crossings on every plane, so at least `p`
landings, and `2t − p < p` when `t < p`. `not_schedulableDomination` is the counterexample with
`t = 0` and `p = 1`, where `SchedulableDomination` as stated fails.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Routes, in order -/

theorem IsRoute.le_dep : ∀ {x : Loc n} {τ : ℕ} {L : List (Leg n t)}, IsRoute x τ L →
    (∀ ℓ ∈ L, ℓ.dep ≤ ℓ.arr) → ∀ ℓ ∈ L, τ ≤ ℓ.dep
  | _, _, [], _, _, _, h => absurd h List.not_mem_nil
  | _, _, m :: L, ⟨_, hτ, hL⟩, hdep, ℓ, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hτ
    · exact hτ.trans ((hdep m List.mem_cons_self).trans
        (hL.le_dep (fun ℓ hℓ => hdep ℓ (List.mem_cons_of_mem _ hℓ)) ℓ h))

theorem IsRoute.pairwise : ∀ {x : Loc n} {τ : ℕ} {L : List (Leg n t)}, IsRoute x τ L →
    (∀ ℓ ∈ L, ℓ.dep ≤ ℓ.arr) → L.Pairwise fun ℓ ℓ' => ℓ.arr ≤ ℓ'.dep
  | _, _, [], _, _ => List.Pairwise.nil
  | _, _, _ :: _, ⟨_, _, hL⟩, hdep => by
    have hdep' := fun ℓ hℓ => hdep ℓ (List.mem_cons_of_mem _ hℓ)
    exact List.Pairwise.cons (fun ℓ hℓ => hL.le_dep hdep' ℓ hℓ) (hL.pairwise hdep')

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

/-! ### Keyed plans, paired into visits -/

/-- Consecutive elements, two by two. -/
def pairs {α : Type*} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

variable {K : Type} [LinearOrder K]

/-- A keyed route without central flights, from a hub to a hub, is a chain of visits. -/
theorem vChain_pairs {N : Network n} : ∀ (L : List (KLeg n t K)) (s : VState n K),
    s.1.isHub = true → IsRoute s.1 s.2.1 (L.map KLeg.leg) →
    (∀ ℓ ∈ L, Flies N ℓ.leg ∧ ℓ.leg.central = false) → L.Pairwise (fun a b => a.key < b.key) →
    (∀ ℓ ∈ L, s.2.2 < (ℓ.key : WithBot K)) → (finalLoc s.1 (L.map KLeg.leg)).isHub = true →
    VChain N s (pairs L) ∧ (vEnd s (pairs L)).1 = finalLoc s.1 (L.map KLeg.leg) ∧
      legsOf (pairs L) = L
  | [], _, _, _, _, _, _, _ => by simp [pairs]
  | [ℓ], s, hs, hr, hf, _, _, hfin => by
    exfalso
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).1.dst_city_of_src_isHub (by
      simp only [List.map_cons, List.map_nil, isRoute_cons] at hr
      rw [hr.1]
      exact hs)
    simp [hx] at hfin
  | ℓ :: ℓ' :: rest, s, hs, hr, hf, hpw, hκ, hfin => by
    simp only [List.map_cons, isRoute_cons] at hr
    obtain ⟨hsrc, hτ, hsrc', hτ', hrest⟩ := hr
    obtain ⟨x, hx⟩ := (hf ℓ List.mem_cons_self).1.dst_city_of_src_isHub (by rw [hsrc]; exact hs)
    have hf' := hf ℓ' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hsrcx : ℓ'.leg.src = .city x := hsrc'.trans hx
    have hhub : ℓ'.leg.dst.isHub = true := by
      have := hf'.2
      simpa [Leg.central, hsrcx] using this
    obtain ⟨hℓ, hpw'⟩ := List.pairwise_cons.mp hpw
    obtain ⟨hℓ', hpw''⟩ := List.pairwise_cons.mp hpw'
    have hvok : VOK N s (ℓ, ℓ') :=
      ⟨hsrc, hτ, hκ ℓ List.mem_cons_self, by rw [hsrc]; exact hs, (hf ℓ List.mem_cons_self).1,
        hf'.1, ⟨x, hx, hsrcx⟩, hτ', hℓ ℓ' List.mem_cons_self, hhub⟩
    obtain ⟨h₁, h₂, h₃⟩ := vChain_pairs rest (ℓ'.leg.dst, ℓ'.leg.arr, (ℓ'.key : WithBot K)) hhub
      hrest (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) hpw''
      (fun m hm => WithBot.coe_lt_coe.mpr (hℓ' m hm)) (by simpa using hfin)
    exact ⟨⟨hvok, h₁⟩, h₂, by simp [pairs, h₃]⟩

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

/-- **Theorem 6.9 from a keyed plan.** A plan without central flights whose legs carry keys
that increase along routes, with departures first in the key, and whose passengers each have a
leg `C_I → x` followed, in time and in key, by a leg `x → C_G`, gives a valid scheduled
configuration with `2t − p` landings, cost at most the plan's and closed form at most its
makespan. -/
theorem sched_of_keyed {N : Network n} (c : Fin n → ℕ) (hpt : p ≤ t) {P : Plan n t p}
    (hP : ∀ k, PlaneFeasible N (P k)) (hcentral : ∀ k, ∀ m ∈ P k, m.central = false)
    (KL : Fin p → List (KLeg n t K)) (hKL : ∀ k, (KL k).map KLeg.leg = P k)
    (hpw : ∀ k, (KL k).Pairwise fun a b => a.key < b.key)
    (hdep : ∀ a b : KLeg n t K, a.key ≤ b.key → (∃ k, a ∈ KL k) → (∃ k, b ∈ KL k) →
      a.leg.dep ≤ b.leg.dep)
    (ℓα ℓβ : Fin t → KLeg n t K) (hmemα : ∀ π, ∃ k, ℓα π ∈ KL k)
    (hmemβ : ∀ π, ∃ k, ℓβ π ∈ KL k) (hpaxα : ∀ π, (ℓα π).leg.pax = some π)
    (hpaxβ : ∀ π, (ℓβ π).leg.pax = some π) (hsrcα : ∀ π, (ℓα π).leg.src = .ci)
    (hdstβ : ∀ π, (ℓβ π).leg.dst = .cg)
    (hcity : ∀ π, ∃ x, (ℓα π).leg.dst = .city x ∧ (ℓβ π).leg.src = .city x)
    (htime : ∀ π, (ℓα π).leg.arr ≤ (ℓβ π).leg.dep) (hkey : ∀ π, (ℓα π).key < (ℓβ π).key) :
    ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧ S.cost c ≤ planCost c P ∧
      S.tmpl N.d N.dbar ≤ planMakespan P := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    obtain rfl : p = 0 := by omega
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Sched.empty_spec (n := n) c N.d N.dbar
    exact ⟨Sched.empty, h₁, h₂, by omega, by omega⟩
  obtain ⟨x₀, -, -⟩ := hcity ⟨0, ht⟩
  set R : Fin p → List (Visit n t K) := fun k => pairs (KL k) with hRdef
  have hRk : ∀ k, VRoute N (R k) ∧ legsOf (R k) = KL k := fun k => by
    have hf : ∀ ℓ ∈ KL k, Flies N ℓ.leg ∧ ℓ.leg.central = false := fun ℓ hℓ => by
      have hm : ℓ.leg ∈ P k := hKL k ▸ List.mem_map_of_mem hℓ
      exact ⟨(hP k).flies _ hm, hcentral k _ hm⟩
    obtain ⟨h₁, h₂, h₃⟩ := vChain_pairs (N := N) (KL k) vStart rfl
      (by rw [hKL k]; exact (hP k).route) hf (hpw k) (fun ℓ _ => WithBot.bot_lt_coe _)
      (by simp only [vStart]; rw [hKL k, (hP k).ends]; rfl)
    refine ⟨⟨h₁, ?_⟩, h₃⟩
    rw [h₂]
    simp only [vStart]
    rw [hKL k]
    exact (hP k).ends
  have hall : allK R = ∑ k, (KL k : Multiset (KLeg n t K)) :=
    Finset.sum_congr rfl fun k _ => by rw [(hRk k).2]
  have hmem : ∀ ℓ, ℓ ∈ allK R ↔ ∃ k, ℓ ∈ KL k := fun ℓ => by
    rw [hall]
    simp [Multiset.mem_sum]
  have hpax : PaxData R ℓα ℓβ := ⟨fun π => (hmem _).mpr (hmemα π),
    fun π => (hmem _).mpr (hmemβ π), hpaxα, hpaxβ, hsrcα, hdstβ, hcity, htime, hkey⟩
  obtain ⟨R', hR', hall', hord⟩ := exists_ordered_handoffs (fun k => (hRk k).1) hpax
    fun ℓ hℓ ℓ' hℓ' h => hdep ℓ ℓ' h ((hmem ℓ).mp hℓ) ((hmem ℓ').mp hℓ')
  have hM : ∀ ℓ ∈ allK R', ℓ.leg.arr ≤ planMakespan P := fun ℓ hℓ => by
    rw [hall'] at hℓ
    obtain ⟨k, hk⟩ := (hmem ℓ).mp hℓ
    have hm : ℓ.leg ∈ P k := hKL k ▸ List.mem_map_of_mem hk
    exact (arr_le_endTime (P k) .ci 0 (hP k).route (fun m hm => ((hP k).flies m hm).dep_le_arr)
      _ hm).trans (endTime_le_planMakespan P k)
  obtain ⟨S, hS, hsize, hcost, htmpl⟩ := exists_sched hR' (hpax.of_allK_eq hall') hord hM hpt x₀ c
  refine ⟨S, hS, hsize, hcost.trans (le_of_eq ?_), htmpl⟩
  rw [hall', hall, sum_map_sum_coe]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hKL k, List.map_map]
  rfl

/-! ### Keys: `(departure, arrival, position)` when no city has `d = d̄ = 0` -/

/-- The lexicographic keys of the event order. -/
abbrev EKey := ℕ ×ₗ ℕ ×ₗ ℕ

theorem dep_le_dep_of_key_le {a b : KLeg n t EKey} (ha : (ofLex a.key).1 = a.leg.dep)
    (hb : (ofLex b.key).1 = b.leg.dep) (h : a.key ≤ b.key) : a.leg.dep ≤ b.leg.dep := by
  rw [← ha, ← hb]
  exact Prod.Lex.monotone_fst _ _ h

/-- The keys `(departure, arrival, position)` of the legs of a route. -/
def nzKeys (L : List (Leg n t)) : List (KLeg n t EKey) :=
  (List.finRange L.length).map fun i => ⟨L[i], toLex (L[i].dep, toLex (L[i].arr, i.val))⟩

theorem nzKeys_map_leg (L : List (Leg n t)) : (nzKeys L).map KLeg.leg = L := by
  simp only [nzKeys, List.map_map]
  exact List.map_getElem_finRange L

theorem nzKeys_dep {L : List (Leg n t)} {a : KLeg n t EKey} (h : a ∈ nzKeys L) :
    (ofLex a.key).1 = a.leg.dep := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  rfl

theorem exists_mem_nzKeys {L : List (Leg n t)} {ℓ : Leg n t} (h : ℓ ∈ L) :
    ∃ i : ℕ, (⟨ℓ, toLex (ℓ.dep, toLex (ℓ.arr, i))⟩ : KLeg n t EKey) ∈ nzKeys L := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩⟩

theorem nzKeys_pairwise {x : Loc n} {τ : ℕ} {L : List (Leg n t)} (hr : IsRoute x τ L)
    (hdep : ∀ ℓ ∈ L, ℓ.dep ≤ ℓ.arr) : (nzKeys L).Pairwise fun a b => a.key < b.key := by
  have hpw := List.pairwise_iff_getElem.mp (hr.pairwise hdep)
  unfold nzKeys
  rw [List.pairwise_map]
  refine (List.pairwise_lt_finRange _).imp fun {i j} hij => ?_
  have hij' : i.val < j.val := hij
  have h₁ := hpw i j i.isLt j.isLt hij'
  have h₂ := hdep L[i] (List.getElem_mem _)
  have h₃ := hdep L[j] (List.getElem_mem _)
  simp only [Fin.getElem_fin] at h₂ h₃ ⊢
  simp only [Prod.Lex.toLex_lt_toLex]
  omega

/-- When no city has `d = d̄ = 0`, a passenger's leg `C_I → x` has a smaller key than its later
leg `x → C_G`: if both depart at the same time, the first lasts `d_x = 0` and the second
`d̄_x > 0`. -/
theorem nz_key_lt {N : Network n} (hNZ : ∀ x, ¬ (N.d x = 0 ∧ N.dbar x = 0)) {ℓo ℓn : Leg n t}
    (hfo : Flies N ℓo) (hfn : Flies N ℓn) (hso : ℓo.src = .ci) {x : Fin n}
    (hx : ℓo.dst = .city x) (hy : ℓn.src = .city x) (hdn : ℓn.dst = .cg)
    (ht : ℓo.arr ≤ ℓn.dep) (i j : ℕ) :
    (toLex (ℓo.dep, toLex (ℓo.arr, i)) : EKey) < toLex (ℓn.dep, toLex (ℓn.arr, j)) := by
  obtain ⟨τo, hdo, hao⟩ := hfo
  obtain ⟨τn, hdn', han⟩ := hfn
  rw [hso, hx] at hdo
  rw [hy, hdn] at hdn'
  simp only [Network.duration, Option.some.injEq] at hdo hdn'
  have := hNZ x
  simp only [Prod.Lex.toLex_lt_toLex]
  omega

/-! ### Keys: `(departure, rank, part)` for an event-ordered plan -/

/-- The keys `(departure, rank, part)` of the halves of a split leg of rank `r`. -/
def eoSplit (N : Network n) (ℓ : Leg n t) (r : ℕ) : List (KLeg n t EKey) :=
  ((splitLeg N ℓ).zipIdx).map fun mi => ⟨mi.1, toLex (mi.1.dep, toLex (r, mi.2))⟩

/-- The keys of the split legs of a list of legs of `P`. -/
def eoKeys (N : Network n) (P : Plan n t p) (rank : LegId P → ℕ) (os : List (LegId P)) :
    List (KLeg n t EKey) :=
  os.flatMap fun o => eoSplit N (legAt P o) (rank o)

/-- The legs of plane `k`, by position. -/
def planeIds (P : Plan n t p) (k : Fin p) : List (LegId P) :=
  (List.finRange (P k).length).map fun i => ⟨k, i⟩

theorem planeIds_map_legAt (P : Plan n t p) (k : Fin p) :
    (planeIds P k).map (legAt P) = P k := by
  simp only [planeIds, List.map_map]
  exact List.map_getElem_finRange (P k)

theorem mem_planeIds (P : Plan n t p) (o : LegId P) : o ∈ planeIds P o.1 :=
  List.mem_map.mpr ⟨o.2, List.mem_finRange _, rfl⟩

theorem eoSplit_map_leg (N : Network n) (ℓ : Leg n t) (r : ℕ) :
    (eoSplit N ℓ r).map KLeg.leg = splitLeg N ℓ := by
  simp only [eoSplit, List.map_map]
  exact List.zipIdx_map_fst 0 _

theorem eoKeys_map_leg (N : Network n) (P : Plan n t p) (rank : LegId P → ℕ)
    (os : List (LegId P)) :
    (eoKeys N P rank os).map KLeg.leg = (os.map (legAt P)).flatMap (splitLeg N) := by
  simp only [eoKeys, List.map_flatMap, eoSplit_map_leg, List.flatMap_map]

theorem mem_eoSplit {N : Network n} {ℓ : Leg n t} {r : ℕ} {a : KLeg n t EKey}
    (h : a ∈ eoSplit N ℓ r) :
    a.leg ∈ splitLeg N ℓ ∧ ∃ i : ℕ, a.key = toLex (a.leg.dep, toLex (r, i)) := by
  obtain ⟨⟨m, i⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨List.fst_mem_of_mem_zipIdx hm, i, rfl⟩

theorem mem_eoKeys {N : Network n} {P : Plan n t p} {rank : LegId P → ℕ} {os : List (LegId P)}
    {a : KLeg n t EKey} (h : a ∈ eoKeys N P rank os) :
    ∃ o ∈ os, a ∈ eoSplit N (legAt P o) (rank o) := by
  simpa [eoKeys] using h

section EO

variable {N : Network n} (hA : N.A1NS)
include hA

theorem splitLeg_bounds {ℓ : Leg n t} (hℓ : Flies N ℓ) {m : Leg n t} (hm : m ∈ splitLeg N ℓ) :
    ℓ.dep ≤ m.dep ∧ m.dep ≤ m.arr ∧ m.arr ≤ ℓ.arr := by
  obtain ⟨hpieces, hroute, -, hend, -⟩ := splitLeg_spec hA hℓ
  have hdep : ∀ m ∈ splitLeg N ℓ, m.dep ≤ m.arr := fun m hm => (hpieces m hm).1.dep_le_arr
  have hr := hroute ℓ.dep le_rfl
  exact ⟨hr.le_dep hdep m hm, hdep m hm,
    (arr_le_endTime _ _ _ hr hdep m hm).trans (hend ℓ.dep)⟩

theorem eoSplit_pairwise {ℓ : Leg n t} (hℓ : Flies N ℓ) (r : ℕ) :
    (eoSplit N ℓ r).Pairwise fun a b => a.key < b.key := by
  obtain ⟨hpieces, hroute, -, -, -⟩ := splitLeg_spec hA hℓ
  have hdep : ∀ m ∈ splitLeg N ℓ, m.dep ≤ m.arr := fun m hm => (hpieces m hm).1.dep_le_arr
  have hpw := List.pairwise_iff_getElem.mp ((hroute ℓ.dep le_rfl).pairwise hdep)
  unfold eoSplit
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_zipIdx] at hi hj
  simp only [List.getElem_zipIdx, zero_add, Prod.Lex.toLex_lt_toLex, lt_self_iff_false,
    false_or, true_and]
  have h₁ := hpw i j hi hj hij
  have h₂ := hdep _ (List.getElem_mem hi)
  omega

theorem eoKeys_pairwise {P : Plan n t p} (rank : LegId P → ℕ) {os : List (LegId P)}
    (hrank : os.Pairwise fun o o' => rank o < rank o')
    (htime : (os.map (legAt P)).Pairwise fun ℓ ℓ' => ℓ.arr ≤ ℓ'.dep)
    (hfl : ∀ o ∈ os, Flies N (legAt P o)) :
    (eoKeys N P rank os).Pairwise fun a b => a.key < b.key := by
  unfold eoKeys
  rw [List.pairwise_flatMap]
  refine ⟨fun o ho => eoSplit_pairwise hA (hfl o ho) _, ?_⟩
  refine (List.Pairwise.and_mem.mp (hrank.and (List.pairwise_map.mp htime))).imp
    fun {o o'} h a ha b hb => ?_
  obtain ⟨ho, ho', hr, ht⟩ := h
  obtain ⟨ha₁, i, hai⟩ := mem_eoSplit ha
  obtain ⟨hb₁, j, hbj⟩ := mem_eoSplit hb
  have h₁ := splitLeg_bounds hA (hfl o ho) ha₁
  have h₂ := splitLeg_bounds hA (hfl o' ho') hb₁
  rw [hai, hbj, Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  omega

end EO

/-! ### Theorem 6.9 -/

/-- **Theorem 6.9 (schedulable domination)**, for `p ≤ t`. Under (A1-NS), every feasible plan
that is event-ordered, or any feasible plan if no city has `d = d̄ = 0`, gives a valid scheduled
configuration with `2t − p` landings, cost at most the plan's and closed form at most its
makespan. -/
theorem schedulableDomination {N : Network n} (c : Fin n → ℕ) (hpt : p ≤ t) :
    SchedulableDomination N c t p := by
  intro hA P hP hcase
  obtain ⟨hP', hcost, hmk, hcentral⟩ := hP.split hA
  suffices H : ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧
      S.cost c ≤ planCost c (splitPlan N P) ∧ S.tmpl N.d N.dbar ≤ planMakespan (splitPlan N P) by
    obtain ⟨S, h₁, h₂, h₃, h₄⟩ := H
    exact ⟨S, h₁, h₂, h₃.trans (hcost c).le, h₄.trans hmk⟩
  rcases hcase with ⟨rank, -, hroute, -, hjs⟩ | hNZ
  · -- An event-ordered plan: keys `(departure, rank, part)`.
    have hflo : ∀ o : LegId P, Flies N (legAt P o) := fun o =>
      (hP.planes o.1).flies _ (List.getElem_mem _)
    set KL : Fin p → List (KLeg n t EKey) := fun k => eoKeys N P rank (planeIds P k) with hKLdef
    have hKL : ∀ k, (KL k).map KLeg.leg = splitPlan N P k := fun k => by
      simp only [KL, eoKeys_map_leg, planeIds_map_legAt]
      rfl
    have hpw : ∀ k, (KL k).Pairwise fun a b => a.key < b.key := fun k =>
      eoKeys_pairwise hA rank
        (by
          unfold planeIds
          rw [List.pairwise_map]
          exact (List.pairwise_lt_finRange _).imp fun {i j} h => hroute k i j h)
        (by
          rw [planeIds_map_legAt]
          exact (hP.planes k).route.pairwise fun ℓ hℓ => ((hP.planes k).flies ℓ hℓ).dep_le_arr)
        (fun o _ => hflo o)
    have hkeydep : ∀ k, ∀ a ∈ KL k, (ofLex a.key).1 = a.leg.dep := fun k a ha => by
      obtain ⟨o, -, ho⟩ := mem_eoKeys ha
      obtain ⟨-, i, hi⟩ := mem_eoSplit ho
      rw [hi]
      rfl
    -- The two flights of every passenger, from its journey split into keyed legs.
    have htr : ∀ π, ∃ a b : KLeg n t EKey, (∃ k, a ∈ KL k) ∧ (∃ k, b ∈ KL k) ∧
        a.leg.pax = some π ∧ b.leg.pax = some π ∧ a.leg.src = .ci ∧ b.leg.dst = .cg ∧
        (∃ x, a.leg.dst = .city x ∧ b.leg.src = .city x) ∧ a.leg.arr ≤ b.leg.dep ∧
        a.key < b.key := by
      intro π
      obtain ⟨js, hperm, hjr, hjf, hjpw⟩ := hjs π
      have hjpax : ∀ o ∈ js, (legAt P o).pax = some π := fun o ho =>
        (mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp (List.mem_map_of_mem ho))).2
      have hjfl : ∀ ℓ ∈ js.map (legAt P), Flies N ℓ := fun ℓ hℓ =>
        hP.flies_of_mem_allLegs (mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)).1
      obtain ⟨a, ha, b, hb, hsrc, hcity, hdst, htime, hkey⟩ :=
        exists_transfer_pw (N := N) KLeg.leg (fun a b : KLeg n t EKey => a.key < b.key)
          (eoKeys N P rank js) 0
          (eoKeys_pairwise hA rank hjpw (hjr.pairwise fun ℓ hℓ => (hjfl ℓ hℓ).dep_le_arr)
            fun o _ => hflo o)
          (by rw [eoKeys_map_leg]; exact isRoute_flatMap_split hA hjr hjfl)
          (fun a ha => by
            obtain ⟨o, -, hao⟩ := mem_eoKeys ha
            have := (splitLeg_spec hA (hflo o)).1 _ (mem_eoSplit hao).1
            exact ⟨this.1, this.2.1⟩)
          (by rw [eoKeys_map_leg, finalLoc_flatMap_split hA _ hjfl]; exact hjf)
      have hmemKL : ∀ a ∈ eoKeys N P rank js, (∃ k, a ∈ KL k) ∧ a.leg.pax = some π :=
        fun a ha => by
          obtain ⟨o, ho, hao⟩ := mem_eoKeys ha
          refine ⟨⟨o.1, List.mem_flatMap.mpr ⟨o, mem_planeIds P o, hao⟩⟩, ?_⟩
          rw [((splitLeg_spec hA (hflo o)).1 _ (mem_eoSplit hao).1).2.2]
          exact hjpax o ho
      exact ⟨a, b, (hmemKL a ha).1, (hmemKL b hb).1, (hmemKL a ha).2, (hmemKL b hb).2, hsrc,
        hdst, hcity, htime, hkey⟩
    choose ℓα ℓβ hmα hmβ hpα hpβ hsα hdβ hcy htm hky using htr
    exact sched_of_keyed c hpt hP'.planes hcentral KL hKL hpw
      (fun a b h ⟨k, ha⟩ ⟨k', hb⟩ => dep_le_dep_of_key_le (hkeydep k a ha) (hkeydep k' b hb) h)
      ℓα ℓβ hmα hmβ hpα hpβ hsα hdβ hcy htm hky
  · -- No city with `d = d̄ = 0`: keys `(departure, arrival, position)`.
    set P' := splitPlan N P with hP'def
    set KL : Fin p → List (KLeg n t EKey) := fun k => nzKeys (P' k) with hKLdef
    have hflies' : ∀ ℓ ∈ allLegs P', Flies N ℓ := fun ℓ hℓ => hP'.flies_of_mem_allLegs hℓ
    have hcent' : ∀ ℓ ∈ allLegs P', ℓ.central = false := fun ℓ hℓ => by
      obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hℓ
      exact hcentral k ℓ hk
    have htr : ∀ π, ∃ a b : KLeg n t EKey, (∃ k, a ∈ KL k) ∧ (∃ k, b ∈ KL k) ∧
        a.leg.pax = some π ∧ b.leg.pax = some π ∧ a.leg.src = .ci ∧ b.leg.dst = .cg ∧
        (∃ x, a.leg.dst = .city x ∧ b.leg.src = .city x) ∧ a.leg.arr ≤ b.leg.dep ∧
        a.key < b.key := by
      intro π
      obtain ⟨route, hperm, hr, hfin⟩ := hP'.pax π
      have hmem : ∀ ℓ ∈ route, ℓ ∈ allLegs P' ∧ ℓ.pax = some π := fun ℓ hℓ =>
        mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)
      obtain ⟨ℓo, hℓo, ℓn, hℓn, hsrc, ⟨x, hx, hy⟩, hdst, htime, -⟩ :=
        exists_transfer_pw (N := N) id (fun _ _ : Leg n t => True) route 0
          (List.pairwise_of_forall fun _ _ => trivial) (by simpa using hr)
          (fun ℓ hℓ => ⟨hflies' ℓ (hmem ℓ hℓ).1, hcent' ℓ (hmem ℓ hℓ).1⟩) (by simpa using hfin)
      obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp (hmem ℓo hℓo).1
      obtain ⟨k', -, hk'⟩ := List.mem_flatMap.mp (hmem ℓn hℓn).1
      obtain ⟨i, hi⟩ := exists_mem_nzKeys hk
      obtain ⟨j, hj⟩ := exists_mem_nzKeys hk'
      exact ⟨_, _, ⟨k, hi⟩, ⟨k', hj⟩, (hmem ℓo hℓo).2, (hmem ℓn hℓn).2, hsrc, hdst, ⟨x, hx, hy⟩,
        htime, nz_key_lt hNZ (hflies' _ (hmem ℓo hℓo).1) (hflies' _ (hmem ℓn hℓn).1) hsrc hx hy
          hdst htime i j⟩
    choose ℓα ℓβ hmα hmβ hpα hpβ hsα hdβ hcy htm hky using htr
    exact sched_of_keyed c hpt hP'.planes hcentral KL (fun k => nzKeys_map_leg _)
      (fun k => nzKeys_pairwise (hP'.planes k).route fun ℓ hℓ =>
        ((hP'.planes k).flies ℓ hℓ).dep_le_arr)
      (fun a b h ⟨_, ha⟩ ⟨_, hb⟩ => dep_le_dep_of_key_le (nzKeys_dep ha) (nzKeys_dep hb) h)
      ℓα ℓβ hmα hmβ hpα hpβ hsα hdβ hcy htm hky

/-- **`SchedulableDomination` needs `p ≤ t`.** With one city (`d = d̄ = 1`), no passenger and one
plane flying `C_I → 1 → C_G`, the plan is feasible, event-ordered and has no city with
`d = d̄ = 0`, but every valid configuration on one plane has an odd number of crossings, so at
least one landing, while `2t − p = 0`. -/
theorem not_schedulableDomination :
    ¬ SchedulableDomination (n := 1) ⟨fun _ => 1, fun _ => 1, fun _ _ => 2⟩ (fun _ => 0) 0 1 := by
  intro h
  have hA : Network.A1NS (⟨fun _ => 1, fun _ => 1, fun _ _ => 2⟩ : Network 1) := fun _ _ => by
    simp
  let P : Plan 1 0 1 := fun _ => [⟨.ci, .city 0, 0, 1, none⟩, ⟨.city 0, .cg, 1, 2, none⟩]
  have hP : Feasible ⟨fun _ => 1, fun _ => 1, fun _ _ => 2⟩ P := by
    refine ⟨fun k => ⟨fun ℓ hℓ => ?_, ?_, rfl⟩, fun π => π.elim0⟩
    · simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl <;> exact ⟨1, rfl, rfl⟩
    · simp [P]
  obtain ⟨S, hS, hsize, -, -⟩ := h hA P hP (Or.inr fun x => by simp)
  obtain ⟨r, hr⟩ := hS.odd 0
  have : (S.cross 0).card ≤ S.size := by
    simp only [Sched.size, Fin.sum_univ_one]
    omega
  omega

end ZenoFront
