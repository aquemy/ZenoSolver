/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Converse

/-!
# The converse to role configurations (Theorem 6.1)

**Theorem 6.1 (N1).** Under (A1-NS), central flights are no shorter than a detour through one of
the hubs: `dc a b ≥ min(d_a + d_b, d̄_a + d̄_b)`. Then every feasible plan with cost `C` and
makespan `M` gives a role configuration on the `p` planes with passenger count `t`, cost at most
`C`, and role loads `λ_k ≤ M` (`Feasible.exists_roleConfig_ns`). The role load of a plane is
`2 δ(Dr_k) + 2 δ̄(Pk_k) + δ(Cr_k) + δ̄(Cr_k)`: a drop-off at `x` weighs `2 d_x`, a pick-up
`2 d̄_x`, a crossing `d_x + d̄_x`.

The proof follows the note.

* **Step 1** (`Feasible.split`). Replace every central flight `a → b` by `a → h → b`, `h` the hub
  of the shorter detour (`splitLeg`). By (A1-NS) the plane reaches `b` no later, and waits there;
  a passenger on board stays on board through `h`. The plan stays feasible, has the same cost and
  no larger makespan, and has no central flight.
* **Steps 2–3.** On a plan without central flights, the landing records of `Converse.lean` (each
  landing with its entry and exit hubs) are exactly its segments, and a landing's two legs last
  exactly its role weight (`roleW_landingRecs_le`). Direct selection
  (`Feasible.exists_roleConfig_records`, shared with Theorem 4.7) gives a role configuration with
  at least `t` passengers whose roles are records of their plane, so `λ_k` is at most the plane's
  flight time.
* **Shrinking** (Lemma 4.4, `RoleConfig.exists_shrink`) brings the passenger count to `t`:
  remove two crossings of a plane that has at least three, or else a drop-off and a pick-up at
  the same city.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-- Assumption (A1-NS): a central flight is no shorter than a detour through one of the hubs. -/
def Network.A1NS (N : Network n) : Prop :=
  ∀ i j, min (N.d i + N.d j) (N.dbar i + N.dbar j) ≤ N.dc i j

/-- Whether a leg joins two central cities. -/
def Leg.central (ℓ : Leg n t) : Bool := !ℓ.src.isHub && !ℓ.dst.isHub

/-! ### Step 1: removing central flights -/

/-- Replace a central flight `a → b` by `a → h → b` through the hub of the shorter detour, with
the same passenger; other legs are kept. -/
def splitLeg (N : Network n) (ℓ : Leg n t) : List (Leg n t) :=
  match ℓ.src, ℓ.dst with
  | .city a, .city b =>
    if N.d a + N.d b ≤ N.dbar a + N.dbar b then
      [⟨.city a, .ci, ℓ.dep, ℓ.dep + N.d a, ℓ.pax⟩,
       ⟨.ci, .city b, ℓ.dep + N.d a, ℓ.dep + N.d a + N.d b, ℓ.pax⟩]
    else
      [⟨.city a, .cg, ℓ.dep, ℓ.dep + N.dbar a, ℓ.pax⟩,
       ⟨.cg, .city b, ℓ.dep + N.dbar a, ℓ.dep + N.dbar a + N.dbar b, ℓ.pax⟩]
  | _, _ => [ℓ]

/-- A plan with every central flight split. -/
def splitPlan (N : Network n) (P : Plan n t p) : Plan n t p := fun k => (P k).flatMap (splitLeg N)

theorem IsRoute.mono : ∀ {x : Loc n} {τ τ' : ℕ} {l : List (Leg n t)},
    IsRoute x τ l → τ' ≤ τ → IsRoute x τ' l
  | _, _, _, [], _, _ => trivial
  | _, _, _, _ :: _, ⟨h₁, h₂, h₃⟩, h => ⟨h₁, h.trans h₂, h₃⟩

theorem isRoute_append : ∀ {x : Loc n} {τ : ℕ} (L M : List (Leg n t)),
    IsRoute x τ (L ++ M) ↔ IsRoute x τ L ∧ IsRoute (finalLoc x L) (endTime τ L) M
  | _, _, [], _ => by simp
  | x, τ, ℓ :: L, M => by
    simp only [List.cons_append, IsRoute, finalLoc_cons, endTime_cons, isRoute_append L M]
    tauto

theorem finalLoc_append (x : Loc n) : ∀ (L M : List (Leg n t)),
    finalLoc x (L ++ M) = finalLoc (finalLoc x L) M
  | [], _ => rfl
  | ℓ :: L, M => finalLoc_append ℓ.dst L M

theorem endTime_append (τ : ℕ) : ∀ (L M : List (Leg n t)),
    endTime τ (L ++ M) = endTime (endTime τ L) M
  | [], _ => rfl
  | ℓ :: L, M => endTime_append ℓ.arr L M

theorem endTime_mono {a b : ℕ} (h : a ≤ b) : ∀ M : List (Leg n t), endTime a M ≤ endTime b M
  | [] => h
  | _ :: _ => le_rfl

/-- What splitting a leg gives, for a flight of the network under (A1-NS). -/
theorem splitLeg_spec {N : Network n} (hA : N.A1NS) {ℓ : Leg n t} (hℓ : Flies N ℓ) :
    (∀ m ∈ splitLeg N ℓ, Flies N m ∧ m.central = false ∧ m.pax = ℓ.pax) ∧
    (∀ τ, τ ≤ ℓ.dep → IsRoute ℓ.src τ (splitLeg N ℓ)) ∧
    (∀ x, finalLoc x (splitLeg N ℓ) = ℓ.dst) ∧
    (∀ τ, endTime τ (splitLeg N ℓ) ≤ ℓ.arr) ∧
    (∀ c : Fin n → ℕ, ((splitLeg N ℓ).map (landCost c)).sum = landCost c ℓ) := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  obtain ⟨τ₀, hdur, harr⟩ := hℓ
  simp only at hdur harr
  cases src with
  | city a =>
    cases dst with
    | city b =>
      simp only [Network.duration, Option.some.injEq] at hdur
      have hA' := hA a b
      simp only [splitLeg]
      split_ifs with hab
      · refine ⟨fun m hm => ?_, fun τ hτ => ?_, fun x => rfl, fun τ => ?_, fun c => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨rfl, hτ, rfl, le_rfl, trivial⟩
        · simp only [endTime_cons, endTime_nil]
          rw [min_eq_left hab] at hA'
          omega
        · simp [landCost]
      · refine ⟨fun m hm => ?_, fun τ hτ => ?_, fun x => rfl, fun τ => ?_, fun c => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
          · exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨rfl, hτ, rfl, le_rfl, trivial⟩
        · simp only [endTime_cons, endTime_nil]
          rw [min_eq_right (by omega)] at hA'
          omega
        · simp [landCost]
    | ci =>
      simp only [splitLeg]
      exact ⟨fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm; exact ⟨⟨τ₀, hdur, harr⟩, rfl, rfl⟩,
        fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
    | cg =>
      simp only [splitLeg]
      exact ⟨fun m hm => by
        simp only [List.mem_singleton] at hm; subst hm; exact ⟨⟨τ₀, hdur, harr⟩, rfl, rfl⟩,
        fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
  | ci =>
    simp only [splitLeg]
    exact ⟨fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact ⟨⟨τ₀, hdur, harr⟩, by simp [Leg.central], rfl⟩,
      fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩
  | cg =>
    simp only [splitLeg]
    exact ⟨fun m hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact ⟨⟨τ₀, hdur, harr⟩, by simp [Leg.central], rfl⟩,
      fun τ hτ => ⟨rfl, hτ, trivial⟩, fun x => rfl, fun τ => le_rfl, fun c => by simp⟩

section Split

variable {N : Network n} (hA : N.A1NS)
include hA

theorem isRoute_flatMap_split : ∀ {x : Loc n} {τ : ℕ} {l : List (Leg n t)}, IsRoute x τ l →
    (∀ ℓ ∈ l, Flies N ℓ) → IsRoute x τ (l.flatMap (splitLeg N))
  | _, _, [], _, _ => trivial
  | x, τ, ℓ :: rest, ⟨hsrc, hdep, hrest⟩, hf => by
    obtain ⟨-, hroute, hfin, hend, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, isRoute_append]
    refine ⟨hsrc ▸ hroute τ hdep, ?_⟩
    rw [hfin]
    exact (isRoute_flatMap_split hrest fun m hm => hf m (List.mem_cons_of_mem _ hm)).mono
      (hend τ)

theorem finalLoc_flatMap_split : ∀ (x : Loc n) {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    finalLoc x (l.flatMap (splitLeg N)) = finalLoc x l
  | _, [], _ => rfl
  | x, ℓ :: rest, hf => by
    obtain ⟨-, -, hfin, -, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, finalLoc_append, hfin, finalLoc_cons]
    exact finalLoc_flatMap_split ℓ.dst fun m hm => hf m (List.mem_cons_of_mem _ hm)

theorem endTime_flatMap_split : ∀ (τ : ℕ) {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    endTime τ (l.flatMap (splitLeg N)) ≤ endTime τ l
  | _, [], _ => le_rfl
  | τ, ℓ :: rest, hf => by
    obtain ⟨-, -, -, hend, -⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, endTime_append, endTime_cons]
    exact (endTime_mono (hend τ) _).trans
      (endTime_flatMap_split ℓ.arr fun m hm => hf m (List.mem_cons_of_mem _ hm))

theorem landCost_flatMap_split (c : Fin n → ℕ) : ∀ {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    ((l.flatMap (splitLeg N)).map (landCost c)).sum = (l.map (landCost c)).sum
  | [], _ => rfl
  | ℓ :: rest, hf => by
    obtain ⟨-, -, -, -, hcost⟩ := splitLeg_spec hA (hf ℓ List.mem_cons_self)
    rw [List.flatMap_cons, List.map_append, List.sum_append, hcost, List.map_cons, List.sum_cons,
      landCost_flatMap_split c fun m hm => hf m (List.mem_cons_of_mem _ hm)]

theorem mem_flatMap_split {l : List (Leg n t)} (hf : ∀ ℓ ∈ l, Flies N ℓ) {m : Leg n t}
    (hm : m ∈ l.flatMap (splitLeg N)) :
    ∃ ℓ ∈ l, Flies N m ∧ m.central = false ∧ m.pax = ℓ.pax := by
  obtain ⟨ℓ, hℓ, hmℓ⟩ := List.mem_flatMap.mp hm
  exact ⟨ℓ, hℓ, (splitLeg_spec hA (hf ℓ hℓ)).1 m hmℓ⟩

theorem filter_flatMap_split (π : Fin t) : ∀ {l : List (Leg n t)}, (∀ ℓ ∈ l, Flies N ℓ) →
    (l.flatMap (splitLeg N)).filter (fun ℓ => decide (ℓ.pax = some π)) =
      (l.filter fun ℓ => decide (ℓ.pax = some π)).flatMap (splitLeg N)
  | [], _ => rfl
  | ℓ :: rest, hf => by
    have hpax := fun m hm => ((splitLeg_spec hA (hf ℓ List.mem_cons_self)).1 m hm).2.2
    have ih := filter_flatMap_split π fun m hm => hf m (List.mem_cons_of_mem _ hm)
    rw [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
    by_cases hℓ : ℓ.pax = some π
    · rw [List.filter_eq_self.mpr fun m hm => by simp [hpax m hm, hℓ]]
      simp [hℓ]
    · rw [List.filter_eq_nil_iff.mpr fun m hm => by simp [hpax m hm, hℓ]]
      simp [hℓ]

/-- **Step 1 of Theorem 6.1.** Under (A1-NS), splitting every central flight keeps a plan
feasible, with the same cost, no larger makespan, and no central flight. -/
theorem Feasible.split {P : Plan n t p} (hP : Feasible N P) :
    Feasible N (splitPlan N P) ∧ (∀ c, planCost c (splitPlan N P) = planCost c P) ∧
      planMakespan (splitPlan N P) ≤ planMakespan P ∧
      ∀ k, ∀ m ∈ splitPlan N P k, m.central = false := by
  have hall : allLegs (splitPlan N P) = (allLegs P).flatMap (splitLeg N) := by
    simp only [allLegs, List.flatMap_assoc]
    rfl
  have hflies : ∀ ℓ ∈ allLegs P, Flies N ℓ := fun ℓ hℓ => hP.flies_of_mem_allLegs hℓ
  refine ⟨⟨fun k => ⟨fun m hm => ?_, ?_, ?_⟩, fun π => ?_⟩, fun c => ?_, ?_, fun k m hm => ?_⟩
  · obtain ⟨ℓ, -, h, -⟩ := mem_flatMap_split hA (hP.planes k).flies hm
    exact h
  · exact isRoute_flatMap_split hA (hP.planes k).route (hP.planes k).flies
  · rw [splitPlan, finalLoc_flatMap_split hA _ (hP.planes k).flies]
    exact (hP.planes k).ends
  · obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
    have hrf : ∀ ℓ ∈ route, Flies N ℓ := fun ℓ hℓ =>
      hflies ℓ (List.mem_filter.mp (hperm.mem_iff.mp hℓ)).1
    refine ⟨route.flatMap (splitLeg N), ?_, isRoute_flatMap_split hA hroute hrf, ?_⟩
    · rw [paxLegs, hall, filter_flatMap_split hA π hflies]
      exact hperm.flatMap_right _
    · rw [finalLoc_flatMap_split hA _ hrf]
      exact hfin
  · exact Finset.sum_congr rfl fun k _ => landCost_flatMap_split hA c (hP.planes k).flies
  · exact Finset.sup_le fun k _ =>
      (endTime_flatMap_split hA 0 (hP.planes k).flies).trans (endTime_le_planMakespan P k)
  · obtain ⟨ℓ, -, -, h, -⟩ := mem_flatMap_split hA (hP.planes k).flies hm
    exact h

end Split

/-! ### Role weights of landing records -/

/-- The role weight of a landing record: its entry leg and its exit leg, `d` through `C_I` and
`d̄` through `C_G`. A crossing (`A`, `Ā`) weighs `d + d̄`, a drop-off (`B`) `2d`, a pick-up (`B̄`)
`2d̄`. -/
def roleW (N : Network n) (r : Fin n × Bool × Bool) : ℕ :=
  (if r.2.1 then N.d r.1 else N.dbar r.1) + (if r.2.2 then N.d r.1 else N.dbar r.1)

theorem landingRecs_cons_of_isHub {ℓ : Leg n t} (h : ℓ.dst.isHub = true) :
    ∀ rest : List (Leg n t), landingRecs (ℓ :: rest) = landingRecs rest
  | [] => rfl
  | ℓ' :: rest => by
    obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
    cases dst <;> simp_all [landingRecs]

/-- **Role weights on a route without central flights**: the role weights of its landing
records add up to at most its flight time. -/
theorem roleW_landingRecs_le (N : Network n) : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ),
    IsRoute x τ legs → (∀ ℓ ∈ legs, Flies N ℓ ∧ ℓ.central = false) → x.isHub = true →
      ((landingRecs legs).map (roleW N)).sum ≤ durSum legs
  | [], _, _, _, _, _ => by simp [landingRecs]
  | [_], _, _, _, _, _ => by simp [landingRecs]
  | ℓ :: ℓ' :: rest, x, τ, hr, hf, hx => by
    obtain ⟨hsrc, -, hsrc', -, hrest⟩ := hr
    obtain ⟨hfl, -⟩ := hf ℓ List.mem_cons_self
    obtain ⟨hfl', hc'⟩ := hf ℓ' (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨y, hy⟩ := hfl.dst_city_of_src_isHub (hsrc ▸ hx)
    have hsrcy : ℓ'.src = .city y := hsrc'.trans hy
    have hdst' : ℓ'.dst.isHub = true := by
      simp only [Leg.central, hsrcy, Loc.isHub, Bool.not_false, Bool.true_and,
        Bool.not_eq_false'] at hc'
      exact hc'
    have ih := roleW_landingRecs_le N rest ℓ'.dst ℓ'.arr hrest
      (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))) hdst'
    have hrec : landingRecs (ℓ :: ℓ' :: rest) =
        (y, ℓ.src.isCI, ℓ'.dst.isCI) :: landingRecs rest := by
      rw [← landingRecs_cons_of_isHub hdst' rest]
      simp only [landingRecs, hy]
    rw [hrec]
    simp only [List.map_cons, List.sum_cons, durSum] at ih ⊢
    have hw : roleW N (y, ℓ.src.isCI, ℓ'.dst.isCI) ≤ (ℓ.arr - ℓ.dep) + (ℓ'.arr - ℓ'.dep) := by
      obtain ⟨τ₁, hd₁, ha₁⟩ := hfl
      obtain ⟨τ₂, hd₂, ha₂⟩ := hfl'
      rw [hy] at hd₁
      rw [hsrcy] at hd₂
      have hx' : ℓ.src.isHub = true := hsrc ▸ hx
      have e₁ : (if ℓ.src.isCI then N.d y else N.dbar y) = τ₁ := by
        rcases hs : ℓ.src with _ | z | _
        · rw [hs] at hd₁; simpa [Network.duration, Loc.isCI] using hd₁
        · rw [hs] at hx'; simp [Loc.isHub] at hx'
        · rw [hs] at hd₁; simpa [Network.duration, Loc.isCI] using hd₁
      have e₂ : (if ℓ'.dst.isCI then N.d y else N.dbar y) = τ₂ := by
        rcases hs : ℓ'.dst with _ | z | _
        · rw [hs] at hd₂; simpa [Network.duration, Loc.isCI] using hd₂
        · rw [hs] at hdst'; simp [Loc.isHub] at hdst'
        · rw [hs] at hd₂; simpa [Network.duration, Loc.isCI] using hd₂
      unfold roleW
      simp only
      rw [e₁, e₂]
      omega
    omega

/-- The role load of plane `k` of a role configuration. -/
def RoleConfig.roleLoad (N : Network n) (cfg : RoleConfig n p) (k : Fin p) : ℕ :=
  2 * load N.d (cfg.drop k) + 2 * load N.dbar (cfg.pick k) + load N.d (cfg.cross k) +
    load N.dbar (cfg.cross k)

theorem sum_roleW (N : Network n) : ∀ R : List (Fin n × Bool × Bool),
    (R.map (roleW N)).sum = 2 * load N.d (recCities (fun r => r.2.1 && r.2.2) R) +
      2 * load N.dbar (recCities (fun r => !r.2.1 && !r.2.2) R) +
      load N.d (recCities (fun r => r.2.1 != r.2.2) R) +
      load N.dbar (recCities (fun r => r.2.1 != r.2.2) R)
  | [] => by simp [recCities]
  | ⟨x, a, b⟩ :: R => by
    have ih := sum_roleW N R
    rw [recCities_cons, recCities_cons, recCities_cons, List.map_cons, List.sum_cons, ih]
    cases a <;> cases b <;> simp [roleW] <;> omega

/-! ### Shrinking a role configuration (Lemma 4.4) -/

theorem RoleConfig.size_groups (cfg : RoleConfig n p) :
    size cfg.groups = 2 * ∑ k, (cfg.drop k).card + ∑ k, (cfg.cross k).card := by
  have h : ∑ k, (cfg.pick k).card = ∑ k, (cfg.drop k).card := by
    rw [← Multiset.card_sum, ← Multiset.card_sum, cfg.sum_drop_eq_sum_pick]
  simp only [size, RoleConfig.card_groups, Finset.sum_add_distrib, h]
  omega

theorem sum_card_update {α : Type*} (f : Fin p → Multiset α) (k₀ : Fin p) (Z : Multiset α) :
    ∑ k, (Function.update f k₀ Z k).card + (f k₀).card = ∑ k, (f k).card + Z.card := by
  have h₁ : ∀ k, (Function.update f k₀ Z k).card =
      Function.update (fun k => (f k).card) k₀ Z.card k := fun k => by
    by_cases hk : k = k₀
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  simp only [h₁]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k₀),
    Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase univ (fun k => (f k).card) (Finset.mem_univ k₀)]
  omega

/-- One shrinking step: a role configuration with at least `p + 2` landings has one with two
fewer, each role a sub-multiset of the old one. -/
theorem RoleConfig.exists_shrink_step (cfg : RoleConfig n p) (h : p + 2 ≤ size cfg.groups) :
    ∃ cfg' : RoleConfig n p, size cfg'.groups + 2 = size cfg.groups ∧
      (∀ k, cfg'.drop k ≤ cfg.drop k) ∧ (∀ k, cfg'.pick k ≤ cfg.pick k) ∧
      (∀ k, cfg'.cross k ≤ cfg.cross k) := by
  classical
  by_cases hcr : ∃ k₀, 3 ≤ (cfg.cross k₀).card
  · -- Remove two crossings.
    obtain ⟨k₀, hk₀⟩ := hcr
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (cfg.cross k₀).card)
    have h1 : ((cfg.cross k₀).erase y).card = (cfg.cross k₀).card - 1 := by
      rw [Multiset.card_erase_of_mem hy]; rfl
    obtain ⟨y', hy'⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by omega : 0 < ((cfg.cross k₀).erase y).card)
    set Z := ((cfg.cross k₀).erase y).erase y' with hZ
    have hZcard : Z.card + 2 = (cfg.cross k₀).card := by
      rw [hZ, Multiset.card_erase_of_mem hy', h1, Nat.pred_eq_sub_one]; omega
    have hZle : Z ≤ cfg.cross k₀ := (Multiset.erase_le _ _).trans (Multiset.erase_le _ _)
    refine ⟨⟨cfg.drop, cfg.pick, Function.update cfg.cross k₀ Z, fun k => ?_,
      cfg.sum_drop_eq_sum_pick⟩, ?_, fun k => le_rfl, fun k => le_rfl, fun k => ?_⟩
    · by_cases hk : k = k₀
      · subst hk
        rw [Function.update_self]
        obtain ⟨r, hr⟩ := cfg.odd_card_cross k
        exact ⟨r - 1, by omega⟩
      · rw [Function.update_of_ne hk]; exact cfg.odd_card_cross k
    · rw [RoleConfig.size_groups, RoleConfig.size_groups]
      dsimp only
      have := sum_card_update cfg.cross k₀ Z
      omega
    · show Function.update cfg.cross k₀ Z k ≤ cfg.cross k
      rw [Function.update_apply]
      split_ifs with hk
      · rw [hk]; exact hZle
      · exact le_rfl
  · -- Every plane has one crossing: remove a drop-off and a pick-up at the same city.
    push Not at hcr
    have hone : ∀ k, (cfg.cross k).card = 1 := fun k => by
      obtain ⟨r, hr⟩ := cfg.odd_card_cross k
      have := hcr k
      omega
    have hsz := cfg.size_groups
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hsz
    obtain ⟨u, hu⟩ : ∃ u, 0 < (cfg.drop u).card := by
      by_contra hall
      push Not at hall
      have : ∑ k, (cfg.drop k).card = 0 := Finset.sum_eq_zero fun k _ => by
        have := hall k; omega
      omega
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hu
    have hxP : x ∈ ∑ k, cfg.pick k := by
      rw [← cfg.sum_drop_eq_sum_pick]
      exact Multiset.mem_sum.mpr ⟨u, Finset.mem_univ _, hx⟩
    obtain ⟨v, -, hv⟩ := Multiset.mem_sum.mp hxP
    have hsplit : ∀ (f : Fin p → Multiset (Fin n)) (w : Fin p), x ∈ f w →
        ∑ k, f k = x ::ₘ ∑ k, Function.update f w ((f w).erase x) k := by
      intro f w hw
      have h1 := Finset.add_sum_erase univ f (Finset.mem_univ w)
      have h2 := Finset.add_sum_erase univ (Function.update f w ((f w).erase x)) (Finset.mem_univ w)
      have h3 : ∑ k ∈ univ.erase w, Function.update f w ((f w).erase x) k =
          ∑ k ∈ univ.erase w, f k :=
        Finset.sum_congr rfl fun k hk => Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _
      rw [Function.update_self] at h2
      rw [← h1, ← h2, h3, ← Multiset.cons_add, Multiset.cons_erase hw]
    refine ⟨⟨Function.update cfg.drop u ((cfg.drop u).erase x),
      Function.update cfg.pick v ((cfg.pick v).erase x), cfg.cross, cfg.odd_card_cross, ?_⟩,
      ?_, fun k => ?_, fun k => ?_, fun k => le_rfl⟩
    · have h₁ := hsplit cfg.drop u hx
      have h₂ := hsplit cfg.pick v hv
      rw [cfg.sum_drop_eq_sum_pick, h₂] at h₁
      exact ((Multiset.cons_inj_right x).mp h₁).symm
    · have hd : (∑ k, (Function.update cfg.drop u ((cfg.drop u).erase x) k).card) + 1 =
          ∑ k, (cfg.drop k).card := by
        rw [← Multiset.card_sum, ← Multiset.card_sum, hsplit cfg.drop u hx, Multiset.card_cons]
      rw [RoleConfig.size_groups]
      dsimp only
      rw [hsz]
      simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      omega
    · show Function.update cfg.drop u ((cfg.drop u).erase x) k ≤ cfg.drop k
      rw [Function.update_apply]
      split_ifs with hk
      · rw [hk]; exact Multiset.erase_le _ _
      · exact le_rfl
    · show Function.update cfg.pick v ((cfg.pick v).erase x) k ≤ cfg.pick k
      rw [Function.update_apply]
      split_ifs with hk
      · rw [hk]; exact Multiset.erase_le _ _
      · exact le_rfl

/-- **Lemma 4.4 (SH), role form.** A role configuration with `s + 2N` landings, `p ≤ s`, has one
with exactly `s` landings, each role a sub-multiset of the old one. -/
theorem RoleConfig.exists_shrink {s : ℕ} (hps : p ≤ s) : ∀ (N : ℕ) (cfg : RoleConfig n p),
    size cfg.groups = s + 2 * N → ∃ cfg' : RoleConfig n p, size cfg'.groups = s ∧
      (∀ k, cfg'.drop k ≤ cfg.drop k) ∧ (∀ k, cfg'.pick k ≤ cfg.pick k) ∧
      (∀ k, cfg'.cross k ≤ cfg.cross k)
  | 0, cfg, h => ⟨cfg, h, fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
  | N + 1, cfg, h => by
    obtain ⟨c₁, h₁, hd₁, hp₁, hc₁⟩ := cfg.exists_shrink_step (by omega)
    obtain ⟨c₂, h₂, hd₂, hp₂, hc₂⟩ := RoleConfig.exists_shrink hps N c₁ (by omega)
    exact ⟨c₂, h₂, fun k => (hd₂ k).trans (hd₁ k), fun k => (hp₂ k).trans (hp₁ k),
      fun k => (hc₂ k).trans (hc₁ k)⟩

theorem RoleConfig.roleLoad_mono (N : Network n) {cfg cfg' : RoleConfig n p} {k : Fin p}
    (hd : cfg'.drop k ≤ cfg.drop k) (hp : cfg'.pick k ≤ cfg.pick k)
    (hc : cfg'.cross k ≤ cfg.cross k) : cfg'.roleLoad N k ≤ cfg.roleLoad N k := by
  unfold RoleConfig.roleLoad
  have := load_mono N.d hd
  have := load_mono N.dbar hp
  have := load_mono N.d hc
  have := load_mono N.dbar hc
  omega

theorem RoleConfig.size_mod_two (cfg : RoleConfig n p) : size cfg.groups % 2 = p % 2 := by
  have h₁ := cfg.size_groups
  have h₂ : (∑ k, (cfg.cross k).card) % 2 = p % 2 := by
    rw [Finset.sum_nat_mod]
    have : ∀ k, (cfg.cross k).card % 2 = 1 := fun k => Nat.odd_iff.mp (cfg.odd_card_cross k)
    simp [this]
  omega

/-! ### Theorem 6.1 -/

/-- **Theorem 6.1 (converse to role configurations).** Under (A1-NS), with `p ≤ t`, every
feasible plan gives a role configuration on the `p` planes with `2t − p` landings (passenger
count `t`), cost at most the plan's, and every role load at most the makespan. -/
theorem Feasible.exists_roleConfig_ns {N : Network n} (hA : N.A1NS) (c : Fin n → ℕ)
    {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ cfg : RoleConfig n p, size cfg.groups = 2 * t - p ∧
      totalCost c cfg.groups ≤ planCost c P ∧ ∀ k, cfg.roleLoad N k ≤ planMakespan P := by
  obtain ⟨hP', hcost, hmk, hsimple⟩ := hP.split hA
  set P' := splitPlan N P
  obtain ⟨cfg, hdr, hpk, hcr, hsize⟩ := hP'.exists_roleConfig_records
  -- Role loads of the selected configuration.
  have hload : ∀ k, cfg.roleLoad N k ≤ planMakespan P := by
    intro k
    have h₁ := roleW_landingRecs_le N (P' k) .ci 0 (hP'.planes k).route
      (fun m hm => ⟨(hP'.planes k).flies m hm, hsimple k m hm⟩) rfl
    have h₂ := add_durSum_le_endTime (P' k) .ci 0 (hP'.planes k).route
      fun ℓ hℓ => ((hP'.planes k).flies ℓ hℓ).dep_le_arr
    rw [sum_roleW] at h₁
    have h₃ := load_mono N.d (hdr k)
    have h₄ := load_mono N.dbar (hpk k)
    have h₅ := endTime_le_planMakespan P' k
    unfold RoleConfig.roleLoad
    rw [hcr k]
    omega
  -- Groups are sub-multisets of the landings, so the cost is at most the plan's.
  have hsub : ∀ k, cfg.groups k ≤ routeLandings (P' k) := by
    intro k
    refine le_trans ?_ (landingRecs_map_fst_le (P' k))
    rw [← recCities_split]
    exact add_le_add (add_le_add (hdr k) (hpk k)) (le_of_eq (hcr k))
  have hcost' : totalCost c cfg.groups ≤ planCost c P := by
    calc totalCost c cfg.groups ≤ ∑ k, cost c (routeLandings (P' k)) :=
          Finset.sum_le_sum fun k _ => cost_mono c (hsub k)
      _ = ∑ k, landCostSum c (P' k) :=
          Finset.sum_congr rfl fun k _ => (landCostSum_eq_cost c (P' k)).symm
      _ = planCost c P := hcost c
  -- Shrink to exactly `2t − p` landings.
  have hmod := cfg.size_mod_two
  obtain ⟨cfg', hs', hd', hp', hc'⟩ := RoleConfig.exists_shrink (s := 2 * t - p) (by omega)
    ((size cfg.groups - (2 * t - p)) / 2) cfg (by omega)
  refine ⟨cfg', hs', ?_, fun k => (RoleConfig.roleLoad_mono N (hd' k) (hp' k) (hc' k)).trans
    (hload k)⟩
  refine le_trans (Finset.sum_le_sum fun k _ => cost_mono c ?_) hcost'
  exact add_le_add (add_le_add (hd' k) (hp' k)) (hc' k)

end ZenoFront
