/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.NonSymmetric
public import ZenoFront.TreeBound
public import ZenoFront.Relaxation

/-!
# The `roles` bound of format v2

The role relaxation of `src/zeno/roles.cpp` (`RoleRelaxation::bound`) is a lower bound on the
cost of every role configuration on `p` planes with `s` landings and role loads at most `T`, the
larger of two bounds:

* **per plane** (`rolesA`): a plane flies an odd number of crossings, of weight `d + d̄`, and its
  drop-offs and pick-ups weigh at least `2 min(d, d̄)`. So its group costs at least the cheapest
  `m` landings with an odd number of crossings and weight at most `T` (`roleM_le`). The planes
  are combined by the relaxation DP over group sizes.
* **all planes** (`rolesB`): drop-offs and pick-ups pair up city by city (the balance), so the
  role loads add up to the crossing weight `δ + δ̄` of all the landings
  (`sum_roleLoad_eq_load_fill`). With every load at most `T`, all `s` landings weigh at most
  `p · T`, and cost at least the one-plane entry `G_fill[s][p · T]`.

With Corollary 5.4 (`Feasible.exists_roleConfig_of_domination`), this bounds the cost of every
feasible plan under (A1-NS).

## Main results

* `ZenoFront.rolesBoundAt_le_totalCost`: the bound is at most the cost of every role
  configuration with `s` landings and role loads at most `T`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### The per-plane table: `m` landings, crossings of a given parity -/

/-- Two rows of the per-plane table at a given number of landings: crossings of even and of odd
number, for budgets `0, …, Tmax`. -/
abbrev RoleRows := Array (WithTop ℕ) × Array (WithTop ℕ)

section Table

variable (d dbar c : Fin n → ℕ) (Tmax : ℕ)

/-- The weight of a crossing at `i`. -/
def fillW (i : Fin n) : ℕ := d i + dbar i

/-- The least weight of a drop-off or a pick-up at `i`. -/
def lowW (i : Fin n) : ℕ := 2 * min (d i) (dbar i)

/-- An entry of the per-plane table with `m + 1` landings, from the rows `prev` at `m`: the last
landing is a crossing (flipping the parity) or a drop-off or pick-up. -/
def roleEntry (prev : RoleRows) (par : Bool) (τ : ℕ) : WithTop ℕ :=
  minFin fun i =>
    min (if fillW d dbar i ≤ τ then
          (c i : WithTop ℕ) + (if par then prev.1 else prev.2).getD (τ - fillW d dbar i) ⊤
        else ⊤)
      (if lowW d dbar i ≤ τ then
          (c i : WithTop ℕ) + (if par then prev.2 else prev.1).getD (τ - lowW d dbar i) ⊤
        else ⊤)

/-- The rows at `m` landings. -/
def roleLayer (look : ℕ → RoleRows) (m : ℕ) : RoleRows :=
  if m = 0 then (Array.ofFn (n := Tmax + 1) fun _ => 0, Array.ofFn (n := Tmax + 1) fun _ => ⊤)
  else
    let prev := look (m - 1)
    (Array.ofFn (n := Tmax + 1) fun τ => roleEntry d dbar c prev false τ,
      Array.ofFn (n := Tmax + 1) fun τ => roleEntry d dbar c prev true τ)

/-- The per-plane table for `0, …, mMax` landings. -/
def roleLayers (mMax : ℕ) : Array RoleRows := buildLayers (roleLayer d dbar c Tmax) (#[], #[]) mMax

/-- The stored entry: `m` landings, crossing parity `par`, budget `τ`. -/
def roleM (mMax m : ℕ) (par : Bool) (τ : ℕ) : WithTop ℕ :=
  let L := (roleLayers d dbar c Tmax mMax).getD m (#[], #[])
  (if par then L.2 else L.1).getD τ ⊤

theorem roleLayer_congr (look look' : ℕ → RoleRows) (m : ℕ) (h : ∀ i < m, look i = look' i) :
    roleLayer d dbar c Tmax look m = roleLayer d dbar c Tmax look' m := by
  unfold roleLayer
  split_ifs with hm
  · rfl
  · rw [h (m - 1) (by omega)]

theorem roleM_eq {mMax m : ℕ} (hm : m ≤ mMax) (par : Bool) {τ : ℕ} (hτ : τ ≤ Tmax) :
    roleM d dbar c Tmax mMax m par τ =
      if m = 0 then (if par then ⊤ else 0)
      else roleEntry d dbar c ((roleLayers d dbar c Tmax mMax).getD (m - 1) (#[], #[])) par τ := by
  unfold roleM roleLayers
  rw [buildLayers_getD _ _ (roleLayer_congr d dbar c Tmax) hm]
  unfold roleLayer
  by_cases h₀ : m = 0
  · cases par <;> simp [h₀, show τ < Tmax + 1 by omega]
  · cases par <;> simp [h₀, show τ < Tmax + 1 by omega]

variable {d dbar c Tmax}

/-- **The per-plane table is a lower bound**: for crossings `Cr` and other landings `O`, with
`|Cr|` of parity `par` and `δ_fill(Cr) + δ_low(O) ≤ τ`, the entry at `|Cr| + |O|` landings is at
most `c(Cr + O)`. -/
theorem roleM_le {mMax : ℕ} : ∀ (m : ℕ) (par : Bool) (τ : ℕ) (Cr O : Multiset (Fin n)),
    m ≤ mMax → τ ≤ Tmax → Cr.card + O.card = m → (Cr.card % 2 = 1 ↔ par = true) →
    load (fillW d dbar) Cr + load (lowW d dbar) O ≤ τ →
      roleM d dbar c Tmax mMax m par τ ≤ (cost c (Cr + O) : WithTop ℕ)
  | 0, par, τ, Cr, O, _, hτ, hcard, hpar, _ => by
    rw [roleM_eq d dbar c Tmax (Nat.zero_le _) par hτ]
    have hCr : Cr = 0 := Multiset.card_eq_zero.mp (by omega)
    have hO : O = 0 := Multiset.card_eq_zero.mp (by omega)
    subst hCr hO
    cases par <;> simp_all
  | m + 1, par, τ, Cr, O, hm, hτ, hcard, hpar, hload => by
    rw [roleM_eq d dbar c Tmax hm par hτ, ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]
    unfold roleEntry
    rw [minFin_eq]
    by_cases hC : Cr = 0
    · -- The last landing is a drop-off or a pick-up.
      subst hC
      obtain ⟨i, O', rfl⟩ : ∃ i O', O = i ::ₘ O' := by
        obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by simp at hcard; omega : 0 < O.card)
        exact ⟨i, _, (Multiset.cons_erase hi).symm⟩
      simp only [load_cons, load_zero, zero_add, Multiset.card_zero, Multiset.card_cons] at hload hcard hpar
      have hO' : O'.card = m := by omega
      have ih := roleM_le (mMax := mMax) m par (τ - lowW d dbar i) 0 O' (by omega) (by omega)
        (by simp [hO']) (by simpa using hpar) (by simp only [load_zero, zero_add]; omega)
      refine (Finset.inf_le (Finset.mem_univ i)).trans ((min_le_right _ _).trans ?_)
      rw [ite_eq_left (by omega)]
      unfold roleM at ih
      cases par <;>
      · simp only [Bool.false_eq_true, ite_false, ite_true] at ih ⊢
        refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
        simp only [zero_add, cost_cons]
        push_cast
        rfl
    · -- The last landing is a crossing.
      obtain ⟨i, Cr', rfl⟩ : ∃ i Cr', Cr = i ::ₘ Cr' := by
        obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hC
        exact ⟨i, _, (Multiset.cons_erase hi).symm⟩
      simp only [load_cons, Multiset.card_cons] at hload hcard hpar
      have ih := roleM_le (mMax := mMax) m (!par) (τ - fillW d dbar i) Cr' O (by omega) (by omega)
        (by omega)
        (by cases par <;> simp at hpar ⊢ <;> omega) (by omega)
      refine (Finset.inf_le (Finset.mem_univ i)).trans ((min_le_left _ _).trans ?_)
      rw [ite_eq_left (by omega)]
      unfold roleM at ih
      cases par <;>
      · simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at ih ⊢
        refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
        simp only [Multiset.cons_add, cost_cons]
        push_cast
        rfl

end Table

/-! ### The bound -/

/-- The `roles` bound at level `T` for `p` planes and `s` landings, with tables up to level
`Tmax`: the larger of the per-plane bound and the all-planes bound; `0` (no bound) if
`T > Tmax`. -/
def rolesBoundAt (p s Tmax : ℕ) (L : Array RoleRows)
    (fillTable : Array (Array (WithTop ℕ))) (T : ℕ) : WithTop ℕ :=
  if T ≤ Tmax then
    max ((relaxRow (fun m => (L.getD m (#[], #[])).2.getD T ⊤) s p).getD s ⊤)
      ((fillTable.getD s #[]).getD (p * T) ⊤)
  else 0

theorem load_finset_sum (f : Fin n → ℕ) (Y : Fin p → Multiset (Fin n)) :
    load f (∑ k, Y k) = ∑ k, load f (Y k) := by
  simp only [load]
  have h₁ : (∑ k, Y k).map f = ∑ k, (Y k).map f := map_sum (Multiset.mapAddMonoidHom f) Y univ
  rw [h₁]
  exact map_sum Multiset.sumAddMonoidHom _ univ

theorem cost_finset_sum (c : Fin n → ℕ) (Y : Fin p → Multiset (Fin n)) :
    cost c (∑ k, Y k) = ∑ k, cost c (Y k) :=
  load_finset_sum c Y

/-- **The role loads add up to the crossing weight of the landings**, by the balance. -/
theorem sum_roleLoad_eq_load_fill (d dbar : Fin n → ℕ) (dc : Fin n → Fin n → ℕ)
    (cfg : RoleConfig n p) :
    ∑ k, cfg.roleLoad ⟨d, dbar, dc⟩ k = load (fillW d dbar) (∑ k, cfg.groups k) := by
  have hfill : ∀ Y, load (fillW d dbar) Y = load d Y + load dbar Y := fun Y =>
    load_add_fun d dbar Y
  have hbal := cfg.sum_drop_eq_sum_pick
  have hD : ∑ k, load d (cfg.drop k) = ∑ k, load d (cfg.pick k) := by
    rw [← load_finset_sum, ← load_finset_sum, hbal]
  have hDb : ∑ k, load dbar (cfg.drop k) = ∑ k, load dbar (cfg.pick k) := by
    rw [← load_finset_sum, ← load_finset_sum, hbal]
  rw [load_finset_sum]
  simp only [RoleConfig.roleLoad, RoleConfig.groups, load_add, hfill, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  omega

/-- **The `roles` bound is a lower bound** on the cost of every role configuration with `s`
landings and every role load at most `T`, for the tables computed from `d`, `d̄` and `c`. -/
theorem rolesBoundAt_le_totalCost (d dbar c : Fin n → ℕ) (dc : Fin n → Fin n → ℕ) {s Tmax T : ℕ}
    (cfg : RoleConfig n p) (hsize : size cfg.groups = s)
    (hload : ∀ k, cfg.roleLoad ⟨d, dbar, dc⟩ k ≤ T) :
    rolesBoundAt p s Tmax (roleLayers d dbar c Tmax s)
      (oneplaneTable (fillW d dbar) c (p * Tmax) s) T ≤ (totalCost c cfg.groups : WithTop ℕ) := by
  subst hsize
  unfold rolesBoundAt
  split_ifs with hT
  · refine max_le ?_ ?_
    · -- Per plane.
      rw [relaxRow_getD _ p le_rfl]
      have := relaxCost_le (fun m => roleM d dbar c Tmax (size cfg.groups) m true T) c
        (List.ofFn cfg.groups)
        fun y hy => by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
          have hcr := cfg.odd_card_cross k
          have hsk : (cfg.groups k).card ≤ size cfg.groups :=
            Finset.single_le_sum (f := fun j => (cfg.groups j).card) (fun j _ => Nat.zero_le _)
              (Finset.mem_univ k)
          refine ⟨by rw [RoleConfig.card_groups]; obtain ⟨r, hr⟩ := hcr; omega, ?_⟩
          have hlow : load (lowW d dbar) (cfg.drop k + cfg.pick k) ≤
              2 * load d (cfg.drop k) + 2 * load dbar (cfg.pick k) := by
            rw [load_add]
            have h₁ : load (lowW d dbar) (cfg.drop k) ≤ 2 * load d (cfg.drop k) := by
              simp only [load]
              rw [← Multiset.sum_map_mul_left]
              exact Multiset.sum_map_le_sum_map _ _ fun i _ => by
                unfold lowW; have := min_le_left (d i) (dbar i); omega
            have h₂ : load (lowW d dbar) (cfg.pick k) ≤ 2 * load dbar (cfg.pick k) := by
              simp only [load]
              rw [← Multiset.sum_map_mul_left]
              exact Multiset.sum_map_le_sum_map _ _ fun i _ => by
                unfold lowW; have := min_le_right (d i) (dbar i); omega
            omega
          have hfill : load (fillW d dbar) (cfg.cross k) =
              load d (cfg.cross k) + load dbar (cfg.cross k) := load_add_fun d dbar _
          have hl := hload k
          unfold RoleConfig.roleLoad at hl
          have h := roleM_le (d := d) (dbar := dbar) (c := c) (Tmax := Tmax)
            (mMax := size cfg.groups) (cfg.groups k).card true T
            (cfg.cross k) (cfg.drop k + cfg.pick k) hsk hT
            (by rw [RoleConfig.card_groups, Multiset.card_add]; omega)
            (by simpa using Nat.odd_iff.mp hcr) (by simp only at hl; omega)
          refine h.trans (le_of_eq ?_)
          congr 1
          simp only [RoleConfig.groups, cost_add]
          omega
      simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn] at this
      refine le_of_eq_of_le ?_ this
      congr 1
    · -- All planes.
      rw [oneplaneTable_getD (fillW d dbar) c le_rfl (Nat.mul_le_mul_left p hT)]
      have hsum := sum_roleLoad_eq_load_fill d dbar dc cfg
      have hle : ∑ k, cfg.roleLoad ⟨d, dbar, dc⟩ k ≤ p * T := by
        have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin p))) => hload k
        simpa using this
      have := oneplane_le_cost (d := fillW d dbar) (c := c) (m := size cfg.groups) (T := p * T)
        (Y := ∑ k, cfg.groups k) (by rw [Multiset.card_sum]; rfl) (hsum ▸ hle)
      rw [cost_finset_sum] at this
      exact this
  · exact zero_le

end ZenoFront
