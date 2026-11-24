/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.RoleBound

/-!
# The `lagrangian` bound of format v2

With one integer multiplier `μ_i` per city, charge a drop-off in `i` `c_i + μ_i` and a pick-up
`c_i − μ_i`. On a balanced role configuration the multipliers cancel (`Σ_k μ(Dr_k) = Σ_k μ(Pk_k)`),
so its cost is the sum of these charges. Dropping the balance, the planes decouple: each plane's
charge is at least the cheapest `m` landings with an odd number of crossings within the level
(`lagM_le`), and the planes combine by a DP over group sizes. So **every** `μ` gives a lower bound
on every balanced configuration with role loads at most `T` (`lagValue_le_totalCost`); the
checker evaluates it at the certificate's `μ` (`lagrangianValue` in `src/zeno/roles.cpp`).

As in the C++ checker, the cities are first reduced to representatives that are no slower to
`C_I`, no slower to `C_G` and no more expensive (`domRep3`); the representative is the first such
city in the order `(d, d̄, c, index)`, so it is one the C++ reduction keeps. Mapping a role
configuration to representatives keeps it balanced, with no larger role loads or cost
(`RoleConfig.map`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### Minima in `WithTop ℤ` -/

/-- The least of `f 0, …, f (u − 1)` (`⊤` for `u = 0`). -/
def minUpToZ (f : ℕ → WithTop ℤ) : ℕ → WithTop ℤ
  | 0 => ⊤
  | u + 1 => min (minUpToZ f u) (f u)

theorem minUpToZ_le (f : ℕ → WithTop ℤ) : ∀ {m u : ℕ}, m < u → minUpToZ f u ≤ f m
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | m, u + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact (min_le_left _ _).trans (minUpToZ_le f h)
    · exact min_le_right _ _

theorem minUpToZ_congr {f g : ℕ → WithTop ℤ} : ∀ {u : ℕ}, (∀ m < u, f m = g m) →
    minUpToZ f u = minUpToZ g u
  | 0, _ => rfl
  | u + 1, h => by
    simp only [minUpToZ]
    rw [minUpToZ_congr fun m hm => h m (by omega), h u (by omega)]

/-- A minimum over a list. -/
def minListZ {β : Type} (l : List β) (f : β → WithTop ℤ) : WithTop ℤ :=
  l.foldr (fun b acc => min (f b) acc) ⊤

theorem minListZ_le {β : Type} (f : β → WithTop ℤ) : ∀ {l : List β} {b : β}, b ∈ l →
    minListZ l f ≤ f b
  | _ :: _, _, .head _ => min_le_left _ _
  | _ :: _, _, .tail _ h => (min_le_right _ _).trans (minListZ_le f h)

theorem sum_map_sum_eq {β : Type*} [AddCommMonoid β] (f : Fin n → β)
    (Y : Fin p → Multiset (Fin n)) : ∑ k, ((Y k).map f).sum = ((∑ k, Y k).map f).sum := by
  suffices h : ∀ t : Finset (Fin p), ∑ k ∈ t, ((Y k).map f).sum = ((∑ k ∈ t, Y k).map f).sum from
    h univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Multiset.map_add,
      Multiset.sum_add]

theorem sum_map_eq_map_sum (f : Fin n → Fin n) (Y : Fin p → Multiset (Fin n)) :
    ∑ k, (Y k).map f = (∑ k, Y k).map f := by
  suffices h : ∀ t : Finset (Fin p), ∑ k ∈ t, (Y k).map f = (∑ k ∈ t, Y k).map f from h univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Multiset.map_add]

/-! ### The per-plane table -/

/-- The data of the Lagrangian bound: crossing, drop-off and pick-up weights (scaled), costs,
multipliers, the cities allowed, and the level. -/
structure LagData (n : ℕ) where
  fill : Fin n → ℕ
  drop : Fin n → ℕ
  pick : Fin n → ℕ
  c : Fin n → ℕ
  mu : Fin n → ℤ
  reps : List (Fin n)
  T : ℕ

/-- Two rows (even and odd crossings) at a number of landings, over budgets `0, …, T`. -/
abbrev ZRows := Array (WithTop ℤ) × Array (WithTop ℤ)

namespace LagData

variable (D : LagData n)

/-- The charge of a drop-off at `i`. -/
def dropCost (i : Fin n) : ℤ := (D.c i : ℤ) + D.mu i

/-- The charge of a pick-up at `i`. -/
def pickCost (i : Fin n) : ℤ := (D.c i : ℤ) - D.mu i

/-- An entry with one more landing than `prev`: a crossing (flipping the parity), a drop-off or
a pick-up. -/
def entry (prev : ZRows) (par : Bool) (τ : ℕ) : WithTop ℤ :=
  minListZ D.reps fun i =>
    min (if D.fill i ≤ τ then
          ((D.c i : ℤ) : WithTop ℤ) + (if par then prev.1 else prev.2).getD (τ - D.fill i) ⊤
        else ⊤)
      (min (if D.drop i ≤ τ then
            (D.dropCost i : WithTop ℤ) + (if par then prev.2 else prev.1).getD (τ - D.drop i) ⊤
          else ⊤)
        (if D.pick i ≤ τ then
            (D.pickCost i : WithTop ℤ) + (if par then prev.2 else prev.1).getD (τ - D.pick i) ⊤
          else ⊤))

/-- The rows at `m` landings. -/
def layer (look : ℕ → ZRows) (m : ℕ) : ZRows :=
  if m = 0 then (Array.ofFn (n := D.T + 1) fun _ => 0, Array.ofFn (n := D.T + 1) fun _ => ⊤)
  else
    let prev := look (m - 1)
    (Array.ofFn (n := D.T + 1) fun τ => D.entry prev false τ,
      Array.ofFn (n := D.T + 1) fun τ => D.entry prev true τ)

/-- The per-plane table for `0, …, mMax` landings. -/
def layers (mMax : ℕ) : Array ZRows := buildLayers D.layer (#[], #[]) mMax

/-- The stored entry. -/
def lagM (mMax m : ℕ) (par : Bool) (τ : ℕ) : WithTop ℤ :=
  let L := (D.layers mMax).getD m (#[], #[])
  (if par then L.2 else L.1).getD τ ⊤

theorem layer_congr (look look' : ℕ → ZRows) (m : ℕ) (h : ∀ i < m, look i = look' i) :
    D.layer look m = D.layer look' m := by
  unfold layer
  split_ifs with hm
  · rfl
  · rw [h (m - 1) (by omega)]

theorem lagM_eq {mMax m : ℕ} (hm : m ≤ mMax) (par : Bool) {τ : ℕ} (hτ : τ ≤ D.T) :
    D.lagM mMax m par τ = if m = 0 then (if par then ⊤ else 0)
      else D.entry ((D.layers mMax).getD (m - 1) (#[], #[])) par τ := by
  unfold lagM layers
  rw [buildLayers_getD _ _ D.layer_congr hm]
  unfold layer
  by_cases h₀ : m = 0
  · cases par <;> simp [h₀, show τ < D.T + 1 by omega]
  · cases par <;> simp [h₀, show τ < D.T + 1 by omega]

/-- The charge of a plane: crossings at cost, drop-offs and pick-ups at their charges. -/
def charge (Cr Dr Pk : Multiset (Fin n)) : ℤ :=
  (cost D.c Cr : ℤ) + (Dr.map D.dropCost).sum + (Pk.map D.pickCost).sum

/-- **The per-plane table is a lower bound** on the charge of every plane whose cities are allowed,
with crossings of parity `par` and weight at most `τ`. -/
theorem lagM_le {mMax : ℕ} : ∀ (m : ℕ) (par : Bool) (τ : ℕ) (Cr Dr Pk : Multiset (Fin n)),
    m ≤ mMax → τ ≤ D.T → Cr.card + Dr.card + Pk.card = m → (Cr.card % 2 = 1 ↔ par = true) →
    (∀ i ∈ Cr + Dr + Pk, i ∈ D.reps) →
    load D.fill Cr + load D.drop Dr + load D.pick Pk ≤ τ →
      D.lagM mMax m par τ ≤ (D.charge Cr Dr Pk : WithTop ℤ)
  | 0, par, τ, Cr, Dr, Pk, _, hτ, hcard, hpar, _, _ => by
    rw [D.lagM_eq (Nat.zero_le _) par hτ]
    have hC : Cr = 0 := Multiset.card_eq_zero.mp (by omega)
    have hD : Dr = 0 := Multiset.card_eq_zero.mp (by omega)
    have hP : Pk = 0 := Multiset.card_eq_zero.mp (by omega)
    subst hC hD hP
    cases par <;> simp_all [charge]
  | m + 1, par, τ, Cr, Dr, Pk, hm, hτ, hcard, hpar, hreps, hload => by
    rw [D.lagM_eq hm par hτ, ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]
    unfold entry
    have hstep : ∀ i ∈ D.reps, ∀ v : WithTop ℤ,
        (min (if D.fill i ≤ τ then ((D.c i : ℤ) : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).1
            else ((D.layers mMax).getD m (#[], #[])).2).getD (τ - D.fill i) ⊤ else ⊤)
        (min (if D.drop i ≤ τ then (D.dropCost i : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).2
            else ((D.layers mMax).getD m (#[], #[])).1).getD (τ - D.drop i) ⊤ else ⊤)
        (if D.pick i ≤ τ then (D.pickCost i : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).2
            else ((D.layers mMax).getD m (#[], #[])).1).getD (τ - D.pick i) ⊤ else ⊤))) ≤ v →
        minListZ D.reps (fun i => min (if D.fill i ≤ τ then ((D.c i : ℤ) : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).1
            else ((D.layers mMax).getD m (#[], #[])).2).getD (τ - D.fill i) ⊤ else ⊤)
        (min (if D.drop i ≤ τ then (D.dropCost i : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).2
            else ((D.layers mMax).getD m (#[], #[])).1).getD (τ - D.drop i) ⊤ else ⊤)
        (if D.pick i ≤ τ then (D.pickCost i : WithTop ℤ) +
          (if par then ((D.layers mMax).getD m (#[], #[])).2
            else ((D.layers mMax).getD m (#[], #[])).1).getD (τ - D.pick i) ⊤ else ⊤))) ≤ v :=
      fun i hi v h => (minListZ_le _ hi).trans h
    by_cases hC : Cr = 0
    · subst hC
      by_cases hD : Dr = 0
      · -- The last landing is a pick-up.
        subst hD
        obtain ⟨i, Pk', rfl⟩ : ∃ i Pk', Pk = i ::ₘ Pk' := by
          obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by simp at hcard; omega :
            0 < Pk.card)
          exact ⟨i, _, (Multiset.cons_erase hi).symm⟩
        simp only [load_cons, load_zero, zero_add, Multiset.card_zero, Multiset.card_cons]
          at hload hcard hpar
        have hi : i ∈ D.reps := hreps i (by simp)
        have ih := lagM_le (mMax := mMax) m par (τ - D.pick i) 0 0 Pk' (by omega) (by omega)
          (by simp; omega) (by simpa using hpar)
          (fun j hj => hreps j (by simp at hj ⊢; exact Or.inr hj)) (by simp; omega)
        refine hstep i hi _ ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
        rw [ite_eq_left (by omega)]
        unfold lagM at ih
        cases par <;>
        · simp only [Bool.false_eq_true, ite_false, ite_true] at ih ⊢
          refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
          rw [← WithTop.coe_add]
          congr 1
          simp only [charge, cost_zero, Multiset.map_zero, Multiset.sum_zero, Multiset.map_cons,
            Multiset.sum_cons]
          ring
      · -- The last landing is a drop-off.
        obtain ⟨i, Dr', rfl⟩ : ∃ i Dr', Dr = i ::ₘ Dr' := by
          obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hD
          exact ⟨i, _, (Multiset.cons_erase hi).symm⟩
        simp only [load_cons, load_zero, zero_add, Multiset.card_zero, Multiset.card_cons]
          at hload hcard hpar
        have hi : i ∈ D.reps := hreps i (by simp)
        have ih := lagM_le (mMax := mMax) m par (τ - D.drop i) 0 Dr' Pk (by omega) (by omega)
          (by simp; omega) (by simpa using hpar)
          (fun j hj => hreps j (by
            simp only [zero_add, Multiset.mem_add] at hj
            simp only [zero_add, Multiset.mem_add, Multiset.mem_cons]
            tauto)) (by simp; omega)
        refine hstep i hi _ ((min_le_right _ _).trans ((min_le_left _ _).trans ?_))
        rw [ite_eq_left (by omega)]
        unfold lagM at ih
        cases par <;>
        · simp only [Bool.false_eq_true, ite_false, ite_true] at ih ⊢
          refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
          rw [← WithTop.coe_add]
          congr 1
          simp only [charge, cost_zero, Multiset.map_cons, Multiset.sum_cons]
          ring
    · -- The last landing is a crossing.
      obtain ⟨i, Cr', rfl⟩ : ∃ i Cr', Cr = i ::ₘ Cr' := by
        obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hC
        exact ⟨i, _, (Multiset.cons_erase hi).symm⟩
      simp only [load_cons, Multiset.card_cons] at hload hcard hpar
      have hi : i ∈ D.reps := hreps i (by simp)
      have ih := lagM_le (mMax := mMax) m (!par) (τ - D.fill i) Cr' Dr Pk (by omega)
        (by omega) (by omega) (by cases par <;> simp at hpar ⊢ <;> omega)
        (fun j hj => hreps j (by
          simp only [Multiset.mem_add] at hj
          simp only [Multiset.cons_add, Multiset.mem_cons, Multiset.mem_add]
          tauto)) (by omega)
      refine hstep i hi _ ((min_le_left _ _).trans ?_)
      rw [ite_eq_left (by omega)]
      unfold lagM at ih
      cases par <;>
      · simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at ih ⊢
        refine (add_le_add le_rfl ih).trans (le_of_eq ?_)
        rw [← WithTop.coe_add]
        congr 1
        simp only [charge, cost_cons]
        push_cast
        ring

/-! ### Combining the planes -/

/-- `For[P'][J]`: `P'` planes with `J` landings, from `P' − 1` planes and one plane of
`m + 1` landings. -/
def forEntry (G : ℕ → WithTop ℤ) (look : ℕ → Array (WithTop ℤ)) (P' J : ℕ) : WithTop ℤ :=
  if P' = 0 then (if J = 0 then 0 else ⊤) else
    minUpToZ (fun m => (look (P' - 1)).getD (J - (m + 1)) ⊤ + G (m + 1)) J

/-- The table `For[P'][·]`. -/
def forLayer (S : ℕ) (G : ℕ → WithTop ℤ) (look : ℕ → Array (WithTop ℤ)) (P' : ℕ) :
    Array (WithTop ℤ) :=
  Array.ofFn (n := S + 1) fun J => forEntry G look P' J

/-- The Lagrangian value for `p` planes and `S` landings. -/
def value (p S : ℕ) : WithTop ℤ :=
  let L := D.layers S
  let G : ℕ → WithTop ℤ := fun m => (L.getD m (#[], #[])).2.getD D.T ⊤
  ((buildLayers (forLayer S G) #[] p).getD p #[]).getD S ⊤

theorem forLayer_congr (S : ℕ) (G : ℕ → WithTop ℤ) (look look' : ℕ → Array (WithTop ℤ))
    (q : ℕ) (h : ∀ i < q, look i = look' i) : forLayer S G look q = forLayer S G look' q := by
  unfold forLayer forEntry
  by_cases hq : q = 0
  · simp [hq]
  · simp only [hq, ite_false, h (q - 1) (by omega)]

/-- The planes' table bounds the sum of the planes' values. -/
theorem forM_le (S : ℕ) (G : ℕ → WithTop ℤ) (P : ℕ) :
    ∀ (l : List (ℕ × ℤ)), l.length ≤ P → (∀ x ∈ l, 1 ≤ x.1 ∧ G x.1 ≤ (x.2 : WithTop ℤ)) →
      (l.map Prod.fst).sum ≤ S →
      ((buildLayers (forLayer S G) #[] P).getD l.length #[]).getD (l.map Prod.fst).sum ⊤ ≤
        ((l.map Prod.snd).sum : WithTop ℤ)
  | [], _, _, _ => by
    simp only [List.length_nil, List.map_nil, List.sum_nil]
    rw [buildLayers_getD _ _ (forLayer_congr S G) (Nat.zero_le _)]
    simp [forLayer, forEntry]
  | x :: l, hP, hx, hS => by
    simp only [List.length_cons, List.map_cons, List.sum_cons] at hP hS ⊢
    obtain ⟨hx1, hxG⟩ := hx x List.mem_cons_self
    have ih := forM_le S G P l (by omega) (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (by omega)
    rw [buildLayers_getD _ _ (forLayer_congr S G) (by omega)]
    simp only [forLayer, getD_ofFn, show x.1 + (l.map Prod.fst).sum < S + 1 by omega, dite_true,
      forEntry, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    refine (minUpToZ_le _ (show x.1 - 1 < x.1 + (l.map Prod.fst).sum by omega)).trans ?_
    rw [show x.1 + (l.map Prod.fst).sum - (x.1 - 1 + 1) = (l.map Prod.fst).sum by omega,
      show x.1 - 1 + 1 = x.1 by omega]
    refine (add_le_add ih hxG).trans (le_of_eq ?_)
    rw [← WithTop.coe_add, add_comm]

end LagData

/-! ### The bound on role configurations -/

/-- **The Lagrangian value is a lower bound** on the cost of every role configuration with `S`
landings whose cities are allowed and whose planes weigh at most `T`
(`fill(Cr) + drop(Dr) + pick(Pk) ≤ T`), for every multiplier. -/
theorem LagData.value_le_totalCost (D : LagData n) (cfg : RoleConfig n p)
    (hreps : ∀ k, ∀ i ∈ cfg.groups k, i ∈ D.reps)
    (hload : ∀ k, load D.fill (cfg.cross k) + load D.drop (cfg.drop k) +
      load D.pick (cfg.pick k) ≤ D.T) :
    D.value p (size cfg.groups) ≤ ((totalCost D.c cfg.groups : ℤ) : WithTop ℤ) := by
  set l : List (ℕ × ℤ) := List.ofFn fun k =>
    ((cfg.groups k).card, D.charge (cfg.cross k) (cfg.drop k) (cfg.pick k)) with hl
  have hlen : l.length = p := by simp [hl]
  have hfst : (l.map Prod.fst).sum = size cfg.groups := by simp [hl, size, List.sum_ofFn]
  have hd : ∀ Y : Multiset (Fin n), (Y.map D.dropCost).sum =
      ((cost D.c Y : ℕ) : ℤ) + (Y.map D.mu).sum := by
    intro Y
    induction Y using Multiset.induction_on with
    | empty => simp
    | cons a Y ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, cost_cons, Nat.cast_add,
        LagData.dropCost]
      ring
  have hp : ∀ Y : Multiset (Fin n), (Y.map D.pickCost).sum =
      ((cost D.c Y : ℕ) : ℤ) - (Y.map D.mu).sum := by
    intro Y
    induction Y using Multiset.induction_on with
    | empty => simp
    | cons a Y ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, cost_cons, Nat.cast_add,
        LagData.pickCost]
      ring
  have hch : ∀ k, D.charge (cfg.cross k) (cfg.drop k) (cfg.pick k) =
      (cost D.c (cfg.groups k) : ℤ) + ((cfg.drop k).map D.mu).sum -
        ((cfg.pick k).map D.mu).sum := by
    intro k
    simp only [LagData.charge, RoleConfig.groups, cost_add, Nat.cast_add, hd, hp]
    ring
  have hbal : ∑ k, ((cfg.drop k).map D.mu).sum = ∑ k, ((cfg.pick k).map D.mu).sum := by
    rw [sum_map_sum_eq, sum_map_sum_eq, cfg.sum_drop_eq_sum_pick]
  have hsnd : (l.map Prod.snd).sum = (totalCost D.c cfg.groups : ℤ) := by
    simp only [hl, List.map_ofFn, List.sum_ofFn, Function.comp_def, hch]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hbal, totalCost, Nat.cast_sum]
    ring
  have hsize : ∀ k, (cfg.groups k).card ≤ size cfg.groups := fun k =>
    Finset.single_le_sum (f := fun j => (cfg.groups j).card) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ k)
  have := LagData.forM_le (size cfg.groups)
      (fun m => ((D.layers (size cfg.groups)).getD m (#[], #[])).2.getD D.T ⊤) p l hlen.le
      (fun x hx => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        refine ⟨by rw [RoleConfig.card_groups]; obtain ⟨r, hr⟩ := cfg.odd_card_cross k; omega, ?_⟩
        have h := D.lagM_le (mMax := size cfg.groups) (cfg.groups k).card true D.T
          (cfg.cross k) (cfg.drop k) (cfg.pick k) (hsize k) le_rfl
          (by rw [RoleConfig.card_groups]; omega) (by simpa using Nat.odd_iff.mp (cfg.odd_card_cross k))
          (fun i hi => hreps k i (by simp only [RoleConfig.groups, Multiset.mem_add] at hi ⊢; tauto))
          (hload k)
        unfold LagData.lagM at h
        simpa using h) (by rw [hfst])
  rw [hlen, hfst, hsnd] at this
  exact this

/-! ### Representatives -/

/-- Whether city `j` comes before city `k` in the order `(d, d̄, c, index)`. -/
def keyLT (d dbar c : Fin n → ℕ) (j k : Fin n) : Bool :=
  decide (d j < d k ∨ (d j = d k ∧ (dbar j < dbar k ∨ (dbar j = dbar k ∧
    (c j < c k ∨ (c j = c k ∧ j.val < k.val))))))

/-- A representative of city `i` that is no slower to either hub and no more expensive: the first
city in the order `(d, d̄, c, index)` among those dominating `i`. -/
def domRep3 (d dbar c : Fin n → ℕ) (i : Fin n) : Fin n :=
  (List.finRange n).foldl (fun best j =>
    if d j ≤ d i ∧ dbar j ≤ dbar i ∧ c j ≤ c i ∧ keyLT d dbar c j best = true then j else best) i

theorem domRep3_le (d dbar c : Fin n → ℕ) (i : Fin n) :
    d (domRep3 d dbar c i) ≤ d i ∧ dbar (domRep3 d dbar c i) ≤ dbar i ∧
      c (domRep3 d dbar c i) ≤ c i := by
  have : ∀ (l : List (Fin n)) (b : Fin n), d b ≤ d i ∧ dbar b ≤ dbar i ∧ c b ≤ c i →
      let r := l.foldl (fun best j => if d j ≤ d i ∧ dbar j ≤ dbar i ∧ c j ≤ c i ∧
        keyLT d dbar c j best = true then j else best) b
      d r ≤ d i ∧ dbar r ≤ dbar i ∧ c r ≤ c i := by
    intro l
    induction l with
    | nil => exact fun b hb => hb
    | cons j l ih =>
      intro b hb
      simp only [List.foldl_cons]
      apply ih
      split_ifs with hj
      · exact ⟨hj.1, hj.2.1, hj.2.2.1⟩
      · exact hb
  exact this _ i ⟨le_rfl, le_rfl, le_rfl⟩

/-- The representatives, listed. -/
def repList3 (d dbar c : Fin n → ℕ) : List (Fin n) :=
  ((List.finRange n).map (domRep3 d dbar c)).dedup

theorem domRep3_mem (d dbar c : Fin n → ℕ) (i : Fin n) : domRep3 d dbar c i ∈ repList3 d dbar c := by
  simp [repList3]

/-- A role configuration with its cities replaced by `rep`. -/
def RoleConfig.map (cfg : RoleConfig n p) (rep : Fin n → Fin n) : RoleConfig n p where
  drop k := (cfg.drop k).map rep
  pick k := (cfg.pick k).map rep
  cross k := (cfg.cross k).map rep
  odd_card_cross k := by simpa using cfg.odd_card_cross k
  sum_drop_eq_sum_pick := by
    rw [sum_map_eq_map_sum, sum_map_eq_map_sum, cfg.sum_drop_eq_sum_pick]

theorem RoleConfig.size_map (cfg : RoleConfig n p) (rep : Fin n → Fin n) :
    size (cfg.map rep).groups = size cfg.groups := by
  simp [size, RoleConfig.card_groups, RoleConfig.map]

theorem RoleConfig.totalCost_map_le (c : Fin n → ℕ) (cfg : RoleConfig n p)
    {rep : Fin n → Fin n} (hrep : ∀ i, c (rep i) ≤ c i) :
    totalCost c (cfg.map rep).groups ≤ totalCost c cfg.groups := by
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [RoleConfig.groups, RoleConfig.map, cost, ← Multiset.map_add, Multiset.map_map]
  exact Multiset.sum_map_le_sum_map _ _ fun i _ => hrep i

theorem RoleConfig.roleLoad_map_le (N : Network n) (cfg : RoleConfig n p)
    {rep : Fin n → Fin n} (hd : ∀ i, N.d (rep i) ≤ N.d i) (hdb : ∀ i, N.dbar (rep i) ≤ N.dbar i)
    (k : Fin p) : (cfg.map rep).roleLoad N k ≤ cfg.roleLoad N k := by
  have h₁ : ∀ (f : Fin n → ℕ), (∀ i, f (rep i) ≤ f i) → ∀ Y : Multiset (Fin n),
      load f (Y.map rep) ≤ load f Y := fun f hf Y => by
    simp only [load, Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ fun i _ => hf i
  unfold RoleConfig.roleLoad
  simp only [RoleConfig.map]
  have := h₁ N.d hd (cfg.drop k)
  have := h₁ N.dbar hdb (cfg.pick k)
  have := h₁ N.d hd (cfg.cross k)
  have := h₁ N.dbar hdb (cfg.cross k)
  omega

theorem RoleConfig.mem_map_groups (cfg : RoleConfig n p) (rep : Fin n → Fin n) {k : Fin p}
    {i : Fin n} (hi : i ∈ (cfg.map rep).groups k) : ∃ j, rep j = i := by
  simp only [RoleConfig.groups, RoleConfig.map, ← Multiset.map_add] at hi
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi
  exact ⟨j, rfl⟩

/-- A Lagrangian value as a bound in `WithTop ℕ`: a negative value bounds nothing. -/
def toNatTop : WithTop ℤ → WithTop ℕ
  | ⊤ => ⊤
  | (v : ℤ) => (v.toNat : WithTop ℕ)

theorem toNatTop_le {x : WithTop ℤ} {c : ℕ} (h : x ≤ ((c : ℤ) : WithTop ℤ)) :
    toNatTop x ≤ (c : WithTop ℕ) := by
  cases x with
  | top => exact absurd h (by simp)
  | coe v =>
    simp only [toNatTop]
    have : v ≤ c := WithTop.coe_le_coe.mp h
    exact WithTop.coe_le_coe.mpr (Int.toNat_le.mpr this)

end ZenoFront
