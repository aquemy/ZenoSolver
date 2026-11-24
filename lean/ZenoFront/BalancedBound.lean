/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.LagrangianBound
public import Std.Data.HashMap

/-!
# The `balanced` bound of format v2

`BalancedRoles` in `src/zeno/roles.cpp` computes the least cost of a balanced role configuration
on `p` planes with `s` landings and role loads at most `T`, by a DP over the planes whose state is
the imbalance vector (drop-offs minus pick-ups so far, per city) and the number of landings. This
file computes the same program and proves the direction the checker needs: its value is at most
the cost of every such configuration (`BalData.value_le_totalCost`).

* A plane's option is its imbalance `δ` (drop-offs `δ⁺`, pick-ups `δ⁻`) and an odd number `r` of
  crossings, of cost `c(δ⁺) + c(δ⁻) + G_fill[r][T − 2d(δ⁺) − 2d̄(δ⁻)]`. A drop-off and a pick-up
  at the same city of one plane weigh and cost exactly two crossings there, so they are counted
  as crossings (`planeOpt`).
* With `N` the number of links left after that, `2N + p ≤ s`, so `N ≤ t − p`; every plane has
  `‖δ‖₁ ≤ N` and every prefix of planes has imbalance `‖v‖₁ ≤ N`, by the balance
  (`norm_delta_le`, `norm_prefix_le`). So restricting options and states to norm `≤ t − p`
  loses no configuration.
* The layers are hash maps from states to the least cost found; the invariant is that a layer
  holds every prefix state of the configuration at a cost no larger than the prefix's
  (`layers_dominate`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-! ### Vectors as lists -/

/-- Coordinate `i` of a vector stored as a list (`0` beyond its end). -/
def coord (l : List ℤ) (i : Fin n) : ℤ := l.getD i.val 0

/-- The `ℓ¹` norm of a vector stored as a list. -/
def vecNorm (l : List ℤ) : ℕ := (l.map Int.natAbs).sum

theorem coord_ofFn (f : Fin n → ℤ) (i : Fin n) : coord (List.ofFn f) i = f i := by
  simp [coord, List.getD_eq_getElem?_getD]

theorem vecNorm_ofFn (f : Fin n → ℤ) : vecNorm (List.ofFn f) = ∑ i, (f i).natAbs := by
  simp [vecNorm, List.sum_ofFn]

/-- All vectors of length `k` and norm at most `left`. -/
def enumVecs : ℕ → ℕ → List (List ℤ)
  | 0, _ => [[]]
  | k + 1, left => (List.range (2 * left + 1)).flatMap fun (a : ℕ) =>
      let v : ℤ := (a : ℤ) - (left : ℤ)
      (enumVecs k (left - v.natAbs)).map (v :: ·)

theorem mem_enumVecs : ∀ (k left : ℕ) (l : List ℤ), l.length = k → vecNorm l ≤ left →
    l ∈ enumVecs k left
  | 0, _, l, hl, _ => by simp [List.length_eq_zero_iff.mp hl, enumVecs]
  | k + 1, left, l, hl, hn => by
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      cases l with
      | nil => simp at hl
      | cons x l' => exact ⟨x, l', rfl⟩
    simp only [vecNorm, List.map_cons, List.sum_cons] at hn
    have hx : x.natAbs ≤ left := by omega
    have hx' : -(left : ℤ) ≤ x ∧ x ≤ left := by
      rcases Int.natAbs_eq x with h | h <;> constructor <;> omega
    have hv : (((x + left).toNat : ℕ) : ℤ) - left = x := by omega
    have hrest : vecNorm l' ≤ left - x.natAbs := by
      simp only [vecNorm]
      generalize x.natAbs = a at hn hx ⊢
      omega
    have h1 := hx'.1
    have h2 := hx'.2
    unfold enumVecs
    refine List.mem_flatMap.mpr ⟨(x + left).toNat, List.mem_range.mpr
      (show (x + left).toNat < 2 * left + 1 by omega), ?_⟩
    show x :: l' ∈ (enumVecs k (left - ((((x + left).toNat : ℕ) : ℤ) - left).natAbs)).map
      (((((x + left).toNat : ℕ) : ℤ) - left) :: ·)
    rw [hv]
    exact List.mem_map.mpr ⟨l', mem_enumVecs k _ l' (by simpa using hl) hrest, rfl⟩

/-! ### The program -/

/-- The landings of an imbalance. -/
def optSize (δ : List ℤ) : ℕ := ∑ i : Fin n, (coord δ i).natAbs

/-- The data of the program at one level: drop-off and pick-up weights (scaled, `2d` and `2d̄`),
costs, the crossing table `G` (`G r τ`: `r` crossings within `τ`), the level `T`, the bound
`links = t − p` on norms, and the number `s` of landings. -/
structure BalData (n : ℕ) where
  dW : Fin n → ℕ
  pW : Fin n → ℕ
  c : Fin n → ℕ
  G : ℕ → ℕ → WithTop ℕ
  T : ℕ
  links : ℕ
  s : ℕ

/-- A state: the imbalance vector and the number of landings so far. -/
abbrev BKey := List ℤ × ℕ

/-- Insert a state, keeping the smaller cost. -/
def insertMin (m : Std.HashMap BKey (WithTop ℕ)) (k : BKey) (c : WithTop ℕ) :
    Std.HashMap BKey (WithTop ℕ) :=
  match m[k]? with
  | some c₀ => if c < c₀ then m.insert k c else m
  | none => m.insert k c

namespace BalData

variable (D : BalData n)

/-- The weight of an imbalance: `2d` per drop-off, `2d̄` per pick-up. -/
def optLoad (δ : List ℤ) : ℕ :=
  ∑ i : Fin n, if 0 < coord δ i then D.dW i * (coord δ i).toNat else D.pW i * (-coord δ i).toNat

/-- The landing cost of an imbalance. -/
def optCost (δ : List ℤ) : ℕ := ∑ i : Fin n, D.c i * (coord δ i).natAbs


/-- The plane imbalances: norm at most `links`, weight at most `T`. -/
def options : List (List ℤ) := (enumVecs n D.links).filter fun δ => decide (D.optLoad δ ≤ D.T)

/-- The odd numbers `1, 3, …` up to `s`. -/
def oddUpTo (s : ℕ) : List ℕ := (List.range ((s + 1) / 2)).map fun k => 2 * k + 1

/-- The successors of the states of `m`. -/
def candidates (opts : List (List ℤ)) (m : Std.HashMap BKey (WithTop ℕ)) :
    List (BKey × WithTop ℕ) :=
  m.toList.flatMap fun x =>
    opts.flatMap fun δ =>
      let v' := List.ofFn fun i : Fin n => coord x.1.1 i + coord δ i
      if vecNorm v' ≤ D.links then
        (oddUpTo D.s).filterMap fun r =>
          let j' := x.1.2 + optSize (n := n) δ + r
          let g := D.G r (D.T - D.optLoad δ)
          if j' ≤ D.s ∧ g ≠ ⊤ then some ((v', j'), x.2 + (D.optCost δ : WithTop ℕ) + g) else none
      else []

/-- One layer from the previous one. -/
def step (opts : List (List ℤ)) (m : Std.HashMap BKey (WithTop ℕ)) :
    Std.HashMap BKey (WithTop ℕ) :=
  (D.candidates opts m).foldl (fun acc x => insertMin acc x.1 x.2) ∅

/-- The zero vector. -/
def zeroVec (n : ℕ) : List ℤ := List.ofFn fun _ : Fin n => (0 : ℤ)

/-- The layers `0, …, q`. -/
def layers (opts : List (List ℤ)) : ℕ → Std.HashMap BKey (WithTop ℕ)
  | 0 => (∅ : Std.HashMap BKey (WithTop ℕ)).insert (zeroVec n, 0) 0
  | q + 1 => D.step opts (layers opts q)

/-- The value of the program for `p` planes: the cost of the final state (balanced, `s`
landings). -/
def value (p : ℕ) : WithTop ℕ :=
  ((D.layers D.options p)[(zeroVec n, D.s)]?).getD ⊤

end BalData

/-! ### The layers dominate the configuration's prefixes -/

theorem insertMin_self (m : Std.HashMap BKey (WithTop ℕ)) (k : BKey) (c : WithTop ℕ) :
    ∃ c', (insertMin m k c)[k]? = some c' ∧ c' ≤ c ∧ ∀ c₀, m[k]? = some c₀ → c' ≤ c₀ := by
  unfold insertMin
  cases h : m[k]? with
  | none => exact ⟨c, by simp, le_rfl, fun c₀ h₀ => by simp at h₀⟩
  | some c₀ =>
    simp only
    split_ifs with hc
    · exact ⟨c, by simp, le_rfl, fun c₁ h₁ => by
        simp only [Option.some.injEq] at h₁; subst h₁; exact hc.le⟩
    · exact ⟨c₀, h, not_lt.mp hc, fun c₁ h₁ => by simp at h₁; rw [h₁]⟩

theorem insertMin_other (m : Std.HashMap BKey (WithTop ℕ)) {k k' : BKey} (c : WithTop ℕ)
    (h : k ≠ k') : (insertMin m k c)[k']? = m[k']? := by
  unfold insertMin
  have hb : (k == k') = false := by simpa using h
  cases m[k]? with
  | none => simp [Std.HashMap.getElem?_insert, hb]
  | some c₀ =>
    simp only
    split_ifs
    · simp [Std.HashMap.getElem?_insert, hb]
    · rfl

/-- Folding `insertMin` keeps every inserted state, at a cost no larger. -/
theorem foldl_insertMin : ∀ (L : List (BKey × WithTop ℕ)) (m : Std.HashMap BKey (WithTop ℕ)),
    (∀ x ∈ L, ∃ c', (L.foldl (fun acc x => insertMin acc x.1 x.2) m)[x.1]? = some c' ∧
      c' ≤ x.2) ∧
    ∀ (k : BKey) (c₀ : WithTop ℕ), m[k]? = some c₀ →
      ∃ c', (L.foldl (fun acc x => insertMin acc x.1 x.2) m)[k]? = some c' ∧ c' ≤ c₀
  | [], m => ⟨by simp, fun k c₀ h => ⟨c₀, h, le_rfl⟩⟩
  | y :: L, m => by
    obtain ⟨ih₁, ih₂⟩ := foldl_insertMin L (insertMin m y.1 y.2)
    simp only [List.foldl_cons]
    refine ⟨fun x hx => ?_, fun k c₀ hk => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨c', hc', hle, -⟩ := insertMin_self m x.1 x.2
        obtain ⟨c'', hc'', hle'⟩ := ih₂ x.1 c' hc'
        exact ⟨c'', hc'', hle'.trans hle⟩
      · exact ih₁ x hx
    · by_cases hky : y.1 = k
      · subst hky
        obtain ⟨c', hc', -, hle⟩ := insertMin_self m y.1 y.2
        obtain ⟨c'', hc'', hle'⟩ := ih₂ y.1 c' hc'
        exact ⟨c'', hc'', hle'.trans (hle c₀ hk)⟩
      · exact ih₂ k c₀ (by rw [insertMin_other m y.2 hky]; exact hk)

/-- A plane of a configuration, as the program sees it: its imbalance, its number of crossings,
and an upper bound on its cost. -/
structure PlaneOpt (n : ℕ) where
  δ : Fin n → ℤ
  r : ℕ
  cost : ℕ

namespace BalData

variable (D : BalData n)

/-- The conditions on one plane: an option of the program whose cost is at most the plane's. -/
def PlaneOK (x : PlaneOpt n) : Prop :=
  List.ofFn x.δ ∈ D.options ∧ x.r ∈ oddUpTo D.s ∧ D.G x.r (D.T - D.optLoad (List.ofFn x.δ)) ≠ ⊤ ∧
    (D.optCost (List.ofFn x.δ) : WithTop ℕ) + D.G x.r (D.T - D.optLoad (List.ofFn x.δ)) ≤
      (x.cost : WithTop ℕ)

/-- The imbalance of a list of planes. -/
def sumδ (l : List (PlaneOpt n)) (i : Fin n) : ℤ := (l.map fun x => x.δ i).sum

/-- The landings of a list of planes. -/
def sumJ (l : List (PlaneOpt n)) : ℕ :=
  (l.map fun x => optSize (n := n) (List.ofFn x.δ) + x.r).sum


/-- **The layers dominate the prefixes**: after `q` planes, the layer holds the prefix's state at
a cost no larger than the prefix's, if every prefix state has norm at most `links` and at most
`s` landings. -/
theorem layers_dominate (ps : List (PlaneOpt n)) (hps : ∀ x ∈ ps, D.PlaneOK x)
    (hnorm : ∀ q ≤ ps.length, vecNorm (List.ofFn (sumδ (ps.take q))) ≤ D.links)
    (hj : sumJ ps ≤ D.s) :
    ∀ q ≤ ps.length, ∃ c', (D.layers D.options q)[(List.ofFn (sumδ (ps.take q)),
      sumJ (ps.take q))]? = some c' ∧ c' ≤ (((ps.take q).map PlaneOpt.cost).sum : WithTop ℕ)
  | 0, _ => by
    refine ⟨0, ?_, by simp⟩
    have h0 : List.ofFn (sumδ (ps.take 0)) = zeroVec n := by
      simp only [List.take_zero, zeroVec]
      rfl
    have hj0 : sumJ (ps.take 0) = 0 := by simp [sumJ]
    rw [h0, hj0]
    simp [layers]
  | q + 1, hq => by
    obtain ⟨c', hc', hle⟩ := layers_dominate ps hps hnorm hj q (by omega)
    set x := ps[q]'(by omega) with hx
    have htake : ps.take (q + 1) = ps.take q ++ [x] := List.take_succ_eq_append_getElem (by omega)
    obtain ⟨hopt, hr, hG, hcost⟩ := hps x (List.getElem_mem _)
    have hjq : sumJ (ps.take (q + 1)) ≤ D.s := by
      refine le_trans ?_ hj
      have := List.take_append_drop (q + 1) ps
      conv_rhs => rw [← this]
      simp only [sumJ, List.map_append, List.sum_append]
      omega
    -- The candidate built from the prefix state and plane `x`.
    have hmem : ((List.ofFn (sumδ (ps.take (q + 1))), sumJ (ps.take (q + 1))),
        c' + (D.optCost (List.ofFn x.δ) : WithTop ℕ) +
          D.G x.r (D.T - D.optLoad (List.ofFn x.δ))) ∈ D.candidates D.options
          (D.layers D.options q) := by
      simp only [candidates, List.mem_flatMap]
      refine ⟨((List.ofFn (sumδ (ps.take q)), sumJ (ps.take q)), c'),
        Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hc', List.ofFn x.δ, hopt, ?_⟩
      have hv : (List.ofFn fun i : Fin n => coord (List.ofFn (sumδ (ps.take q))) i +
          coord (List.ofFn x.δ) i) = List.ofFn (sumδ (ps.take (q + 1))) := by
        congr 1
        funext i
        simp [coord_ofFn, htake, sumδ]
      simp only [hv, ite_eq_left (hnorm (q + 1) hq)]
      refine List.mem_filterMap.mpr ⟨x.r, hr, ?_⟩
      have hj' : sumJ (ps.take q) + optSize (n := n) (List.ofFn x.δ) + x.r =
          sumJ (ps.take (q + 1)) := by
        simp only [sumJ, htake, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        omega
      simp only [hj']
      rw [ite_eq_left ⟨hjq, hG⟩]
    obtain ⟨hdom, -⟩ := foldl_insertMin (D.candidates D.options (D.layers D.options q)) ∅
    obtain ⟨c₃, h₃, hle₃⟩ := hdom _ hmem
    refine ⟨c₃, h₃, hle₃.trans ?_⟩
    rw [htake, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Nat.cast_add, add_assoc]
    exact add_le_add hle hcost

end BalData


/-! ### From a role configuration to plane options -/

theorem card_eq_sum_count (M : Multiset (Fin n)) : M.card = ∑ i, M.count i := by
  rw [← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simpa using hi

theorem load_eq_sum_count (f : Fin n → ℕ) (M : Multiset (Fin n)) :
    load f M = ∑ i, f i * M.count i := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [load_cons, ih]
    simp only [Multiset.count_cons, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    omega

theorem sum_take_le (l : List ℕ) (q : ℕ) : (l.take q).sum ≤ l.sum := by
  have h := List.take_append_drop q l
  calc (l.take q).sum ≤ (l.take q).sum + (l.drop q).sum := Nat.le_add_right _ _
    _ = l.sum := by rw [← List.sum_append, h]

theorem sum_map_sub_eq : ∀ (P : List (ℕ × ℕ)),
    (P.map fun x => (x.1 : ℤ) - x.2).sum = ((P.map Prod.fst).sum : ℤ) - (P.map Prod.snd).sum
  | [] => by simp
  | x :: P => by
    simp only [List.map_cons, List.sum_cons, sum_map_sub_eq P]
    push_cast
    ring

section Planes

variable (cfg : RoleConfig n p)

/-- Drop-offs and pick-ups of plane `k` at the same city. -/
def RoleConfig.shared (k : Fin p) : Multiset (Fin n) := cfg.drop k ∩ cfg.pick k
/-- Drop-offs of plane `k` left after cancelling. -/
def RoleConfig.dplus (k : Fin p) : Multiset (Fin n) := cfg.drop k - cfg.pick k
/-- Pick-ups of plane `k` left after cancelling. -/
def RoleConfig.dminus (k : Fin p) : Multiset (Fin n) := cfg.pick k - cfg.drop k

theorem RoleConfig.drop_eq (k : Fin p) : cfg.drop k = cfg.shared k + cfg.dplus k := by
  ext i
  simp only [RoleConfig.shared, RoleConfig.dplus, Multiset.count_add, Multiset.count_inter,
    Multiset.count_sub]
  omega

theorem RoleConfig.pick_eq (k : Fin p) : cfg.pick k = cfg.shared k + cfg.dminus k := by
  ext i
  simp only [RoleConfig.shared, RoleConfig.dminus, Multiset.count_add, Multiset.count_inter,
    Multiset.count_sub]
  omega

theorem RoleConfig.count_dplus_or (k : Fin p) (i : Fin n) :
    (cfg.dplus k).count i = 0 ∨ (cfg.dminus k).count i = 0 := by
  simp only [RoleConfig.dplus, RoleConfig.dminus, Multiset.count_sub]
  omega

/-- The imbalance of plane `k`. -/
def RoleConfig.delta (k : Fin p) (i : Fin n) : ℤ :=
  ((cfg.dplus k).count i : ℤ) - (cfg.dminus k).count i

theorem RoleConfig.sum_dplus_eq : ∑ k, cfg.dplus k = ∑ k, cfg.dminus k := by
  have h := cfg.sum_drop_eq_sum_pick
  simp only [cfg.drop_eq, cfg.pick_eq, Finset.sum_add_distrib] at h
  exact add_left_cancel h

/-- The number of links after cancelling. -/
def RoleConfig.links : ℕ := ∑ k, (cfg.dplus k).card

theorem RoleConfig.card_groups_eq (k : Fin p) : (cfg.groups k).card =
    2 * (cfg.shared k).card + (cfg.dplus k).card + (cfg.dminus k).card + (cfg.cross k).card := by
  rw [RoleConfig.card_groups, cfg.drop_eq, cfg.pick_eq]
  simp only [Multiset.card_add]
  omega

theorem RoleConfig.two_links_add_le : 2 * cfg.links + p ≤ size cfg.groups := by
  have hc : ∑ k, (cfg.dminus k).card = ∑ k, (cfg.dplus k).card := by
    rw [← Multiset.card_sum, ← Multiset.card_sum, cfg.sum_dplus_eq]
  have h₁ : ∀ k, (cfg.dplus k).card + (cfg.dminus k).card + 1 ≤ (cfg.groups k).card := by
    intro k
    rw [cfg.card_groups_eq]
    obtain ⟨r, hr⟩ := cfg.odd_card_cross k
    omega
  have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin p))) => h₁ k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, hc] at this
  unfold RoleConfig.links
  rw [size]
  omega

theorem RoleConfig.natAbs_delta (k : Fin p) (i : Fin n) :
    (cfg.delta k i).natAbs = (cfg.dplus k).count i + (cfg.dminus k).count i := by
  unfold RoleConfig.delta
  rcases cfg.count_dplus_or k i with h | h <;> rw [h] <;> omega

/-- **Every plane's imbalance has norm at most the number of links.** -/
theorem RoleConfig.norm_delta_le (k : Fin p) :
    ∑ i, (cfg.delta k i).natAbs ≤ cfg.links := by
  have hbal : ∀ i, ∑ k', (cfg.dplus k').count i = ∑ k', (cfg.dminus k').count i := fun i => by
    rw [← Multiset.count_sum', ← Multiset.count_sum', cfg.sum_dplus_eq]
  have hlinks : cfg.links = ∑ i, ∑ k', (cfg.dplus k').count i := by
    unfold RoleConfig.links
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k' _ => card_eq_sum_count _
  rw [hlinks]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [cfg.natAbs_delta]
  rcases cfg.count_dplus_or k i with h | h
  · rw [h, zero_add, hbal i]
    exact Finset.single_le_sum (f := fun k' => (cfg.dminus k').count i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  · rw [h, add_zero]
    exact Finset.single_le_sum (f := fun k' => (cfg.dplus k').count i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)

/-- The plane options of a configuration. -/
def RoleConfig.planeOpts (c : Fin n → ℕ) : List (PlaneOpt n) :=
  List.ofFn fun k => ⟨cfg.delta k, (cfg.cross k + cfg.shared k + cfg.shared k).card,
    cost c (cfg.groups k)⟩

/-- **Every prefix of planes has imbalance norm at most the number of links.** -/
theorem RoleConfig.norm_prefix_le (c : Fin n → ℕ) (q : ℕ) :
    vecNorm (List.ofFn (BalData.sumδ ((cfg.planeOpts c).take q))) ≤ cfg.links := by
  have hbal : ∀ i, ∑ k', (cfg.dplus k').count i = ∑ k', (cfg.dminus k').count i := fun i => by
    rw [← Multiset.count_sum', ← Multiset.count_sum', cfg.sum_dplus_eq]
  have hlinks : cfg.links = ∑ i, ∑ k', (cfg.dplus k').count i := by
    unfold RoleConfig.links
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k' _ => card_eq_sum_count _
  rw [vecNorm_ofFn, hlinks]
  refine Finset.sum_le_sum fun i _ => ?_
  have key : BalData.sumδ ((cfg.planeOpts c).take q) i =
      (((List.ofFn fun k => ((cfg.dplus k).count i, (cfg.dminus k).count i)).take q).map
        fun x => (x.1 : ℤ) - x.2).sum := by
    simp only [BalData.sumδ, RoleConfig.planeOpts, List.map_take, List.map_ofFn]
    rfl
  rw [key]
  set P := (List.ofFn fun k => ((cfg.dplus k).count i, (cfg.dminus k).count i)).take q
  have hsub : (P.map fun x => (x.1 : ℤ) - x.2).sum =
      ((P.map Prod.fst).sum : ℤ) - ((P.map Prod.snd).sum : ℤ) := sum_map_sub_eq P
  have hA : (P.map Prod.fst).sum ≤ ∑ k', (cfg.dplus k').count i := by
    simp only [P, List.map_take, List.map_ofFn]
    refine (sum_take_le _ q).trans (le_of_eq ?_)
    rw [List.sum_ofFn]
    rfl
  have hB : (P.map Prod.snd).sum ≤ ∑ k', (cfg.dminus k').count i := by
    simp only [P, List.map_take, List.map_ofFn]
    refine (sum_take_le _ q).trans (le_of_eq ?_)
    rw [List.sum_ofFn]
    rfl
  rw [hsub]
  have := hbal i
  omega

theorem RoleConfig.sumδ_planeOpts (c : Fin n → ℕ) :
    BalData.sumδ (cfg.planeOpts c) = fun _ => 0 := by
  funext i
  simp only [BalData.sumδ, RoleConfig.planeOpts, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, RoleConfig.delta, Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Multiset.count_sum', ← Multiset.count_sum',
    cfg.sum_dplus_eq, sub_self]

end Planes

/-! ### The bound -/

/-- **The `balanced` program is a lower bound** on the cost of every balanced role configuration
with `s` landings and role loads at most `T`, for durations `dR`, `dbR` (scaled) when the program
weighs a drop-off `2 dR`, a pick-up `2 dbR`, `links ≥ (s − p)/2`, and `G` bounds the crossings. -/
theorem BalData.value_le_totalCost (D : BalData n) (dR dbR : Fin n → ℕ)
    (dc : Fin n → Fin n → ℕ) (hdW : D.dW = fun i => 2 * dR i)
    (hpW : D.pW = fun i => 2 * dbR i) (hlinks : D.s ≤ 2 * D.links + p)
    (hG : ∀ r τ (Y : Multiset (Fin n)), Y.card = r → r ≤ D.s → τ ≤ D.T →
      load (fillW dR dbR) Y ≤ τ → D.G r τ ≤ cost D.c Y)
    (cfg : RoleConfig n p) (hsize : size cfg.groups = D.s)
    (hload : ∀ k, cfg.roleLoad ⟨dR, dbR, dc⟩ k ≤ D.T) :
    D.value p ≤ (totalCost D.c cfg.groups : WithTop ℕ) := by
  set ps := cfg.planeOpts D.c with hps
  have hN := cfg.two_links_add_le
  have hcardk : ∀ k, (cfg.groups k).card ≤ size cfg.groups := fun k =>
    Finset.single_le_sum (f := fun j => (cfg.groups j).card) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ k)
  -- Every plane is an option of the program.
  have hok : ∀ x ∈ ps, D.PlaneOK x := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    have hnat := cfg.natAbs_delta k
    have hcoord : ∀ i, coord (List.ofFn (cfg.delta k)) i = cfg.delta k i := coord_ofFn _
    have hsize' : optSize (n := n) (List.ofFn (cfg.delta k)) =
        (cfg.dplus k).card + (cfg.dminus k).card := by
      simp only [optSize, hcoord, hnat, Finset.sum_add_distrib, ← card_eq_sum_count]
    have hloadδ : D.optLoad (List.ofFn (cfg.delta k)) =
        load D.dW (cfg.dplus k) + load D.pW (cfg.dminus k) := by
      simp only [BalData.optLoad, hcoord, load_eq_sum_count, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold RoleConfig.delta
      rcases cfg.count_dplus_or k i with h | h <;> rw [h] <;> split_ifs <;> simp_all
      omega
    have hcostδ : D.optCost (List.ofFn (cfg.delta k)) =
        cost D.c (cfg.dplus k) + cost D.c (cfg.dminus k) := by
      simp only [BalData.optCost, hcoord, hnat, mul_add, Finset.sum_add_distrib]
      show _ = load D.c _ + load D.c _
      rw [load_eq_sum_count, load_eq_sum_count]
    have hrl := hload k
    unfold RoleConfig.roleLoad at hrl
    simp only at hrl
    rw [cfg.drop_eq, cfg.pick_eq, load_add, load_add] at hrl
    have hfill : load (fillW dR dbR) (cfg.cross k + cfg.shared k + cfg.shared k) =
        load dR (cfg.cross k) + load dbR (cfg.cross k) + 2 * load dR (cfg.shared k) +
          2 * load dbR (cfg.shared k) := by
      rw [load_add, load_add]
      have e₁ : load (fillW dR dbR) (cfg.cross k) = load dR (cfg.cross k) + load dbR (cfg.cross k) :=
        load_add_fun _ _ _
      have e₂ : load (fillW dR dbR) (cfg.shared k) =
          load dR (cfg.shared k) + load dbR (cfg.shared k) := load_add_fun _ _ _
      omega
    have hdWl : load D.dW (cfg.dplus k) = 2 * load dR (cfg.dplus k) := by
      rw [hdW]; simp only [load]; rw [Multiset.sum_map_mul_left]
    have hpWl : load D.pW (cfg.dminus k) = 2 * load dbR (cfg.dminus k) := by
      rw [hpW]; simp only [load]; rw [Multiset.sum_map_mul_left]
    have hlnorm : (cfg.dplus k).card + (cfg.dminus k).card ≤ D.links := by
      have := cfg.norm_delta_le k
      simp only [hnat, Finset.sum_add_distrib, ← card_eq_sum_count] at this
      omega
    have hr_le : (cfg.cross k + cfg.shared k + cfg.shared k).card ≤ D.s := by
      have := cfg.card_groups_eq k
      have := hcardk k
      simp only [Multiset.card_add]
      omega
    have hGle := hG _ (D.T - D.optLoad (List.ofFn (cfg.delta k)))
      (cfg.cross k + cfg.shared k + cfg.shared k) rfl hr_le (Nat.sub_le _ _) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine List.mem_filter.mpr ⟨mem_enumVecs n D.links _ (by simp) ?_, ?_⟩
      · rw [vecNorm_ofFn]
        simp only [hnat, Finset.sum_add_distrib, ← card_eq_sum_count]
        exact hlnorm
      · simp only [decide_eq_true_eq]
        omega
    · simp only [BalData.oddUpTo, List.mem_map, List.mem_range]
      obtain ⟨r, hr⟩ := cfg.odd_card_cross k
      refine ⟨r + (cfg.shared k).card, ?_, ?_⟩
      · simp only [Multiset.card_add] at hr_le
        omega
      · simp only [Multiset.card_add]
        omega
    · exact ne_top_of_le_ne_top (WithTop.coe_ne_top) hGle
    · refine (add_le_add le_rfl hGle).trans (le_of_eq ?_)
      rw [hcostδ]
      have e : cost D.c (cfg.dplus k) + cost D.c (cfg.dminus k) +
          cost D.c (cfg.cross k + cfg.shared k + cfg.shared k) = cost D.c (cfg.groups k) := by
        simp only [RoleConfig.groups, cfg.drop_eq, cfg.pick_eq, cost_add]
        omega
      exact_mod_cast e
  -- The prefixes.
  have hlen : ps.length = p := by simp [hps, RoleConfig.planeOpts]
  have hnorm : ∀ q ≤ ps.length, vecNorm (List.ofFn (BalData.sumδ (ps.take q))) ≤ D.links :=
    fun q _ => (cfg.norm_prefix_le D.c q).trans (by omega)
  have hJ : BalData.sumJ ps = D.s := by
    rw [← hsize, size]
    simp only [BalData.sumJ, hps, RoleConfig.planeOpts, List.map_ofFn, List.sum_ofFn,
      Function.comp_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hnat := cfg.natAbs_delta k
    have hcoord : ∀ i, coord (List.ofFn (cfg.delta k)) i = cfg.delta k i := coord_ofFn _
    rw [cfg.card_groups_eq]
    simp only [optSize, hcoord, hnat, Finset.sum_add_distrib, ← card_eq_sum_count,
      Multiset.card_add]
    omega
  obtain ⟨c', hc', hle⟩ := D.layers_dominate ps hok hnorm hJ.le p (by omega)
  have htk : ps.take p = ps := by rw [← hlen, List.take_length]
  rw [htk] at hc' hle
  rw [hJ, cfg.sumδ_planeOpts] at hc'
  have hz : (List.ofFn fun _ : Fin n => (0 : ℤ)) = zeroVec n := rfl
  rw [hz] at hc'
  unfold BalData.value
  rw [hc', Option.getD_some]
  refine hle.trans (le_of_eq ?_)
  simp only [hps, RoleConfig.planeOpts, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    totalCost]

end ZenoFront
