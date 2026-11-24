/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.SearchGap

/-!
# Scheduled configurations on representatives

The `search` kind of the v2 checker runs on the representatives of the cities (`domRep3`), with
durations in units of `rolesScale`. This file moves a scheduled configuration there.

* `Sched.map`: every city replaced by `rep`, the matching unchanged. It stays valid
  (`Sched.Valid.map`) with the same number of landings (`Sched.size_map`); its cost and closed
  form do not increase when `rep` makes no city more expensive or slower
  (`Sched.cost_map_le`, `Sched.tmpl_map_le`).
* `Sched.mul_tmpl_map_le`: when `d = g · d'` and `d̄ = g · d̄'` on the cities `rep` returns, the
  closed form on `d'`, `d̄'`, times `g`, is at most the closed form on `d`, `d̄`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

namespace Sched

/-- The configuration with its cities replaced by `rep`. -/
def map (S : Sched n p) (rep : Fin n → Fin n) : Sched n p :=
  ⟨fun k => (S.drops k).map rep, fun k => (S.picks k).map rep, fun k => (S.cross k).map rep,
    S.mate⟩

variable {S : Sched n p} {rep : Fin n → Fin n}

theorem Valid.map (h : S.Valid) (rep : Fin n → Fin n) : (S.map rep).Valid := by
  refine ⟨fun k => by simpa [Sched.map] using h.odd k, fun v l hl => ?_,
    fun v l v' l' hl hl' he => ?_, ?_⟩
  · simp only [Sched.map, List.length_map] at hl ⊢
    rw [List.getElem?_map, List.getElem?_map, h.city v l hl]
  · simp only [Sched.map, List.length_map] at hl hl' he
    exact h.inj v l v' l' hl hl' he
  · simpa [Sched.map] using h.count

theorem size_map : (S.map rep).size = S.size := by
  simp [Sched.size, Sched.map]

theorem cost_map_le (c : Fin n → ℕ) (hc : ∀ i, c (rep i) ≤ c i) :
    (S.map rep).cost c ≤ S.cost c := by
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Sched.map, List.map_map, ZenoFront.cost, Multiset.map_map]
  have h₁ : ((S.drops k).map (c ∘ rep)).sum ≤ ((S.drops k).map c).sum :=
    List.sum_le_sum fun i _ => hc i
  have h₂ : ((S.picks k).map (c ∘ rep)).sum ≤ ((S.picks k).map c).sum :=
    List.sum_le_sum fun i _ => hc i
  have h₃ : ((S.cross k).map (c ∘ rep)).sum ≤ ((S.cross k).map c).sum :=
    Multiset.sum_map_le_sum_map _ _ fun i _ => hc i
  omega

theorem load_map_le (d db : Fin n → ℕ) (hd : ∀ i, d (rep i) ≤ d i)
    (hdb : ∀ i, db (rep i) ≤ db i) (k : Fin p) : (S.map rep).load d db k ≤ S.load d db k := by
  simp only [Sched.load, Sched.map, List.map_map, ZenoFront.load, Multiset.map_map]
  have h₁ : ((S.drops k).map (d ∘ rep)).sum ≤ ((S.drops k).map d).sum :=
    List.sum_le_sum fun i _ => hd i
  have h₂ : ((S.picks k).map (db ∘ rep)).sum ≤ ((S.picks k).map db).sum :=
    List.sum_le_sum fun i _ => hdb i
  have h₃ : ((S.cross k).map (d ∘ rep)).sum ≤ ((S.cross k).map d).sum :=
    Multiset.sum_map_le_sum_map _ _ fun i _ => hd i
  have h₄ : ((S.cross k).map (db ∘ rep)).sum ≤ ((S.cross k).map db).sum :=
    Multiset.sum_map_le_sum_map _ _ fun i _ => hdb i
  omega

theorem picks_map_getElem (v : Fin p) (l : Fin ((S.map rep).picks v).length) :
    ((S.map rep).picks v)[l] =
      rep ((S.picks v)[l.val]'(by simpa [Sched.map] using l.isLt)) :=
  List.getElem_map rep

theorem pre_map (f : Fin n → ℕ) (u : Fin p) (j : ℕ) :
    (S.map rep).pre f u j = 2 * (((S.drops u).take j).map (f ∘ rep)).sum := by
  simp only [Sched.pre, Sched.map, ← List.map_take, List.map_map]

theorem suf_map (f : Fin n → ℕ) (v : Fin p) (l : ℕ) :
    (S.map rep).suf f v l = 2 * (((S.picks v).drop (l + 1)).map (f ∘ rep)).sum := by
  simp only [Sched.suf, Sched.map, ← List.map_drop, List.map_map]

theorem term_map_le (d db : Fin n → ℕ) (hd : ∀ i, d (rep i) ≤ d i)
    (hdb : ∀ i, db (rep i) ≤ db i) (v : Fin p) (l : Fin ((S.map rep).picks v).length) :
    (S.map rep).term d db v l ≤ S.term d db v ⟨l, by simpa [Sched.map] using l.isLt⟩ := by
  unfold Sched.term
  rw [picks_map_getElem, pre_map, suf_map, show (S.map rep).mate = S.mate from rfl]
  simp only [Fin.getElem_fin, Sched.pre, Sched.suf]
  have h₁ : (((S.drops (S.mate v l).1).take (S.mate v l).2).map (d ∘ rep)).sum ≤
      (((S.drops (S.mate v l).1).take (S.mate v l).2).map d).sum :=
    List.sum_le_sum fun i _ => hd i
  have h₂ : (((S.picks v).drop (l + 1)).map (db ∘ rep)).sum ≤
      (((S.picks v).drop (l + 1)).map db).sum :=
    List.sum_le_sum fun i _ => hdb i
  have h₃ := hd ((S.picks v)[l.val]'(by simpa [Sched.map] using l.isLt))
  have h₄ := hdb ((S.picks v)[l.val]'(by simpa [Sched.map] using l.isLt))
  change 2 * _ + _ + _ + 2 * _ ≤ 2 * _ + _ + _ + 2 * _
  omega

theorem tmpl_map_le (d db : Fin n → ℕ) (hd : ∀ i, d (rep i) ≤ d i)
    (hdb : ∀ i, db (rep i) ≤ db i) : (S.map rep).tmpl d db ≤ S.tmpl d db := by
  unfold Sched.tmpl
  refine max_le_max (Finset.sup_le fun k _ => (S.load_map_le d db hd hdb k).trans
    (Finset.le_sup (f := fun k => S.load d db k) (Finset.mem_univ k)))
    (Finset.sup_le fun v _ => Finset.sup_le fun l _ => (S.term_map_le d db hd hdb v l).trans ?_)
  exact (Finset.le_sup (f := fun l => S.term d db v l) (Finset.mem_univ _)).trans
    (Finset.le_sup (f := fun v => univ.sup fun l => S.term d db v l) (Finset.mem_univ v))

/-- **Rescaling.** When `d = g · d'` and `d̄ = g · d̄'` on the cities `rep` returns, `g` times the
closed form on `d'`, `d̄'` is at most the closed form on `d`, `d̄` (they are equal). -/
theorem mul_tmpl_map_le {d db d' db' : Fin n → ℕ} {g : ℕ} (hg : 0 < g)
    (hd : ∀ i, d (rep i) = g * d' (rep i)) (hdb : ∀ i, db (rep i) = g * db' (rep i)) :
    g * (S.map rep).tmpl d' db' ≤ (S.map rep).tmpl d db := by
  rw [mul_comm, ← Nat.le_div_iff_mul_le hg]
  have hsum : ∀ (f f' : Fin n → ℕ), (∀ i, f (rep i) = g * f' (rep i)) → ∀ L : List (Fin n),
      ((L.map rep).map f).sum = g * ((L.map rep).map f').sum := fun f f' hf L => by
    rw [List.map_map, List.map_map, ← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun i _ => hf i)
  have hmsum : ∀ (f f' : Fin n → ℕ), (∀ i, f (rep i) = g * f' (rep i)) → ∀ Y : Multiset (Fin n),
      ZenoFront.load f (Y.map rep) = g * ZenoFront.load f' (Y.map rep) := fun f f' hf Y => by
    simp only [ZenoFront.load, Multiset.map_map]
    rw [← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => hf i)
  unfold Sched.tmpl
  refine max_le (Finset.sup_le fun k _ => ?_) (Finset.sup_le fun v _ => Finset.sup_le fun l _ => ?_)
  · rw [Nat.le_div_iff_mul_le hg]
    refine le_of_eq_of_le ?_ ((Finset.le_sup (f := fun k => (S.map rep).load d db k)
      (Finset.mem_univ k)).trans (le_max_left _ _))
    simp only [Sched.load, Sched.map]
    rw [hsum d d' hd, hsum db db' hdb, hmsum d d' hd, hmsum db db' hdb]
    ring
  · rw [Nat.le_div_iff_mul_le hg]
    refine le_of_eq_of_le ?_ ((Finset.le_sup (f := fun l => (S.map rep).term d db v l)
      (Finset.mem_univ l)).trans ((Finset.le_sup (f := fun v => univ.sup fun l =>
        (S.map rep).term d db v l) (Finset.mem_univ v)).trans (le_max_right _ _)))
    have hsum' : ∀ (f f' : Fin n → ℕ), (∀ i, f (rep i) = g * f' (rep i)) → ∀ L : List (Fin n),
        (L.map (f ∘ rep)).sum = g * (L.map (f' ∘ rep)).sum := fun f f' hf L => by
      rw [← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun i _ => hf i)
    show (_ + _ + _ + _) * g = _ + _ + _ + _
    rw [picks_map_getElem, pre_map, suf_map, pre_map, suf_map, hsum' d d' hd, hsum' db db' hdb,
      hd, hdb]
    ring

end Sched

end ZenoFront
