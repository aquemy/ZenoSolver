/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.MinimalWitness

/-!
# Link forests (Lemma 2.6, "only if")

A *link forest* for a grouping is a forest on its planes whose edges carry city labels, such that
the links at a plane use distinct copies of its landings (F1) and every plane keeps an odd
number of *free* landings (F2). Lemma 2.6 of the note: a grouping is admissible iff it has a
link forest. The tree DP of the checker (`TreeBound.lean`) needs only "only if", in rooted form,
and this file proves exactly that.

A rooted link tree (`LTree`) is a plane with its free landings and a list of *child items*
(`LKids`): a link label and the subtree hanging from it. The group of a plane is its free
landings, one copy of each child label, and one copy of its parent's label (`LTree.groups`).
(F1) holds by construction, and (F2) is `LTree.WF`.

The proof is by induction on the number of planes, by removing a leaf. Take a parity witness
`h` with the fewest edges (`Admissible.exists_minimal`).

* If some plane has `h u = ∅`, its group has odd size: it is an isolated vertex. Remove it.
* Otherwise some plane has `|h u| = 1` (`exists_card_eq_one_of_minimal`). The edge vectors of a
  minimal witness are independent, so `#edges + 1 ≤ p + #touched`; and `2 · #touched ≤ #edges`.
  If every `|h k| ≥ 2`, then `#edges ≥ 2p`, a contradiction. With `h u = {i}`, another plane
  `v` has `i ∈ h v`. Remove `u`, and one copy of `i` from `X v` and from `h v`. This is a parity
  witness again. By induction the smaller grouping has a link forest; hang `u` from the plane
  whose group is `X v − {i}`, by a link labelled `i` (`attachForest`).

## Main results

* `ZenoFront.LTree`, `ZenoFront.LKids`, `ZenoFront.LTree.groups`, `ZenoFront.LTree.WF`.
* `ZenoFront.Admissible.exists_linkForest`: an admissible grouping is the multiset of groups of a
  list of rooted link trees.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n : ℕ}

mutual
/-- A rooted link tree: a plane, its free landings, and its child items. -/
inductive LTree (n : ℕ) : Type where
  | node (free : Multiset (Fin n)) (kids : LKids n)
/-- The child items of a plane: link labels, each with the subtree hanging from it. -/
inductive LKids (n : ℕ) : Type where
  | nil
  | cons (b : Fin n) (child : LTree n) (rest : LKids n)
end

/-- The labels of the child items. -/
def LKids.labels : LKids n → Multiset (Fin n)
  | .nil => 0
  | .cons b _ rest => b ::ₘ rest.labels

mutual
/-- The groups of the planes of a tree. The root's group is its free landings, one copy of each
child label and `extra` (one copy of the parent's label for a hanging tree, `0` for a root). -/
def LTree.groups : LTree n → Multiset (Fin n) → Multiset (Multiset (Fin n))
  | .node free kids, extra => (free + kids.labels + extra) ::ₘ kids.groups
/-- The groups of the planes of the subtrees of the child items. -/
def LKids.groups : LKids n → Multiset (Multiset (Fin n))
  | .nil => 0
  | .cons b child rest => child.groups {b} + rest.groups
end

mutual
/-- (F2): every plane has an odd number of free landings. -/
def LTree.WF : LTree n → Prop
  | .node free kids => Odd free.card ∧ kids.WF
/-- (F2) for every subtree. -/
def LKids.WF : LKids n → Prop
  | .nil => True
  | .cons _ child rest => child.WF ∧ rest.WF
end

/-- The groups of a forest of rooted trees. -/
def forestGroups (F : List (LTree n)) : Multiset (Multiset (Fin n)) :=
  (F.map fun t => t.groups 0).sum

/-! ### Hanging a leaf -/

section Attach

variable (i : Fin n) (f : Multiset (Fin n)) (hf : Odd f.card)
include hf

set_option linter.unusedSectionVars false in
mutual
/-- Hanging a leaf with free landings `f` by a link labelled `i` from the plane of group `g`:
that group becomes `i ::ₘ g`, and the leaf's group is `i ::ₘ f`. -/
theorem LTree.attach : ∀ (t : LTree n) (extra g : Multiset (Fin n))
    (R : Multiset (Multiset (Fin n))), t.WF → t.groups extra = g ::ₘ R →
      ∃ t' : LTree n, t'.WF ∧ t'.groups extra = (i ::ₘ g) ::ₘ (i ::ₘ f) ::ₘ R
  | .node free kids, extra, g, R, hwf, hgr => by
    simp only [LTree.groups] at hgr
    obtain ⟨hfree, hkids⟩ := hwf
    rcases Multiset.cons_eq_cons.mp hgr with ⟨hg, hR⟩ | ⟨-, cs, hkg, hR⟩
    · refine ⟨.node free (.cons i (.node f .nil) kids), ⟨hfree, ⟨hf, trivial⟩, hkids⟩, ?_⟩
      simp only [LTree.groups, LKids.groups, LKids.labels, ← hg, ← hR]
      rw [show f + 0 + {i} = i ::ₘ f by rw [add_zero, add_comm, Multiset.singleton_add]]
      simp only [Multiset.cons_add, zero_add, Multiset.add_cons]
    · obtain ⟨k', hwf', hlab, hgr'⟩ := LKids.attach kids g cs hkids hkg
      refine ⟨.node free k', ⟨hfree, hwf'⟩, ?_⟩
      simp only [LTree.groups, hlab, hgr', hR]
      rw [Multiset.cons_swap, Multiset.cons_swap (free + kids.labels + extra) (i ::ₘ f)]

/-- `LTree.attach` inside the subtrees of the child items. The labels do not change. -/
theorem LKids.attach : ∀ (k : LKids n) (g : Multiset (Fin n)) (R : Multiset (Multiset (Fin n))),
    k.WF → k.groups = g ::ₘ R →
      ∃ k' : LKids n, k'.WF ∧ k'.labels = k.labels ∧ k'.groups = (i ::ₘ g) ::ₘ (i ::ₘ f) ::ₘ R
  | .nil, g, R, _, hgr => by
    simp only [LKids.groups] at hgr
    exact absurd hgr.symm (Multiset.cons_ne_zero)
  | .cons b child rest, g, R, hwf, hgr => by
    simp only [LKids.groups] at hgr
    obtain ⟨hchild, hrest⟩ := hwf
    have hmem : g ∈ child.groups {b} + rest.groups := by rw [hgr]; exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.mp hmem with hc | hr
    · obtain ⟨R₁, hR₁⟩ := Multiset.exists_cons_of_mem hc
      obtain ⟨c', hwf', hgr'⟩ := LTree.attach child {b} g R₁ hchild hR₁
      refine ⟨.cons b c' rest, ⟨hwf', hrest⟩, rfl, ?_⟩
      have : R = R₁ + rest.groups := by
        rw [hR₁, Multiset.cons_add] at hgr
        exact (Multiset.cons_inj_right g).mp hgr |>.symm
      simp only [LKids.groups, hgr', this, Multiset.cons_add]
    · obtain ⟨R₂, hR₂⟩ := Multiset.exists_cons_of_mem hr
      obtain ⟨r', hwf', hlab, hgr'⟩ := LKids.attach rest g R₂ hrest hR₂
      refine ⟨.cons b child r', ⟨hchild, hwf'⟩, by simp [LKids.labels, hlab], ?_⟩
      have : R = child.groups {b} + R₂ := by
        rw [hR₂, Multiset.add_cons] at hgr
        exact (Multiset.cons_inj_right g).mp hgr |>.symm
      simp only [LKids.groups, hgr', this, Multiset.add_cons]
end

/-- `LTree.attach` in a forest. -/
theorem attachForest : ∀ (F : List (LTree n)) (g : Multiset (Fin n))
    (R : Multiset (Multiset (Fin n))), (∀ t ∈ F, t.WF) → forestGroups F = g ::ₘ R →
      ∃ F' : List (LTree n), (∀ t ∈ F', t.WF) ∧ forestGroups F' = (i ::ₘ g) ::ₘ (i ::ₘ f) ::ₘ R
  | [], g, R, _, hgr => by
    simp only [forestGroups, List.map_nil, List.sum_nil] at hgr
    exact absurd hgr.symm Multiset.cons_ne_zero
  | t :: F, g, R, hwf, hgr => by
    simp only [forestGroups, List.map_cons, List.sum_cons] at hgr
    change t.groups 0 + forestGroups F = g ::ₘ R at hgr
    have hmem : g ∈ t.groups 0 + forestGroups F := by
      rw [hgr]; exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.mp hmem with hc | hr
    · obtain ⟨R₁, hR₁⟩ := Multiset.exists_cons_of_mem hc
      obtain ⟨t', hwf', hgr'⟩ := LTree.attach i f hf t 0 g R₁ (hwf t List.mem_cons_self) hR₁
      refine ⟨t' :: F, fun u hu => ?_, ?_⟩
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact hwf'
        · exact hwf u (List.mem_cons_of_mem _ hu)
      · have : R = R₁ + forestGroups F := by
          rw [hR₁, Multiset.cons_add] at hgr
          exact (Multiset.cons_inj_right g).mp hgr |>.symm
        simp only [forestGroups, List.map_cons, List.sum_cons] at this ⊢
        rw [hgr', this, Multiset.cons_add, Multiset.cons_add]
    · obtain ⟨R₂, hR₂⟩ := Multiset.exists_cons_of_mem hr
      obtain ⟨F', hwf', hgr'⟩ := attachForest F g R₂ (fun u hu => hwf u (List.mem_cons_of_mem _ hu))
        hR₂
      refine ⟨t :: F', fun u hu => ?_, ?_⟩
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact hwf u List.mem_cons_self
        · exact hwf' u hu
      · have : R = t.groups 0 + R₂ := by
          rw [hR₂, Multiset.add_cons] at hgr
          exact (Multiset.cons_inj_right g).mp hgr |>.symm
        simp only [forestGroups, List.map_cons, List.sum_cons] at hgr' ⊢
        rw [hgr', this, Multiset.add_cons, Multiset.add_cons]

end Attach

/-! ### Leaves of a minimal witness -/

variable {p : ℕ}

/-- In a parity witness with the fewest edges and no empty set, some plane has exactly one
city. -/
theorem IsParityWitness.exists_card_eq_one_of_minimal {X : Groups n (p + 1)}
    {h : Fin (p + 1) → Finset (Fin n)} (hw : IsParityWitness X h)
    (hmin : ∀ h', IsParityWitness X h' → edgeCount h ≤ edgeCount h')
    (hne : ∀ k, (h k).Nonempty) : ∃ u, (h u).card = 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : ∀ k, 2 ≤ (h k).card := fun k => by
    have := Finset.card_pos.mpr (hne k)
    have := hcon k
    omega
  have hli : LinearIndependent (ZMod 2) (edgeVec h) := by
    by_contra hli
    obtain ⟨h', hw', -, hlt⟩ := hw.exists_edgeCount_lt hli
    exact absurd (hmin h' hw') (not_le.mpr hlt)
  have h₁ := edgeCount_add_one_le_of_linearIndependent hli 0
  have h₂ := hw.two_mul_card_touched_le_edgeCount
  have h₃ : 2 * (p + 1) ≤ edgeCount h := by
    have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin (p + 1)))) => h2 k
    simpa [edgeCount, mul_comm] using this
  omega

/-! ### Removing a plane -/

theorem univ_val_map_succAbove {α : Type*} (X : Fin (p + 1) → α) (u : Fin (p + 1)) :
    (univ : Finset (Fin (p + 1))).val.map X =
      X u ::ₘ (univ : Finset (Fin p)).val.map fun k => X (u.succAbove k) := by
  rw [Fin.univ_succAbove p u]
  simp [Finset.map_val, Function.comp_def]

theorem card_filter_succAbove (P : Fin (p + 1) → Prop) [DecidablePred P] (u : Fin (p + 1)) :
    #{k | P k} = (if P u then 1 else 0) + #{k : Fin p | P (u.succAbove k)} := by
  simp only [Finset.card_filter]
  exact Fin.sum_univ_succAbove _ u

theorem univ_val_map_erase {α : Type*} (X : Fin p → α) (v : Fin p) :
    (univ : Finset (Fin p)).val.map X = X v ::ₘ ((univ : Finset (Fin p)).val.erase v).map X := by
  conv_lhs => rw [← Multiset.cons_erase (Finset.mem_univ_val v)]
  rw [Multiset.map_cons]

/-- **Lemma 2.6, "only if", rooted form.** The groups of an admissible grouping are the groups of
a list of rooted link trees satisfying (F2). -/
theorem Admissible.exists_linkForest : ∀ {p : ℕ} {X : Groups n p}, Admissible X →
    ∃ F : List (LTree n), (∀ t ∈ F, t.WF) ∧ forestGroups F = univ.val.map X
  | 0, X, _ => ⟨[], by simp, by simp [forestGroups]⟩
  | p + 1, X, hX => by
    classical
    obtain ⟨h, hw, hmin⟩ := hX.exists_minimal
    by_cases hempty : ∃ u, h u = ∅
    · -- An isolated plane.
      obtain ⟨u, hu⟩ := hempty
      have hodd : Odd (X u).card := by
        have := hw.row u
        rw [hu, Finset.card_empty] at this
        exact Nat.odd_iff.mpr (by omega)
      have hw' : IsParityWitness (fun k => X (u.succAbove k)) fun k => h (u.succAbove k) :=
        ⟨fun k => hw.subset _, fun k => hw.row _, fun i => by
          have := hw.col i
          rw [card_filter_succAbove (fun k => i ∈ h k) u, hu] at this
          simpa using this⟩
      obtain ⟨F, hF, hFg⟩ := Admissible.exists_linkForest ⟨_, hw'⟩
      refine ⟨.node (X u) .nil :: F, fun t ht => ?_, ?_⟩
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hodd, trivial⟩
        · exact hF t ht
      · rw [univ_val_map_succAbove X u, ← hFg]
        simp [forestGroups, LTree.groups, LKids.groups, LKids.labels]
    · -- A leaf `u`, linked at `i` to a plane `v`.
      push Not at hempty
      obtain ⟨u, hu1⟩ := hw.exists_card_eq_one_of_minimal hmin hempty
      obtain ⟨i, hui⟩ := Finset.card_eq_one.mp hu1
      have hiu : i ∈ h u := by rw [hui]; exact Finset.mem_singleton_self i
      have hcol := hw.col i
      have htwo : 1 < #{k | i ∈ h k} := by
        have hpos : 0 < #{k | i ∈ h k} := Finset.card_pos.mpr ⟨u, by simpa using hiu⟩
        obtain ⟨r, hr⟩ := hcol
        omega
      obtain ⟨v, hv, hvu⟩ : ∃ v, i ∈ h v ∧ v ≠ u := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        by_cases hau : a = u
        · exact ⟨b, hb, fun hbu => hab (hau.trans hbu.symm)⟩
        · exact ⟨a, ha, hau⟩
      obtain ⟨v', rfl⟩ := Fin.exists_succAbove_eq hvu
      have hiXv : i ∈ X (u.succAbove v') := Multiset.mem_toFinset.mp (hw.subset _ hv)
      have hiXu : i ∈ X u := Multiset.mem_toFinset.mp (hw.subset _ hiu)
      set X' : Groups n p := fun k =>
        if k = v' then (X (u.succAbove k)).erase i else X (u.succAbove k) with hX'
      set h' : Fin p → Finset (Fin n) := fun k =>
        if k = v' then (h (u.succAbove k)).erase i else h (u.succAbove k) with hh'
      have hw' : IsParityWitness X' h' := by
        refine ⟨fun k => ?_, fun k => ?_, fun j => ?_⟩
        · simp only [hX', hh']
          split_ifs with hk
          · intro j hj
            obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
            exact Multiset.mem_toFinset.mpr
              ((Multiset.mem_erase_of_ne hji).mpr (Multiset.mem_toFinset.mp (hw.subset _ hj)))
          · exact hw.subset _
        · simp only [hX', hh']
          split_ifs with hk
          · subst hk
            rw [Finset.card_erase_of_mem hv, Multiset.card_erase_of_mem hiXv, Nat.pred_eq_sub_one]
            have := hw.row (u.succAbove k)
            have h₁ := Finset.card_pos.mpr ⟨i, hv⟩
            have h₂ := Multiset.card_pos_iff_exists_mem.mpr ⟨i, hiXv⟩
            omega
          · exact hw.row _
        · have hfull := hw.col j
          rw [card_filter_succAbove (fun k => j ∈ h k) u] at hfull
          rw [Finset.card_filter] at hfull ⊢
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')] at hfull ⊢
          have hrest : ∑ k ∈ univ.erase v', (if j ∈ h' k then 1 else 0) =
              ∑ k ∈ univ.erase v', (if j ∈ h (u.succAbove k) then 1 else 0) :=
            Finset.sum_congr rfl fun k hk => by
              simp [hh', (Finset.mem_erase.mp hk).1]
          rw [hrest]
          simp only [hh', ite_true] at hfull ⊢
          by_cases hji : j = i
          · subst hji
            simp only [hiu, hv, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
              ite_true, ite_false] at hfull ⊢
            obtain ⟨r, hr⟩ := hfull
            exact ⟨r - 1, by omega⟩
          · have hju : j ∉ h u := by rw [hui]; simpa using hji
            simp only [hju, ite_false, Finset.mem_erase, ne_eq, hji, not_false_eq_true,
              true_and] at hfull ⊢
            simpa using hfull
      obtain ⟨F, hF, hFg⟩ := Admissible.exists_linkForest ⟨h', hw'⟩
      have hfodd : Odd ((X u).erase i).card := by
        have := hw.row u
        rw [hu1] at this
        rw [Multiset.card_erase_of_mem hiXu, Nat.pred_eq_sub_one]
        have := Multiset.card_pos_iff_exists_mem.mpr ⟨i, hiXu⟩
        exact Nat.odd_iff.mpr (by omega)
      rw [univ_val_map_erase X' v'] at hFg
      obtain ⟨F', hF', hF'g⟩ := attachForest i _ hfodd F _ _ hF hFg
      refine ⟨F', hF', ?_⟩
      rw [hF'g, univ_val_map_succAbove X u, univ_val_map_erase _ v']
      have hv'X : X' v' = (X (u.succAbove v')).erase i := by simp [hX']
      have hmap : ((univ : Finset (Fin p)).val.erase v').map X' =
          ((univ : Finset (Fin p)).val.erase v').map fun k => X (u.succAbove k) :=
        Multiset.map_congr rfl fun k hk => by
          have hk' : k ≠ v' := ((Multiset.Nodup.mem_erase_iff (Finset.nodup _)).mp hk).1
          simp [hX', hk']
      rw [hv'X, hmap, Multiset.cons_erase hiXv, Multiset.cons_erase hiXu, Multiset.cons_swap]

end ZenoFront
