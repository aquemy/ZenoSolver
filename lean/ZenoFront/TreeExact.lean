/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.MinCost
public import ZenoFront.TreeBound

/-!
# The link-forest DP is exact

The link-forest DP of the checker (`TreeBound.lean`, Theorem 6.7) is a lower bound on `E(T)`
(`treeBoundAt_le_totalCost`). This file proves the other direction: every finite value of the DP
is the cost of an admissible partition with loads at most `T`. So the DP is `E(T)`
(`treeBoundAt_eq_minCost`). Its cost is polynomial in the number of non-dominated cities, unlike
the σ-DP's.

* **Lemma 2.6, "if"** (`admissible_forestPartition`). The groups of a forest of rooted link trees
  in which every plane keeps an odd number of free landings (F2) form an admissible partition.
  The witness of a plane is the set of cities with an odd number of links there
  (`linkWitness`). Its size has the parity of the number of links, so of `|X_k| + 1` (F2). Every
  link counts at both its planes, so every city's column is even (`sum_links_forest`). With
  `Admissible.exists_linkForest` ("only if"), a grouping is admissible iff it has a link forest.
* **Attainment** (`TreeData.attained_ch_sub`, `attained_root`, `attained_for`). By induction
  on the number of planes, every finite entry of `Ch`, `Sub`, `Root` and `For` is the cost of
  child items, a subtree, a tree or a forest with those parameters, whose groups have loads at
  most `T`. The free landings come from the one-plane table (`GAttained`).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n : ℕ}

/-! ### Lemma 2.6, "if": a link forest gives an admissible partition -/

mutual
/-- The planes of a tree, each with its group and its links (the labels of its child items and
of its parent link). -/
def LTree.linkPairs : LTree n → Multiset (Fin n) → List (Multiset (Fin n) × Multiset (Fin n))
  | .node free kids, extra => (free + kids.labels + extra, kids.labels + extra) :: kids.linkPairs
/-- The planes of the subtrees of child items, with their groups and links. -/
def LKids.linkPairs : LKids n → List (Multiset (Fin n) × Multiset (Fin n))
  | .nil => []
  | .cons b child rest => child.linkPairs {b} ++ rest.linkPairs
end

/-- The planes of a forest, with their groups and links. -/
def forestPairs (F : List (LTree n)) : List (Multiset (Fin n) × Multiset (Fin n)) :=
  F.flatMap fun t => t.linkPairs 0

mutual
theorem LTree.groups_linkPairs : ∀ (t : LTree n) (e : Multiset (Fin n)),
    (((t.linkPairs e).map Prod.fst : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
      t.groups e
  | .node free kids, e => by
    simp only [LTree.linkPairs, LTree.groups, List.map_cons, ← Multiset.cons_coe]
    rw [LKids.groups_linkPairs kids]
theorem LKids.groups_linkPairs : ∀ k : LKids n,
    (((k.linkPairs).map Prod.fst : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
      k.groups
  | .nil => rfl
  | .cons b child rest => by
    simp only [LKids.linkPairs, LKids.groups, List.map_append, ← Multiset.coe_add]
    rw [LTree.groups_linkPairs child, LKids.groups_linkPairs rest]
end

theorem groups_forestPairs : ∀ F : List (LTree n),
    (((forestPairs F).map Prod.fst : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
      forestGroups F
  | [] => rfl
  | t :: F => by
    have h : forestPairs (t :: F) = t.linkPairs 0 ++ forestPairs F := List.flatMap_cons
    rw [h, List.map_append, ← Multiset.coe_add, LTree.groups_linkPairs t 0, groups_forestPairs F]
    simp [forestGroups]

mutual
/-- Every plane keeps an odd number of free landings besides its links (F2). -/
theorem LTree.free_linkPairs : ∀ (t : LTree n) (e : Multiset (Fin n)), t.WF →
    ∀ pr ∈ t.linkPairs e, ∃ f : Multiset (Fin n), Odd f.card ∧ pr.1 = f + pr.2
  | .node free kids, e, hwf => by
    obtain ⟨hfree, hk⟩ := hwf
    intro pr hpr
    simp only [LTree.linkPairs, List.mem_cons] at hpr
    rcases hpr with rfl | hpr
    · exact ⟨free, hfree, by simp only [add_assoc]⟩
    · exact LKids.free_linkPairs kids hk pr hpr
theorem LKids.free_linkPairs : ∀ k : LKids n, k.WF →
    ∀ pr ∈ k.linkPairs, ∃ f : Multiset (Fin n), Odd f.card ∧ pr.1 = f + pr.2
  | .nil, _ => by simp [LKids.linkPairs]
  | .cons b child rest, hwf => by
    obtain ⟨hc, hr⟩ := hwf
    intro pr hpr
    simp only [LKids.linkPairs, List.mem_append] at hpr
    rcases hpr with hpr | hpr
    · exact LTree.free_linkPairs child {b} hc pr hpr
    · exact LKids.free_linkPairs rest hr pr hpr
end

mutual
/-- Every link is counted at both of its planes: the links of a tree add up to its parent link
plus an even multiset. -/
theorem LTree.sum_links : ∀ (t : LTree n) (e : Multiset (Fin n)),
    ∃ M : Multiset (Fin n), (((t.linkPairs e).map Prod.snd : List (Multiset (Fin n))).sum) =
      e + (M + M)
  | .node free kids, e => by
    obtain ⟨M, hM⟩ := LKids.sum_links kids
    refine ⟨kids.labels + M, ?_⟩
    simp only [LTree.linkPairs, List.map_cons, List.sum_cons, hM]
    abel
theorem LKids.sum_links : ∀ k : LKids n,
    ∃ M : Multiset (Fin n), (((k.linkPairs).map Prod.snd : List (Multiset (Fin n))).sum) =
      k.labels + (M + M)
  | .nil => ⟨0, by simp [LKids.linkPairs, LKids.labels]⟩
  | .cons b child rest => by
    obtain ⟨M₁, h₁⟩ := LTree.sum_links child {b}
    obtain ⟨M₂, h₂⟩ := LKids.sum_links rest
    refine ⟨M₁ + M₂, ?_⟩
    simp only [LKids.linkPairs, List.map_append, List.sum_append, h₁, h₂, LKids.labels,
      ← Multiset.singleton_add]
    abel
end

theorem sum_links_forest : ∀ F : List (LTree n),
    ∃ M : Multiset (Fin n), (((forestPairs F).map Prod.snd : List (Multiset (Fin n))).sum) =
      M + M
  | [] => ⟨0, rfl⟩
  | t :: F => by
    obtain ⟨M₁, h₁⟩ := LTree.sum_links t 0
    obtain ⟨M₂, h₂⟩ := sum_links_forest F
    refine ⟨M₁ + M₂, ?_⟩
    simp only [forestPairs, List.flatMap_cons, List.map_append, List.sum_append] at h₂ ⊢
    rw [h₁, h₂]
    abel

/-- The cities of odd multiplicity in a multiset are as many, mod 2, as its elements. -/
theorem card_filter_odd_count (L : Multiset (Fin n)) :
    (L.toFinset.filter fun i => Odd (L.count i)).card % 2 = L.card % 2 := by
  classical
  rw [← Multiset.toFinset_sum_count_eq L, Finset.sum_nat_mod, Finset.card_filter,
    Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : Odd (L.count i)
  · rw [ite_eq_left h, Nat.odd_iff.mp h]
  · rw [ite_eq_right h, Nat.not_odd_iff_even.mp h |> Nat.even_iff.mp]

/-- **Lemma 2.6, "if", for links.** If every group is its plane's links plus an odd number of
free landings, and the links add up to an even multiset (every link at two planes), the cities
with an odd number of links at each plane form a parity witness. -/
theorem isParityWitness_of_links {P : ℕ} (X : Groups n P) (L : Fin P → Multiset (Fin n))
    (hfree : ∀ k, ∃ f : Multiset (Fin n), Odd f.card ∧ X k = f + L k)
    {M : Multiset (Fin n)} (heven : ∑ k, L k = M + M) :
    IsParityWitness X fun k => (L k).toFinset.filter fun i => Odd ((L k).count i) := by
  classical
  refine ⟨fun k i hi => ?_, fun k => ?_, fun i => ?_⟩
  · obtain ⟨f, -, hf⟩ := hfree k
    simp only [Finset.mem_filter, Multiset.mem_toFinset] at hi
    rw [Multiset.mem_toFinset, hf]
    exact Multiset.mem_add.mpr (Or.inr hi.1)
  · obtain ⟨f, hodd, hf⟩ := hfree k
    rw [card_filter_odd_count, hf, Multiset.card_add]
    obtain ⟨r, hr⟩ := hodd
    omega
  · have hiff : ∀ k, i ∈ (L k).toFinset.filter (fun i => Odd ((L k).count i)) ↔
        Odd ((L k).count i) := fun k => by
      simp only [Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨Multiset.count_pos.mp (Nat.pos_of_ne_zero
        fun h0 => by rw [h0] at h; exact Nat.not_odd_zero h), h⟩⟩
    have hcount : ∑ k, (L k).count i = 2 * M.count i := by
      rw [← Multiset.count_sum', heven, Multiset.count_add, two_mul]
    have hterm : ∀ k, (if i ∈ (L k).toFinset.filter (fun i => Odd ((L k).count i)) then 1 else 0) =
        (L k).count i % 2 := fun k => by
      by_cases h : Odd ((L k).count i)
      · rw [ite_eq_left ((hiff k).mpr h), Nat.odd_iff.mp h]
      · rw [ite_eq_right (mt (hiff k).mp h), Nat.not_odd_iff_even.mp h |> Nat.even_iff.mp]
    rw [Nat.even_iff, Finset.card_filter, Finset.sum_congr rfl fun k _ => hterm k,
      ← Finset.sum_nat_mod, hcount]
    omega

/-- The parity witness of a list of planes with groups and links: the cities with an odd number
of links at the plane. -/
def linkWitness (L : List (Multiset (Fin n) × Multiset (Fin n))) {P : ℕ} (k : Fin P) :
    Finset (Fin n) :=
  let ℓ := (L.getD k (0, 0)).2
  ℓ.toFinset.filter fun i => Odd (ℓ.count i)

/-- **Lemma 2.6, "if", list form.** Planes whose groups are their links plus an odd number of
free landings, and whose links add up to an even multiset, form an admissible partition. -/
theorem isParityWitness_linkWitness (L : List (Multiset (Fin n) × Multiset (Fin n))) {P : ℕ}
    (hlen : L.length = P)
    (hfree : ∀ pr ∈ L, ∃ f : Multiset (Fin n), Odd f.card ∧ pr.1 = f + pr.2)
    {M : Multiset (Fin n)} (heven : ((L.map Prod.snd : List (Multiset (Fin n))).sum) = M + M) :
    IsParityWitness (fun k : Fin P => (L.getD k (0, 0)).1) (linkWitness L) := by
  have hmem : ∀ k : Fin P, L.getD k (0, 0) ∈ L := fun k => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hL : (List.finRange P).map (fun k : Fin P => L.getD k (0, 0)) = L :=
    map_finRange_getD L (0, 0) hlen
  have hsum : ∑ k : Fin P, (L.getD k (0, 0)).2 = (L.map Prod.snd).sum := by
    rw [Fin.sum_univ_def]
    conv_rhs => rw [← hL]
    rw [List.map_map]
    rfl
  exact isParityWitness_of_links _ (fun k => (L.getD k (0, 0)).2) (fun k => hfree _ (hmem k))
    (hsum.trans heven)

/-- A family whose values are the first components of a multiset of pairs can be completed into
those pairs. -/
theorem exists_snd_of_map_fst {α β γ : Type*} [DecidableEq α] [Inhabited γ] (f : α → β) :
    ∀ (A : Multiset α), A.Nodup → ∀ (M : Multiset (β × γ)), A.map f = M.map Prod.fst →
      ∃ g : α → γ, A.map (fun a => (f a, g a)) = M := by
  intro A
  induction A using Multiset.induction_on with
  | empty =>
    intro _ M h
    refine ⟨fun _ => default, ?_⟩
    rw [Multiset.map_zero, eq_comm, ← Multiset.map_eq_zero (f := Prod.fst), ← h, Multiset.map_zero]
  | cons a A ih =>
    intro hnd M h
    obtain ⟨ha, hnd'⟩ := Multiset.nodup_cons.mp hnd
    rw [Multiset.map_cons] at h
    obtain ⟨m, hm, hma⟩ : ∃ m ∈ M, m.1 = f a := by
      have : f a ∈ M.map Prod.fst := by rw [← h]; exact Multiset.mem_cons_self _ _
      obtain ⟨m, hm, hma⟩ := Multiset.mem_map.mp this
      exact ⟨m, hm, hma⟩
    obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hm
    rw [Multiset.map_cons, hma] at h
    obtain ⟨g', hg'⟩ := ih hnd' M' ((Multiset.cons_inj_right _).mp h)
    refine ⟨Function.update g' a m.2, ?_⟩
    rw [Multiset.map_cons, Function.update_self]
    have hA : A.map (fun x => (f x, Function.update g' a m.2 x)) = A.map fun x => (f x, g' x) :=
      Multiset.map_congr rfl fun x hx => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha)]
    rw [hA, hg', ← hma]

/-- The partition of a forest: plane `k` takes the `k`-th group of `forestPairs`. -/
def forestPartition (F : List (LTree n)) (P : ℕ) : Groups n P :=
  fun k => ((forestPairs F).getD k (0, 0)).1

/-- **Lemma 2.6, "if".** The groups of a forest of rooted link trees satisfying (F2), one per
plane, form an admissible partition, whose multiset of groups is the forest's. -/
theorem admissible_forestPartition (F : List (LTree n)) (hwf : ∀ t ∈ F, t.WF) {P : ℕ}
    (hP : (forestGroups F).card = P) :
    Admissible (forestPartition F P) ∧ univ.val.map (forestPartition F P) = forestGroups F := by
  have hlen : (forestPairs F).length = P := by
    rw [← hP, ← groups_forestPairs F]
    simp
  obtain ⟨M, hM⟩ := sum_links_forest F
  have hfree : ∀ pr ∈ forestPairs F, ∃ f : Multiset (Fin n), Odd f.card ∧ pr.1 = f + pr.2 := by
    intro pr hpr
    obtain ⟨t, ht, hpr⟩ := List.mem_flatMap.mp hpr
    exact LTree.free_linkPairs t 0 (hwf t ht) pr hpr
  refine ⟨⟨_, isParityWitness_linkWitness (forestPairs F) hlen hfree hM⟩, ?_⟩
  rw [← groups_forestPairs F, Fin.univ_val_map, List.ofFn_eq_map]
  conv_rhs => rw [← map_finRange_getD (forestPairs F) (0, 0) hlen]
  rw [List.map_map]
  rfl

/-! ### The tree DP is attained -/

theorem minUpTo_attained (f : ℕ → WithTop ℕ) {u v : ℕ} (h : minUpTo f u = v) :
    ∃ m < u, f m = v := by
  rw [minUpTo_eq] at h
  obtain ⟨m, hm, hfm⟩ := exists_mem_eq_of_inf_eq _ _ h
  exact ⟨m, mem_range.mp hm, hfm⟩

theorem minList_attained {β : Type} (f : β → WithTop ℕ) :
    ∀ (l : List β) {v : ℕ}, minList l f = v → ∃ b ∈ l, f b = v
  | [], v, h => absurd h WithTop.top_ne_coe
  | b :: l, v, h => by
    change min (f b) (minList l f) = v at h
    rcases min_choice (f b) (minList l f) with h' | h'
    · exact ⟨b, List.mem_cons_self, h' ▸ h⟩
    · obtain ⟨b', hb', hfb'⟩ := minList_attained f l (h' ▸ h)
      exact ⟨b', List.mem_cons_of_mem _ hb', hfb'⟩

namespace TreeData

variable (D : TreeData n)

/-- The property of `G` used: every finite `G[m][τ]` is the cost of an `m`-multiset of load at
most `τ`. -/
def GAttained : Prop :=
  ∀ m τ (v : ℕ), m ≤ D.S → τ ≤ D.T → D.G m τ = v →
    ∃ Y : Multiset (Fin n), Y.card = m ∧ load D.d Y ≤ τ ∧ cost D.c Y = v

/-- Child items realising `Ch_q[τ][j] = v`, with loads at most `T`. -/
def ChWitness (K : LKids n) (q τ j v : ℕ) : Prop :=
  K.WF ∧ K.groups.card = q ∧ load D.d K.labels = τ ∧
    K.labels.card + (K.groups.map Multiset.card).sum = j ∧
    cost D.c K.labels + (K.groups.map (cost D.c)).sum = v ∧ ∀ g ∈ K.groups, load D.d g ≤ D.T

/-- A subtree hanging from a link labelled `b` realising `Sub_b[q + 1][j] = v`. -/
def SubWitness (t : LTree n) (b : Fin n) (q j v : ℕ) : Prop :=
  t.WF ∧ (t.groups {b}).card = q + 1 ∧ ((t.groups {b}).map Multiset.card).sum = j ∧
    ((t.groups {b}).map (cost D.c)).sum = v ∧ ∀ g ∈ t.groups {b}, load D.d g ≤ D.T

theorem coe_add_eq {a b : WithTop ℕ} {v : ℕ} (h : a + b = v) :
    ∃ x y : ℕ, a = x ∧ b = y ∧ x + y = v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := WithTop.add_eq_coe.mp h
  exact ⟨x, y, hx.symm, hy.symm, by exact_mod_cast hxy⟩

/-- **`Ch` and `Sub` are attained**, by induction on the number of planes. -/
theorem attained_ch_sub (hG : D.GAttained) (Q : ℕ) : ∀ q, q ≤ Q →
    (∀ τ j (v : ℕ), τ ≤ D.T → j ≤ D.S → D.chM Q q τ j = v → ∃ K, D.ChWitness K q τ j v) ∧
    (∀ (b : Fin n) j (v : ℕ), b ∈ D.reps → j ≤ D.S → D.subM Q q b j = v →
      ∃ t, D.SubWitness t b q j v) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  have hch : ∀ τ j (v : ℕ), τ ≤ D.T → j ≤ D.S → D.chM Q q τ j = v →
      ∃ K, D.ChWitness K q τ j v := by
    intro τ j v hτ hj h
    rw [D.chM_eq hq hτ hj] at h
    unfold chEntry at h
    by_cases hq0 : q = 0
    · rw [ite_eq_left hq0] at h
      split_ifs at h with h0
      · obtain ⟨rfl, rfl⟩ := h0
        have hv : v = 0 := by exact_mod_cast h.symm
        subst hv hq0
        exact ⟨.nil, trivial, rfl, by simp [LKids.labels], by simp [LKids.labels, LKids.groups],
          by simp [LKids.labels, LKids.groups], by simp [LKids.groups]⟩
      · exact absurd h WithTop.top_ne_coe
    · rw [ite_eq_right hq0] at h
      obtain ⟨q₁, hq₁, h₁⟩ := minUpTo_attained _ h
      obtain ⟨b, hb, h₂⟩ := minList_attained _ _ h₁
      dsimp only at h₂
      split_ifs at h₂ with hdb
      · obtain ⟨j₁, hj₁, h₃⟩ := minUpTo_attained _ h₂
        change D.chM Q (q - 1 - q₁) (τ - D.d b) (j - 1 - j₁) + (D.c b : WithTop ℕ) +
          D.subM Q q₁ b j₁ = v at h₃
        obtain ⟨x, y, hx, hy, hxy⟩ := coe_add_eq h₃
        obtain ⟨a, cb, ha, hcb, hacb⟩ := coe_add_eq hx
        have hcb' : cb = D.c b := by exact_mod_cast hcb.symm
        obtain ⟨K, hK₁, hK₂, hK₃, hK₄, hK₅, hK₆⟩ :=
          ((ih (q - 1 - q₁) (by omega) (by omega)).1 _ _ a (by omega) (by omega) ha)
        obtain ⟨t, ht₁, ht₂, ht₃, ht₄, ht₅⟩ :=
          ((ih q₁ hq₁ (by omega)).2 b j₁ y hb (by omega) hy)
        refine ⟨.cons b t K, ⟨ht₁, hK₁⟩, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [LKids.groups, Multiset.card_add, ht₂, hK₂]
          omega
        · simp only [LKids.labels, load_cons, hK₃]
          omega
        · simp only [LKids.labels, LKids.groups, Multiset.card_cons, Multiset.map_add,
            Multiset.sum_add, ht₃]
          omega
        · simp only [LKids.labels, LKids.groups, cost_cons, Multiset.map_add, Multiset.sum_add,
            ht₄]
          omega
        · intro g hg
          simp only [LKids.groups, Multiset.mem_add] at hg
          rcases hg with hg | hg
          · exact ht₅ g hg
          · exact hK₆ g hg
      · exact absurd h₂ WithTop.top_ne_coe
  refine ⟨hch, fun b j₁ v hb hj h => ?_⟩
  rw [D.subM_eq hq hb hj] at h
  unfold subEntry at h
  obtain ⟨cb, x, hcb, hx, hcbx⟩ := coe_add_eq h
  have hcb' : cb = D.c b := by exact_mod_cast hcb.symm
  obtain ⟨τ, hτ, h₁⟩ := minUpTo_attained _ hx
  split_ifs at h₁ with hdτ
  · dsimp only at h₁
    obtain ⟨j₂, hj₂, h₂⟩ := minUpTo_attained _ h₁
    split_ifs at h₂ with hodd
    · change D.chM Q q τ j₂ + D.G (j₁ - 1 - j₂) (D.T - D.d b - τ) = _ at h₂
      obtain ⟨a, g, ha, hg, hag⟩ := coe_add_eq h₂
      obtain ⟨K, hK₁, hK₂, hK₃, hK₄, hK₅, hK₆⟩ := hch τ j₂ a (by omega) (by omega) ha
      obtain ⟨Y, hY, hYload, hYcost⟩ := hG _ _ g (by omega) (by omega) hg
      refine ⟨.node Y K, ⟨Nat.odd_iff.mpr (by rw [hY]; exact hodd), hK₁⟩, ?_, ?_, ?_, ?_⟩
      · simp only [LTree.groups, Multiset.card_cons, hK₂]
      · simp only [LTree.groups, Multiset.map_cons, Multiset.sum_cons, Multiset.card_add,
          Multiset.card_singleton, hY]
        omega
      · simp only [LTree.groups, Multiset.map_cons, Multiset.sum_cons, cost_add, hYcost]
        simp only [show cost D.c {b} = D.c b by simp [cost]]
        omega
      · intro g' hg'
        simp only [LTree.groups, Multiset.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · simp only [load_add, hK₃, show load D.d {b} = D.d b by simp [load]]
          omega
        · exact hK₆ g' hg'
    · exact absurd h₂ WithTop.top_ne_coe
  · exact absurd h₁ WithTop.top_ne_coe

/-- **`Root` is attained.** -/
theorem attained_root (hG : D.GAttained) {Q P q j v : ℕ} (hqP : q < P) (hqQ : q ≤ Q)
    (hj : j ≤ D.S) (h : D.rootM Q P q j = v) :
    ∃ t : LTree n, t.WF ∧ (t.groups 0).card = q + 1 ∧ ((t.groups 0).map Multiset.card).sum = j ∧
      ((t.groups 0).map (cost D.c)).sum = v ∧ ∀ g ∈ t.groups 0, load D.d g ≤ D.T := by
  simp only [rootM, roots, getD_ofFn, hqP, show j < D.S + 1 by omega, dite_true,
    rootEntry] at h
  obtain ⟨τ, hτ, h₁⟩ := minUpTo_attained _ h
  obtain ⟨j₂, hj₂, h₂⟩ := minUpTo_attained _ h₁
  split_ifs at h₂ with hodd
  · change D.chM Q q τ j₂ + D.G (j - j₂) (D.T - τ) = _ at h₂
    obtain ⟨a, g, ha, hg, hag⟩ := coe_add_eq h₂
    obtain ⟨K, hK₁, hK₂, hK₃, hK₄, hK₅, hK₆⟩ :=
      (D.attained_ch_sub hG Q q hqQ).1 τ j₂ a (by omega) (by omega) ha
    obtain ⟨Y, hY, hYload, hYcost⟩ := hG _ _ g (by omega) (by omega) hg
    refine ⟨.node Y K, ⟨Nat.odd_iff.mpr (by rw [hY]; exact hodd), hK₁⟩, ?_, ?_, ?_, ?_⟩
    · simp only [LTree.groups, Multiset.card_cons, hK₂]
    · simp only [LTree.groups, Multiset.map_cons, Multiset.sum_cons, Multiset.card_add,
        add_zero, hY]
      omega
    · simp only [LTree.groups, Multiset.map_cons, Multiset.sum_cons, cost_add,
        add_zero, hYcost]
      omega
    · intro g' hg'
      simp only [LTree.groups, Multiset.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · simp only [load_add, add_zero, hK₃]
        omega
      · exact hK₆ g' hg'
  · exact absurd h₂ WithTop.top_ne_coe

/-- **`For` is attained**, by induction on the number of planes. -/
theorem attained_for (hG : D.GAttained) {Q P : ℕ} (hPQ : P ≤ Q + 1) : ∀ P', P' ≤ P →
    ∀ J (v : ℕ), J ≤ D.S → D.forM Q P P' J = v →
      ∃ F : List (LTree n), (∀ t ∈ F, t.WF) ∧ (forestGroups F).card = P' ∧
        ((forestGroups F).map Multiset.card).sum = J ∧
        ((forestGroups F).map (cost D.c)).sum = v ∧ ∀ g ∈ forestGroups F, load D.d g ≤ D.T := by
  intro P'
  induction P' using Nat.strong_induction_on with
  | _ P' ih =>
  intro hP' J v hJ h
  rw [D.forM_eq hP' hJ] at h
  by_cases hP0 : P' = 0
  · rw [ite_eq_left hP0] at h
    split_ifs at h with hJ0
    · have hv : v = 0 := by exact_mod_cast h.symm
      subst hv hJ0 hP0
      exact ⟨[], by simp, by simp [forestGroups], by simp [forestGroups],
        by simp [forestGroups], by simp [forestGroups]⟩
    · exact absurd h WithTop.top_ne_coe
  · rw [ite_eq_right hP0] at h
    obtain ⟨q, hq, h₁⟩ := minUpTo_attained _ h
    obtain ⟨j, hj, h₂⟩ := minUpTo_attained _ h₁
    obtain ⟨a, r, ha, hr, har⟩ := coe_add_eq h₂
    obtain ⟨F, hF₁, hF₂, hF₃, hF₄, hF₅⟩ := ih (P' - 1 - q) (by omega) (by omega) (J - j) a
      (by omega) ha
    obtain ⟨t, ht₁, ht₂, ht₃, ht₄, ht₅⟩ := D.attained_root hG (by omega) (by omega) (by omega) hr
    refine ⟨t :: F, fun u hu => ?_, ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact ht₁
      · exact hF₁ u hu
    · rw [forestGroups_cons, Multiset.card_add, ht₂, hF₂]
      omega
    · rw [forestGroups_cons, Multiset.map_add, Multiset.sum_add, ht₃, hF₃]
      omega
    · rw [forestGroups_cons, Multiset.map_add, Multiset.sum_add, ht₄, hF₄]
      omega
    · intro g hg
      rw [forestGroups_cons, Multiset.mem_add] at hg
      rcases hg with hg | hg
      · exact ht₅ g hg
      · exact hF₅ g hg

/-- **The tree DP is attained**: a finite value is the cost of an admissible partition of `S`
landings into `P` groups with loads at most `T`. -/
theorem value_attained (hG : D.GAttained) {P v : ℕ} (hP : 1 ≤ P) (h : D.value P = v) :
    ∃ X : Groups n P, Admissible X ∧ size X = D.S ∧ (∀ k, load D.d (X k) ≤ D.T) ∧
      totalCost D.c X = v := by
  rw [value_eq] at h
  obtain ⟨F, hwf, hcard, hsize, hcost, hload⟩ :=
    D.attained_for hG (P := P) (Q := P - 1) (by omega) P le_rfl D.S v le_rfl h
  obtain ⟨hX, hmap⟩ := admissible_forestPartition F hwf hcard
  refine ⟨forestPartition F P, hX, ?_, fun k => hload _ ?_, ?_⟩
  · rw [size, Finset.sum_eq_multiset_sum,
      show (fun k => (forestPartition F P k).card) = Multiset.card ∘ forestPartition F P from rfl,
      ← Multiset.map_map, hmap, hsize]
  · rw [← hmap]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
  · rw [totalCost, Finset.sum_eq_multiset_sum,
      show (fun k => cost D.c (forestPartition F P k)) = cost D.c ∘ forestPartition F P from rfl,
      ← Multiset.map_map, hmap, hcost]

end TreeData

/-- **The tree DP is exact.** At a level `T ≤ Tmax`, with `1 ≤ p ≤ t`, the tree-DP bound of the
checker (`treeBoundAt`) is `E(T)`: it is at most the cost of every admissible partition
(`treeBoundAt_le_totalCost`), and every finite value is the cost of one. -/
theorem treeBoundAt_eq_minCost (d c : Fin n → ℕ) {p t Tmax T : ℕ} (hp : 1 ≤ p)
    (hT : T ≤ Tmax) :
    treeBoundAt d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T =
      minCost d c t p T := by
  apply le_antisymm
  · exact le_sInf fun x ⟨X, hX, hsize, hload, hx⟩ =>
      hx ▸ treeBoundAt_le_totalCost d c hp hX hsize hload
  · generalize hv : treeBoundAt d c p (2 * t - p) Tmax (oneplaneTable d c Tmax (2 * t - p)) T
      = v
    cases v using WithTop.recTopCoe with
    | top => exact le_top
    | coe v =>
      unfold treeBoundAt at hv
      simp only [hT, ↓reduceIte] at hv
      set D : TreeData n := ⟨d, c, repList d c,
        fun m τ => ((oneplaneTable d c Tmax (2 * t - p)).getD m #[]).getD τ ⊤, T, 2 * t - p⟩
      have hG : D.GAttained := fun m τ w hm hτ hw => by
        change ((oneplaneTable d c Tmax (2 * t - p)).getD m #[]).getD τ ⊤ = w at hw
        rw [oneplaneTable_getD d c hm (hτ.trans hT)] at hw
        obtain ⟨Y, hY, hYload, hYcost⟩ := exists_cost_eq_oneplane (d := d) (c := c)
          (by rw [hw]; exact WithTop.coe_ne_top)
        exact ⟨Y, hY, hYload, by rw [hYcost] at hw; exact_mod_cast hw⟩
      obtain ⟨X, hX, hsize, hload, hcost⟩ := D.value_attained hG hp hv
      exact (minCost_le d c hX hsize hload).trans (le_of_eq (by rw [← hcost]; rfl))

/-- **Lemma 2.6 (link forest).** A grouping is admissible iff its groups are, as a multiset, the
groups of a forest of rooted link trees in which every plane keeps an odd number of free
landings. -/
theorem admissible_iff_exists_linkForest {P : ℕ} (X : Groups n P) :
    Admissible X ↔ ∃ F : List (LTree n), (∀ t ∈ F, t.WF) ∧ forestGroups F = univ.val.map X := by
  classical
  constructor
  · exact fun hX => hX.exists_linkForest
  · rintro ⟨F, hwf, hF⟩
    have hmap : univ.val.map X =
        (((forestPairs F : List (Multiset (Fin n) × Multiset (Fin n))) :
          Multiset (Multiset (Fin n) × Multiset (Fin n)))).map Prod.fst := by
      rw [← hF, ← groups_forestPairs F, Multiset.map_coe]
    obtain ⟨L, hL⟩ := exists_snd_of_map_fst X univ.val univ.nodup _ hmap
    obtain ⟨M, hM⟩ := sum_links_forest F
    have hfree : ∀ k, ∃ f : Multiset (Fin n), Odd f.card ∧ X k = f + L k := fun k => by
      have hk : (X k, L k) ∈ forestPairs F := by
        rw [← Multiset.mem_coe, ← hL]
        exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
      obtain ⟨t, ht, hpr⟩ := List.mem_flatMap.mp hk
      exact LTree.free_linkPairs t 0 (hwf t ht) _ hpr
    have heven : ∑ k, L k = M + M := by
      rw [← hM, Finset.sum_eq_multiset_sum, ← Multiset.sum_coe, ← Multiset.map_coe, ← hL,
        Multiset.map_map]
      rfl
    exact ⟨_, isParityWitness_of_links X L hfree heven⟩

end ZenoFront
