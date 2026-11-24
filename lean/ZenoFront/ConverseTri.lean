/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.TriCore

/-!
# The converse under (S) and (AΔ) (Theorem 4.10)

**Theorem 4.10.** Under symmetric durations (S) and the triangle inequality (AΔ), with no (A1),
every feasible plan with cost `C` and flight times `F_k` is weakly dominated by an admissible
partition: some admissible `X_1, …, X_p` has `Σ_k |X_k| = s = 2t − p`, `c(X) ≤ C` and
`ℓ(X_k) = 2 δ(X_k) ≤ F_k ≤ M` for every plane (`Feasible.exists_admissible_ATri`). The plan is
on any number `p ≤ t` of planes, which is the note's form for a set `Q` of planes with
`t ≥ |Q|`.

The proof is the note's (§4.6), with (AΔ) used only on the triangles through a hub
(`Network.ATriHub`), which (A1) also implies:

* **Segments** (`PlaneFeasible.exists_segments_tri`). Each plane's route is cut into its
  `σ_k` segments, each a block of landings with `F(γ) ≥ 2 d_x` for every landing `x`.
* **Step 1, sharing components.** Planes are connected when they land in a common central city.
  Every passenger has a *chain* (`ToGoal`): its last departure from `C_I` and the legs up to its
  next arrival in `C_G`, which meet in central cities, so they stay in one class. Counting
  (Lemma 3.2) in each class `K` gives `2 t_K ≤ σ_K + q_K`. In each class with `σ_K + q_K` odd,
  two segments of a plane with `σ_k ≥ 2` are merged into one block (`exists_merge`); a merged
  block still flies at least `2 d_x` for each of its landings. The number of planes with an even
  number of blocks is then even in every class, and the blocks number at least `2t − p`.
* **Steps 2–5** (`exists_admissible_of_blocks`, in `TriCore.lean`): links from a `T`-join,
  re-pairing at the smaller-duration city, payments, Lemma 2.3.
* **Lemma 4.11** (`Admissible.exists_shrink`) brings the partition to exactly `2t − p`
  landings.

Every group pays with distinct central landings of the plan, so `c(X) ≤ C`, and plane `k`'s
group has one city per block within the block's largest duration, so `2 δ(X_k) ≤ F_k`.

## Main results

* `ZenoFront.ToGoal`, `ZenoFront.Feasible.exists_chains`: the passengers' chains.
* `ZenoFront.exists_merge`: one merge per class of odd parity.
* `ZenoFront.exists_admissible_of_chains`: Theorem 4.10 for planes that end in `C_G` and
  passengers that have chains (used by the bridge, Theorem 4.9).
* `ZenoFront.Feasible.exists_admissible_ATri`: **Theorem 4.10**, with `ℓ(X_k) ≤ F_k ≤ M`.
* `ZenoFront.Feasible.exists_admissible_ATri_makespan`: the same in the shape of
  `Feasible.exists_admissible` (Theorem 4.7).
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### Chains -/

/-- A *chain* from `x` at time `τ`: a route that lands only in central cities until its last
leg, which arrives in `C_G`. A passenger's last departure from `C_I` and the legs up to its next
arrival in `C_G` form a chain from `C_I` (`Feasible.exists_chains`). -/
def ToGoal : Loc n → ℕ → List (Leg n t) → Prop
  | _, _, [] => False
  | x, τ, ℓ :: rest => ℓ.src = x ∧ τ ≤ ℓ.dep ∧
      ((ℓ.dst = .cg ∧ rest = []) ∨ ((∃ y, ℓ.dst = .city y) ∧ ToGoal ℓ.dst ℓ.arr rest))

/-- A route from a central city that never departs from `C_I` and ends in `C_G` starts with a
chain. -/
theorem toGoal_of_central {N : Network n} : ∀ (l : List (Leg n t)) (y : Fin n) (τ : ℕ),
    IsRoute (.city y) τ l → (∀ ℓ ∈ l, Flies N ℓ) → finalLoc (.city y) l = .cg →
    (∀ ℓ ∈ l, ℓ.src ≠ .ci) → ∃ c : List (Leg n t), (∀ ℓ ∈ c, ℓ ∈ l) ∧ ToGoal (.city y) τ c
  | [], y, τ, _, _, h, _ => by simp at h
  | ℓ :: rest, y, τ, hr, hf, hfin, hnci => by
    obtain ⟨hsrc, hdep, hrest⟩ := hr
    have hfin' : finalLoc ℓ.dst rest = .cg := by simpa using hfin
    cases hdst : ℓ.dst with
    | ci =>
      exfalso
      rw [hdst] at hrest hfin'
      cases rest with
      | nil => simp at hfin'
      | cons ℓ' r => exact hnci ℓ' (by simp) hrest.1
    | cg => exact ⟨[ℓ], by simp, by simp [ToGoal, hsrc, hdep, hdst]⟩
    | city y' =>
      rw [hdst] at hrest hfin'
      obtain ⟨c, hc, hg⟩ := toGoal_of_central rest y' ℓ.arr hrest
        (fun m hm => hf m (List.mem_cons_of_mem _ hm)) hfin'
        (fun m hm => hnci m (List.mem_cons_of_mem _ hm))
      refine ⟨ℓ :: c, fun m hm => ?_, ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hc m hm)
      · refine ⟨hsrc, hdep, Or.inr ⟨⟨y', hdst⟩, ?_⟩⟩
        rw [hdst]
        exact hg

/-- A route that departs from `C_I` somewhere and ends in `C_G` contains a chain from `C_I`: its
last departure from `C_I` and the legs up to the next arrival in `C_G`. -/
theorem exists_chain {N : Network n} : ∀ (l : List (Leg n t)) (x : Loc n) (τ : ℕ),
    IsRoute x τ l → (∀ ℓ ∈ l, Flies N ℓ) → finalLoc x l = .cg → (∃ ℓ ∈ l, ℓ.src = .ci) →
    ∃ c : List (Leg n t), (∀ ℓ ∈ c, ℓ ∈ l) ∧ ∃ τ', ToGoal .ci τ' c
  | [], _, _, _, _, _, h => by simp at h
  | ℓ :: rest, x, τ, hr, hf, hfin, hci => by
    obtain ⟨hsrc, hdep, hrest⟩ := hr
    have hf' : ∀ m ∈ rest, Flies N m := fun m hm => hf m (List.mem_cons_of_mem _ hm)
    have hfin' : finalLoc ℓ.dst rest = .cg := by simpa using hfin
    by_cases h' : ∃ ℓ' ∈ rest, ℓ'.src = .ci
    · obtain ⟨c, hc, hg⟩ := exists_chain rest ℓ.dst ℓ.arr hrest hf' hfin' h'
      exact ⟨c, fun m hm => List.mem_cons_of_mem _ (hc m hm), hg⟩
    · push Not at h'
      have hℓ : ℓ.src = .ci := by
        obtain ⟨m, hm, hms⟩ := hci
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hms
        · exact absurd hms (h' m hm)
      obtain ⟨y, hy⟩ := (hf ℓ List.mem_cons_self).dst_city_of_src_isHub (by simp [hℓ])
      rw [hy] at hrest hfin'
      obtain ⟨c, hc, hg⟩ := toGoal_of_central rest y ℓ.arr hrest hf' hfin' h'
      refine ⟨ℓ :: c, fun m hm => ?_, τ, hℓ, hdep, Or.inr ⟨⟨y, hy⟩, by rw [hy]; exact hg⟩⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hc m hm)

/-- **The passengers' chains.** In a feasible plan, every passenger rides a chain from `C_I`. -/
theorem Feasible.exists_chains {N : Network n} {P : Plan n t p} (hP : Feasible N P) :
    ∀ π : Fin t, ∃ ch : List (Leg n t), (∃ τ, ToGoal .ci τ ch) ∧
      ∀ ℓ ∈ ch, ℓ ∈ allLegs P ∧ ℓ.pax = some π := by
  intro π
  obtain ⟨route, hperm, hroute, hfin⟩ := hP.pax π
  have hmem : ∀ ℓ ∈ route, ℓ ∈ allLegs P ∧ ℓ.pax = some π := fun ℓ hℓ =>
    mem_allLegs_of_mem_paxLegs (hperm.mem_iff.mp hℓ)
  have hci : ∃ ℓ ∈ route, ℓ.src = .ci := by
    cases route with
    | nil => simp at hfin
    | cons ℓ r => exact ⟨ℓ, List.mem_cons_self, hroute.1⟩
  obtain ⟨c, hc, hg⟩ := exists_chain route .ci 0 hroute
    (fun ℓ hℓ => hP.flies_of_mem_allLegs (hmem ℓ hℓ).1) hfin hci
  exact ⟨c, hg, fun ℓ hℓ => hmem ℓ (hc ℓ hℓ)⟩

theorem ToGoal.exists_head {x : Loc n} {τ : ℕ} {ch : List (Leg n t)} (h : ToGoal x τ ch) :
    ∃ ℓ₀, ch.head? = some ℓ₀ ∧ ℓ₀.src = x := by
  cases ch with
  | nil => exact absurd h id
  | cons ℓ rest => exact ⟨ℓ, rfl, h.1⟩

theorem ToGoal.exists_cg : ∀ {x : Loc n} {τ : ℕ} {ch : List (Leg n t)}, ToGoal x τ ch →
    ∃ ℓ ∈ ch, ℓ.dst = .cg
  | _, _, [], h => absurd h id
  | _, _, ℓ :: rest, h => by
    rcases h.2.2 with ⟨hd, -⟩ | ⟨-, h'⟩
    · exact ⟨ℓ, List.mem_cons_self, hd⟩
    · obtain ⟨m, hm, hmd⟩ := ToGoal.exists_cg h'
      exact ⟨m, List.mem_cons_of_mem _ hm, hmd⟩

/-- A property that passes from a leg to the next one through their central city holds along the
whole chain once it holds at its first leg. -/
theorem ToGoal.forall_of_head {G : Leg n t → Prop} : ∀ (ch : List (Leg n t)) (x : Loc n) (τ : ℕ),
    ToGoal x τ ch →
    (∀ ℓ ∈ ch, ∀ ℓ' ∈ ch, ∀ y, ℓ.dst = .city y → ℓ'.src = .city y → G ℓ → G ℓ') →
    ∀ ℓ₀, ch.head? = some ℓ₀ → G ℓ₀ → ∀ ℓ ∈ ch, G ℓ
  | [], _, _, h, _, _, _, _ => absurd h id
  | ℓ :: rest, x, τ, h, hprop, ℓ₀, h₀, hG => by
    obtain rfl : ℓ = ℓ₀ := by simpa using h₀
    intro m hm
    rcases h.2.2 with ⟨-, rfl⟩ | ⟨⟨y, hy⟩, h'⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hG
      · simp at hm
    · obtain ⟨ℓ', hℓ', hs⟩ := h'.exists_head
      have hmem' : ℓ' ∈ rest := List.mem_of_mem_head? hℓ'
      have hG' : G ℓ' := hprop ℓ List.mem_cons_self ℓ' (List.mem_cons_of_mem _ hmem') y hy
        (by rw [hs, hy]) hG
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hG
      · exact ToGoal.forall_of_head rest _ _ h'
          (fun a ha b hb => hprop a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
          ℓ' hℓ' hG' m hm

/-! ### Landings of a route -/

theorem mem_landList_of_mem {legs : List (Leg n t)} {ℓ : Leg n t} (h : ℓ ∈ legs) {y : Fin n}
    (hy : ℓ.dst = .city y) : y ∈ landList legs := by
  simp only [landList, List.mem_filterMap]
  exact ⟨ℓ, h, by simp [hy]⟩

/-- A leg leaving a central city `y` on a route from `x` either leaves `x = y` or follows a leg
landing in `y`. -/
theorem mem_landList_of_src : ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs →
    ∀ ℓ ∈ legs, ∀ y : Fin n, ℓ.src = .city y → x = .city y ∨ y ∈ landList legs
  | [], _, _, _, ℓ, h, _, _ => absurd h List.not_mem_nil
  | m :: rest, x, τ, hr, ℓ, h, y, hy => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (hr.1.symm.trans hy)
    · rcases mem_landList_of_src rest m.dst m.arr hr.2.2 ℓ h y hy with h' | h'
      · exact Or.inr (mem_landList_of_mem List.mem_cons_self h')
      · right
        rw [show m :: rest = [m] ++ rest from rfl, landList_append]
        exact List.mem_append_right _ h'

theorem landList_flatten : ∀ L : List (List (Leg n t)),
    (L.map landList).flatten = landList L.flatten
  | [] => rfl
  | l :: L => by
    rw [List.map_cons, List.flatten_cons, List.flatten_cons, landList_append, landList_flatten L]

theorem durSum_flatten : ∀ L : List (List (Leg n t)), (L.map durSum).sum = durSum L.flatten
  | [] => rfl
  | l :: L => by rw [List.map_cons, List.sum_cons, List.flatten_cons, durSum_append,
      durSum_flatten L]

theorem routeLandings_eq_landList (legs : List (Leg n t)) :
    routeLandings legs = (landList legs : Multiset (Fin n)) := (coe_landList legs).symm

/-- A feasible plane has a segment: its last leg arrives in `C_G`. -/
theorem PlaneFeasible.one_le_hubArrivals {N : Network n} {legs : List (Leg n t)}
    (h : PlaneFeasible N legs) : 1 ≤ hubArrivals legs := by
  have hne := isRoute_ne_nil_of_finalLoc_ne h.ends (by simp)
  obtain ⟨ℓ, hℓ, hdst⟩ := exists_mem_dst_finalLoc .ci legs hne
  rw [h.ends] at hdst
  exact List.countP_pos_iff.mpr ⟨ℓ, hℓ, by simp [hdst]⟩

/-! ### Merging two blocks -/

/-- Merge the first two blocks of a list. -/
def mergeTwo {α : Type*} : List (List α) → List (List α)
  | a :: b :: r => (a ++ b) :: r
  | l => l

theorem flatten_mergeTwo {α : Type*} (L : List (List α)) : (mergeTwo L).flatten = L.flatten := by
  match L with
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => simp [mergeTwo]

theorem length_mergeTwo {α : Type*} {L : List (List α)} (h : 2 ≤ L.length) :
    (mergeTwo L).length + 1 = L.length := by
  match L, h with
  | a :: b :: r, _ => simp [mergeTwo]

theorem ne_nil_mergeTwo {α : Type*} {L : List (List α)} (h : ∀ γ ∈ L, γ ≠ []) :
    ∀ γ ∈ mergeTwo L, γ ≠ [] := by
  match L, h with
  | [], h => exact h
  | [_], h => exact h
  | a :: b :: r, h =>
    intro γ hγ
    simp only [mergeTwo, List.mem_cons] at hγ
    rcases hγ with rfl | hγ
    · simp [h a List.mem_cons_self]
    · exact h γ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hγ))

theorem sum_maxD_mergeTwo (d : Fin n → ℕ) (L : List (List (Fin n))) :
    ((mergeTwo L).map (maxD d)).sum ≤ (L.map (maxD d)).sum := by
  match L with
  | [] => exact le_rfl
  | [_] => exact le_rfl
  | a :: b :: r =>
    simp only [mergeTwo, List.map_cons, List.sum_cons, maxD_append]
    have := max_le_add_of_nonneg (Nat.zero_le (maxD d a)) (Nat.zero_le (maxD d b))
    omega

/-! ### Step 1: one merge per class of odd parity -/

open Classical in
/-- **Choosing the merges.** Let planes have `σ_k ≥ 1` segments, be connected by a symmetric
relation `R`, and let passengers be assigned to planes with `2 t_K ≤ σ_K + q_K` in every class
`K` (counting per class). Then removing one segment in each class with `σ_K + q_K` odd, from a
plane with at least two, leaves an even number of planes with an even number of segments in
every class, and at least `2t − p` segments. -/
theorem exists_merge (σ : Fin p → ℕ) (hσ : ∀ k, 1 ≤ σ k) (R : Fin p → Fin p → Prop)
    (hsymm : ∀ k k', R k k' → R k' k) (kπ : Fin t → Fin p)
    (hbound : ∀ a, 2 * #{π | Relation.ReflTransGen R a (kπ π)} ≤
      ∑ k ∈ univ.filter (Relation.ReflTransGen R a), (σ k + 1)) :
    ∃ m : Fin p → ℕ, (∀ k, m k = σ k ∨ (m k + 1 = σ k ∧ 1 ≤ m k)) ∧
      (∀ a, Even #{k | Relation.ReflTransGen R a k ∧ Even (m k)}) ∧ 2 * t ≤ ∑ k, m k + p := by
  set Conn := Relation.ReflTransGen R with hConn
  have csymm : ∀ {a b}, Conn a b → Conn b a := fun h => by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih
  have ctrans : ∀ {a b c}, Conn a b → Conn b c → Conn a c := fun h₁ h₂ => h₁.trans h₂
  set C : Fin p → Finset (Fin p) := fun a => univ.filter (Conn a) with hC
  have hCeq : ∀ {a b}, Conn a b → C a = C b := fun hab => by
    ext k
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ctrans (csymm hab) h, fun h => ctrans hab h⟩
  have hmemC : ∀ a, a ∈ C a := fun a => by
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  set Q : Fin p → ℕ := fun a => ∑ k ∈ C a, (σ k + 1) with hQ
  set big : Fin p → Finset (Fin p) := fun a => (C a).filter fun k => 2 ≤ σ k with hbig
  have hbig_ne : ∀ a, Odd (Q a) → (big a).Nonempty := fun a hodd => by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Q a = ∑ k ∈ C a, 2 := Finset.sum_congr rfl fun k hk => by
      have : k ∉ big a := by rw [hne]; exact Finset.notMem_empty k
      simp only [hbig, Finset.mem_filter, not_and, not_le] at this
      have := this hk
      have := hσ k
      omega
    rw [this, Finset.sum_const, smul_eq_mul] at hodd
    exact Nat.not_even_iff_odd.mpr hodd ⟨(C a).card, by ring⟩
  -- A class merges at its least plane with two segments, if its parity is odd.
  set merge : Fin p → Prop := fun k => Odd (Q k) ∧ k ∈ big k ∧ ∀ k' ∈ big k, k ≤ k' with hmerge
  set m : Fin p → ℕ := fun k => if merge k then σ k - 1 else σ k with hm
  have hmerge2 : ∀ k, merge k → 2 ≤ σ k := fun k h => by
    have := h.2.1
    simp only [hbig, Finset.mem_filter] at this
    exact this.2
  have hm_add : ∀ k, m k + (if merge k then 1 else 0) = σ k := fun k => by
    simp only [hm]
    split_ifs with h
    · have := hmerge2 k h; omega
    · rfl
  have hcount : ∀ a, #{k ∈ C a | merge k} = if Odd (Q a) then 1 else 0 := fun a => by
    have hiff : ∀ k ∈ C a, merge k ↔ Odd (Q a) ∧ k ∈ big a ∧ ∀ k' ∈ big a, k ≤ k' := by
      intro k hk
      have hak : Conn a k := by simpa [hC] using hk
      have h₁ : C k = C a := (hCeq hak).symm
      have h₂ : Q k = Q a := by simp only [hQ, h₁]
      have h₃ : big k = big a := by simp only [hbig, h₁]
      simp only [hmerge, h₂, h₃]
    split_ifs with hodd
    · obtain hne := hbig_ne a hodd
      rw [Finset.card_eq_one]
      refine ⟨(big a).min' hne, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, hmk⟩
        obtain ⟨-, hkb, hkmin⟩ := (hiff k hk).mp hmk
        exact le_antisymm (hkmin _ (Finset.min'_mem _ _)) (Finset.min'_le _ _ hkb)
      · rintro rfl
        have hmem := Finset.min'_mem _ hne
        have hkC : (big a).min' hne ∈ C a := (Finset.mem_filter.mp hmem).1
        exact ⟨hkC, (hiff _ hkC).mpr ⟨hodd, hmem, fun k' hk' => Finset.min'_le _ _ hk'⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k hk hmk => hodd ((hiff k hk).mp hmk).1
  refine ⟨m, fun k => ?_, fun a => ?_, ?_⟩
  · by_cases h : merge k
    · right
      have := hmerge2 k h
      simp only [hm, h, ↓reduceIte]
      omega
    · left
      simp [hm, h]
  · -- Parity in the class of `a`.
    have hsum : ∑ k ∈ C a, (m k + 1) + (if Odd (Q a) then 1 else 0) = Q a := by
      rw [← hcount a, Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := hm_add k
      omega
    have hev : (∑ k ∈ C a, (m k + 1)) % 2 = 0 := by
      split_ifs at hsum with hodd
      · obtain ⟨r, hr⟩ := hodd
        omega
      · obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hodd
        omega
    have hfilt : ({k | Conn a k ∧ Even (m k)} : Finset (Fin p)) =
        (C a).filter fun k => Odd (m k + 1) := by
      ext k
      simp [hC, Nat.odd_add_one]
    rw [hfilt, Nat.even_iff, TriCore.card_odd_mod_two]
    exact hev
  · -- The count, summed over the classes (one representative each).
    set rep : Fin p → Fin p := fun k => (C k).min' ⟨k, hmemC k⟩ with hrep
    have hrepC : ∀ k, Conn k (rep k) := fun k => by
      have := Finset.min'_mem (C k) ⟨k, hmemC k⟩
      simpa [hC] using this
    have hrep_eq : ∀ {k k'}, Conn k k' → rep k = rep k' := fun h => by
      simp only [hrep, hCeq h]
    have hfib : ∀ r, rep r = r → ∀ k, rep k = r ↔ Conn r k := fun r hr k => by
      constructor
      · rintro rfl
        exact csymm (hrepC k)
      · intro h
        rw [← hrep_eq h, hr]
    have hfib0 : ∀ r, rep r ≠ r → ∀ k, rep k ≠ r := fun r hr k hk => by
      apply hr
      rw [← hk] at hr ⊢
      exact (hrep_eq (hrepC k)).symm
    have hper : ∀ r, 2 * #{π | rep (kπ π) = r} + #{k | rep k = r ∧ merge k} ≤
        ∑ k ∈ univ.filter (fun k => rep k = r), (σ k + 1) := fun r => by
      by_cases hr : rep r = r
      · have h₁ : (univ.filter fun π => rep (kπ π) = r) = univ.filter fun π => Conn r (kπ π) := by
          ext π; simp [hfib r hr]
        have h₂ : (univ.filter fun k => rep k = r ∧ merge k) = (C r).filter merge := by
          ext k; simp [hC, hfib r hr]
        have h₃ : univ.filter (fun k => rep k = r) = C r := by
          ext k; simp [hC, hfib r hr]
        rw [h₁, h₂, h₃, hcount r]
        have := hbound r
        change 2 * _ ≤ Q r at this
        change _ ≤ Q r
        split_ifs with hodd
        · have : 2 * #{π | Conn r (kπ π)} ≠ Q r := by
            intro h
            rw [← h] at hodd
            exact Nat.not_even_iff_odd.mpr hodd ⟨_, two_mul _⟩
          omega
        · omega
      · have h₁ : (univ.filter fun π => rep (kπ π) = r) = ∅ := by
          ext π; simp [hfib0 r hr (kπ π)]
        have h₂ : (univ.filter fun k => rep k = r ∧ merge k) = ∅ := by
          ext k; simp [hfib0 r hr k]
        simp [h₁, h₂]
    have hsum := Finset.sum_le_sum fun r (_ : r ∈ (univ : Finset (Fin p))) => hper r
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have ht : ∑ r, #{π | rep (kπ π) = r} = t := by
      rw [← Finset.card_eq_sum_card_fiberwise (f := fun π => rep (kπ π)) (t := univ)
        fun _ _ => Finset.mem_univ _]
      simp
    have hmg : ∑ r, #{k | rep k = r ∧ merge k} = #{k | merge k} := by
      rw [Finset.card_eq_sum_card_fiberwise (f := rep) (s := univ.filter merge) (t := univ)
        fun _ _ => Finset.mem_univ _]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.filter_filter]
      congr 1
      ext k
      simp [and_comm]
    have hσsum : ∑ r, ∑ k ∈ univ.filter (fun k => rep k = r), (σ k + 1) = ∑ k, (σ k + 1) :=
      Finset.sum_fiberwise univ rep fun k => σ k + 1
    rw [ht, hmg, hσsum] at hsum
    have hmsum : ∑ k, (m k + 1) + #{k | merge k} = ∑ k, (σ k + 1) := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := hm_add k
      omega
    have : ∑ k, (m k + 1) = ∑ k, m k + p := by
      rw [Finset.sum_add_distrib]
      simp
    omega

/-! ### Theorem 4.10 -/

open Classical in
/-- **Theorem 4.10 from chains.** Under (S) and (AΔ) on the triangles through a hub, with
`p ≤ t`: if every plane flies from `C_I` to `C_G` and every passenger rides a chain from `C_I`
(legs of the plan carrying it), some admissible `X_1, …, X_p` has `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤ F_k` (the plane's flight time) for every plane, and total cost at most the plan's
cost. -/
theorem exists_admissible_of_chains {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub)
    (c : Fin n → ℕ) {P : Plan n t p} (hplanes : ∀ k, PlaneFeasible N (P k))
    (hch : ∀ π : Fin t, ∃ ch : List (Leg n t), (∃ τ, ToGoal .ci τ ch) ∧
      ∀ ℓ ∈ ch, ℓ ∈ allLegs P ∧ ℓ.pax = some π) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ durSum (P k)) ∧ totalCost c X ≤ planCost c P := by
  -- Segments: the blocks of every plane.
  choose segs hflat hlen hsegs using fun k => (hplanes k).exists_segments_tri hS hL
  set L : Fin p → List (List (Fin n)) := fun k => (segs k).map landList with hLdef
  have hLflat : ∀ k, (L k).flatten = landList (P k) := fun k => by
    simp only [hLdef, landList_flatten, hflat k]
  have hLlen : ∀ k, (L k).length = hubArrivals (P k) := fun k => by simp [hLdef, hlen k]
  have hLne : ∀ k, ∀ γ ∈ L k, γ ≠ [] := fun k γ hγ => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hγ
    exact (hsegs k g hg).2.2.1
  have hLload : ∀ k, 2 * ((L k).map (maxD N.d)).sum ≤ durSum (P k) := fun k => by
    rw [← hflat k, ← durSum_flatten, hLdef, List.map_map, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun g hg => ?_
    obtain ⟨-, -, hne, hle⟩ := hsegs k g hg
    obtain ⟨x, hx, hxd⟩ := exists_mem_maxD N.d hne
    simp only [Function.comp_apply, ← hxd]
    exact hle x hx
  -- Sharing, and the passengers' first and last legs.
  set R : Fin p → Fin p → Prop :=
    fun k k' => ∃ y, y ∈ (L k).flatten ∧ y ∈ (L k').flatten with hRdef
  have hRsymm : ∀ k k', R k k' → R k' k := fun k k' ⟨y, h₁, h₂⟩ => ⟨y, h₂, h₁⟩
  have hmemP : ∀ ℓ ∈ allLegs P, ∃ k, ℓ ∈ P k := fun ℓ h => by
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
    exact ⟨k, hk⟩
  choose ch hτ hchm using hch
  choose ℓo hℓo hℓosrc using fun π => (hτ π).choose_spec.exists_head
  choose ℓg hℓg hℓgdst using fun π => (hτ π).choose_spec.exists_cg
  have hℓo_mem : ∀ π, ℓo π ∈ ch π := fun π => List.mem_of_mem_head? (hℓo π)
  choose kπ hkπ using fun π => hmemP _ (hchm π _ (hℓo_mem π)).1
  have hinj : ∀ f : Fin t → Leg n t, (∀ π, (f π).pax = some π) → Function.Injective f :=
    fun f hf π π' h => by
      have := hf π
      rw [h, hf π'] at this
      exact (Option.some_injective _ this).symm
  -- Counting per class (Lemma 3.2): `2 t_K ≤ σ_K + q_K`.
  have hbound : ∀ a, 2 * #{π | Relation.ReflTransGen R a (kπ π)} ≤
      ∑ k ∈ univ.filter (Relation.ReflTransGen R a), (hubArrivals (P k) + 1) := by
    intro a
    set Pa : Plan n t p := fun k => if Relation.ReflTransGen R a k then P k else [] with hPa
    have hmemPa : ∀ k ℓ, Relation.ReflTransGen R a k → ℓ ∈ P k → ℓ ∈ allLegs Pa :=
      fun k ℓ hk hℓ => List.mem_flatMap.mpr ⟨k, List.mem_finRange _, by simp [hPa, hk, hℓ]⟩
    have hcountPa : ∀ q : Leg n t → Bool, (allLegs Pa).countP q =
        ∑ k ∈ univ.filter (Relation.ReflTransGen R a), (P k).countP q := fun q => by
      rw [countP_allLegs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hPa]
      split_ifs <;> simp
    -- The chain of a passenger of the class stays in the class.
    have hclosed : ∀ π, Relation.ReflTransGen R a (kπ π) →
        ∃ k, Relation.ReflTransGen R a k ∧ ℓg π ∈ P k := fun π hπ => by
      refine ToGoal.forall_of_head (G := fun ℓ => ∃ k, Relation.ReflTransGen R a k ∧ ℓ ∈ P k)
        (ch π) _ _ (hτ π).choose_spec ?_ (ℓo π) (hℓo π) ⟨kπ π, hπ, hkπ π⟩ (ℓg π) (hℓg π)
      rintro ℓ - ℓ' hℓ' y hy hy' ⟨k, hk, hℓk⟩
      obtain ⟨k', hk'⟩ := hmemP _ (hchm π _ hℓ').1
      refine ⟨k', Relation.ReflTransGen.tail hk ⟨y, ?_, ?_⟩, hk'⟩
      · rw [hLflat]
        exact mem_landList_of_mem hℓk hy
      · rw [hLflat]
        rcases mem_landList_of_src (P k') .ci 0 (hplanes k').route ℓ' hk' y hy' with h | h
        · cases h
        · exact h
    choose kg hkg hkgP using hclosed
    have h₁ : #{π | Relation.ReflTransGen R a (kπ π)} ≤
        ∑ k ∈ univ.filter (Relation.ReflTransGen R a), ciDepartures (P k) := by
      refine (card_le_countP_of_injective _ (allLegs Pa) (fun ℓ => ℓ.src.isCI) ℓo
        (hinj ℓo fun π => (hchm π _ (hℓo_mem π)).2) fun π hπ => ?_).trans
        (hcountPa (fun ℓ => ℓ.src.isCI)).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      exact ⟨hmemPa _ _ hπ (hkπ π), by simp [hℓosrc π]⟩
    have h₂ : #{π | Relation.ReflTransGen R a (kπ π)} ≤
        ∑ k ∈ univ.filter (Relation.ReflTransGen R a), cgArrivals (P k) := by
      refine (card_le_countP_of_injective _ (allLegs Pa) (fun ℓ => ℓ.dst.isCG) ℓg
        (hinj ℓg fun π => (hchm π _ (hℓg π)).2) fun π hπ => ?_).trans
        (hcountPa (fun ℓ => ℓ.dst.isCG)).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      exact ⟨hmemPa _ _ (hkg π hπ) (hkgP π hπ), by simp [hℓgdst π]⟩
    have h₃ : ∑ k ∈ univ.filter (Relation.ReflTransGen R a),
        (ciDepartures (P k) + cgArrivals (P k)) =
        ∑ k ∈ univ.filter (Relation.ReflTransGen R a), (hubArrivals (P k) + 1) :=
      Finset.sum_congr rfl fun k _ => (hplanes k).ciDepartures_add_cgArrivals
    rw [Finset.sum_add_distrib] at h₃
    omega
  -- Step 1: one merge per class of odd parity.
  obtain ⟨m, hm, hmpar, hmcount⟩ := exists_merge (fun k => hubArrivals (P k))
    (fun k => (hplanes k).one_le_hubArrivals) R hRsymm kπ hbound
  set blocks : Fin p → List (List (Fin n)) :=
    fun k => if m k = hubArrivals (P k) then L k else mergeTwo (L k) with hblocks
  have hbflat : ∀ k, (blocks k).flatten = (L k).flatten := fun k => by
    simp only [hblocks]
    split_ifs
    · rfl
    · exact flatten_mergeTwo _
  have hblen : ∀ k, (blocks k).length = m k := fun k => by
    simp only [hblocks]
    split_ifs with h
    · rw [hLlen, h]
    · rcases hm k with h' | ⟨h', h''⟩
      · exact absurd h' h
      · have := length_mergeTwo (L := L k) (by rw [hLlen]; omega)
        rw [hLlen] at this
        omega
  have hbne : ∀ k, ∀ γ ∈ blocks k, γ ≠ [] := fun k => by
    simp only [hblocks]
    split_ifs
    · exact hLne k
    · exact ne_nil_mergeTwo (hLne k)
  have hbload : ∀ k, ((blocks k).map (maxD N.d)).sum ≤ ((L k).map (maxD N.d)).sum := fun k => by
    simp only [hblocks]
    split_ifs
    · exact le_rfl
    · exact sum_maxD_mergeTwo _ _
  -- Steps 2–5.
  obtain ⟨X₀, hX₀, hX₀card, hX₀load, hX₀sub⟩ := exists_admissible_of_blocks N.d blocks hbne
    (fun a => by
      have := hmpar a
      simp only [hbflat, hblen]
      exact this)
  have hsize₀ : 2 * t - p ≤ size X₀ := by
    have : size X₀ = ∑ k, m k := Finset.sum_congr rfl fun k _ => by rw [hX₀card, hblen]
    omega
  -- Lemma 4.11: shrink to exactly `2t − p` landings.
  obtain ⟨X, hX, hle, hsize⟩ := hX₀.exists_shrink (s := 2 * t - p) (by omega) (by omega) hsize₀
  refine ⟨X, hX, hsize, fun k => ?_, ?_⟩
  · calc 2 * load N.d (X k) ≤ 2 * load N.d (X₀ k) := Nat.mul_le_mul_left 2 (load_mono _ (hle k))
      _ ≤ 2 * ((L k).map (maxD N.d)).sum :=
          Nat.mul_le_mul_left 2 ((hX₀load k).trans (hbload k))
      _ ≤ durSum (P k) := hLload k
  · have hsub : landings X ≤ ∑ k, routeLandings (P k) := by
      calc landings X ≤ landings X₀ := Finset.sum_le_sum fun k _ => hle k
        _ ≤ ∑ k, ((blocks k).flatten : Multiset (Fin n)) := hX₀sub
        _ = ∑ k, routeLandings (P k) := Finset.sum_congr rfl fun k _ => by
            rw [hbflat, hLflat, routeLandings_eq_landList]
    calc totalCost c X = cost c (landings X) := totalCost_eq_cost_landings c X
      _ ≤ cost c (∑ k, routeLandings (P k)) := cost_mono c hsub
      _ = ∑ k, cost c (routeLandings (P k)) :=
          (totalCost_eq_cost_landings c fun k => routeLandings (P k)).symm
      _ = ∑ k, landCostSum c (P k) :=
          Finset.sum_congr rfl fun k _ => (landCostSum_eq_cost c (P k)).symm
      _ = planCost c P := rfl

/-- A plane's flight time is at most its end time, hence at most the makespan: `F_k ≤ M`. -/
theorem PlaneFeasible.durSum_le_planMakespan {N : Network n} {P : Plan n t p} {k : Fin p}
    (h : PlaneFeasible N (P k)) : durSum (P k) ≤ planMakespan P := by
  have := add_durSum_le_endTime (P k) .ci 0 h.route fun ℓ hℓ => (h.flies ℓ hℓ).dep_le_arr
  have := endTime_le_planMakespan P k
  omega

/-- **Theorem 4.10 under the triangles through a hub.** Under (S) and `ATriHub`, with `p ≤ t`,
every feasible plan gives an admissible `X_1, …, X_p` with `Σ_k |X_k| = 2t − p`,
`2 δ(X_k) ≤ F_k ≤ M` for every plane and `c(X) ≤ C`. -/
theorem Feasible.exists_admissible_hub {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub)
    (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ durSum (P k) ∧ durSum (P k) ≤ planMakespan P) ∧
      totalCost c X ≤ planCost c P := by
  obtain ⟨X, hX, hsize, hload, hcost⟩ :=
    exists_admissible_of_chains hS hL c hP.planes hP.exists_chains hpt
  exact ⟨X, hX, hsize, fun k => ⟨hload k, (hP.planes k).durSum_le_planMakespan⟩, hcost⟩

/-- **Theorem 4.10 (converse without (A1)).** Under (S) and (AΔ), with `p ≤ t` (a plan on any
number of planes, at most `t`), every feasible plan with cost `C`, makespan `M` and flight times
`F_k` gives an admissible partition `X_1, …, X_p` of a multiset with `Σ_k |X_k| = 2t − p`,
`ℓ(X_k) = 2 δ(X_k) ≤ F_k ≤ M` for every plane and `c(X) ≤ C`. -/
theorem Feasible.exists_admissible_ATri {N : Network n} (hS : N.dbar = N.d) (hA : N.ATri)
    (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ durSum (P k) ∧ durSum (P k) ≤ planMakespan P) ∧
      totalCost c X ≤ planCost c P :=
  hP.exists_admissible_hub hS hA.hub c hpt

/-- **Theorem 4.10, makespan form**, in the shape of `Feasible.exists_admissible`
(Theorem 4.7): `2 δ(X_k) ≤ M`. -/
theorem Feasible.exists_admissible_ATri_makespan {N : Network n} (hS : N.dbar = N.d)
    (hA : N.ATri) (c : Fin n → ℕ) {P : Plan n t p} (hP : Feasible N P) (hpt : p ≤ t) :
    ∃ X : Groups n p, Admissible X ∧ size X = 2 * t - p ∧
      (∀ k, 2 * load N.d (X k) ≤ planMakespan P) ∧ totalCost c X ≤ planCost c P := by
  obtain ⟨X, hX, hsize, hload, hcost⟩ := hP.exists_admissible_ATri hS hA c hpt
  exact ⟨X, hX, hsize, fun k => (hload k).1.trans (hload k).2, hcost⟩

end ZenoFront
