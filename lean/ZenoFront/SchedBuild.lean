/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Visits
public import ZenoFront.LinkCount
public import ZenoFront.SearchGap
public import ZenoFront.Converse
public import Mathlib.Tactic.Ring

/-!
# Steps 4–6 of Theorem 6.9: the scheduled configuration

From the visits of the planes (`PlanesOK`, as Step 2 leaves them, `Rewire.lean`) and links
between drop-off visits (`B`: entered from and left towards `C_I`) and pick-up visits (`B̄`:
entered from and left towards `C_G`), with `a(B) ≤ e(B̄)` at the same city, this file builds a
scheduled configuration (`Sched`, `toSched`): per plane, its linked `B` visits in route order
are its drop-offs, its linked `B̄` visits its pick-ups, and crossings are taken among its `A` and
`Ā` visits. The matching sends each pick-up to the drop-off it is linked to.

* `toSched_valid`: the configuration is valid.
* `toSched_cost_le`: its cost is at most the landing cost of the legs.
* `toSched_tmpl_le` (**Step 5**): its closed form (Lemma 6.3) is at most any bound `M` on the
  arrival times. A plane flies its earlier drop-offs before the linked one, so
  `Pre_u(j) + d_x ≤ a(B)`; after `e(B̄)` it flies to `C_G` and its later pick-ups by `M`, so
  `e(B̄) + d̄_x + Suf_v(l) ≤ M`; and `a(B) ≤ e(B̄)`. Role loads are at most the flight times.
* `exists_sched_of` (**Steps 3–6**): with the hand-offs ordered as Step 2 leaves them, the links
  of `exists_links` and Lemma 4.4's shrinking give a valid configuration with `2t − p` landings.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ} {K : Type}

/-- The central city of a location, `x₀` at a hub. -/
def Loc.cityOr (x₀ : Fin n) : Loc n → Fin n
  | .city i => i
  | _ => x₀

@[simp] theorem Loc.cityOr_city (x₀ i : Fin n) : (Loc.city i).cityOr x₀ = i := rfl

/-- The flight time of a visit. -/
def Visit.w (v : Visit n t K) : ℕ := (v.1.leg.arr - v.1.leg.dep) + (v.2.leg.arr - v.2.leg.dep)

/-- A crossing `A`: entered from `C_I`, left towards `C_G`. -/
def Visit.isA (v : Visit n t K) : Bool := v.1.leg.src.isCI && !v.2.leg.dst.isCI

/-- A crossing `Ā`: entered from `C_G`, left towards `C_I`. -/
def Visit.isAbar (v : Visit n t K) : Bool := !v.1.leg.src.isCI && v.2.leg.dst.isCI

/-- The local facts of a visit: it flies from a hub into a central city and out of it to a hub,
the exit after the entry. -/
structure LocOK (N : Network n) (v : Visit n t K) : Prop where
  hub : v.1.leg.src.isHub = true
  flies₁ : Flies N v.1.leg
  flies₂ : Flies N v.2.leg
  city : ∃ x, v.1.leg.dst = .city x ∧ v.2.leg.src = .city x
  wait : v.1.leg.arr ≤ v.2.leg.dep
  exit : v.2.leg.dst.isHub = true

/-- What Steps 3–6 need of the visits of every plane, in the order of the configuration: the
local facts; a drop-off (`C_I → x → C_I`) enters `x` after the flight time of the visits before
it; a pick-up (`C_G → x → C_G`) is followed by the visits after it by `M`; the flight time is at
most `M`; and `#A = #Ā + 1`. The rewired visits satisfy them (`planesOK_withLoops`). -/
structure PlanesOK (N : Network n) (M : ℕ) (R : Fin p → List (Visit n t K)) : Prop where
  loc : ∀ k, ∀ v ∈ R k, LocOK N v
  pre : ∀ k (m : ℕ) (hm : m < (R k).length), (R k)[m].1.leg.src = .ci →
    (R k)[m].2.leg.dst = .ci → (((R k).take m).map Visit.w).sum ≤ (R k)[m].1.leg.dep
  suf : ∀ k (m : ℕ) (hm : m < (R k).length), (R k)[m].1.leg.src = .cg →
    (R k)[m].2.leg.dst = .cg → (R k)[m].2.leg.arr + (((R k).drop (m + 1)).map Visit.w).sum ≤ M
  load : ∀ k, ((R k).map Visit.w).sum ≤ M
  par : ∀ k, (R k).countP Visit.isA = (R k).countP Visit.isAbar + 1

/-- The two flights of every passenger, without keys: `ℓα π : C_I → x` and `ℓβ π : x → C_G`,
both carrying `π`. -/
structure PaxEnds (ℓα ℓβ : Fin t → KLeg n t K) : Prop where
  paxα : ∀ π, (ℓα π).leg.pax = some π
  paxβ : ∀ π, (ℓβ π).leg.pax = some π
  srcα : ∀ π, (ℓα π).leg.src = .ci
  dstβ : ∀ π, (ℓβ π).leg.dst = .cg
  city : ∀ π, ∃ x, (ℓα π).leg.dst = .city x ∧ (ℓβ π).leg.src = .city x

theorem PaxEnds.injα {ℓα ℓβ : Fin t → KLeg n t K} (h : PaxEnds ℓα ℓβ) {π π' : Fin t}
    (he : ℓα π = ℓα π') : π = π' := by
  have := h.paxα π
  rw [he, h.paxα π'] at this
  exact (Option.some_injective _ this).symm

theorem PaxEnds.injβ {ℓα ℓβ : Fin t → KLeg n t K} (h : PaxEnds ℓα ℓβ) {π π' : Fin t}
    (he : ℓβ π = ℓβ π') : π = π' := by
  have := h.paxβ π
  rw [he, h.paxβ π'] at this
  exact (Option.some_injective _ this).symm

theorem Loc.eq_ci_of_isCI {l : Loc n} (h : l.isCI = true) : l = .ci := by
  cases l <;> simp_all

theorem Loc.eq_cg_of_isHub {l : Loc n} (h : l.isHub = true) (h' : l.isCI = false) : l = .cg := by
  cases l <;> simp_all

/-! ### Visits as nodes -/

/-- The visits of the planes, by plane and position. -/
abbrev Node (R : Fin p → List (Visit n t K)) := (k : Fin p) × Fin (R k).length

section Nodes

variable {R : Fin p → List (Visit n t K)}

/-- The visit at a node. -/
def Node.vis (x : Node R) : Visit n t K := (R x.1)[x.2]

/-- Whether the visit is entered from `C_I`. -/
def Node.eI (x : Node R) : Bool := x.vis.1.leg.src.isCI

/-- Whether the visit is left towards `C_I`. -/
def Node.xI (x : Node R) : Bool := x.vis.2.leg.dst.isCI

/-- The city of the visit (`x₀` stands for nothing: every visit is at a central city). -/
def Node.city (x₀ : Fin n) (x : Node R) : Fin n := x.vis.1.leg.dst.cityOr x₀

/-- When the visit's entry leg arrives. -/
def Node.a (x : Node R) : ℕ := x.vis.1.leg.arr

/-- When the visit's exit leg departs. -/
def Node.e (x : Node R) : ℕ := x.vis.2.leg.dep

variable (R) in
/-- The nodes of plane `k`, in route order. -/
def planeNodes (k : Fin p) : List (Node R) := (List.finRange (R k).length).map fun i => ⟨k, i⟩

theorem planeNodes_map_vis (k : Fin p) : (planeNodes R k).map Node.vis = R k := by
  simp only [planeNodes, List.map_map]
  exact List.map_getElem_finRange (R k)

@[simp] theorem length_planeNodes (k : Fin p) : (planeNodes R k).length = (R k).length := by
  simp [planeNodes]

theorem mem_planeNodes {k : Fin p} {x : Node R} : x ∈ planeNodes R k ↔ x.1 = k := by
  obtain ⟨u, i⟩ := x
  simp only [planeNodes, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact (congrArg Sigma.fst hj).symm
  · rintro rfl
    exact ⟨i, rfl⟩

theorem nodup_planeNodes (k : Fin p) : (planeNodes R k).Nodup :=
  (List.nodup_finRange _).map fun i j h => by simpa using h

theorem planeNodes_getElem (x : Node R) (h : x.2.val < (planeNodes R x.1).length) :
    (planeNodes R x.1)[x.2.val] = x := by
  simp [planeNodes]

theorem planeNodes_split (x : Node R) :
    planeNodes R x.1 = (planeNodes R x.1).take x.2 ++ x :: (planeNodes R x.1).drop (x.2 + 1) := by
  have h : x.2.val < (planeNodes R x.1).length := by simp
  conv_lhs => rw [list_eq_take_cons_drop _ _ h]
  rw [planeNodes_getElem x h]

theorem take_planeNodes_map_vis (k : Fin p) (m : ℕ) :
    ((planeNodes R k).take m).map Node.vis = (R k).take m := by
  rw [List.map_take, planeNodes_map_vis]

theorem drop_planeNodes_map_vis (k : Fin p) (m : ℕ) :
    ((planeNodes R k).drop m).map Node.vis = (R k).drop m := by
  rw [List.map_drop, planeNodes_map_vis]

/-- Counting nodes plane by plane. -/
theorem card_filter_node (P : Node R → Bool) :
    (univ.filter fun x => P x = true).card = ∑ k, ((planeNodes R k).filter P).length := by
  have h₁ : (univ.filter fun x : Node R => P x = true) =
      univ.sigma fun k => univ.filter fun i : Fin (R k).length => P ⟨k, i⟩ = true := by
    ext ⟨k, i⟩
    simp
  rw [h₁, Finset.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [planeNodes, List.filter_map, List.length_map]
  rw [Fin.univ_def]
  simp [Finset.card, Finset.filter_val, Function.comp_def]

end Nodes

/-! ### Small list facts -/

theorem take_drop_of_getElem_eq {α : Type*} {L A B : List α} {y : α} (hL : L = A ++ y :: B)
    (hnd : L.Nodup) {l : ℕ} (hl : l < L.length) (hy : L[l] = y) :
    L.take l = A ∧ L.drop (l + 1) = B := by
  subst hL
  have hA : A.length < (A ++ y :: B).length := by simp
  have : l = A.length := by
    have h₂ : (A ++ y :: B)[A.length] = y := by simp
    exact (hnd.getElem_inj_iff (hi := hl) (hj := hA)).mp (hy.trans h₂.symm)
  subst this
  simp

theorem sum_filter_eq_sum_ite {α : Type*} (q : α → Bool) (f : α → ℕ) : ∀ l : List α,
    ((l.filter q).map f).sum = (l.map fun x => if q x then f x else 0).sum
  | [] => rfl
  | x :: l => by
    have ih := sum_filter_eq_sum_ite q f l
    by_cases hx : q x = true <;> simp [hx, ih]

/-- Three pairwise exclusive selections weigh at most the whole. -/
theorem sum_filter_three_le {α : Type*} (q₁ q₂ q₃ : α → Bool) (f : α → ℕ) (l : List α)
    (h : ∀ x ∈ l, (q₁ x = true → q₂ x = false ∧ q₃ x = false) ∧ (q₂ x = true → q₃ x = false)) :
    ((l.filter q₁).map f).sum + ((l.filter q₂).map f).sum + ((l.filter q₃).map f).sum ≤
      (l.map f).sum := by
  rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, ← List.sum_map_add,
    ← List.sum_map_add]
  refine List.sum_le_sum fun x hx => ?_
  obtain ⟨h₁, h₂⟩ := h x hx
  by_cases hq₁ : q₁ x = true
  · simp [hq₁, (h₁ hq₁).1, (h₁ hq₁).2]
  · by_cases hq₂ : q₂ x = true
    · simp [hq₁, hq₂, h₂ hq₂]
    · by_cases hq₃ : q₃ x = true <;> simp [hq₁, hq₂, hq₃]

/-! ### The scheduled configuration of a set of links -/

section Build

variable {R : Fin p → List (Visit n t K)} (Λ : Finset (Node R × Node R))

/-- Whether a node is a linked drop-off. -/
def isDrop (x : Node R) : Bool := decide (∃ z ∈ Λ, z.1 = x)

/-- Whether a node is a linked pick-up. -/
def isPick (x : Node R) : Bool := decide (∃ z ∈ Λ, z.2 = x)

/-- The linked drop-offs of plane `u`, in route order. -/
def dropNodes (u : Fin p) : List (Node R) := (planeNodes R u).filter (isDrop Λ)

/-- The linked pick-ups of plane `v`, in route order. -/
def pickNodes (v : Fin p) : List (Node R) := (planeNodes R v).filter (isPick Λ)

/-- The position of a node among the linked drop-offs of its plane. -/
def dpos (x : Node R) : ℕ := (((planeNodes R x.1).take x.2).filter (isDrop Λ)).length

/-- The drop-off linked to a pick-up. -/
noncomputable def partner (y : Node R) : Node R :=
  if h : ∃ z ∈ Λ, z.2 = y then (Classical.choose h).1 else y

theorem partner_mem {y : Node R} (h : isPick Λ y = true) : (partner Λ y, y) ∈ Λ := by
  have h' : ∃ z ∈ Λ, z.2 = y := by simpa [isPick] using h
  unfold partner
  simp only [h', ↓reduceDIte]
  obtain ⟨hz, hzy⟩ := Classical.choose_spec h'
  exact (show ((Classical.choose h').1, y) = Classical.choose h' from Prod.ext rfl hzy.symm) ▸ hz

theorem isDrop_of_mem {x y : Node R} (h : (x, y) ∈ Λ) : isDrop Λ x = true := by
  simp only [isDrop, decide_eq_true_eq]
  exact ⟨_, h, rfl⟩

theorem isPick_of_mem_pickNodes {v : Fin p} {y : Node R} (h : y ∈ pickNodes Λ v) :
    isPick Λ y = true ∧ y.1 = v := by
  obtain ⟨h₁, h₂⟩ := List.mem_filter.mp h
  exact ⟨h₂, mem_planeNodes.mp h₁⟩

theorem dropNodes_split {x : Node R} (hx : isDrop Λ x = true) :
    dropNodes Λ x.1 = ((planeNodes R x.1).take x.2).filter (isDrop Λ) ++
      x :: ((planeNodes R x.1).drop (x.2 + 1)).filter (isDrop Λ) := by
  rw [dropNodes]
  conv_lhs => rw [planeNodes_split x]
  rw [List.filter_append, List.filter_cons_of_pos hx]

theorem pickNodes_split {y : Node R} (hy : isPick Λ y = true) :
    pickNodes Λ y.1 = ((planeNodes R y.1).take y.2).filter (isPick Λ) ++
      y :: ((planeNodes R y.1).drop (y.2 + 1)).filter (isPick Λ) := by
  rw [pickNodes]
  conv_lhs => rw [planeNodes_split y]
  rw [List.filter_append, List.filter_cons_of_pos hy]

theorem dropNodes_getElem?_dpos {x : Node R} (hx : isDrop Λ x = true) :
    (dropNodes Λ x.1)[dpos Λ x]? = some x := by
  rw [dropNodes_split Λ hx, dpos, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

theorem take_dropNodes_dpos {x : Node R} (hx : isDrop Λ x = true) :
    (dropNodes Λ x.1).take (dpos Λ x) = ((planeNodes R x.1).take x.2).filter (isDrop Λ) := by
  rw [dropNodes_split Λ hx, dpos, List.take_left' rfl]

theorem nodup_pickNodes (v : Fin p) : (pickNodes Λ v).Nodup :=
  (nodup_planeNodes v).filter _

theorem drop_pickNodes {v : Fin p} {l : ℕ} (hl : l < (pickNodes Λ v).length) :
    (pickNodes Λ v).drop (l + 1) = ((planeNodes R (pickNodes Λ v)[l].1).drop
      ((pickNodes Λ v)[l].2 + 1)).filter (isPick Λ) := by
  obtain ⟨hpick, hv⟩ := isPick_of_mem_pickNodes Λ (List.getElem_mem hl)
  exact (take_drop_of_getElem_eq ((congrArg (pickNodes Λ) hv.symm).trans
    (pickNodes_split Λ hpick)) (nodup_pickNodes Λ v) hl rfl).2

theorem card_filter_isDrop (h₁ : ∀ z ∈ Λ, ∀ z' ∈ Λ, z.1 = z'.1 → z = z') :
    ∑ k, (dropNodes Λ k).length = Λ.card := by
  rw [show (∑ k, (dropNodes Λ k).length) = ∑ k, ((planeNodes R k).filter (isDrop Λ)).length
    from rfl, ← card_filter_node]
  have : (univ.filter fun x => isDrop Λ x = true) = Λ.image Prod.fst := by
    ext x
    simp [isDrop]
  rw [this, Finset.card_image_of_injOn fun z hz z' hz' h => h₁ z hz z' hz' h]

theorem card_filter_isPick (h₂ : ∀ z ∈ Λ, ∀ z' ∈ Λ, z.2 = z'.2 → z = z') :
    ∑ k, (pickNodes Λ k).length = Λ.card := by
  rw [show (∑ k, (pickNodes Λ k).length) = ∑ k, ((planeNodes R k).filter (isPick Λ)).length
    from rfl, ← card_filter_node]
  have : (univ.filter fun x => isPick Λ x = true) = Λ.image Prod.snd := by
    ext x
    simp [isPick]
  rw [this, Finset.card_image_of_injOn fun z hz z' hz' h => h₂ z hz z' hz' h]

variable (x₀ : Fin n)

/-- **The scheduled configuration of the links `Λ`**, with crossings `Cr`: per plane, its linked
drop-offs and pick-ups in route order, and each pick-up matched to the drop-off it is linked
to. -/
noncomputable def toSched (Cr : Fin p → Multiset (Fin n)) : Sched n p where
  drops u := (dropNodes Λ u).map (Node.city x₀)
  picks v := (pickNodes Λ v).map (Node.city x₀)
  cross := Cr
  mate v l :=
    if h : l < (pickNodes Λ v).length then
      ((partner Λ (pickNodes Λ v)[l]).1, dpos Λ (partner Λ (pickNodes Λ v)[l]))
    else (v, 0)

/-- The links are valid: from a drop-off to a pick-up at the same city, at most one at each
node. -/
structure LinksOK : Prop where
  city : ∀ z ∈ Λ, z.1.city x₀ = z.2.city x₀
  inj₁ : ∀ z ∈ Λ, ∀ z' ∈ Λ, z.1 = z'.1 → z = z'
  inj₂ : ∀ z ∈ Λ, ∀ z' ∈ Λ, z.2 = z'.2 → z = z'

theorem toSched_mate {Cr : Fin p → Multiset (Fin n)} {v : Fin p} {l : ℕ}
    (hl : l < (pickNodes Λ v).length) :
    (toSched Λ x₀ Cr).mate v l =
      ((partner Λ (pickNodes Λ v)[l]).1, dpos Λ (partner Λ (pickNodes Λ v)[l])) := by
  simp only [toSched, hl, ↓reduceDIte]

theorem toSched_valid {Cr : Fin p → Multiset (Fin n)} (hΛ : LinksOK Λ x₀)
    (hodd : ∀ k, Odd (Cr k).card) : (toSched Λ x₀ Cr).Valid := by
  refine ⟨hodd, fun v l hl => ?_, fun v l v' l' hl hl' he => ?_, ?_⟩
  · simp only [toSched, List.length_map] at hl
    rw [toSched_mate Λ x₀ hl]
    set y := (pickNodes Λ v)[l] with hy
    have hpick := (isPick_of_mem_pickNodes Λ (List.getElem_mem hl)).1
    rw [← hy] at hpick
    have hmem := partner_mem Λ hpick
    simp only [toSched, List.getElem?_map,
      dropNodes_getElem?_dpos Λ (isDrop_of_mem Λ hmem), List.getElem?_eq_getElem hl, ← hy,
      Option.map_some, hΛ.city _ hmem]
  · simp only [toSched, List.length_map] at hl hl'
    rw [toSched_mate Λ x₀ hl, toSched_mate Λ x₀ hl', Prod.mk.injEq] at he
    set y := (pickNodes Λ v)[l] with hy
    set y' := (pickNodes Λ v')[l'] with hy'
    obtain ⟨hpick, hv⟩ := isPick_of_mem_pickNodes Λ (List.getElem_mem hl)
    obtain ⟨hpick', hv'⟩ := isPick_of_mem_pickNodes Λ (List.getElem_mem hl')
    rw [← hy] at hpick hv
    rw [← hy'] at hpick' hv'
    have hmem := partner_mem Λ hpick
    have hmem' := partner_mem Λ hpick'
    have h₁ := dropNodes_getElem?_dpos Λ (isDrop_of_mem Λ hmem)
    have h₂ := dropNodes_getElem?_dpos Λ (isDrop_of_mem Λ hmem')
    rw [he.1, he.2, h₂] at h₁
    have hpp : partner Λ y = partner Λ y' := (Option.some_injective _ h₁).symm
    have hyy : y = y' := congrArg Prod.snd (hΛ.inj₁ _ hmem _ hmem' hpp)
    have hvv : v = v' := hv.symm.trans ((congrArg Sigma.fst hyy).trans hv')
    subst hvv
    refine ⟨rfl, ?_⟩
    exact ((nodup_pickNodes Λ v).getElem_inj_iff (hi := hl) (hj := hl')).mp (hy.symm.trans
      (hyy.trans hy'))
  · simp only [toSched, List.length_map]
    rw [card_filter_isDrop Λ hΛ.inj₁, card_filter_isPick Λ hΛ.inj₂]

theorem toSched_size {Cr : Fin p → Multiset (Fin n)} (hΛ : LinksOK Λ x₀) :
    (toSched Λ x₀ Cr).size = 2 * Λ.card + ∑ k, (Cr k).card := by
  simp only [Sched.size, toSched, List.length_map, Finset.sum_add_distrib]
  rw [card_filter_isDrop Λ hΛ.inj₁, card_filter_isPick Λ hΛ.inj₂]
  ring

end Build

/-! ### Cost and closed form (Step 5) -/

section Bounds

variable {N : Network n} {R : Fin p → List (Visit n t K)}
  (hloc : ∀ k, ∀ v ∈ R k, LocOK N v) (x₀ : Fin n)

include hloc

theorem Node.loc (x : Node R) : LocOK N x.vis := hloc x.1 _ (List.getElem_mem _)

theorem Node.dst_eq (x : Node R) : x.vis.1.leg.dst = .city (x.city x₀) := by
  have hs := x.loc hloc
  obtain ⟨y, hy, -⟩ := hs.city
  simp [Node.city, hy]

theorem Node.entry_arr (x : Node R) : x.vis.1.leg.arr =
    x.vis.1.leg.dep + (if x.eI then N.d (x.city x₀) else N.dbar (x.city x₀)) := by
  have hs := x.loc hloc
  have hx := x.dst_eq hloc x₀
  obtain ⟨τ, hd, ha⟩ := hs.flies₁
  have hub := hs.hub
  unfold Node.eI
  rw [hx] at hd
  rcases h : x.vis.1.leg.src with _ | z | _ <;> simp_all [Network.duration]

theorem Node.exit_arr (x : Node R) : x.vis.2.leg.arr =
    x.vis.2.leg.dep + (if x.xI then N.d (x.city x₀) else N.dbar (x.city x₀)) := by
  have hs := x.loc hloc
  have hx := x.dst_eq hloc x₀
  obtain ⟨y, hy₁, hy₂⟩ := hs.city
  rw [hx] at hy₁
  cases Loc.city.inj hy₁
  obtain ⟨τ, hd, ha⟩ := hs.flies₂
  have hub := hs.exit
  unfold Node.xI
  rw [hy₂] at hd
  rcases h : x.vis.2.leg.dst with _ | z | _ <;> simp_all [Network.duration]

theorem Node.w_eq (x : Node R) : x.vis.w =
    (if x.eI then N.d (x.city x₀) else N.dbar (x.city x₀)) +
      (if x.xI then N.d (x.city x₀) else N.dbar (x.city x₀)) := by
  have h₁ := x.entry_arr hloc x₀
  have h₂ := x.exit_arr hloc x₀
  unfold Visit.w
  omega

omit hloc in
/-- The `A` and `Ā` visits of plane `k`. -/
def crossNodes (R : Fin p → List (Visit n t K)) (k : Fin p) : List (Node R) :=
  (planeNodes R k).filter fun x => x.eI != x.xI

omit hloc in
/-- The cities of the `A` and `Ā` visits of plane `k`: the crossings to choose from. -/
def crossCities (R : Fin p → List (Visit n t K)) (k : Fin p) : Multiset (Fin n) :=
  ((crossNodes R k).map (Node.city x₀) : List (Fin n))

variable {Λ : Finset (Node R × Node R)}
  (hty : ∀ z ∈ Λ, z.1.eI = true ∧ z.1.xI = true ∧ z.2.eI = false ∧ z.2.xI = false)

include hty

omit hloc in
theorem isDrop_types {x : Node R} (h : isDrop Λ x = true) : x.eI = true ∧ x.xI = true := by
  simp only [isDrop, decide_eq_true_eq] at h
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨(hty z hz).1, (hty z hz).2.1⟩

omit hloc in
theorem isPick_types {x : Node R} (h : isPick Λ x = true) : x.eI = false ∧ x.xI = false := by
  simp only [isPick, decide_eq_true_eq] at h
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨(hty z hz).2.2.1, (hty z hz).2.2.2⟩

omit hloc in
theorem exclusive (x : Node R) :
    (isDrop Λ x = true → isPick Λ x = false ∧ (x.eI != x.xI) = false) ∧
      (isPick Λ x = true → (x.eI != x.xI) = false) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · obtain ⟨h₁, -⟩ := isDrop_types hty h
    by_contra h'
    rw [Bool.not_eq_false] at h'
    rw [(isPick_types hty h').1] at h₁
    exact absurd h₁ (by decide)
  · obtain ⟨h₁, h₂⟩ := isDrop_types hty h
    simp [h₁, h₂]
  · obtain ⟨h₁, h₂⟩ := isPick_types hty h
    simp [h₁, h₂]

omit hty in
theorem sum_legs_landCost (c : Fin n → ℕ) : ∀ L : List (Node R),
    ((legsOf (L.map Node.vis)).map fun ℓ => landCost c ℓ.leg).sum =
      (L.map fun x => c (x.city x₀)).sum
  | [] => rfl
  | x :: L => by
    have hs := x.loc hloc
    have ih := sum_legs_landCost c L
    simp only [List.map_cons, legsOf_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have h₁ : landCost c x.vis.1.leg = c (x.city x₀) := by
      simp [landCost, x.dst_eq hloc x₀]
    have h₂ : landCost c x.vis.2.leg = 0 := by
      have := hs.exit
      unfold landCost
      rcases h : x.vis.2.leg.dst with _ | z | _ <;> simp_all
    rw [h₁, h₂]
    ring

omit hty in
theorem allK_landCost (c : Fin n → ℕ) :
    ((allK R).map fun ℓ => landCost c ℓ.leg).sum =
      ∑ k, ((planeNodes R k).map fun x => c (x.city x₀)).sum := by
  rw [← Finset.sum_congr rfl fun k _ => sum_legs_landCost hloc x₀ c (planeNodes R k)]
  simp only [planeNodes_map_vis]
  exact map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom
    fun ℓ : KLeg n t K => landCost c ℓ.leg)) (fun k => (legsOf (R k) : Multiset _)) univ

/-- **The cost** of the configuration is at most the landing cost of the legs. -/
theorem toSched_cost_le {Cr : Fin p → Multiset (Fin n)} (hCr : ∀ k, Cr k ≤ crossCities x₀ R k)
    (c : Fin n → ℕ) :
    (toSched Λ x₀ Cr).cost c ≤ ((allK R).map fun ℓ => landCost c ℓ.leg).sum := by
  rw [allK_landCost hloc x₀ c]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [toSched, List.map_map]
  have h₁ : ZenoFront.cost c (Cr k) ≤
      ((crossNodes R k).map fun x => c (x.city x₀)).sum := by
    refine (cost_mono c (hCr k)).trans (le_of_eq ?_)
    simp [crossCities, cost, Function.comp_def]
  have h₂ := sum_filter_three_le (isDrop Λ) (isPick Λ) (fun x : Node R => x.eI != x.xI)
    (fun x => c (x.city x₀)) (planeNodes R k) fun x _ => exclusive hty x
  simp only [Function.comp_def, dropNodes, pickNodes]
  simp only [crossNodes] at h₁
  omega

/-- **Step 5: the closed form** of the configuration (Lemma 6.3) is at most any bound `M` on the
arrival times: role loads are at most the flight times, and each link's term is at most
`a(B) + (M − e(B̄)) ≤ M`. -/
theorem toSched_tmpl_le {Cr : Fin p → Multiset (Fin n)} (hCr : ∀ k, Cr k ≤ crossCities x₀ R k)
    (hΛ : LinksOK Λ x₀) (htime : ∀ z ∈ Λ, z.1.a ≤ z.2.e) {M : ℕ} (hP : PlanesOK N M R) :
    (toSched Λ x₀ Cr).tmpl N.d N.dbar ≤ M := by
  have hw := fun x : Node R => x.w_eq hloc x₀
  -- A selection along a route weighs at most the visits it is taken from.
  have hsel : ∀ (q : Node R → Bool) (f : Node R → ℕ) (L : List (Node R)),
      (∀ x ∈ L, q x = true → f x ≤ x.vis.w) →
      ((L.filter q).map f).sum ≤ (L.map fun x => x.vis.w).sum := by
    intro q f L h
    refine (List.sum_le_sum fun x hx => h x (List.mem_of_mem_filter hx)
      (List.mem_filter.mp hx).2).trans ?_
    exact (List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _
  unfold Sched.tmpl
  refine max_le (Finset.sup_le fun k _ => ?_)
    (Finset.sup_le fun v _ => Finset.sup_le fun l _ => ?_)
  · -- The role load of plane `k`.
    have htot : ((planeNodes R k).map fun x => x.vis.w).sum ≤ M := by
      have := hP.load k
      rwa [← planeNodes_map_vis (R := R) k, List.map_map] at this
    have h₃ := sum_filter_three_le (isDrop Λ) (isPick Λ) (fun x : Node R => x.eI != x.xI)
      (fun x => x.vis.w) (planeNodes R k) fun x _ => exclusive hty x
    have hd : (((planeNodes R k).filter (isDrop Λ)).map fun x => 2 * N.d (x.city x₀)).sum ≤
        (((planeNodes R k).filter (isDrop Λ)).map fun x => x.vis.w).sum := by
      refine List.sum_le_sum fun x hx => ?_
      obtain ⟨h₁, h₂⟩ := isDrop_types hty (List.mem_filter.mp hx).2
      rw [hw x, h₁, h₂]
      simp only [ite_true]
      omega
    have hp : (((planeNodes R k).filter (isPick Λ)).map fun x => 2 * N.dbar (x.city x₀)).sum ≤
        (((planeNodes R k).filter (isPick Λ)).map fun x => x.vis.w).sum := by
      refine List.sum_le_sum fun x hx => ?_
      obtain ⟨h₁, h₂⟩ := isPick_types hty (List.mem_filter.mp hx).2
      rw [hw x, h₁, h₂]
      simp only [Bool.false_eq_true, ite_false]
      omega
    have hc : load N.d (Cr k) + load N.dbar (Cr k) ≤
        (((planeNodes R k).filter fun x => x.eI != x.xI).map fun x => x.vis.w).sum := by
      refine (add_le_add (load_mono N.d (hCr k)) (load_mono N.dbar (hCr k))).trans ?_
      simp only [crossCities, crossNodes, load, Multiset.map_coe, Multiset.sum_coe, List.map_map,
        ← List.sum_map_add]
      refine List.sum_le_sum fun x hx => ?_
      have hne := (List.mem_filter.mp hx).2
      rw [Function.comp_apply, Function.comp_apply, hw x]
      rcases h₁ : x.eI <;> rcases h₂ : x.xI <;> simp_all; omega
    simp only [Sched.load, toSched, List.map_map, dropNodes, pickNodes, Function.comp_def,
      ← List.sum_map_mul_left]
    omega
  · -- The term of the link into pick-up slot `(v, l)`.
    have hl : l.val < (pickNodes Λ v).length := by simpa [toSched] using l.isLt
    unfold Sched.term
    rw [toSched_mate Λ x₀ hl]
    dsimp only
    set y := (pickNodes Λ v)[l.val] with hy
    have hpick : isPick Λ y = true := (isPick_of_mem_pickNodes Λ (List.getElem_mem hl)).1
    have hmem := partner_mem Λ hpick
    set x := partner Λ y with hx
    have hdrop := isDrop_of_mem Λ hmem
    obtain ⟨hxe, -⟩ := isDrop_types hty hdrop
    obtain ⟨-, hyx⟩ := isPick_types hty hpick
    have hpl : ((toSched Λ x₀ Cr).picks v)[l] = y.city x₀ :=
      List.getElem_map (Node.city x₀) (l := pickNodes Λ v) (h := by simpa [toSched] using l.isLt)
    rw [hpl]
    -- `Pre_u(j) + d_x ≤ a(B)`.
    have hpre : (toSched Λ x₀ Cr).pre N.d x.1 (dpos Λ x) + N.d (y.city x₀) ≤ x.a := by
      have h₁ : (toSched Λ x₀ Cr).pre N.d x.1 (dpos Λ x) ≤ x.vis.1.leg.dep := by
        obtain ⟨hxe', hxx'⟩ := isDrop_types hty hdrop
        have h₂ := hP.pre x.1 x.2 x.2.isLt (Loc.eq_ci_of_isCI hxe') (Loc.eq_ci_of_isCI hxx')
        refine le_trans ?_ h₂
        simp only [Sched.pre, toSched, ← List.map_take, take_dropNodes_dpos Λ hdrop,
          List.map_map, ← List.sum_map_mul_left]
        rw [← take_planeNodes_map_vis, List.map_map]
        refine hsel _ _ _ fun z _ hz => ?_
        obtain ⟨h₁, h₂⟩ := isDrop_types hty hz
        rw [Function.comp_apply, hw z, h₁, h₂]
        simp only [ite_true]
        omega
      have h₃ := x.entry_arr hloc x₀
      have hc : x.city x₀ = y.city x₀ := hΛ.city _ hmem
      simp only [hxe, ↓reduceIte, hc] at h₃
      unfold Node.a
      omega
    -- `e(B̄) + d̄_x + Suf_v(l) ≤ M`.
    have hsuf : y.e + N.dbar (y.city x₀) + (toSched Λ x₀ Cr).suf N.dbar v l ≤ M := by
      have h₁ : (toSched Λ x₀ Cr).suf N.dbar v l ≤ (((R y.1).drop (y.2 + 1)).map Visit.w).sum := by
        simp only [Sched.suf, toSched, ← List.map_drop, drop_pickNodes Λ hl, ← hy,
          List.map_map, ← List.sum_map_mul_left]
        rw [← drop_planeNodes_map_vis, List.map_map]
        refine hsel _ _ _ fun z _ hz => ?_
        obtain ⟨h₁, h₂⟩ := isPick_types hty hz
        rw [Function.comp_apply, hw z, h₁, h₂]
        simp only [Bool.false_eq_true, ite_false]
        omega
      have hs := y.loc hloc
      obtain ⟨hye', hyx'⟩ := isPick_types hty hpick
      have h₂ := hP.suf y.1 y.2 y.2.isLt (Loc.eq_cg_of_isHub hs.hub hye')
        (Loc.eq_cg_of_isHub hs.exit hyx')
      have h₃ := y.exit_arr hloc x₀
      simp only [hyx, Bool.false_eq_true, ↓reduceIte] at h₃
      unfold Node.e
      change y.vis.2.leg.arr + _ ≤ M at h₂
      omega
    have hlink : x.a ≤ y.e := htime _ hmem
    omega

end Bounds

/-! ### Steps 3–6 -/

section Steps

variable {N : Network n} {R : Fin p → List (Visit n t K)}

theorem card_crossNodes (hpar : ∀ k, (R k).countP Visit.isA = (R k).countP Visit.isAbar + 1)
    (k : Fin p) : (crossNodes R k).length = 2 * (R k).countP Visit.isAbar + 1 := by
  have h₁ := hpar k
  have h₂ : (crossNodes R k).length = (R k).countP Visit.isA + (R k).countP Visit.isAbar := by
    rw [crossNodes, ← List.countP_eq_length_filter, ← planeNodes_map_vis (R := R) k,
      List.countP_map, List.countP_map]
    induction planeNodes R k with
    | nil => rfl
    | cons x L ih =>
      simp only [List.countP_cons, ih]
      have key : (if (x.eI != x.xI) = true then 1 else 0) =
          (if (Visit.isA ∘ Node.vis) x = true then 1 else 0) +
            (if (Visit.isAbar ∘ Node.vis) x = true then 1 else 0) := by
        simp only [Function.comp_apply, Node.eI, Node.xI, Visit.isA, Visit.isAbar]
        rcases Bool.eq_false_or_eq_true x.vis.1.leg.src.isCI with h | h <;>
          rcases Bool.eq_false_or_eq_true x.vis.2.leg.dst.isCI with h' | h' <;> simp [h, h']
      omega
  omega

/-- **Steps 3–6 of Theorem 6.9**, on any visits of the planes with what the steps need
(`PlanesOK`). Take visits in which every passenger's hand-off is ordered in time (as Step 2 leaves
them), and `p ≤ t`. Then some valid scheduled configuration has `2t − p` landings, cost at most
the landing cost of the legs, and closed form at most `M`. -/
theorem exists_sched_of {M : ℕ} (hP : PlanesOK N M R) {ℓα ℓβ : Fin t → KLeg n t K}
    (hpax : PaxEnds ℓα ℓβ)
    (hord : ∀ π, ∃ (u : Fin p) (i : Fin (R u).length) (v : Fin p) (j : Fin (R v).length),
      (R u)[i].1 = ℓα π ∧ (R v)[j].2 = ℓβ π ∧
      ((⟨u, i⟩ : (k : Fin p) × Fin (R k).length) ≠ ⟨v, j⟩ →
        (R u)[i].2.leg.dep ≤ (R v)[j].1.leg.arr))
    (hpt : p ≤ t) (x₀ : Fin n) (c : Fin n → ℕ) :
    ∃ S : Sched n p, S.Valid ∧ S.size = 2 * t - p ∧
      S.cost c ≤ ((allK R).map fun ℓ => landCost c ℓ.leg).sum ∧ S.tmpl N.d N.dbar ≤ M := by
  classical
  have hR := hP.loc
  choose u i v j hi hj hle using hord
  set src : Fin t → Node R := fun π => ⟨u π, i π⟩ with hsrc
  set dst : Fin t → Node R := fun π => ⟨v π, j π⟩ with hdst
  have hsrcα : ∀ π, (src π).vis.1 = ℓα π := hi
  have hdstβ : ∀ π, (dst π).vis.2 = ℓβ π := hj
  have hinjs : Function.Injective src := fun π π' h =>
    hpax.injα ((hsrcα π).symm.trans ((congrArg (fun x : Node R => x.vis.1) h).trans (hsrcα π')))
  have hinjd : Function.Injective dst := fun π π' h =>
    hpax.injβ ((hdstβ π).symm.trans ((congrArg (fun x : Node R => x.vis.2) h).trans (hdstβ π')))
  -- The arrows: one per passenger.
  set E : Finset (Node R × Node R) := univ.image fun π => (src π, dst π) with hE
  have hEcard : E.card = t := by
    rw [hE, Finset.card_image_of_injective _ fun π π' h => hinjs (congrArg Prod.fst h)]
    simp
  have hmemE : ∀ z ∈ E, ∃ π, z = (src π, dst π) := fun z hz => by
    obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨π, rfl⟩
  obtain ⟨Λ₀, hΛ₀, hΛ₀₁, hΛ₀₂, hcount⟩ := exists_links Node.eI Node.xI (Node.city x₀) Node.a
    Node.e (fun x => (x.loc hR).wait) univ E
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    (fun z hz z' hz' h => by
      obtain ⟨π, rfl⟩ := hmemE z hz
      obtain ⟨π', rfl⟩ := hmemE z' hz'
      rw [hinjs h])
    (fun z hz z' hz' h => by
      obtain ⟨π, rfl⟩ := hmemE z hz
      obtain ⟨π', rfl⟩ := hmemE z' hz'
      rw [hinjd h])
    (fun z hz => by
      obtain ⟨π, rfl⟩ := hmemE z hz
      obtain ⟨x, hx₁, hx₂⟩ := hpax.city π
      refine ⟨?_, ?_, ?_, hle π⟩
      · simp [Node.eI, hsrcα π, hpax.srcα π]
      · simp [Node.xI, hdstβ π, hpax.dstβ π]
      · have h₁ := (src π).dst_eq hR x₀
        rw [hsrcα π, hx₁] at h₁
        obtain ⟨y, hy₁, hy₂⟩ := ((dst π).loc hR).city
        rw [hdstβ π, hx₂] at hy₂
        have h₂ := (dst π).dst_eq hR x₀
        rw [hy₁, ← hy₂] at h₂
        exact (Loc.city.inj h₁).symm.trans (Loc.city.inj h₂))
  -- The `A` visits: `#A = #Ā + 1` per plane.
  set a : Fin p → ℕ := fun k => (R k).countP Visit.isAbar with ha
  have hA : (univ.filter fun w : Node R => w.eI = true ∧ w.xI = false).card = ∑ k, a k + p := by
    have : (univ.filter fun w : Node R => w.eI = true ∧ w.xI = false) =
        univ.filter fun w : Node R => (w.vis.isA) = true :=
      Finset.filter_congr fun w _ => by simp [Node.eI, Node.xI, Visit.isA]
    rw [this, card_filter_node]
    have h : ∀ k, ((planeNodes R k).filter fun w => w.vis.isA).length = a k + 1 := fun k => by
      rw [← List.countP_eq_length_filter, ← hP.par k, ← planeNodes_map_vis (R := R) k,
        List.countP_map]
      rfl
    simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  rw [hEcard, hA] at hcount
  have hcross : ∀ k, (crossCities x₀ R k).card = 2 * a k + 1 := fun k => by
    simp [crossCities, card_crossNodes hP.par k, ha]
  have hLinks : ∀ Λ ⊆ Λ₀, LinksOK Λ x₀ ∧
      (∀ z ∈ Λ, z.1.eI = true ∧ z.1.xI = true ∧ z.2.eI = false ∧ z.2.xI = false) ∧
      ∀ z ∈ Λ, z.1.a ≤ z.2.e := fun Λ hΛ =>
    ⟨⟨fun z hz => (hΛ₀ z (hΛ hz)).2.2.2.2.1,
      fun z hz z' hz' => hΛ₀₁ z (hΛ hz) z' (hΛ hz'),
      fun z hz z' hz' => hΛ₀₂ z (hΛ hz) z' (hΛ hz')⟩,
      fun z hz => ⟨(hΛ₀ z (hΛ hz)).1, (hΛ₀ z (hΛ hz)).2.1, (hΛ₀ z (hΛ hz)).2.2.1,
        (hΛ₀ z (hΛ hz)).2.2.2.1⟩,
      fun z hz => (hΛ₀ z (hΛ hz)).2.2.2.2.2⟩
  -- Step 6: shrink to `2t − p` landings.
  have hshrink : ∃ Λ ⊆ Λ₀, ∃ Cr : Fin p → Multiset (Fin n), (∀ k, Cr k ≤ crossCities x₀ R k) ∧
      (∀ k, Odd (Cr k).card) ∧ 2 * Λ.card + ∑ k, (Cr k).card = 2 * t - p := by
    have hsum : ∑ k, (crossCities x₀ R k).card = 2 * ∑ k, a k + p := by
      simp only [hcross, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one, ← Finset.mul_sum]
    by_cases hD : Λ₀.card + (∑ k, a k + p) - t ≤ Λ₀.card
    · obtain ⟨Λ, hΛ, hcard⟩ := Finset.exists_subset_card_eq
        (show Λ₀.card - (Λ₀.card + (∑ k, a k + p) - t) ≤ Λ₀.card by omega)
      refine ⟨Λ, hΛ, crossCities x₀ R, fun k => le_rfl, fun k => ?_, ?_⟩
      · rw [hcross k]
        exact odd_two_mul_add_one _
      · rw [hcard, hsum]
        omega
    · obtain ⟨b, hb, hbsum⟩ := exists_le_sum_eq a (∑ k, a k + p - t) (by omega)
      refine ⟨∅, Finset.empty_subset _,
        fun k => (((crossNodes R k).map (Node.city x₀)).take (2 * (a k - b k) + 1) :
          Multiset (Fin n)), fun k => ?_, fun k => ?_, ?_⟩
      · exact Multiset.coe_le.mpr (List.take_sublist _ _).subperm
      · have := hcross k
        simp only [crossCities, Multiset.coe_card] at this
        simp only [Multiset.coe_card, List.length_take, this]
        rw [min_eq_left (by have := hb k; omega)]
        exact odd_two_mul_add_one _
      · have hk : ∀ k, (((crossNodes R k).map (Node.city x₀)).take (2 * (a k - b k) + 1) :
            Multiset (Fin n)).card = 2 * (a k - b k) + 1 := fun k => by
          have := hcross k
          simp only [crossCities, Multiset.coe_card] at this
          simp only [Multiset.coe_card, List.length_take, this]
          exact min_eq_left (by have := hb k; omega)
        simp only [hk, Finset.card_empty, mul_zero, zero_add, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        have hsub : ∑ k, (a k - b k) + ∑ k, b k = ∑ k, a k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hb k)
        rw [← Finset.mul_sum]
        omega
  obtain ⟨Λ, hΛ, Cr, hCr, hodd, hsize⟩ := hshrink
  obtain ⟨hok, hty, htime⟩ := hLinks Λ hΛ
  exact ⟨toSched Λ x₀ Cr, toSched_valid Λ x₀ hok hodd, (toSched_size Λ x₀ hok).trans hsize,
    toSched_cost_le hR x₀ hty hCr c, toSched_tmpl_le hR x₀ hty hCr hok htime hP⟩

end Steps

end ZenoFront
