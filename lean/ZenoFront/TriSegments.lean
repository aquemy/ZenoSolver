/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Converse

/-!
# The triangle inequality (AΔ) and the segment bound

**(AΔ)** (§1.4 of `doc/theory/exact-front.md`): `dur(a, b) ≤ dur(a, x) + dur(x, b)` whenever the
three flights exist (`Network.ATri`). In the note a flight joins two distinct locations. The Lean
network also has a central flight `i → i` (`dc i i`), which the note does not; the hypothesis
`a ≠ b` leaves these unconstrained, so `Network.ATri` is exactly the note's (AΔ) on the flights
the note has. Central durations may also differ by direction (`dc i j ≠ dc j i`); (AΔ) is then
read on the directed durations.

The proof of Theorem 4.10, and so every symmetric result built on it (the fronts, the solver
and the checkers), uses (AΔ) only on the triangles through a hub: under (S),
`d_j ≤ d_i + dc i j` (through `C_I → i → j`) and `d_i ≤ dc i j + d_j` (through `i → j → C_I`).
This is `Network.ATriHub`. It follows from (AΔ) (`Network.ATri.hub`) and from (A1)
(`Network.A1.hub`), so each of those results is stated once, under `ATriHub`.

**Lemma 3.3(b) under (S), the segment bound.** Under (S) and `ATriHub`, a segment `γ` of a route
(the legs between two hub arrivals) flies at least `2 d_x` for every central city `x` it lands
in: `F(γ) ≥ 2 d_x`. Along the segment, the part from its first hub to the current city `w` lasts
at least `d_w`, and the part so far plus `d_w` is at least `2 d_x` for every city `x` visited so
far; leaving `w` for the last hub adds `d_w`.

## Main results

* `ZenoFront.Network.ATri`: (AΔ). `ZenoFront.Network.ATriHub`: its triangles through a hub.
* `ZenoFront.segment_bound`: **the segment bound**, `2 d_x ≤ F(γ)` for every landing `x` of a
  segment `γ`.
* `ZenoFront.PlaneFeasible.exists_segments_tri`: a feasible plane's route is the concatenation
  of its segments, one per hub arrival, each landing at least once and satisfying the segment
  bound.
* `ZenoFront.Admissible.exists_remove_two`: **Lemma 4.11**, removing two landings from an
  admissible partition with `|X| ≥ p + 2`.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n t p : ℕ}

/-! ### (AΔ) -/

/-- **Assumption (AΔ)**, the triangle inequality for the flights that exist:
`dur(a, b) ≤ dur(a, x) + dur(x, b)` whenever the flights `a–b`, `a–x` and `x–b` exist and
`a ≠ b`. The note's flights join distinct locations; the condition `a ≠ b` leaves the Lean
network's self-loops `dc i i` free (and `a = x` or `x = b` is trivial). -/
def Network.ATri (N : Network n) : Prop :=
  ∀ a x b : Loc n, a ≠ b → ∀ τab τax τxb : ℕ, N.duration a b = some τab →
    N.duration a x = some τax → N.duration x b = some τxb → τab ≤ τax + τxb

/-- (AΔ) on the triangles through `C_I`: `d_j ≤ d_i + dc i j` (`C_I → i → j` against `C_I → j`)
and `d_i ≤ dc i j + d_j` (`i → j → C_I` against `i → C_I`). Under (S) these are also the
triangles through `C_G`. This is all that Theorem 4.10 and its corollaries use. -/
def Network.ATriHub (N : Network n) : Prop :=
  ∀ i j : Fin n, N.d j ≤ N.d i + N.dc i j ∧ N.d i ≤ N.dc i j + N.d j

/-- (AΔ) implies its triangles through a hub. -/
theorem Network.ATri.hub {N : Network n} (h : N.ATri) : N.ATriHub := fun i j =>
  ⟨h .ci (.city i) (.city j) (by simp) _ _ _ rfl rfl rfl,
    h (.city i) (.city j) .ci (by simp) _ _ _ rfl rfl rfl⟩

/-- (A1) implies the triangles through a hub. -/
theorem Network.A1.hub {N : Network n} (h : N.A1) : N.ATriHub := fun i j => by
  have := h i j
  constructor <;> omega

/-! ### Landings as a list -/

/-- The central landings of a list of legs, in flight order. -/
def landList (legs : List (Leg n t)) : List (Fin n) :=
  legs.filterMap fun ℓ =>
    match ℓ.dst with
    | .city i => some i
    | _ => none

@[simp] theorem landList_nil : landList ([] : List (Leg n t)) = [] := rfl

theorem landList_append (L M : List (Leg n t)) :
    landList (L ++ M) = landList L ++ landList M := List.filterMap_append

theorem landList_cons_city (ℓ : Leg n t) (rest : List (Leg n t)) {i : Fin n}
    (h : ℓ.dst = .city i) : landList (ℓ :: rest) = i :: landList rest := by
  simp [landList, h]

theorem landList_cons_hub (ℓ : Leg n t) (rest : List (Leg n t)) (h : ℓ.dst.isHub = true) :
    landList (ℓ :: rest) = landList rest := by
  obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
  cases dst <;> simp_all [landList]

theorem coe_landList : ∀ legs : List (Leg n t),
    (landList legs : Multiset (Fin n)) = routeLandings legs
  | [] => rfl
  | ⟨src, dst, dep, arr, pax⟩ :: rest => by
    have ih := coe_landList rest
    cases dst with
    | city i =>
      rw [landList_cons_city _ rest rfl, ← Multiset.cons_coe, ih]
      rfl
    | ci => rw [landList_cons_hub _ rest rfl, ih]; rfl
    | cg => rw [landList_cons_hub _ rest rfl, ih]; rfl

theorem durSum_append (L M : List (Leg n t)) : durSum (L ++ M) = durSum L + durSum M := by
  simp [durSum]

@[simp] theorem durSum_nil : durSum ([] : List (Leg n t)) = 0 := rfl

theorem durSum_cons (ℓ : Leg n t) (rest : List (Leg n t)) :
    durSum (ℓ :: rest) = (ℓ.arr - ℓ.dep) + durSum rest := by
  simp [durSum]

theorem hubArrivals_append (L M : List (Leg n t)) :
    hubArrivals (L ++ M) = hubArrivals L + hubArrivals M := by
  simp [hubArrivals, List.countP_append]

/-! ### The segment bound -/

/-- **Segments.** A route from `x` that ends at a hub is the concatenation of its segments, one
per hub arrival, each ending with its only hub arrival, landing at least once, and flying at
least `2 d_y` for each of its landings `y`. Second part: in the middle of a segment, at city `w`,
with the legs `pre` of the segment so far (from its first hub to `w`), which fly at least `d_w`
and at least `2 d_y − d_w` for every landing `y` so far. -/
theorem exists_segs_aux {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub) :
    ∀ (legs : List (Leg n t)) (x : Loc n) (τ : ℕ), IsRoute x τ legs → (∀ ℓ ∈ legs, Flies N ℓ) →
      (finalLoc x legs).isHub = true →
      (x.isHub = true → ∃ segs : List (List (Leg n t)), segs.flatten = legs ∧
          segs.length = hubArrivals legs ∧ ∀ γ ∈ segs, hubArrivals γ = 1 ∧
            (∃ ℓ, γ.getLast? = some ℓ ∧ ℓ.dst.isHub = true) ∧ landList γ ≠ [] ∧
            ∀ y ∈ landList γ, 2 * N.d y ≤ durSum γ) ∧
      (∀ (w : Fin n) (pre : List (Leg n t)), x = .city w → hubArrivals pre = 0 →
          landList pre ≠ [] → N.d w ≤ durSum pre →
          (∀ y ∈ landList pre, 2 * N.d y ≤ durSum pre + N.d w) →
          ∃ segs : List (List (Leg n t)), segs.flatten = pre ++ legs ∧
            segs.length = hubArrivals legs ∧ ∀ γ ∈ segs, hubArrivals γ = 1 ∧
              (∃ ℓ, γ.getLast? = some ℓ ∧ ℓ.dst.isHub = true) ∧ landList γ ≠ [] ∧
              ∀ y ∈ landList γ, 2 * N.d y ≤ durSum γ)
  | [], x, _, _, _, hend => by
    refine ⟨fun _ => ⟨[], rfl, rfl, by simp⟩, fun w pre hx => ?_⟩
    subst hx
    simp at hend
  | ℓ :: rest, x, τ, hroute, hflies, hend => by
    obtain ⟨hsrc, -, hrest⟩ := hroute
    have hfl : Flies N ℓ := hflies _ List.mem_cons_self
    have ih := exists_segs_aux hS hL rest ℓ.dst ℓ.arr hrest
      (fun m hm => hflies m (List.mem_cons_of_mem _ hm)) hend
    obtain ⟨τ', hdur, harr⟩ := hfl
    have hd : ℓ.arr - ℓ.dep = τ' := by omega
    refine ⟨fun hx => ?_, fun w pre hx hpre0 hpre hw hpreb => ?_⟩
    · -- From a hub: the first leg goes to a city `w'` and opens a segment.
      obtain ⟨w', hw'⟩ : ∃ w', ℓ.dst = .city w' := by
        obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
        simp only at hsrc hdur ⊢
        subst hsrc
        cases src <;> cases dst <;> simp_all [Network.duration]
      have hτ' : τ' = N.d w' := by
        obtain ⟨src, dst, dep, arr, pax⟩ := ℓ
        simp only at hsrc hdur hw' ⊢
        subst hsrc hw'
        cases src <;> simp_all [Network.duration]
      obtain ⟨segs, hflat, hlen, hsegs⟩ := ih.2 w' [ℓ] hw'
        (by simp [hubArrivals, hw'])
        (by simp [landList_cons_city ℓ [] hw'])
        (by simp [durSum_cons, hd, hτ'])
        (by
          intro y hy
          rw [landList_cons_city ℓ [] hw'] at hy
          simp only [landList_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy
          rw [durSum_cons, durSum_nil, hd, hτ']
          omega)
      refine ⟨segs, by simpa using hflat, ?_, hsegs⟩
      rw [hlen]
      simp [hubArrivals, hw']
    · -- Mid-segment at `w`.
      subst hx
      cases hdst : ℓ.dst with
      | city w' =>
        have hτ' : τ' = N.dc w w' := by
          rw [hsrc, hdst] at hdur
          simpa [Network.duration] using hdur.symm
        obtain ⟨h₁, h₂⟩ := hL w w'
        obtain ⟨segs, hflat, hlen, hsegs⟩ := (ih.2 w' (pre ++ [ℓ]) hdst
          (by rw [hubArrivals_append, hpre0]; simp [hubArrivals, hdst])
          (by rw [landList_append]; simp [hpre])
          (by rw [durSum_append, durSum_cons, durSum_nil, hd, hτ']; omega)
          (by
            intro y hy
            rw [landList_append, landList_cons_city ℓ [] hdst] at hy
            rw [durSum_append, durSum_cons, durSum_nil, hd, hτ']
            rcases List.mem_append.mp hy with hy | hy
            · have := hpreb y hy
              omega
            · simp only [landList_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
              subst hy
              omega))
        refine ⟨segs, by simpa using hflat, ?_, hsegs⟩
        rw [hlen]
        simp [hubArrivals, hdst]
      | ci =>
        have hτ' : τ' = N.d w := by
          rw [hsrc, hdst] at hdur
          simpa [Network.duration] using hdur.symm
        obtain ⟨segs, hflat, hlen, hsegs⟩ := ih.1 (by simp [hdst])
        refine ⟨(pre ++ [ℓ]) :: segs, by simp [hflat], ?_, ?_⟩
        · simp [hlen, hubArrivals, hdst]
        · intro γ hγ
          rcases List.mem_cons.mp hγ with rfl | hγ
          · refine ⟨by rw [hubArrivals_append, hpre0]; simp [hubArrivals, hdst],
              ⟨ℓ, by simp, by simp [hdst]⟩, ?_, ?_⟩
            · rw [landList_append, landList_cons_hub ℓ [] (by simp [hdst])]
              simpa using hpre
            · intro y hy
              rw [landList_append, landList_cons_hub ℓ [] (by simp [hdst])] at hy
              rw [durSum_append, durSum_cons, durSum_nil, hd, hτ']
              simp only [landList_nil, List.append_nil] at hy
              exact hpreb y hy
          · exact hsegs γ hγ
      | cg =>
        have hτ' : τ' = N.d w := by
          rw [hsrc, hdst] at hdur
          simpa [Network.duration, hS] using hdur.symm
        obtain ⟨segs, hflat, hlen, hsegs⟩ := ih.1 (by simp [hdst])
        refine ⟨(pre ++ [ℓ]) :: segs, by simp [hflat], ?_, ?_⟩
        · simp [hlen, hubArrivals, hdst]
        · intro γ hγ
          rcases List.mem_cons.mp hγ with rfl | hγ
          · refine ⟨by rw [hubArrivals_append, hpre0]; simp [hubArrivals, hdst],
              ⟨ℓ, by simp, by simp [hdst]⟩, ?_, ?_⟩
            · rw [landList_append, landList_cons_hub ℓ [] (by simp [hdst])]
              simpa using hpre
            · intro y hy
              rw [landList_append, landList_cons_hub ℓ [] (by simp [hdst])] at hy
              rw [durSum_append, durSum_cons, durSum_nil, hd, hτ']
              simp only [landList_nil, List.append_nil] at hy
              exact hpreb y hy
          · exact hsegs γ hγ

/-- **The segment bound** (Lemma 3.3(b) under (S)). Under (S) and (AΔ) on the triangles through a
hub, a segment — a route from a hub whose only hub arrival is its last leg — flies at least
`2 d_y` for every central city `y` it lands in: `2 d_y ≤ F(γ)`. -/
theorem segment_bound {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub)
    {γ : List (Leg n t)} {h : Loc n} {τ : ℕ} (hh : h.isHub = true) (hr : IsRoute h τ γ)
    (hf : ∀ ℓ ∈ γ, Flies N ℓ) (hone : hubArrivals γ = 1) {ℓ : Leg n t}
    (hlast : γ.getLast? = some ℓ) (hℓ : ℓ.dst.isHub = true) :
    ∀ y ∈ landList γ, 2 * N.d y ≤ durSum γ := by
  have hfin : (finalLoc h γ).isHub = true := by
    have hne : γ ≠ [] := by rintro rfl; simp at hlast
    obtain ⟨m, hm, hdst⟩ := exists_mem_dst_finalLoc h γ hne
    have : finalLoc h γ = ℓ.dst := by
      have key : ∀ (x : Loc n) (l : List (Leg n t)) (m : Leg n t), l.getLast? = some m →
          finalLoc x l = m.dst := by
        intro x l
        induction l generalizing x with
        | nil => simp
        | cons a l ih =>
          intro m hm
          cases l with
          | nil => simp_all
          | cons b l => exact ih a.dst m (by simpa using hm)
      exact key h γ ℓ hlast
    rw [this]
    exact hℓ
  obtain ⟨segs, hflat, hlen, hsegs⟩ := (exists_segs_aux hS hL γ h τ hr hf hfin).1 hh
  rw [hone] at hlen
  obtain ⟨γ', rfl⟩ : ∃ γ', segs = [γ'] := List.length_eq_one_iff.mp hlen
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hflat
  subst hflat
  exact (hsegs γ' (List.mem_singleton_self γ')).2.2.2

/-- **The segments of a feasible plane.** Under (S) and (AΔ) on the triangles through a hub, the
route is the concatenation of its segments: one per hub arrival, each ending with its only hub
arrival, landing at least once, and flying at least `2 d_y` for each of its landings `y`. -/
theorem PlaneFeasible.exists_segments_tri {N : Network n} (hS : N.dbar = N.d) (hL : N.ATriHub)
    {legs : List (Leg n t)} (h : PlaneFeasible N legs) :
    ∃ segs : List (List (Leg n t)), segs.flatten = legs ∧ segs.length = hubArrivals legs ∧
      ∀ γ ∈ segs, hubArrivals γ = 1 ∧ (∃ ℓ, γ.getLast? = some ℓ ∧ ℓ.dst.isHub = true) ∧
        landList γ ≠ [] ∧ ∀ y ∈ landList γ, 2 * N.d y ≤ durSum γ :=
  (exists_segs_aux hS hL legs .ci 0 h.route h.flies (by simp [h.ends])).1 rfl

/-! ### Lemma 4.11 -/

/-- **Lemma 4.11 (shrinking).** An admissible partition with `|X| ≥ p + 2` stays admissible after
removing two landings, each new group a sub-multiset of the old one. This is SH
(`Admissible.exists_shrink`) with `s = |X| − 2`, whose parity hypothesis holds by
`IsParityWitness.size_mod_two`. -/
theorem Admissible.exists_remove_two {X : Groups n p} (hX : Admissible X)
    (h : p + 2 ≤ size X) :
    ∃ Y : Groups n p, Admissible Y ∧ (∀ k, Y k ≤ X k) ∧ size Y + 2 = size X := by
  obtain ⟨w, hw⟩ := hX
  have hmod := hw.size_mod_two
  obtain ⟨Y, hY, hle, hsize⟩ :=
    Admissible.exists_shrink ⟨w, hw⟩ (s := size X - 2) (by omega) (by omega) (by omega)
  exact ⟨Y, hY, hle, by omega⟩

end ZenoFront
