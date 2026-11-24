/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod

/-!
# Steps 3–4 of Theorem 6.9: links along the hand-offs

After the exchanges of Step 2, the hand-offs of a plan at a city form *arrows* between its
visits: an arrow `γ → γ'` for each passenger that arrives with the entry leg of `γ` and leaves
with the exit leg of `γ'` (a passenger carried through one visit is an arrow `γ → γ`). Each visit
has at most one outgoing and one incoming arrow (capacity one), an arrow leaves a visit entered
from `C_I` and enters a visit left towards `C_G`, and, by Step 2, `e(γ) ≤ a(γ')` when `γ ≠ γ'`.

The note decomposes the arrows into paths and cycles: inner visits of a path are crossings `A`
(entered from `C_I`, left towards `C_G`), and a path from a drop-off `B` to a pick-up `B̄` gives a
link with `a(B) ≤ e(B̄)`. `exists_links` proves the resulting count directly, by induction on the
number of `A` visits: an `A` visit `w` is removed, and arrows `s → w → d` are contracted to
`s → d` (still `e(s) ≤ a(w) ≤ e(w) ≤ a(d)`). When no `A` visit is left, every arrow runs from a
`B` to a `B̄` and is a link. So the number of arrows (passengers) is at most the number of links
plus the number of `A` visits.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {V C : Type*} [DecidableEq V]

/-- **The count of Steps 3–4.** Visits `V` have an entry flag `eI` (entered from `C_I`), an exit
flag `xI` (left towards `C_I`), a city and times `a ≤ e`. Let `E` be arrows between visits of `S`,
at most one leaving and one entering each visit, each leaving a visit entered from `C_I` and
entering a visit left towards `C_G` at the same city, with `e(γ) ≤ a(γ')` unless `γ = γ'`. Then
some links `Λ`, each from a `B` (entered from and left towards `C_I`) to a `B̄` (entered from and
left towards `C_G`) at the same city with `a(B) ≤ e(B̄)`, at most one at each visit, number at
least `|E|` minus the number of `A` visits of `S`. -/
theorem exists_links (eI xI : V → Bool) (city : V → C) (a e : V → ℕ) (hae : ∀ v, a v ≤ e v) :
    ∀ (S : Finset V) (E : Finset (V × V)), (∀ x ∈ E, x.1 ∈ S ∧ x.2 ∈ S) →
      (∀ x ∈ E, ∀ y ∈ E, x.1 = y.1 → x = y) → (∀ x ∈ E, ∀ y ∈ E, x.2 = y.2 → x = y) →
      (∀ x ∈ E, eI x.1 = true ∧ xI x.2 = false ∧ city x.1 = city x.2 ∧
        (x.1 ≠ x.2 → e x.1 ≤ a x.2)) →
      ∃ Λ : Finset (V × V),
        (∀ x ∈ Λ, eI x.1 = true ∧ xI x.1 = true ∧ eI x.2 = false ∧ xI x.2 = false ∧
          city x.1 = city x.2 ∧ a x.1 ≤ e x.2) ∧
        (∀ x ∈ Λ, ∀ y ∈ Λ, x.1 = y.1 → x = y) ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, x.2 = y.2 → x = y) ∧
        E.card ≤ Λ.card + (S.filter fun w => eI w = true ∧ xI w = false).card := by
  intro S E
  set m := (S.filter fun w => eI w = true ∧ xI w = false).card with hm
  clear_value m
  induction m generalizing S E with
  | zero =>
    intro hS h₁ h₂ hE
    have hnoA : ∀ w ∈ S, ¬ (eI w = true ∧ xI w = false) := fun w hw hA =>
      (Finset.card_eq_zero.mp hm.symm ▸ Finset.notMem_empty w) (Finset.mem_filter.mpr ⟨hw, hA⟩)
    refine ⟨E, fun x hx => ?_, h₁, h₂, by omega⟩
    obtain ⟨hs, hd⟩ := hS x hx
    obtain ⟨he₁, hx₂, hc, ht⟩ := hE x hx
    have hx₁ : xI x.1 = true := by
      by_contra h
      exact hnoA _ hs ⟨he₁, by simpa using h⟩
    have he₂ : eI x.2 = false := by
      by_contra h
      exact hnoA _ hd ⟨by simpa using h, hx₂⟩
    have hne : x.1 ≠ x.2 := fun h => by rw [h, hx₂] at hx₁; exact absurd hx₁ (by simp)
    exact ⟨he₁, hx₁, he₂, hx₂, hc, (hae _).trans ((ht hne).trans (hae _))⟩
  | succ m ih =>
    intro hS h₁ h₂ hE
    obtain ⟨w, hw⟩ : (S.filter fun w => eI w = true ∧ xI w = false).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨hwS, hwA⟩ := Finset.mem_filter.mp hw
    set S' := S.erase w with hS'
    have hm' : m = (S'.filter fun w => eI w = true ∧ xI w = false).card := by
      rw [hS', Finset.filter_erase, Finset.card_erase_of_mem hw]
      omega
    set E₀ := E.filter fun x => x.1 ≠ w ∧ x.2 ≠ w with hE₀
    have hE₀S : ∀ x ∈ E₀, x.1 ∈ S' ∧ x.2 ∈ S' := fun x hx => by
      obtain ⟨hx, hne₁, hne₂⟩ := Finset.mem_filter.mp hx
      exact ⟨Finset.mem_erase.mpr ⟨hne₁, (hS x hx).1⟩, Finset.mem_erase.mpr ⟨hne₂, (hS x hx).2⟩⟩
    -- The arrows touching `w`.
    have hsplit : E.card = E₀.card + (E.filter fun x => ¬ (x.1 ≠ w ∧ x.2 ≠ w)).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    by_cases hpath : ∃ s d, (s, w) ∈ E ∧ (w, d) ∈ E ∧ s ≠ w
    · -- Contract `s → w → d` to `s → d`.
      obtain ⟨s, d, hsw, hwd, hsne⟩ := hpath
      have hdne : d ≠ w := by
        rintro rfl
        exact hsne (congrArg Prod.fst (h₂ _ hsw _ hwd rfl))
      have htouch : (E.filter fun x => ¬ (x.1 ≠ w ∧ x.2 ≠ w)) = {(s, w), (w, d)} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, not_and_or,
          not_not]
        constructor
        · rintro ⟨hx, h | h⟩
          · exact Or.inr (h₁ _ hx _ hwd h)
          · exact Or.inl (h₂ _ hx _ hsw h)
        · rintro (rfl | rfl)
          · exact ⟨hsw, Or.inr rfl⟩
          · exact ⟨hwd, Or.inl rfl⟩
      have hne : (s, w) ≠ (w, d) := fun h => hsne (congrArg Prod.fst h)
      have hsd : (s, d) ∉ E₀ := by
        intro h
        obtain ⟨h, -, -⟩ := Finset.mem_filter.mp h
        exact hdne (congrArg Prod.snd (h₁ _ h _ hsw rfl))
      have hcard : E.card = (insert (s, d) E₀).card + 1 := by
        rw [hsplit, htouch, Finset.card_insert_of_notMem hsd, Finset.card_pair hne]
      obtain ⟨hes, -, hcs, hts⟩ := hE _ hsw
      obtain ⟨-, hxd, hcd, htd⟩ := hE _ hwd
      obtain ⟨Λ, hΛ, hΛ₁, hΛ₂, hle⟩ := ih S' (insert (s, d) E₀) hm'
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ⟨Finset.mem_erase.mpr ⟨hsne, (hS _ hsw).1⟩,
              Finset.mem_erase.mpr ⟨hdne, (hS _ hwd).2⟩⟩
          · exact hE₀S x hx)
        (fun x hx y hy hxy => by
          rcases Finset.mem_insert.mp hx with rfl | hx <;>
            rcases Finset.mem_insert.mp hy with rfl | hy
          · rfl
          · obtain ⟨hy, hy₁, hy₂⟩ := Finset.mem_filter.mp hy
            exact absurd (congrArg Prod.snd (h₁ _ hy _ hsw hxy.symm)) hy₂
          · obtain ⟨hx, hx₁, hx₂⟩ := Finset.mem_filter.mp hx
            exact absurd (congrArg Prod.snd (h₁ _ hx _ hsw hxy)) hx₂
          · exact h₁ _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 hxy)
        (fun x hx y hy hxy => by
          rcases Finset.mem_insert.mp hx with rfl | hx <;>
            rcases Finset.mem_insert.mp hy with rfl | hy
          · rfl
          · obtain ⟨hy, hy₁, hy₂⟩ := Finset.mem_filter.mp hy
            exact absurd (congrArg Prod.fst (h₂ _ hy _ hwd hxy.symm)) hy₁
          · obtain ⟨hx, hx₁, hx₂⟩ := Finset.mem_filter.mp hx
            exact absurd (congrArg Prod.fst (h₂ _ hx _ hwd hxy)) hx₁
          · exact h₂ _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 hxy)
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · refine ⟨hes, hxd, hcs.trans hcd, fun _ => ?_⟩
            exact (hts hsne).trans ((hae w).trans (htd hdne.symm))
          · exact hE x (Finset.mem_filter.mp hx).1)
      exact ⟨Λ, hΛ, hΛ₁, hΛ₂, by omega⟩
    · -- At most one arrow touches `w`: drop it.
      push Not at hpath
      have htouch : (E.filter fun x => ¬ (x.1 ≠ w ∧ x.2 ≠ w)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun x hx y hy => ?_
        simp only [Finset.mem_filter, not_and_or, not_not] at hx hy
        obtain ⟨hx, hx'⟩ := hx
        obtain ⟨hy, hy'⟩ := hy
        rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
        · exact h₁ _ hx _ hy (hx'.trans hy'.symm)
        · -- `y = (s, w)` and `x = (w, d)`: then `s = w`, so `y = (w, w)`.
          have := hpath y.1 x.2 (by rw [← hy']; exact hy) (by rw [← hx']; exact hx)
          exact h₁ _ hx _ hy (hx'.trans this.symm)
        · have := hpath x.1 y.2 (by rw [← hx']; exact hx) (by rw [← hy']; exact hy)
          exact h₁ _ hx _ hy (this.trans hy'.symm)
        · exact h₂ _ hx _ hy (hx'.trans hy'.symm)
      obtain ⟨Λ, hΛ, hΛ₁, hΛ₂, hle⟩ := ih S' E₀ hm' hE₀S
        (fun x hx y hy => h₁ x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
        (fun x hx y hy => h₂ x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
        (fun x hx => hE x (Finset.mem_filter.mp hx).1)
      exact ⟨Λ, hΛ, hΛ₁, hΛ₂, by omega⟩

end ZenoFront
