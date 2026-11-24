/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.TriSegments
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Relation

/-!
# The combinatorial core of Theorem 4.10

The proof of Theorem 4.10 (§4.6 of `doc/theory/exact-front.md`) uses no timing: only the planes,
their segments, the central landings of each segment and which planes share which cities. This
file proves its combinatorial part on abstract data (`TriCore.Data`):

* *landings* `e : Λ`, each in a city `city e` and in a *block* `blk e : B` (a segment, or two
  segments of one plane merged); each block belongs to a plane `pl γ`;
* for each block `γ`, a landing `z γ` of `γ` in a city of largest duration, `R(γ) = d(z γ)`.

**Statement** (`TriCore.exists_selection`). If, in every class of planes connected by shared
cities, the number of planes with an even number of blocks is even, then every block `γ` can be
given a city `x γ` with `d(x γ) ≤ R(γ)` and a landing `pay γ` in `x γ`, `pay` injective, such that
the groups `X_k = {x γ | γ a block of k}` are admissible.

The proof follows Steps 2, 3 and 5 of the note, with ends recorded by their payments: `own e = γ`
says that landing `e` pays an end of block `γ` at the city of `e`.

* **Links** (Step 2, `exists_tjoin`). A `T`-join of the plane–city graph, `T` the planes with an
  even number of blocks, built from paths between pairs of planes of `T` in one class. Each
  landing in the join pays an end of its own block.
* **Re-pairing** (Step 3, `Inv.step`). While a block `γ` has two ends `e₁, e₂`, with
  `d(e₁) ≤ d(e₂)` and `e₁ ≠ z γ`, take another end `e₃` at the city of `e₂`, of a block `γ₃`
  (the number of ends at a city stays even). If `γ₃ = γ`, delete the ends `e₂, e₃`. Otherwise
  delete `e₂, e₃` and move `e₁` to `γ₃`: the link `(γ, γ₃)` at `e₂`'s city and the link at `e₁`'s
  city become one link `(γ₁, γ₃)` at `e₁`'s city, paid by `e₁`. This keeps every end within `R`
  (`d(e₁) ≤ d(e₂) ≤ R(γ₃)`), every city's number of ends even, every plane's number of ends mod 2,
  and the claim of the note: no `z γ` pays an end of another block. It removes two ends.
* **Selection** (Step 5, Lemma 2.3). When every block has at most one end, a block with an end
  takes the end's city and landing, and a block without one takes `z γ`. The cities with an odd
  number of ends at a plane form a parity witness.
-/

@[expose] public section

namespace ZenoFront

open Finset

namespace TriCore

/-- The abstract data of Theorem 4.10: landings in cities and in blocks, blocks in planes, and in
each block a landing of largest duration. -/
structure Data (n p : ℕ) (Λ B : Type*) where
  /-- The durations. -/
  d : Fin n → ℕ
  /-- The city of a landing. -/
  city : Λ → Fin n
  /-- The block (segment) of a landing. -/
  blk : Λ → B
  /-- The plane of a block. -/
  pl : B → Fin p
  /-- A landing of the block in a city of largest duration. -/
  z : B → Λ
  blk_z : ∀ γ, blk (z γ) = γ
  le_z : ∀ e, d (city e) ≤ d (city (z (blk e)))

variable {n p : ℕ} {Λ B : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B]

namespace Data

variable (D : Data n p Λ B)

/-- `R(γ)`: the largest duration of a landing of the block. -/
def R (γ : B) : ℕ := D.d (D.city (D.z γ))

/-- Two planes share a city: both land in it. -/
def Share (k k' : Fin p) : Prop :=
  ∃ e e' : Λ, D.pl (D.blk e) = k ∧ D.pl (D.blk e') = k' ∧ D.city e = D.city e'

/-- The planes connected to `k` by shared cities. -/
def Conn : Fin p → Fin p → Prop := Relation.ReflTransGen D.Share

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
theorem share_symm {k k' : Fin p} (h : D.Share k k') : D.Share k' k := by
  obtain ⟨e, e', h₁, h₂, h₃⟩ := h
  exact ⟨e', e, h₂, h₁, h₃.symm⟩

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
theorem conn_symm {k k' : Fin p} (h : D.Conn k k') : D.Conn k' k := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (D.share_symm hbc) ih

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
theorem conn_trans {a b c : Fin p} (h₁ : D.Conn a b) (h₂ : D.Conn b c) : D.Conn a c :=
  Relation.ReflTransGen.trans h₁ h₂

end Data

/-! ### Step 2: a `T`-join of the plane–city graph -/

/-- The degree of a plane in an edge vector over `ZMod 2`. -/
def Data.pdeg (D : Data n p Λ B) (v : Λ → ZMod 2) (k : Fin p) : ZMod 2 :=
  ∑ e ∈ univ.filter (fun e => D.pl (D.blk e) = k), v e

/-- The degree of a city in an edge vector over `ZMod 2`. -/
def Data.cdeg (D : Data n p Λ B) (v : Λ → ZMod 2) (y : Fin n) : ZMod 2 :=
  ∑ e ∈ univ.filter (fun e => D.city e = y), v e

theorem ind_add_ind_self (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ZMod 2) + if P then 1 else 0) = 0 := by
  split_ifs <;> decide

omit [Fintype B] [DecidableEq B] in
/-- **A path.** Two connected planes are the odd-degree planes of an edge vector in which every
city has even degree. -/
theorem exists_path (D : Data n p Λ B) {a b : Fin p} (h : D.Conn a b) :
    ∃ v : Λ → ZMod 2, (∀ k, D.pdeg v k = (if k = a then 1 else 0) + (if k = b then 1 else 0)) ∧
      ∀ y, D.cdeg v y = 0 := by
  induction h with
  | refl =>
    refine ⟨0, fun k => ?_, fun y => ?_⟩
    · simp only [Data.pdeg, Pi.zero_apply, Finset.sum_const_zero]
      exact (ind_add_ind_self _).symm
    · simp [Data.cdeg]
  | @tail b c _ hbc ih =>
    obtain ⟨v, hv, hc⟩ := ih
    obtain ⟨e₁, e₂, h₁, h₂, h₃⟩ := hbc
    refine ⟨v + Pi.single e₁ 1 + Pi.single e₂ 1, fun k => ?_, fun y => ?_⟩
    · have hsum : D.pdeg (v + Pi.single e₁ 1 + Pi.single e₂ 1) k =
          D.pdeg v k + (if k = b then 1 else 0) + (if k = c then 1 else 0) := by
        simp only [Data.pdeg, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
          Finset.mem_filter, Finset.mem_univ, true_and, h₁, h₂, @eq_comm _ b k, @eq_comm _ c k]
      rw [hsum, hv k, add_assoc (if k = a then (1 : ZMod 2) else 0), ind_add_ind_self, add_zero]
    · have hsum : D.cdeg (v + Pi.single e₁ 1 + Pi.single e₂ 1) y =
          D.cdeg v y + (if D.city e₂ = y then 1 else 0) + (if D.city e₂ = y then 1 else 0) := by
        simp only [Data.cdeg, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
          Finset.mem_filter, Finset.mem_univ, true_and, h₃]
      rw [hsum, hc y, zero_add]
      exact ind_add_ind_self _

omit [Fintype B] [DecidableEq B] in
open Classical in
/-- **The `T`-join** (Step 2). If every class of connected planes has an even number of planes of
`T`, some edge vector has odd degree exactly at the planes of `T` and even degree at every city. -/
theorem exists_tjoin (D : Data n p Λ B) : ∀ (m : ℕ) (T : Finset (Fin p)), T.card = m →
    (∀ a, Even #{k ∈ T | D.Conn a k}) →
    ∃ v : Λ → ZMod 2, (∀ k, D.pdeg v k = if k ∈ T then 1 else 0) ∧ ∀ y, D.cdeg v y = 0
  | m, T, hm, hpar => by
    rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, fun k => by simp [Data.pdeg], fun y => by simp [Data.cdeg]⟩
    · have hcard : 1 < #{k ∈ T | D.Conn a k} := by
        have hmem : a ∈ ({k ∈ T | D.Conn a k} : Finset (Fin p)) :=
          Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩
        have hpos := Finset.card_pos.mpr ⟨a, hmem⟩
        obtain ⟨r, hr⟩ := hpar a
        omega
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
      obtain ⟨hbT, hab⟩ := Finset.mem_filter.mp hb
      obtain ⟨T', hT'⟩ : ∃ T', T' = (T.erase a).erase b := ⟨_, rfl⟩
      have hbT' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨hba, hbT⟩
      have hcard' : T'.card + 2 = T.card := by
        rw [hT', Finset.card_erase_of_mem hbT', Finset.card_erase_of_mem ha]
        have := Finset.card_pos.mpr ⟨a, ha⟩
        have : 1 < T.card := by
          have := Finset.card_le_card (Finset.filter_subset (fun k => D.Conn a k) T)
          omega
        omega
      have hpar' : ∀ a', Even #{k ∈ T' | D.Conn a' k} := by
        intro a'
        have hf : ({k ∈ T' | D.Conn a' k} : Finset (Fin p)) =
            (({k ∈ T | D.Conn a' k} : Finset (Fin p)).erase a).erase b := by
          rw [hT', Finset.filter_erase, Finset.filter_erase]
        rw [hf]
        by_cases ha' : D.Conn a' a
        · have hb' : D.Conn a' b := D.conn_trans ha' hab
          have h₁ : a ∈ ({k ∈ T | D.Conn a' k} : Finset (Fin p)) :=
            Finset.mem_filter.mpr ⟨ha, ha'⟩
          have h₂ : b ∈ (({k ∈ T | D.Conn a' k} : Finset (Fin p)).erase a) :=
            Finset.mem_erase.mpr ⟨hba, Finset.mem_filter.mpr ⟨hbT, hb'⟩⟩
          rw [Finset.card_erase_of_mem h₂, Finset.card_erase_of_mem h₁]
          obtain ⟨r, hr⟩ := hpar a'
          have : 1 < #{k ∈ T | D.Conn a' k} := by
            have := Finset.card_erase_of_mem h₁
            have := Finset.card_pos.mpr ⟨b, h₂⟩
            omega
          exact ⟨r - 1, by omega⟩
        · have hb' : ¬ D.Conn a' b := fun h => ha' (D.conn_trans h (D.conn_symm hab))
          rw [Finset.erase_eq_of_notMem (by simp [hb']), Finset.erase_eq_of_notMem
            (by simp [ha'])]
          exact hpar a'
      obtain ⟨v, hv, hc⟩ := exists_tjoin D T'.card T' rfl hpar'
      obtain ⟨w, hw, hwc⟩ := exists_path D hab
      refine ⟨v + w, fun k => ?_, fun y => ?_⟩
      · have h₁ := hv k
        have h₂ := hw k
        simp only [Data.pdeg, Pi.add_apply, Finset.sum_add_distrib] at h₁ h₂ ⊢
        rw [h₁, h₂]
        by_cases hka : k = a
        · subst hka
          have : k ∉ T' := by simp [hT']
          simp [this, ha, Ne.symm hba]
        · by_cases hkb : k = b
          · subst hkb
            have : k ∉ T' := by simp [hT']
            simp [this, hbT, hka]
          · have : k ∈ T' ↔ k ∈ T := by simp [hT', hka, hkb]
            simp [this, hka, hkb]
      · have h₁ := hc y
        have h₂ := hwc y
        simp only [Data.cdeg, Pi.add_apply, Finset.sum_add_distrib] at h₁ h₂ ⊢
        rw [h₁, h₂, add_zero]
termination_by m => m
decreasing_by omega

/-! ### Step 3: re-pairing -/

/-- The parity a plane's number of ends must have: odd iff it has an even number of blocks. -/
def Data.tau (D : Data n p Λ B) (k : Fin p) : ℕ := if Even #{γ | D.pl γ = k} then 1 else 0

/-- The invariant of the re-pairing, for the ends recorded by their payments (`own e = some γ`:
landing `e` pays an end of block `γ` at `city e`). -/
structure Inv (D : Data n p Λ B) (own : Λ → Option B) : Prop where
  /-- Every end is within `R`. -/
  le : ∀ e γ, own e = some γ → D.d (D.city e) ≤ D.R γ
  /-- Every city has an even number of ends. -/
  col : ∀ y, Even #{e | D.city e = y ∧ own e ≠ none}
  /-- Every plane's number of ends has the parity `tau`. -/
  row : ∀ k, #{e | (own e).map D.pl = some k} % 2 = D.tau k
  /-- No `z γ` pays an end of another block (the claim of the note). -/
  zown : ∀ γ γ', own (D.z γ) = some γ' → γ' = γ

/-- Changing a function at one point changes the count of a property by the difference of its
indicators there. -/
theorem card_filter_update {α β : Type*} [Fintype α] [DecidableEq α] (f : α → β) (a : α) (v : β)
    (Q : α → β → Prop) [∀ x y, Decidable (Q x y)] :
    #{x | Q x (Function.update f a v x)} + (if Q a (f a) then 1 else 0) =
      #{x | Q x (f x)} + (if Q a v then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have : ∑ x ∈ univ.erase a, (if Q x (Function.update f a v x) then 1 else 0) =
      ∑ x ∈ univ.erase a, (if Q x (f x) then 1 else 0) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  omega

omit [DecidableEq B] in
/-- Choosing the two ends of a re-pairing: `e₁ ≠ z γ` and `d(e₁) ≤ d(e₂)`. -/
theorem Inv.exists_pair {D : Data n p Λ B} {own : Λ → Option B} (hI : Inv D own) {γ : B}
    {a b : Λ} (hab : a ≠ b) (ha : own a = some γ) (hb : own b = some γ) :
    ∃ e₁ e₂, e₁ ≠ e₂ ∧ own e₁ = some γ ∧ own e₂ = some γ ∧ e₁ ≠ D.z γ ∧
      D.d (D.city e₁) ≤ D.d (D.city e₂) := by
  by_cases hbz : b = D.z γ
  · refine ⟨a, b, hab, ha, hb, hbz ▸ hab, ?_⟩
    have := hI.le a γ ha
    rw [hbz]
    exact this
  · by_cases haz : a = D.z γ
    · refine ⟨b, a, Ne.symm hab, hb, ha, haz ▸ Ne.symm hab, ?_⟩
      have := hI.le b γ hb
      rw [haz]
      exact this
    · by_cases hle : D.d (D.city a) ≤ D.d (D.city b)
      · exact ⟨a, b, hab, ha, hb, haz, hle⟩
      · exact ⟨b, a, Ne.symm hab, hb, ha, hbz, by omega⟩

omit [Fintype B] [DecidableEq B] in
/-- Deleting an end `e` of `γ`: one end fewer, one fewer at `city e` and at the plane of `γ`. -/
theorem card_del (D : Data n p Λ B) (own : Λ → Option B) {e : Λ} {γ : B} (h : own e = some γ) :
    #{x | Function.update own e none x ≠ none} + 1 = #{x | own x ≠ none} ∧
    (∀ y, #{x | D.city x = y ∧ Function.update own e none x ≠ none} +
      (if D.city e = y then 1 else 0) = #{x | D.city x = y ∧ own x ≠ none}) ∧
    (∀ k, #{x | (Function.update own e none x).map D.pl = some k} +
      (if D.pl γ = k then 1 else 0) = #{x | (own x).map D.pl = some k}) := by
  refine ⟨?_, fun y => ?_, fun k => ?_⟩
  · have := card_filter_update own e none (fun _ o => o ≠ none)
    rw [h] at this
    simpa using this
  · have := card_filter_update own e none (fun x o => D.city x = y ∧ o ≠ none)
    rw [h] at this
    simpa using this
  · have := card_filter_update own e none (fun _ o => o.map D.pl = some k)
    rw [h] at this
    simpa using this

omit [Fintype B] [DecidableEq B] in
/-- Moving an end `e` from `γ` to `γ'`: the same ends at every city; the plane of `γ` loses one
and the plane of `γ'` gains one. -/
theorem card_mv (D : Data n p Λ B) (own : Λ → Option B) {e : Λ} {γ : B} (h : own e = some γ)
    (γ' : B) :
    #{x | Function.update own e (some γ') x ≠ none} = #{x | own x ≠ none} ∧
    (∀ y, #{x | D.city x = y ∧ Function.update own e (some γ') x ≠ none} =
      #{x | D.city x = y ∧ own x ≠ none}) ∧
    (∀ k, #{x | (Function.update own e (some γ') x).map D.pl = some k} +
      (if D.pl γ = k then 1 else 0) =
        #{x | (own x).map D.pl = some k} + (if D.pl γ' = k then 1 else 0)) := by
  refine ⟨?_, fun y => ?_, fun k => ?_⟩
  · have := card_filter_update own e (some γ') (fun _ o => o ≠ none)
    rw [h] at this
    simpa using this
  · have := card_filter_update own e (some γ') (fun x o => D.city x = y ∧ o ≠ none)
    rw [h] at this
    simpa using this
  · have := card_filter_update own e (some γ') (fun _ o => o.map D.pl = some k)
    rw [h] at this
    simpa using this

/-- **One re-pairing step.** A block with two ends loses two ends of the plan, keeping the
invariant. -/
theorem Inv.step {D : Data n p Λ B} {own : Λ → Option B} (hI : Inv D own) {γ : B} {a b : Λ}
    (hab : a ≠ b) (ha : own a = some γ) (hb : own b = some γ) :
    ∃ own', Inv D own' ∧ #{e | own' e ≠ none} + 2 = #{e | own e ≠ none} := by
  obtain ⟨e₁, e₂, h12, h1, h2, h1z, hd12⟩ := hI.exists_pair hab ha hb
  -- Another end at the city of `e₂`.
  have hcol := hI.col (D.city e₂)
  have hmem : e₂ ∈ ({e | D.city e = D.city e₂ ∧ own e ≠ none} : Finset Λ) := by simp [h2]
  have hone : 1 < #{e | D.city e = D.city e₂ ∧ own e ≠ none} := by
    have := Finset.card_pos.mpr ⟨e₂, hmem⟩
    obtain ⟨r, hr⟩ := hcol
    omega
  obtain ⟨e₃, he₃, h32⟩ := Finset.exists_mem_ne hone e₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₃
  obtain ⟨hc3, hn3⟩ := he₃
  obtain ⟨γ₃, h3⟩ := Option.ne_none_iff_exists'.mp hn3
  obtain ⟨o₁, ho₁⟩ : ∃ o, o = Function.update own e₂ none := ⟨_, rfl⟩
  have hp₁ : ∀ x, x ≠ e₂ → o₁ x = own x := fun x hx => by rw [ho₁, Function.update_of_ne hx]
  obtain ⟨E₁, C₁, R₁⟩ := card_del D own h2
  rw [← ho₁] at E₁ C₁ R₁
  have h3' : o₁ e₃ = some γ₃ := by rw [hp₁ e₃ h32, h3]
  obtain ⟨o₂, ho₂⟩ : ∃ o, o = Function.update o₁ e₃ none := ⟨_, rfl⟩
  have hp₂ : ∀ x, x ≠ e₂ → x ≠ e₃ → o₂ x = own x := fun x hx hx' => by
    rw [ho₂, Function.update_of_ne hx', hp₁ x hx]
  have hn₂ : o₂ e₂ = none ∧ o₂ e₃ = none := by
    rw [ho₂, ho₁]
    simp [h32.symm]
  obtain ⟨E₂, C₂, R₂⟩ := card_del D o₁ h3'
  rw [← ho₂] at E₂ C₂ R₂
  have hcol' := hI.col
  have hrow' := hI.row
  simp only [Nat.even_iff] at hcol'
  by_cases hγ₃ : γ₃ = γ
  · -- The other end is of `γ` too: delete both.
    subst hγ₃
    refine ⟨o₂, ⟨fun e γ' he => ?_, fun y => ?_, fun k => ?_, fun γ' γ'' hz => ?_⟩, by omega⟩
    · by_cases hx₂ : e = e₂
      · rw [hx₂, hn₂.1] at he; cases he
      · by_cases hx₃ : e = e₃
        · rw [hx₃, hn₂.2] at he; cases he
        · rw [hp₂ e hx₂ hx₃] at he
          exact hI.le e γ' he
    · have h₁ := C₁ y
      have h₂ := C₂ y
      have := hcol' y
      rw [hc3] at h₂
      rw [Nat.even_iff]
      split_ifs at h₁ h₂ <;> omega
    · have h₁ := R₁ k
      have h₂ := R₂ k
      have := hrow' k
      split_ifs at h₁ h₂ <;> omega
    · by_cases hx₂ : D.z γ' = e₂
      · rw [hx₂, hn₂.1] at hz; cases hz
      · by_cases hx₃ : D.z γ' = e₃
        · rw [hx₃, hn₂.2] at hz; cases hz
        · rw [hp₂ _ hx₂ hx₃] at hz
          exact hI.zown γ' γ'' hz
  · -- Move `e₁` to `γ₃`: one link at the city of `e₁`.
    have h13 : e₁ ≠ e₃ := fun h => hγ₃ (by
      rw [h, h3] at h1
      exact (Option.some_injective _ h1))
    have h1' : o₂ e₁ = some γ := by rw [hp₂ e₁ h12 h13, h1]
    obtain ⟨o₃, ho₃⟩ : ∃ o, o = Function.update o₂ e₁ (some γ₃) := ⟨_, rfl⟩
    obtain ⟨E₃, C₃, R₃⟩ := card_mv D o₂ h1' γ₃
    rw [← ho₃] at E₃ C₃ R₃
    have hv₃ : ∀ x, o₃ x = if x = e₁ then some γ₃ else o₂ x := fun x => by
      rw [ho₃, Function.update_apply]
    refine ⟨o₃, ⟨fun e γ' he => ?_, fun y => ?_, fun k => ?_, fun γ' γ'' hz => ?_⟩, by omega⟩
    · rw [hv₃] at he
      split_ifs at he with hx₁
      · obtain rfl := Option.some_injective _ he
        have := hI.le e₃ γ₃ h3
        rw [hc3] at this
        rw [hx₁]
        exact hd12.trans this
      · by_cases hx₂ : e = e₂
        · rw [hx₂, hn₂.1] at he; cases he
        · by_cases hx₃ : e = e₃
          · rw [hx₃, hn₂.2] at he; cases he
          · rw [hp₂ e hx₂ hx₃] at he
            exact hI.le e γ' he
    · have h₁ := C₁ y
      have h₂ := C₂ y
      have h₃ := C₃ y
      have := hcol' y
      rw [hc3] at h₂
      rw [Nat.even_iff]
      split_ifs at h₁ h₂ <;> omega
    · have h₁ := R₁ k
      have h₂ := R₂ k
      have h₃ := R₃ k
      have := hrow' k
      split_ifs at h₁ h₂ h₃ <;> omega
    · rw [hv₃] at hz
      split_ifs at hz with hx₁
      · -- `z γ' = e₁` is owned by `γ`, so `γ' = γ`; but `e₁ ≠ z γ`.
        exfalso
        have := hI.zown γ' γ (hx₁ ▸ h1)
        subst this
        exact h1z hx₁.symm
      · by_cases hx₂ : D.z γ' = e₂
        · rw [hx₂, hn₂.1] at hz; cases hz
        · by_cases hx₃ : D.z γ' = e₃
          · rw [hx₃, hn₂.2] at hz; cases hz
          · rw [hp₂ _ hx₂ hx₃] at hz
            exact hI.zown γ' γ'' hz

/-- **Step 3.** Re-pairing until every block has at most one end. -/
theorem Inv.exists_final {D : Data n p Λ B} : ∀ (m : ℕ) (own : Λ → Option B),
    #{e | own e ≠ none} = m → Inv D own →
    ∃ own', Inv D own' ∧ ∀ γ, #{e | own' e = some γ} ≤ 1
  | m, own, hm, hI => by
    by_cases hall : ∀ γ, #{e | own e = some γ} ≤ 1
    · exact ⟨own, hI, hall⟩
    · push Not at hall
      obtain ⟨γ, hγ⟩ := hall
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨own', hI', hcard⟩ := hI.step hab ha hb
      exact Inv.exists_final _ own' rfl hI'
termination_by m => m
decreasing_by omega

/-! ### The initial ends and the selection -/

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
/-- An edge vector over `ZMod 2` counts, mod 2, the landings where it is `1`. -/
theorem natCast_card_eq_sum (s : Finset Λ) (v : Λ → ZMod 2) :
    ((#{e ∈ s | v e = 1} : ℕ) : ZMod 2) = ∑ e ∈ s, v e := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases this (v e) with h | h <;> simp [h]

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
theorem mod_two_of_natCast {N : ℕ} {b : ℕ} (hb : b < 2) (h : ((N : ℕ) : ZMod 2) = (b : ℕ)) :
    N % 2 = b := by
  have := (ZMod.natCast_eq_natCast_iff' N b 2).mp h
  omega

omit [DecidableEq B] in
open Classical in
/-- **The initial ends** (Step 2): every landing of a `T`-join pays an end of its own block. -/
theorem exists_init (D : Data n p Λ B)
    (hpar : ∀ a, Even #{k | D.Conn a k ∧ Even #{γ | D.pl γ = k}}) : ∃ own, Inv D own := by
  set T : Finset (Fin p) := univ.filter fun k => Even #{γ | D.pl γ = k} with hT
  obtain ⟨v, hv, hc⟩ := exists_tjoin D T.card T rfl fun a => by
    have := hpar a
    convert this using 2
    ext k
    simp [hT, and_comm]
  refine ⟨fun e => if v e = 1 then some (D.blk e) else none, ⟨fun e γ he => ?_, fun y => ?_,
    fun k => ?_, fun γ γ' hz => ?_⟩⟩
  · split_ifs at he
    obtain rfl := Option.some_injective _ he
    exact D.le_z e
  · have h₁ : #{e | D.city e = y ∧ (if v e = 1 then some (D.blk e) else none) ≠ none} =
        #{e ∈ univ.filter (fun e => D.city e = y) | v e = 1} := by
      rw [Finset.filter_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have h₂ := natCast_card_eq_sum (univ.filter fun e => D.city e = y) v
    have h₃ := hc y
    simp only [Data.cdeg] at h₃
    rw [h₁, Nat.even_iff]
    exact mod_two_of_natCast (b := 0) (by omega) (by rw [h₂, h₃]; simp)
  · have h₁ : #{e | (if v e = 1 then some (D.blk e) else none).map D.pl = some k} =
        #{e ∈ univ.filter (fun e => D.pl (D.blk e) = k) | v e = 1} := by
      rw [Finset.filter_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have h₂ := natCast_card_eq_sum (univ.filter fun e => D.pl (D.blk e) = k) v
    have h₃ := hv k
    simp only [Data.pdeg] at h₃
    rw [h₁]
    unfold Data.tau
    by_cases hk : Even #{γ | D.pl γ = k}
    · have hkT : k ∈ T := by simp [hT, hk]
      simp only [hk, ↓reduceIte]
      exact mod_two_of_natCast (b := 1) (by omega) (by rw [h₂, h₃]; simp [hkT])
    · have hkT : k ∉ T := by simp [hT, hk]
      simp only [hk, ↓reduceIte]
      exact mod_two_of_natCast (b := 0) (by omega) (by rw [h₂, h₃]; simp [hkT])
  · split_ifs at hz
    obtain rfl := Option.some_injective _ hz
    exact D.blk_z γ

omit [Fintype B] [DecidableEq Λ] in
/-- When every block has at most one end, landings paying an end correspond to blocks with an
end. -/
theorem card_owned (own : Λ → Option B) (h1 : ∀ γ, #{e | own e = some γ} ≤ 1)
    (Q : Λ → B → Prop) [∀ e γ, Decidable (Q e γ)] [Fintype B] :
    #{e | ∃ γ, own e = some γ ∧ Q e γ} = #{γ | ∃ e, own e = some γ ∧ Q e γ} := by
  classical
  refine Finset.card_bij (fun e he => Classical.choose (Finset.mem_filter.mp he).2)
    (fun e he => ?_) (fun e he e' he' h => ?_) (fun γ hγ => ?_)
  · have := Classical.choose_spec (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, this⟩
  · set γ := Classical.choose (Finset.mem_filter.mp he).2 with hγ
    have h₁ : own e = some γ := (Classical.choose_spec (Finset.mem_filter.mp he).2).1
    have h₂ : own e' = some γ := by
      rw [h]
      exact (Classical.choose_spec (Finset.mem_filter.mp he').2).1
    exact Finset.card_le_one.mp (h1 γ) e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁⟩) e'
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩)
  · obtain ⟨e, he, hq⟩ := (Finset.mem_filter.mp hγ).2
    have hmem : e ∈ ({e | ∃ γ, own e = some γ ∧ Q e γ} : Finset Λ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, γ, he, hq⟩
    refine ⟨e, hmem, ?_⟩
    have := (Classical.choose_spec (Finset.mem_filter.mp hmem).2).1
    exact (Option.some_injective _ (this.symm.trans he))

omit [Fintype Λ] [DecidableEq Λ] [Fintype B] [DecidableEq B] in
/-- The number of points where `f` is odd has the parity of the sum of `f`. -/
theorem card_odd_mod_two {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    #{x ∈ s | Odd (f x)} % 2 = (∑ x ∈ s, f x) % 2 := by
  have := Finset.even_sum_iff_even_card_odd (s := s) f
  rw [Nat.even_iff, Nat.even_iff] at this
  omega

open Classical in
/-- **The selection** (Steps 2, 3 and 5 of Theorem 4.10). If every class of connected planes has
an even number of planes with an even number of blocks, every block `γ` gets a city `x γ` within
`R(γ)` and a landing `pay γ` in it, `pay` injective, and the groups `X_k = {x γ | γ ∈ k}` are
admissible. -/
theorem exists_selection (D : Data n p Λ B)
    (hpar : ∀ a, Even #{k | D.Conn a k ∧ Even #{γ | D.pl γ = k}}) :
    ∃ x : B → Fin n, ∃ pay : B → Λ, Function.Injective pay ∧ (∀ γ, D.city (pay γ) = x γ) ∧
      (∀ γ, D.d (x γ) ≤ D.R γ) ∧
      Admissible fun k => (univ.filter fun γ => D.pl γ = k).val.map x := by
  obtain ⟨own₀, hI₀⟩ := exists_init D hpar
  obtain ⟨own, hI, h1⟩ := Inv.exists_final _ own₀ rfl hI₀
  set pay : B → Λ := fun γ => if h : ∃ e, own e = some γ then h.choose else D.z γ with hpaydef
  have hpay1 : ∀ γ, (∃ e, own e = some γ) → own (pay γ) = some γ := fun γ h => by
    simp only [hpaydef, h, ↓reduceDIte]
    exact h.choose_spec
  have hpay0 : ∀ γ, ¬ (∃ e, own e = some γ) → pay γ = D.z γ := fun γ h => by
    simp only [hpaydef, h, ↓reduceDIte]
  have huniq : ∀ γ e, own e = some γ → pay γ = e := fun γ e he =>
    Finset.card_le_one.mp (h1 γ) _ (by simp [hpay1 γ ⟨e, he⟩]) e (by simp [he])
  set x : B → Fin n := fun γ => D.city (pay γ) with hxdef
  refine ⟨x, pay, fun γ γ' h => ?_, fun γ => rfl, fun γ => ?_, ?_⟩
  · -- `pay` is injective: ends have one owner, and no `z γ` pays another block's end.
    by_cases hγ : ∃ e, own e = some γ
    · by_cases hγ' : ∃ e, own e = some γ'
      · have h₁ := hpay1 γ hγ
        rw [h, hpay1 γ' hγ'] at h₁
        exact (Option.some_injective _ h₁).symm
      · have h₁ := hpay1 γ hγ
        rw [h, hpay0 γ' hγ'] at h₁
        exact (hI.zown γ' γ h₁)
    · by_cases hγ' : ∃ e, own e = some γ'
      · have h₁ := hpay1 γ' hγ'
        rw [← h, hpay0 γ hγ] at h₁
        exact (hI.zown γ γ' h₁).symm
      · have h₁ := congrArg D.blk h
        rwa [hpay0 γ hγ, hpay0 γ' hγ', D.blk_z, D.blk_z] at h₁
  · by_cases hγ : ∃ e, own e = some γ
    · exact hI.le _ γ (hpay1 γ hγ)
    · simp only [hxdef, hpay0 γ hγ]
      exact le_rfl
  · -- The parity witness: the cities with an odd number of ends at the plane.
    refine ⟨fun k => univ.filter fun y =>
      Odd #{γ | (D.pl γ = k ∧ ∃ e, own e = some γ) ∧ x γ = y}, ⟨fun k y hy => ?_, fun k => ?_,
      fun y => ?_⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨γ, hγ⟩ := Finset.card_pos.mp hy.pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
      rw [Multiset.mem_toFinset, Multiset.mem_map]
      exact ⟨γ, by simp [hγ.1.1], hγ.2⟩
    · -- Row: the plane's number of ends, which has the parity of `tau`.
      rw [Multiset.card_map, Finset.card_val, card_odd_mod_two]
      have hfib : ∑ y, #{γ | (D.pl γ = k ∧ ∃ e, own e = some γ) ∧ x γ = y} =
          #{γ | D.pl γ = k ∧ ∃ e, own e = some γ} := by
        rw [Finset.card_eq_sum_card_fiberwise (f := x) (t := univ) fun _ _ => Finset.mem_univ _]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.filter_filter]
      have hown : #{γ | D.pl γ = k ∧ ∃ e, own e = some γ} =
          #{e | (own e).map D.pl = some k} := by
        have := card_owned own h1 (fun _ γ => D.pl γ = k)
        rw [show (#{γ | D.pl γ = k ∧ ∃ e, own e = some γ} : ℕ) =
            #{γ | ∃ e, own e = some γ ∧ D.pl γ = k} by
          congr 1; ext γ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h₁, e, he⟩; exact ⟨e, he, h₁⟩
          · rintro ⟨e, he, h₁⟩; exact ⟨h₁, e, he⟩, ← this]
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.map_eq_some_iff]
      rw [hfib, hown, hI.row k]
      unfold Data.tau
      split_ifs with hk
      · obtain ⟨r, hr⟩ := hk
        omega
      · obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hk
        omega
    · -- Column: the city's number of ends, which is even.
      have h₁ : #{k | y ∈ univ.filter fun y =>
          Odd #{γ | (D.pl γ = k ∧ ∃ e, own e = some γ) ∧ x γ = y}} =
          #{k ∈ univ | Odd #{γ | (D.pl γ = k ∧ ∃ e, own e = some γ) ∧ x γ = y}} := by
        congr 1
        ext k
        simp
      rw [h₁, Nat.even_iff, card_odd_mod_two]
      have hfib : ∑ k, #{γ | (D.pl γ = k ∧ ∃ e, own e = some γ) ∧ x γ = y} =
          #{γ | (∃ e, own e = some γ) ∧ x γ = y} := by
        rw [Finset.card_eq_sum_card_fiberwise (f := D.pl) (t := univ) fun _ _ =>
          Finset.mem_univ _]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.filter_filter]
        congr 1
        ext γ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hown : #{γ | (∃ e, own e = some γ) ∧ x γ = y} =
          #{e | D.city e = y ∧ own e ≠ none} := by
        have := card_owned own h1 (fun e _ => D.city e = y)
        rw [show (#{γ | (∃ e, own e = some γ) ∧ x γ = y} : ℕ) =
            #{γ | ∃ e, own e = some γ ∧ D.city e = y} by
          congr 1; ext γ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨e, he⟩, h₁⟩
            exact ⟨e, he, by rw [← huniq γ e he]; exact h₁⟩
          · rintro ⟨e, he, h₁⟩
            exact ⟨⟨e, he⟩, by simp only [hxdef]; rw [huniq γ e he]; exact h₁⟩, ← this]
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
        constructor
        · rintro ⟨γ, he, h₁⟩; exact ⟨h₁, by simp [he]⟩
        · rintro ⟨h₁, he⟩
          obtain ⟨γ, hγ⟩ := Option.ne_none_iff_exists'.mp he
          exact ⟨γ, hγ, h₁⟩
      rw [hfib, hown]
      have := hI.col y
      rw [Nat.even_iff] at this
      exact this

end TriCore

/-! ### Blocks given as lists -/

/-- The largest duration of a list of cities (`0` for none). -/
def maxD {n : ℕ} (d : Fin n → ℕ) (l : List (Fin n)) : ℕ := (l.map d).foldr max 0

section maxD

variable {n : ℕ} (d : Fin n → ℕ)

@[simp] theorem maxD_nil : maxD d [] = 0 := rfl

@[simp] theorem maxD_cons (x : Fin n) (l : List (Fin n)) :
    maxD d (x :: l) = max (d x) (maxD d l) := rfl

theorem le_maxD {l : List (Fin n)} {x : Fin n} (h : x ∈ l) : d x ≤ maxD d l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp [ih h]

theorem maxD_le {l : List (Fin n)} {T : ℕ} (h : ∀ x ∈ l, d x ≤ T) : maxD d l ≤ T := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maxD_cons, max_le_iff]
    exact ⟨h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem exists_mem_maxD {l : List (Fin n)} (h : l ≠ []) : ∃ x ∈ l, d x = maxD d l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    by_cases hl : l = []
    · subst hl
      exact ⟨a, List.mem_cons_self, by simp⟩
    · obtain ⟨x, hx, hxd⟩ := ih hl
      by_cases hle : d a ≤ maxD d l
      · exact ⟨x, List.mem_cons_of_mem _ hx, by simp [hxd, hle]⟩
      · exact ⟨a, List.mem_cons_self, by simp; omega⟩

theorem maxD_append (l l' : List (Fin n)) : maxD d (l ++ l') = max (maxD d l) (maxD d l') := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, max_assoc]

end maxD

theorem sum_fin_getElem {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f l[i] = (l.map f).sum := by
  rw [← List.sum_ofFn]
  simp only [Fin.getElem_fin]
  rw [List.ofFn_getElem_eq_map]

theorem sum_map_singleton_list {α : Type*} (l : List α) :
    (l.map fun a => ({a} : Multiset α)).sum = (l : Multiset α) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, Multiset.singleton_add, Multiset.cons_coe]

theorem sum_map_coe_list {α : Type*} (L : List (List α)) :
    (L.map Multiset.ofList).sum = (L.flatten : Multiset α) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatten_cons, Multiset.coe_add]

theorem filter_fst_eq_map {p : ℕ} (m : Fin p → ℕ) (k : Fin p) :
    (univ.filter fun γ : (Σ k, Fin (m k)) => γ.1 = k) =
      univ.map ⟨Sigma.mk k, sigma_mk_injective⟩ := by
  ext ⟨k', j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro rfl
    exact ⟨j, rfl⟩
  · rintro ⟨j', h⟩
    exact (congrArg Sigma.fst h).symm

/-- The cities of a list of blocks, as landings of the sigma type of their positions. -/
theorem mem_flatten_iff_sigma {n : ℕ} (L : List (List (Fin n))) (y : Fin n) :
    y ∈ L.flatten ↔ ∃ (j : Fin L.length) (i : Fin L[j].length), L[j][i] = y := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hy⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    exact ⟨⟨j, hj⟩, ⟨i, hi⟩, rfl⟩
  · rintro ⟨j, i, rfl⟩
    exact ⟨L[j], List.getElem_mem _, List.getElem_mem _⟩

open Classical in
/-- **The combinatorial core of Theorem 4.10, list form.** Let every plane `k` have a list of
blocks, each a non-empty list of cities (its landings). If, in every class of planes connected
by shared cities, the number of planes with an even number of blocks is even, there is an
admissible partition with one landing per block (`|X_k| = #blocks of k`), with
`δ(X_k) ≤ Σ_γ max_{x ∈ γ} d_x`, and whose landings are, as a multiset, at most all the blocks'
landings. -/
theorem exists_admissible_of_blocks {n p : ℕ} (d : Fin n → ℕ)
    (blocks : Fin p → List (List (Fin n))) (hne : ∀ k, ∀ γ ∈ blocks k, γ ≠ [])
    (hpar : ∀ a, Even #{k | Relation.ReflTransGen
      (fun k k' => ∃ y, y ∈ (blocks k).flatten ∧ y ∈ (blocks k').flatten) a k ∧
        Even (blocks k).length}) :
    ∃ X : Groups n p, Admissible X ∧ (∀ k, (X k).card = (blocks k).length) ∧
      (∀ k, load d (X k) ≤ ((blocks k).map (maxD d)).sum) ∧
      ∑ k, X k ≤ ∑ k, ((blocks k).flatten : Multiset (Fin n)) := by
  -- Blocks and landings as sigma types of positions.
  let Bt := Σ k : Fin p, Fin (blocks k).length
  let Lt := Σ γ : Bt, Fin ((blocks γ.1)[γ.2]).length
  let city : Lt → Fin n := fun e => (blocks e.1.1)[e.1.2][e.2]
  have hne' : ∀ γ : Bt, (blocks γ.1)[γ.2] ≠ [] := fun γ => hne _ _ (List.getElem_mem _)
  have hz : ∀ γ : Bt, ∃ i : Fin ((blocks γ.1)[γ.2]).length,
      d ((blocks γ.1)[γ.2][i]) = maxD d (blocks γ.1)[γ.2] := fun γ => by
    obtain ⟨x, hx, hxd⟩ := exists_mem_maxD d (hne' γ)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨i, hi⟩, hxd⟩
  choose iz hiz using hz
  let D : TriCore.Data n p Lt Bt :=
    { d := d
      city := city
      blk := Sigma.fst
      pl := Sigma.fst
      z := fun γ => ⟨γ, iz γ⟩
      blk_z := fun _ => rfl
      le_z := fun e => by
        show d ((blocks e.1.1)[e.1.2][e.2]) ≤ d ((blocks e.1.1)[e.1.2][iz e.1])
        rw [hiz e.1]
        exact le_maxD d (List.getElem_mem _) }
  have hR : ∀ γ : Bt, D.R γ = maxD d (blocks γ.1)[γ.2] := fun γ => hiz γ
  have hcard : ∀ k, #{γ : Bt | D.pl γ = k} = (blocks k).length := fun k => by
    change #(univ.filter fun γ : Bt => γ.1 = k) = _
    rw [filter_fst_eq_map (fun k => (blocks k).length) k, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hshare : D.Share = fun k k' => ∃ y, y ∈ (blocks k).flatten ∧ y ∈ (blocks k').flatten := by
    funext k k'
    apply propext
    constructor
    · rintro ⟨e, e', rfl, rfl, h⟩
      refine ⟨city e, (mem_flatten_iff_sigma _ _).mpr ⟨e.1.2, e.2, rfl⟩,
        (mem_flatten_iff_sigma _ _).mpr ⟨e'.1.2, e'.2, h.symm⟩⟩
    · rintro ⟨y, hy, hy'⟩
      obtain ⟨j, i, rfl⟩ := (mem_flatten_iff_sigma _ _).mp hy
      obtain ⟨j', i', h'⟩ := (mem_flatten_iff_sigma _ _).mp hy'
      exact ⟨⟨⟨k, j⟩, i⟩, ⟨⟨k', j'⟩, i'⟩, rfl, rfl, h'.symm⟩
  have hpar' : ∀ a, Even #{k | D.Conn a k ∧ Even #{γ | D.pl γ = k}} := fun a => by
    have := hpar a
    simp only [TriCore.Data.Conn, hshare, hcard]
    convert this using 3
  obtain ⟨x, pay, hinj, hcity, hle, hadm⟩ := TriCore.exists_selection D hpar'
  refine ⟨_, hadm, fun k => ?_, fun k => ?_, ?_⟩
  · rw [Multiset.card_map, Finset.card_val, hcard]
  · change ((((univ.filter fun γ : Bt => γ.1 = k).val.map x).map d).sum) ≤ _
    rw [Multiset.map_map, Finset.sum_map_val, filter_fst_eq_map (fun k => (blocks k).length) k,
      Finset.sum_map, ← sum_fin_getElem]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hle ⟨k, j⟩
    rw [hR] at this
    exact this
  · -- The landings: one per block, paid injectively.
    have hsum : ∑ k, (univ.filter fun γ : Bt => D.pl γ = k).val.map x = univ.val.map x := by
      have h₁ : ∀ s : Finset Bt, s.val.map x = ∑ γ ∈ s, ({x γ} : Multiset (Fin n)) := fun s => by
        rw [← Finset.sum_map_val, show (fun γ => ({x γ} : Multiset (Fin n))) =
          (fun a => ({a} : Multiset (Fin n))) ∘ x from rfl, ← Multiset.map_map,
          Multiset.sum_map_singleton]
      simp only [h₁]
      exact Finset.sum_fiberwise univ D.pl fun γ => ({x γ} : Multiset (Fin n))
    have hpay : univ.val.map x ≤ (univ : Finset Lt).val.map city := by
      have : (univ : Finset Bt).val.map x = ((univ : Finset Bt).val.map pay).map city := by
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl fun γ _ => (hcity γ).symm
      rw [this]
      refine Multiset.map_le_map ?_
      have := Finset.map_val ⟨pay, hinj⟩ univ
      simp only [Function.Embedding.coeFn_mk] at this
      rw [← this]
      exact Finset.val_le_iff.mpr (Finset.subset_univ _)
    have hall : (univ : Finset Lt).val.map city = ∑ k, ((blocks k).flatten : Multiset (Fin n)) := by
      rw [← Multiset.sum_map_singleton ((univ : Finset Lt).val.map city), Multiset.map_map,
        Finset.sum_map_val]
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sum_map_coe_list, ← sum_fin_getElem]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← sum_map_singleton_list, ← sum_fin_getElem]
      rfl
    rw [hsum, ← hall]
    exact hpay

end ZenoFront
