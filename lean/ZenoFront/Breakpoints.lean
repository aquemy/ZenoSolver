/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Data.List.Pairwise

/-!
# Breakpoints of a non-increasing function

The front is read off the breakpoints of `E`, the levels where it drops (`Solver.lean`).

* `scanFront E T₀ k prev` visits the levels `T₀, …, T₀ + k − 1` and keeps `(E(T), 2T)` whenever
  `E(T)` is below the last kept value. `mem_scanFront` characterises its points and
  `scanFront_pairwise` orders them. It evaluates `E` at every level.
* `splitFront E a (E a) b (E b)` finds the same points in `(a, b]` by splitting intervals at their
  midpoint as long as `E` drops on them, as `zeno --levels search` does. With `r` breakpoints it
  evaluates `E` at `O(r log(b − a))` levels. For `E` non-increasing on `[a, b]` it is the scan
  (`splitFront_eq`, by `scanFront_append`). `breakpoints E a b` adds the level `a`
  (`breakpoints_eq_scanFront`).
-/

@[expose] public section

namespace ZenoFront

/-- The scan of the levels `T₀, …, T₀ + k − 1`: `(E(T), 2T)` is kept when `E(T)` is below the
last kept value `prev`. -/
def scanFront (E : ℕ → WithTop ℕ) : ℕ → ℕ → WithTop ℕ → List (ℕ × ℕ)
  | _, 0, _ => []
  | T, k + 1, prev =>
    if E T < prev then ((E T).untopD 0, 2 * T) :: scanFront E (T + 1) k (E T)
    else scanFront E (T + 1) k prev

theorem mem_scanFront (E : ℕ → WithTop ℕ) : ∀ (T₀ k : ℕ) (prev : WithTop ℕ) (C M : ℕ),
    (C, M) ∈ scanFront E T₀ k prev ↔ ∃ T, T₀ ≤ T ∧ T < T₀ + k ∧ M = 2 * T ∧ E T = C ∧
      (C : WithTop ℕ) < prev ∧ ∀ T', T₀ ≤ T' → T' < T → (C : WithTop ℕ) < E T'
  | T₀, 0, prev, C, M => by simp [scanFront]; omega
  | T₀, k + 1, prev, C, M => by
    simp only [scanFront]
    split_ifs with hlt
    · rw [List.mem_cons, mem_scanFront E (T₀ + 1) k (E T₀) C M]
      obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have he' : ((e : ℕ) : WithTop ℕ) = E T₀ := he
      have hu : (E T₀).untopD 0 = e := by rw [← he]; rfl
      rw [hu]
      constructor
      · rintro (h | ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩)
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨T₀, le_rfl, by omega, rfl, he'.symm, ?_, fun T' h₁ h₂ => by omega⟩
          rw [he']
          exact hlt
        · refine ⟨T, by omega, by omega, h₃, h₄, h₅.trans hlt, fun T' h₇ h₈ => ?_⟩
          rcases Nat.eq_or_lt_of_le h₇ with rfl | h₇
          · exact h₅
          · exact h₆ T' h₇ h₈
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · left
          have : e = C := by exact_mod_cast he'.trans h₄
          rw [this, h₃]
        · right
          exact ⟨T, h₁, by omega, h₃, h₄, h₆ T₀ le_rfl h₁, fun T' h₇ h₈ => h₆ T' (by omega) h₈⟩
    · rw [mem_scanFront E (T₀ + 1) k prev C M]
      push Not at hlt
      constructor
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        refine ⟨T, by omega, by omega, h₃, h₄, h₅, fun T' h₇ h₈ => ?_⟩
        rcases Nat.eq_or_lt_of_le h₇ with rfl | h₇
        · exact h₅.trans_le hlt
        · exact h₆ T' h₇ h₈
      · rintro ⟨T, h₁, h₂, h₃, h₄, h₅, h₆⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · exact absurd (h₄ ▸ h₅) (not_lt.mpr hlt)
        · exact ⟨T, h₁, by omega, h₃, h₄, h₅, fun T' h₇ h₈ => h₆ T' (by omega) h₈⟩

theorem scanFront_pairwise (E : ℕ → WithTop ℕ) : ∀ (T₀ k : ℕ) (prev : WithTop ℕ),
    (∀ x ∈ scanFront E T₀ k prev, 2 * T₀ ≤ x.2 ∧ (x.1 : WithTop ℕ) < prev) ∧
      (scanFront E T₀ k prev).Pairwise fun a b => a.2 < b.2 ∧ b.1 < a.1
  | T₀, 0, prev => by simp [scanFront]
  | T₀, k + 1, prev => by
    obtain ⟨ih₁, ih₂⟩ := scanFront_pairwise E (T₀ + 1) k (E T₀)
    obtain ⟨ih₁', ih₂'⟩ := scanFront_pairwise E (T₀ + 1) k prev
    simp only [scanFront]
    split_ifs with hlt
    · obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have he' : ((e : ℕ) : WithTop ℕ) = E T₀ := he
      have hu : (E T₀).untopD 0 = e := by rw [← he]; rfl
      rw [hu]
      refine ⟨fun x hx => ?_, List.Pairwise.cons (fun b hb => ?_) ih₂⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨le_rfl, ?_⟩
          show ((e : ℕ) : WithTop ℕ) < prev
          rw [he']
          exact hlt
        · have := ih₁ x hx
          exact ⟨by omega, this.2.trans hlt⟩
      · have := ih₁ b hb
        rw [← he'] at this
        exact ⟨by simp only; omega, show b.1 < e from WithTop.coe_lt_coe.mp this.2⟩
    · exact ⟨fun x hx => by have := ih₁' x hx; exact ⟨by omega, this.2⟩, ih₂'⟩

theorem scanFront_congr {E E' : ℕ → WithTop ℕ} : ∀ (T₀ k : ℕ) (prev : WithTop ℕ),
    (∀ T, T₀ ≤ T → T < T₀ + k → E T = E' T) → scanFront E T₀ k prev = scanFront E' T₀ k prev
  | _, 0, _, _ => rfl
  | T₀, k + 1, prev, h => by
    simp only [scanFront]
    rw [h T₀ le_rfl (by omega),
      scanFront_congr (T₀ + 1) k (E' T₀) fun T h₁ h₂ => h T (by omega) (by omega),
      scanFront_congr (T₀ + 1) k prev fun T h₁ h₂ => h T (by omega) (by omega)]

/-! ### Skipping levels -/

/-- Levels where `E` is not below `prev` are skipped. -/
theorem scanFront_skip (E : ℕ → WithTop ℕ) : ∀ (j a k : ℕ) (prev : WithTop ℕ),
    (∀ T, a ≤ T → T < a + j → ¬ E T < prev) →
      scanFront E a (j + k) prev = scanFront E (a + j) k prev
  | 0, a, k, prev, _ => by simp
  | j + 1, a, k, prev, h => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [scanFront, ite_eq_right (h a le_rfl (by omega))]
    rw [scanFront_skip E j (a + 1) k prev fun T h₁ h₂ => h T (by omega) (by omega),
      show a + 1 + j = a + (j + 1) by omega]

theorem scanFront_nil_of_ge (E : ℕ → WithTop ℕ) (a k : ℕ) (prev : WithTop ℕ)
    (h : ∀ T, a ≤ T → T < a + k → ¬ E T < prev) : scanFront E a k prev = [] := by
  have := scanFront_skip E k a 0 prev h
  rw [Nat.add_zero] at this
  rw [this]
  rfl

/-! ### Splitting intervals -/

/-- For `E` non-increasing, the scan from `a + 1` below `E a` splits at any level: the second
part starts below `E (a + j)`. -/
theorem scanFront_append (E : ℕ → WithTop ℕ) (b : ℕ) : ∀ (j a k : ℕ), a + j + k ≤ b →
    (∀ T T', a ≤ T → T ≤ T' → T' ≤ b → E T' ≤ E T) →
      scanFront E (a + 1) (j + k) (E a) =
        scanFront E (a + 1) j (E a) ++ scanFront E (a + 1 + j) k (E (a + j))
  | 0, a, k, _, _ => by simp [scanFront]
  | j + 1, a, k, hb, hE => by
    have ih := scanFront_append E b j (a + 1) k (by omega)
      fun T T' h₁ h₂ h₃ => hE T T' (by omega) h₂ h₃
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [scanFront]
    split_ifs with hlt
    · rw [ih, show a + 1 + 1 + j = a + 1 + (j + 1) by omega, show a + 1 + j = a + (j + 1) by omega]
      rfl
    · have heq : E (a + 1) = E a :=
        le_antisymm (hE a (a + 1) le_rfl (by omega) (by omega)) (not_lt.mp hlt)
      rw [← heq, ih, show a + 1 + 1 + j = a + 1 + (j + 1) by omega,
        show a + 1 + j = a + (j + 1) by omega]

/-- The breakpoints of `E` in `(a, b]`, given `ea = E a` and `eb = E b`: `[]` if `E` does not
drop on the interval, the level `b` if it is `a + 1`, and otherwise the two halves split at the
midpoint. With `r` breakpoints this evaluates `E` at `O(r log(b − a))` levels, as
`zeno --levels search` does. -/
def splitFront (E : ℕ → WithTop ℕ) (a : ℕ) (ea : WithTop ℕ) (b : ℕ) (eb : WithTop ℕ) :
    List (ℕ × ℕ) :=
  if _h : b ≤ a then []
  else if eb < ea then
    if _h' : b = a + 1 then [(eb.untopD 0, 2 * b)]
    else
      let m := (a + b) / 2
      let em := E m
      splitFront E a ea m em ++ splitFront E m em b eb
  else []
termination_by b - a
decreasing_by all_goals omega

/-- **Splitting finds the same breakpoints as the scan**, for `E` non-increasing on `[a, b]`. -/
theorem splitFront_eq (E : ℕ → WithTop ℕ) : ∀ (k a b : ℕ), b - a = k →
    (∀ T T', a ≤ T → T ≤ T' → T' ≤ b → E T' ≤ E T) →
      splitFront E a (E a) b (E b) = scanFront E (a + 1) (b - a) (E a) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a b hk hE
    rw [splitFront]
    by_cases h₁ : b ≤ a
    · rw [dite_eq_left h₁, show b - a = 0 by omega]
      rfl
    rw [dite_eq_right h₁]
    by_cases h₂ : E b < E a
    · rw [ite_eq_left h₂]
      by_cases h₃ : b = a + 1
      · rw [dite_eq_left h₃]
        subst h₃
        rw [show a + 1 - a = 0 + 1 by omega]
        simp only [scanFront, ite_eq_left h₂]
      · rw [dite_eq_right h₃]
        set m := (a + b) / 2 with hm
        dsimp only
        rw [ih (m - a) (by omega) a m rfl fun T T' h₄ h₅ h₆ => hE T T' h₄ h₅ (by omega),
          ih (b - m) (by omega) m b rfl fun T T' h₄ h₅ h₆ => hE T T' (by omega) h₅ h₆,
          show b - a = (m - a) + (b - m) by omega,
          scanFront_append E b (m - a) a (b - m) (by omega) hE, show a + (m - a) = m by omega,
          show a + 1 + (m - a) = m + 1 by omega]
    · rw [ite_eq_right h₂]
      refine (scanFront_nil_of_ge E (a + 1) (b - a) (E a) fun T h₄ h₅ h₆ => h₂ ?_).symm
      exact lt_of_le_of_lt (hE T b (by omega) (by omega) le_rfl) h₆

/-- The breakpoints of `E` on `[a, b]`: the level `a` if `E a` is finite, then `splitFront`. -/
def breakpoints (E : ℕ → WithTop ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  let ea := E a
  (if ea < ⊤ then [(ea.untopD 0, 2 * a)] else []) ++ splitFront E a ea b (E b)

/-- **The breakpoints are the scan**, for `E` non-increasing on `[a, b]`, `a ≤ b`. -/
theorem breakpoints_eq_scanFront (E : ℕ → WithTop ℕ) {a b : ℕ} (hab : a ≤ b)
    (hE : ∀ T T', a ≤ T → T ≤ T' → T' ≤ b → E T' ≤ E T) :
    breakpoints E a b = scanFront E a (b + 1 - a) ⊤ := by
  dsimp only [breakpoints]
  rw [splitFront_eq E (b - a) a b rfl hE, show b + 1 - a = (b - a) + 1 by omega]
  simp only [scanFront]
  split_ifs with h
  · rfl
  · rw [not_lt_top_iff.mp h]
    rfl

end ZenoFront
