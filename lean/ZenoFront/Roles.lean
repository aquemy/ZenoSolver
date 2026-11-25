/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Admissible

/-!
# Role configurations

A *role configuration* gives every plane `k` three multisets of landings:

* `drop k` (`D_k`): drop-off halves, `C_I → i → C_I` carrying a passenger to `i`;
* `pick k` (`P_k`): pick-up halves, `C_G → i → C_G` carrying a passenger from `i`;
* `cross k` (`Cr_k`): crossings `C_I → i → C_G` or `C_G → i → C_I`, an odd number of them
  (every plane makes one more crossing towards `C_G` than back, Lemma 2.1 of the note);

and every city receives as many drop-offs as pick-ups: `Σ_k D_k = Σ_k P_k`.

This is the abstraction of a plan used by the non-symmetric results: every feasible plan gives
one under (A1-NS) (Theorem 6.1, `Feasible.exists_roleConfig_of_domination`, from Theorem 6.9),
and the bounds of the v2 checker are lower bounds on the cost of role configurations. Its
grouping is `X_k = D_k + P_k + Cr_k`.

## Main results

* `ZenoFront.RoleConfig`, `ZenoFront.RoleConfig.groups`: role configurations and their groupings.
* `ZenoFront.IsParityWitness.val_le`: the cities of a parity witness at a plane lie in its group.
-/

@[expose] public section

namespace ZenoFront

open Finset

variable {n p : ℕ}

/-- A role configuration: per plane, drop-off halves, pick-up halves and an odd number of
crossings, with as many drop-offs as pick-ups at every city. -/
structure RoleConfig (n p : ℕ) where
  /-- Drop-off halves `D_k` of each plane. -/
  drop : Fin p → Multiset (Fin n)
  /-- Pick-up halves `P_k` of each plane. -/
  pick : Fin p → Multiset (Fin n)
  /-- Crossings `Cr_k` of each plane. -/
  cross : Fin p → Multiset (Fin n)
  odd_card_cross : ∀ k, Odd (cross k).card
  sum_drop_eq_sum_pick : ∑ k, drop k = ∑ k, pick k

namespace RoleConfig

variable (R : RoleConfig n p)

/-- The grouping of a role configuration, `X_k = D_k + P_k + Cr_k`. -/
def groups : Groups n p := fun k => R.drop k + R.pick k + R.cross k

theorem card_groups (k : Fin p) :
    (R.groups k).card = (R.drop k).card + (R.pick k).card + (R.cross k).card := by
  simp [groups]

end RoleConfig

namespace IsParityWitness

variable {X : Groups n p} {h : Fin p → Finset (Fin n)}

theorem val_le (hw : IsParityWitness X h) (k : Fin p) : (h k).val ≤ X k := by
  rw [Multiset.le_iff_subset (h k).nodup]
  intro i hi
  simpa using hw.subset k hi

end IsParityWitness

end ZenoFront
