/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.Checker

/-!
# Kernel-checked fronts

Two certificates checked by the Lean **kernel** alone (`decide +kernel`, no compiled code), so
with `Cert.check_sound_relaxed` they give fully kernel-checked statements about concrete
instances.

* `lptCounterexample`: the instance `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2` of §4 of
  the theory note, on which the papers' greedy misses the point `(260, 60)`. Its exact front has
  six points (`tests/golden/data/lpt-counterexample.dat`).
* `fourPlanes`: `n = 3`, `t = p = 4`; one point, `(248, 88)`.

The literals mirror the files in `lean/test/certificates/accepted/` (cities and passengers
numbered from `0`).
-/

@[expose] public section

namespace ZenoFront

namespace Examples

/-- The certificate of the LPT counterexample (`golden-lpt-counterexample.cert`). -/
def lptCounterexample : Cert where
  n := 2
  t := 5
  p := 2
  d := ![6, 10]
  dbar := ![6, 10]
  c := ![40, 20]
  assumptions := ["S"]
  front := [(320, 48), (280, 56), (260, 60), (240, 64), (200, 72), (160, 80)]
  plans := [
    ![[⟨.ci, .city 0, 0, 6, some 0⟩, ⟨.city 0, .ci, 6, 12, none⟩,
        ⟨.ci, .city 0, 12, 18, some 1⟩, ⟨.city 0, .cg, 18, 24, some 1⟩,
        ⟨.cg, .city 0, 24, 30, none⟩, ⟨.city 0, .ci, 30, 36, none⟩,
        ⟨.ci, .city 0, 36, 42, some 2⟩, ⟨.city 0, .cg, 42, 48, some 2⟩],
      [⟨.ci, .city 0, 0, 6, some 3⟩, ⟨.city 0, .cg, 6, 12, some 3⟩,
        ⟨.cg, .city 0, 12, 18, none⟩, ⟨.city 0, .ci, 18, 24, none⟩,
        ⟨.ci, .city 0, 24, 30, some 4⟩, ⟨.city 0, .cg, 30, 36, some 4⟩,
        ⟨.cg, .city 0, 36, 42, none⟩, ⟨.city 0, .cg, 42, 48, some 0⟩]],
    ![[⟨.ci, .city 0, 0, 6, some 0⟩, ⟨.city 0, .ci, 6, 12, none⟩,
        ⟨.ci, .city 0, 12, 18, some 1⟩, ⟨.city 0, .cg, 18, 24, some 1⟩,
        ⟨.cg, .city 0, 24, 30, none⟩, ⟨.city 0, .ci, 30, 36, none⟩,
        ⟨.ci, .city 1, 36, 46, some 2⟩, ⟨.city 1, .cg, 46, 56, some 2⟩],
      [⟨.ci, .city 0, 0, 6, some 3⟩, ⟨.city 0, .cg, 6, 12, some 3⟩,
        ⟨.cg, .city 0, 12, 18, none⟩, ⟨.city 0, .ci, 18, 24, none⟩,
        ⟨.ci, .city 1, 24, 34, some 4⟩, ⟨.city 1, .cg, 34, 44, some 4⟩,
        ⟨.cg, .city 0, 44, 50, none⟩, ⟨.city 0, .cg, 50, 56, some 0⟩]],
    ![[⟨.ci, .city 1, 0, 10, some 0⟩, ⟨.city 1, .cg, 10, 20, some 0⟩,
        ⟨.cg, .city 1, 20, 30, none⟩, ⟨.city 1, .ci, 30, 40, none⟩,
        ⟨.ci, .city 1, 40, 50, some 1⟩, ⟨.city 1, .cg, 50, 60, some 1⟩],
      [⟨.ci, .city 0, 0, 6, some 2⟩, ⟨.city 0, .cg, 6, 12, some 2⟩,
        ⟨.cg, .city 0, 12, 18, none⟩, ⟨.city 0, .ci, 18, 24, none⟩,
        ⟨.ci, .city 0, 24, 30, some 3⟩, ⟨.city 0, .cg, 30, 36, some 3⟩,
        ⟨.cg, .city 0, 36, 42, none⟩, ⟨.city 0, .ci, 42, 48, none⟩,
        ⟨.ci, .city 0, 48, 54, some 4⟩, ⟨.city 0, .cg, 54, 60, some 4⟩]],
    ![[⟨.ci, .city 0, 0, 6, some 0⟩, ⟨.city 0, .ci, 6, 12, none⟩,
        ⟨.ci, .city 0, 12, 18, some 1⟩, ⟨.city 0, .cg, 18, 24, some 1⟩,
        ⟨.cg, .city 1, 24, 34, none⟩, ⟨.city 1, .ci, 34, 44, none⟩,
        ⟨.ci, .city 1, 44, 54, some 2⟩, ⟨.city 1, .cg, 54, 64, some 2⟩],
      [⟨.ci, .city 0, 0, 6, some 3⟩, ⟨.city 0, .cg, 6, 12, some 3⟩,
        ⟨.cg, .city 1, 12, 22, none⟩, ⟨.city 1, .ci, 22, 32, none⟩,
        ⟨.ci, .city 1, 32, 42, some 4⟩, ⟨.city 1, .cg, 42, 52, some 4⟩,
        ⟨.cg, .city 0, 52, 58, none⟩, ⟨.city 0, .cg, 58, 64, some 0⟩]],
    ![[⟨.ci, .city 0, 0, 6, some 0⟩, ⟨.city 0, .ci, 6, 12, none⟩,
        ⟨.ci, .city 1, 12, 22, some 1⟩, ⟨.city 1, .cg, 22, 32, some 1⟩,
        ⟨.cg, .city 1, 32, 42, none⟩, ⟨.city 1, .ci, 42, 52, none⟩,
        ⟨.ci, .city 1, 52, 62, some 2⟩, ⟨.city 1, .cg, 62, 72, some 2⟩],
      [⟨.ci, .city 1, 0, 10, some 3⟩, ⟨.city 1, .cg, 10, 20, some 3⟩,
        ⟨.cg, .city 1, 20, 30, none⟩, ⟨.city 1, .ci, 30, 40, none⟩,
        ⟨.ci, .city 1, 40, 50, some 4⟩, ⟨.city 1, .cg, 50, 60, some 4⟩,
        ⟨.cg, .city 0, 60, 66, none⟩, ⟨.city 0, .cg, 66, 72, some 0⟩]],
    ![[⟨.ci, .city 1, 0, 10, some 0⟩, ⟨.city 1, .ci, 10, 20, none⟩,
        ⟨.ci, .city 1, 20, 30, some 1⟩, ⟨.city 1, .cg, 30, 40, some 1⟩,
        ⟨.cg, .city 1, 40, 50, none⟩, ⟨.city 1, .ci, 50, 60, none⟩,
        ⟨.ci, .city 1, 60, 70, some 2⟩, ⟨.city 1, .cg, 70, 80, some 2⟩],
      [⟨.ci, .city 1, 0, 10, some 3⟩, ⟨.city 1, .cg, 10, 20, some 3⟩,
        ⟨.cg, .city 1, 20, 30, none⟩, ⟨.city 1, .ci, 30, 40, none⟩,
        ⟨.ci, .city 1, 40, 50, some 4⟩, ⟨.city 1, .cg, 50, 60, some 4⟩,
        ⟨.cg, .city 1, 60, 70, none⟩, ⟨.city 1, .cg, 70, 80, some 0⟩]]]
  gaps := [.relaxed, .relaxed, .relaxed, .relaxed, .relaxed]

set_option maxRecDepth 100000 in
/-- The kernel accepts the LPT counterexample's certificate. -/
theorem lptCounterexample_check : lptCounterexample.check = true := by decide +kernel

/-- **The exact front of the LPT counterexample**, checked by the kernel: for every table of
central flight durations, the Pareto front of `d = (6, 10)`, `c = (40, 20)`, `t = 5`, `p = 2`
is `(320, 48), (280, 56), (260, 60), (240, 64), (200, 72), (160, 80)`. In particular the point
`(260, 60)`, which the papers' greedy misses, is on the front. -/
theorem lptCounterexample_front (dc : Fin 2 → Fin 2 → ℕ) :
    IsParetoFront (achievable ⟨![6, 10], ![6, 10], dc⟩ ![40, 20] 5 2)
      [(320, 48), (280, 56), (260, 60), (240, 64), (200, 72), (160, 80)] :=
  lptCounterexample.check_sound_relaxed lptCounterexample_check (by decide) dc

/-- A one-point certificate (`relaxed-r100.cert`). -/
def fourPlanes : Cert where
  n := 3
  t := 4
  p := 4
  d := ![44, 74, 76]
  dbar := ![44, 74, 76]
  c := ![62, 82, 63]
  assumptions := ["S"]
  front := [(248, 88)]
  plans := [fun k => [⟨.ci, .city 0, 0, 44, some k⟩, ⟨.city 0, .cg, 44, 88, some k⟩]]
  gaps := []

set_option maxRecDepth 10000 in
theorem fourPlanes_check : fourPlanes.check = true := by decide +kernel

end Examples

end ZenoFront
