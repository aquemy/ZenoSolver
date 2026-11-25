import ZenoFront.Solver
import ZenoFront.Parse

/-!
# `zeno-front`: the verified symmetric solver

`lake exe zeno-front FILE` reads an instance from the header of `FILE` (the lines
`instance n t p`, `d …`, `dbar …` and `c …` of a certificate, `doc/certificate-format.md`; an
optional `zeno-certificate` line first, and anything after `c` ignored) and prints its Pareto
front as `cost makespan` lines by increasing cost, as `zeno front` does.

The front is `ZenoFront.solveFront d c t p`. By `ZenoFront.solveFront_isParetoFront_hub`, it is
the exact Pareto front of the feasible plans when `d = dbar` (S), `1 ≤ p ≤ t`, and for every
table of central flights satisfying the triangles through a hub, in particular (A1)
(`solveFront_isParetoFront`) and (AΔ) (`solveFront_isParetoFront_ATri`). The parser and this
wrapper are not verified: the theorem is about the parsed values.
-/

open ZenoFront Parse

/-- The instance header. -/
def instanceHeader : ParseM (Σ _ : ℕ, ℕ × ℕ × Array ℕ × Array ℕ × Array ℕ) := do
  match ← get with
  | (_, tok :: _) :: rest => if tok == "zeno-certificate" then set rest
  | _ => pure ()
  let (num, head) ← nextLine "instance" (some 4)
  let n ← number num (head.getD 1 "")
  let t ← number num (head.getD 2 "")
  let p ← number num (head.getD 3 "")
  let d ← numbers "d" n
  let dbar ← numbers "dbar" n
  let c ← numbers "c" n
  return ⟨n, t, p, d, dbar, c⟩

def main (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln "usage: zeno-front FILE"
    return 64
  let text ← IO.FS.readFile file
  match (instanceHeader.run (tokenize text)).map Prod.fst with
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1
  | .ok ⟨n, t, p, d, dbar, c⟩ =>
    if !(1 ≤ p && p ≤ t) then
      IO.eprintln "error: the solver needs 1 ≤ p ≤ t"
      return 1
    if d != dbar then
      IO.eprintln "error: the solver needs symmetric durations (d = dbar)"
      return 1
    let front := solveFront (n := n) (fun i => d.getD i.val 0) (fun i => c.getD i.val 0) t p
    for (cost, makespan) in front.reverse do
      IO.println s!"{cost} {makespan}"
    return 0
