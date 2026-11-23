import ZenoFront.Parse

/-!
# `zeno-check`: the Lean checker for front certificates

`lake exe zeno-check FILE` parses a certificate (format v1), runs the verified checker
`ZenoFront.Cert.check`, and prints

* `accepted: …` (exit code 0) when `check` returns `true`: by `ZenoFront.Cert.check_sound`, the
  listed points are then the exact Pareto front of the instance;
* `rejected: <reason>` (exit code 1) when the certificate is malformed or an obligation fails;
* `not supported: <reason>` (exit code 2) when every obligation the checker supports holds but a
  gap names the `forest` bound, which needs the converse theorem (not formalised yet).

Only the `accepted` verdict is backed by the theorem; the reasons are diagnostics recomputed
here, outside the verified function.
-/

open ZenoFront

/-- Print an element of `WithTop ℕ`. -/
def showBound (b : WithTop ℕ) : String :=
  match (b : Option ℕ) with
  | some v => toString v
  | none => "∞"

/-- Why a plan is rejected. -/
def planReason (C : Cert) (i : ℕ) (P : Plan C.n C.t C.p) (x : ℕ × ℕ) : Option String :=
  match (List.finRange C.p).find? (fun k => !planeOK C.d C.dbar (P k)) with
  | some k => some s!"plan {i + 1}: plane {k.val + 1} does not fly a route of hub–central \
      flights from C_I to C_G"
  | none =>
    match (List.finRange C.t).find? (fun π => !paxOK P π) with
    | some π => some s!"plan {i + 1}: passenger {π.val + 1} cannot follow its legs from C_I to C_G"
    | none =>
      if planCost C.c P != x.1 || planMakespan P != x.2 then
        some s!"plan {i + 1} has cost {planCost C.c P} and makespan {planMakespan P}, \
          not {x.1} and {x.2}"
      else none

/-- The failed obligations, and the unsupported ones (`forest` gaps). -/
def reasons (C : Cert) : Array String × Array String := Id.run do
  let mut errs : Array String := #[]
  let mut unsupported : Array String := #[]
  if !C.headerOK then
    errs := errs.push "the header needs 1 ≤ n, 1 ≤ p ≤ t, symmetric durations (d = dbar) and \
      assumption S"
  if C.front.isEmpty then
    errs := errs.push "the front is empty"
  if !strictlyMonotone C.front then
    errs := errs.push "the points are not strictly increasing in makespan and decreasing in cost"
  if C.plans.length != C.front.length || C.gaps.length + 1 != C.front.length then
    errs := errs.push "one plan per point and one lower bound per gap are required"
  for ((P, x), i) in (C.plans.zip C.front).zipIdx do
    if let some why := planReason C i P x then
      errs := errs.push why
  if !C.firstOK then
    errs := errs.push s!"the fastest point's makespan is not 2 * d_min * ceil(s / p) = \
      {2 * minOf C.d * ((C.s + C.p - 1) / C.p)}"
  if !C.lastOK then
    errs := errs.push s!"the cheapest point's cost is not s * c_min = {C.s * minOf C.c}"
  if errs.isEmpty then
    let table := C.table
    for (((x, y), g), i) in ((C.front.zip C.front.tail).zip C.gaps).zipIdx do
      match g with
      | .forest =>
        unsupported := unsupported.push s!"gap {i + 1} uses the forest bound, which the Lean \
          checker does not support yet"
      | .relaxed =>
        let b := C.gapBound table y.2
        if !decide ((x.1 : WithTop ℕ) ≤ b) then
          errs := errs.push s!"gap {i + 1}: the relaxed bound {showBound b} is below the cost {x.1}"
  return (errs, unsupported)

def main (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln "usage: zeno-check FILE"
    return 64
  let text ← IO.FS.readFile file
  match parseCert text with
  | .error e =>
    IO.println s!"rejected: {e}"
    return 1
  | .ok C =>
    if C.check then
      IO.println s!"accepted: the {C.front.length} points are the Pareto front \
        (all gaps relaxed; ZenoFront.Cert.check_sound)"
      return 0
    let (errs, unsupported) := reasons C
    if errs.isEmpty && !unsupported.isEmpty then
      IO.println s!"not supported: {unsupported[0]!} ({unsupported.size} forest gap(s))"
      return 2
    IO.println s!"rejected: {errs.getD 0 "an obligation fails"}"
    return 1
