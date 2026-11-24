import ZenoFront.Parse

/-!
# `zeno-check`: the Lean checker for front certificates

`lake exe zeno-check FILE` parses a certificate (format v1 or v2), runs the verified checker
(`ZenoFront.Cert.check` or `ZenoFront.Cert2.check`), and prints

* `accepted: …` (exit code 0) when the checker returns `true`. By `ZenoFront.Cert.check_sound`,
  the listed points of a v1 certificate are then the exact Pareto front of the instance: for every
  table of central flight durations if all gaps are `relaxed`, and for every table satisfying
  (A1) otherwise. By `ZenoFront.Cert2.check_sound`, those of a v2 certificate are the exact front
  for every table;
* `rejected: <reason>` (exit code 1) when the certificate is malformed or an obligation fails.

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
def planReason {n t p : ℕ} (d dbar c : Fin n → ℕ) (i : ℕ) (P : Plan n t p) (x : ℕ × ℕ) :
    Option String :=
  match (List.finRange p).find? (fun k => !planeOK d dbar (P k)) with
  | some k => some s!"plan {i + 1}: plane {k.val + 1} does not fly a route of hub–central \
      flights from C_I to C_G"
  | none =>
    match (List.finRange t).find? (fun π => !paxOK P π) with
    | some π => some s!"plan {i + 1}: passenger {π.val + 1} cannot follow its legs from C_I to C_G"
    | none =>
      if planCost c P != x.1 || planMakespan P != x.2 then
        some s!"plan {i + 1} has cost {planCost c P} and makespan {planMakespan P}, \
          not {x.1} and {x.2}"
      else none

/-- The failed obligations. -/
def reasons (C : Cert) : Array String := Id.run do
  let mut errs : Array String := #[]
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
    if let some why := planReason C.d C.dbar C.c i P x then
      errs := errs.push why
  if !C.firstOK then
    errs := errs.push s!"the fastest point's makespan is not 2 * d_min * ceil(s / p) = \
      {2 * minOf C.d * ((C.s + C.p - 1) / C.p)}"
  if !C.lastOK then
    errs := errs.push s!"the cheapest point's cost is not s * c_min = {C.s * minOf C.c}"
  if errs.isEmpty then
    let scale := durationScale C.d
    let Tmax := (C.front.map fun x => (x.2 - 1) / 2 / scale).foldr max 0
    let dArr := Array.ofFn (n := C.n) fun i => C.d i / scale
    let dS : Fin C.n → ℕ := fun i => dArr.getD i 0
    let bound := C.boundWith scale Tmax dS (oneplaneTable dS C.c Tmax C.s)
    for (((x, y), g), i) in ((C.front.zip C.front.tail).zip C.gaps).zipIdx do
      match g with
      | .forest =>
        if !C.assumptions.contains "A1" then
          errs := errs.push s!"gap {i + 1} uses the forest bound, which needs assumption A1"
        else
          let b := bound .forest y.2
          if !decide ((x.1 : WithTop ℕ) ≤ b) then
            errs := errs.push s!"gap {i + 1}: the forest bound {showBound b} is below the cost \
              {x.1}"
      | .relaxed =>
        let b := bound .relaxed y.2
        if !decide ((x.1 : WithTop ℕ) ≤ b) then
          errs := errs.push s!"gap {i + 1}: the relaxed bound {showBound b} is below the cost {x.1}"
  return errs

/-- The failed obligations of a v2 certificate. -/
def reasons2 (C : Cert2) : Array String := Id.run do
  let mut errs : Array String := #[]
  if !C.headerOK then
    errs := errs.push "the header needs 1 ≤ n, 1 ≤ p ≤ t, and assumption S only for symmetric \
      durations"
  if C.front.isEmpty then
    errs := errs.push "the front is empty"
  if !strictlyMonotone C.front then
    errs := errs.push "the points are not strictly increasing in makespan and decreasing in cost"
  if C.plans.length != C.front.length || C.gaps.length + 1 != C.front.length then
    errs := errs.push "one plan per point and one lower bound per gap are required"
  for ((P, x), i) in (C.plans.zip C.front).zipIdx do
    if let some why := planReason C.d C.dbar C.c i P x then
      errs := errs.push why
  if !C.lastOK then
    errs := errs.push s!"the cheapest point's cost is not s * c_min = {C.s * minOf C.c}"
  if errs.isEmpty then
    let scale := durationScale C.weight
    let Tmax := C.maxLevel scale
    let wArr := Array.ofFn (n := C.n) fun i => C.weight i / scale
    let wS : Fin C.n → ℕ := fun i => wArr.getD i 0
    let bound := C.boundWith scale Tmax (oneplaneTable wS C.c Tmax C.s)
    if !C.fastestOK bound then
      errs := errs.push (match C.fastest with
        | .closed => "fastest point: the closed form needs symmetric durations and makespan \
            2 * d_min * ceil(s / p)"
        | .relaxed => "fastest point: the relaxed bound does not rule out faster plans"
        | k => s!"fastest point: the {k.name} bound is not verified by the Lean checker")
    for (((x, y), g), i) in ((C.front.zip C.front.tail).zip C.gaps).zipIdx do
      match g with
      | .relaxed =>
        let b := bound .relaxed y.2
        if !decide ((x.1 : WithTop ℕ) ≤ b) then
          errs := errs.push s!"gap {i + 1}: the relaxed bound {showBound b} is below the cost {x.1}"
      | k => errs := errs.push s!"gap {i + 1}: the {k.name} bound is not verified by the Lean \
          checker"
  return errs

def main (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln "usage: zeno-check FILE"
    return 64
  let text ← IO.FS.readFile file
  match parseAnyCert text with
  | .error e =>
    IO.println s!"rejected: {e}"
    return 1
  | .ok (.v2 C) =>
    if C.check then
      IO.println s!"accepted: the {C.front.length} points are the Pareto front (version 2, \
        fastest {C.fastest.name}, all gaps relaxed: for every central flight table; \
        ZenoFront.Cert2.check_sound)"
      return 0
    IO.println s!"rejected: {(reasons2 C).getD 0 "an obligation fails"}"
    return 1
  | .ok (.v1 C) =>
    if C.check then
      let forest := (C.gaps.filter (· = .forest)).length
      let scope := if forest = 0 then "all gaps relaxed: for every central flight table"
        else s!"{forest} forest gap(s): for every central flight table satisfying A1"
      IO.println s!"accepted: the {C.front.length} points are the Pareto front ({scope}; \
        ZenoFront.Cert.check_sound)"
      return 0
    IO.println s!"rejected: {(reasons C).getD 0 "an obligation fails"}"
    return 1
