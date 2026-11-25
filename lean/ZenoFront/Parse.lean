/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under the license of the ZenoSolver repository.
-/
module

public import ZenoFront.CheckerV2

/-!
# Parser for certificate formats v1 and v2 (untrusted)

Reads the text format of `doc/certificate-format.md` into a `Cert` (v1) or a `Cert2` (v2),
mirroring `readCertificate`
in `src/zeno/certificate.cpp`: blank lines and lines starting with `#` are ignored, tokens are
separated by white space, numbers are non-negative integers, plans, planes and gaps are listed
in order, and nothing may follow `end`. An assumption other than `S`, `A1`, `A1|AD` and `A1-NS`
is rejected.

The parser is **not** part of the verified statement: `Cert.check_sound` is about the `Cert`
value. A wrong parser could make the checker verify a different front than the file's. It is
kept small and only translates numbers and indices (`1`-based in the file, `0`-based in Lean).
-/

@[expose] public section

namespace ZenoFront

namespace Parse

/-- The parser's state: the remaining lines, each with its line number and tokens. -/
abbrev ParseM := StateT (List (ℕ × List String)) (Except String)

/-- Split a text into numbered lines of tokens, dropping blank lines and comments. -/
def tokenize (text : String) : List (ℕ × List String) :=
  let lines := text.splitOn "\n"
  let numbered := lines.zipIdx.map fun (line, i) =>
    (i + 1, ((line.split Char.isWhitespace).toList.map toString).filter fun w => !w.isEmpty)
  numbered.filter fun (_, toks) => match toks with
    | [] => false
    | tok :: _ => !tok.startsWith "#"

/-- The next line, checking its keyword (unless empty) and its number of tokens (if given). -/
def nextLine (keyword : String) (arity : Option ℕ) : ParseM (ℕ × List String) := do
  match ← get with
  | [] => throw s!"certificate: unexpected end of file, expected '{keyword}'"
  | (num, toks) :: rest =>
    set rest
    if keyword != "" && toks.head? != some keyword then
      throw s!"certificate, line {num}: expected '{keyword}', found '{toks.headD ""}'"
    if let some a := arity then
      if toks.length != a then
        throw s!"certificate, line {num}: expected {a} tokens"
    return (num, toks)

/-- A non-negative integer. -/
def number (num : ℕ) (tok : String) : ParseM ℕ :=
  match tok.toNat? with
  | some v => pure v
  | none => throw s!"certificate, line {num}: expected a non-negative integer, found '{tok}'"

/-- A list of `k` numbers following a keyword. -/
def numbers (keyword : String) (k : ℕ) : ParseM (Array ℕ) := do
  let (num, toks) ← nextLine keyword (some (k + 1))
  let vals ← (toks.drop 1).mapM (number num)
  return vals.toArray

/-- A location: `0` is `C_I`, `1..n` the central cities, `n + 1` is `C_G`. -/
def location (n : ℕ) (num v : ℕ) : ParseM (Loc n) :=
  if h0 : v = 0 then pure .ci
  else if h : v ≤ n then pure (.city ⟨v - 1, by omega⟩)
  else if v = n + 1 then pure .cg
  else throw s!"certificate, line {num}: unknown location {v}"

/-- A passenger: `0` is none, `1..t` a passenger. -/
def passenger (t : ℕ) (num v : ℕ) : ParseM (Option (Fin t)) :=
  if h0 : v = 0 then pure none
  else if h : v ≤ t then pure (some ⟨v - 1, by omega⟩)
  else throw s!"certificate, line {num}: unknown passenger {v}"

/-- One leg: `from to depart arrive passenger`. -/
def leg (n t : ℕ) : ParseM (Leg n t) := do
  let (num, toks) ← nextLine "" (some 5)
  let v ← toks.mapM (number num)
  match v with
  | [src, dst, dep, arr, pax] =>
    return ⟨← location n num src, ← location n num dst, dep, arr, ← passenger t num pax⟩
  | _ => throw s!"certificate, line {num}: expected 5 numbers"

/-- One plane: `plane k m` and its `m` legs. -/
def plane (n t : ℕ) (k : ℕ) : ParseM (List (Leg n t)) := do
  let (num, toks) ← nextLine "plane" (some 3)
  if (← number num (toks.getD 1 "")) != k + 1 then
    throw s!"certificate, line {num}: planes must be listed in order"
  let m ← number num (toks.getD 2 "")
  (List.range m).mapM fun _ => leg n t

/-- One plan: `plan i p` and its `p` planes. -/
def plan (n t p : ℕ) (i : ℕ) : ParseM (Plan n t p) := do
  let (num, toks) ← nextLine "plan" (some 3)
  if (← number num (toks.getD 1 "")) != i + 1 then
    throw s!"certificate, line {num}: plans must be listed in order"
  let planes ← number num (toks.getD 2 "")
  if planes != p then
    throw s!"certificate, line {num}: plan {i + 1} has {planes} planes, the instance {p}"
  let legs ← (List.range p).mapM (plane n t)
  let arr := legs.toArray
  return fun k => arr.getD k.val []

/-- One gap: `i relaxed` or `i forest`. -/
def gap (i : ℕ) : ParseM GapKind := do
  let (num, toks) ← nextLine "" (some 2)
  if (← number num (toks.getD 0 "")) != i + 1 then
    throw s!"certificate, line {num}: lower bounds must be listed in order"
  match toks.getD 1 "" with
  | "relaxed" => return .relaxed
  | "forest" => return .forest
  | other => throw s!"certificate, line {num}: unknown lower bound '{other}'"

/-- A signed integer (a Lagrangian multiplier). -/
def signedNumber (num : ℕ) (tok : String) : ParseM ℤ :=
  match tok.toInt? with
  | some v => pure v
  | none => throw s!"certificate, line {num}: expected an integer, found '{tok}'"

/-- A v2 kind without multipliers. -/
def kind2 (num : ℕ) : String → ParseM Kind2
  | "closed" => pure .closed
  | "relaxed" => pure .relaxed
  | "forest" => pure .forest
  | "roles" => pure .roles
  | "balanced" => pure .balanced
  | "search" => pure .search
  | other => throw s!"certificate, line {num}: unknown bound '{other}'"

/-- One v2 gap: `i <kind>`, or `i lagrangian mu_1 … mu_n`. -/
def gap2 (n : ℕ) (i : ℕ) : ParseM Kind2 := do
  let (num, toks) ← nextLine "" none
  if toks.length < 2 then
    throw s!"certificate, line {num}: lower bounds must be listed as '<gap> <kind>'"
  if (← number num (toks.getD 0 "")) != i + 1 then
    throw s!"certificate, line {num}: lower bounds must be listed in order"
  match toks.getD 1 "" with
  | "lagrangian" =>
    if toks.length != n + 2 then
      throw s!"certificate, line {num}: a lagrangian bound lists one multiplier per city"
    return .lagrangian (← (toks.drop 2).mapM (signedNumber num))
  | name =>
    if toks.length != 2 then
      throw s!"certificate, line {num}: unexpected values after '{name}'"
    match ← kind2 num name with
    | .closed => throw s!"certificate, line {num}: unknown lower bound 'closed'"
    | k => return k

/-- A parsed certificate of either version. -/
inductive AnyCert where
  | v1 (C : Cert)
  | v2 (C : Cert2)

/-- The assumptions a certificate may list (`doc/certificate-format.md`). -/
def knownAssumptions : List String := ["S", "A1", "A1|AD", "A1-NS"]

/-- A whole certificate. -/
def anyCert : ParseM AnyCert := do
  let (num, header) ← nextLine "zeno-certificate" (some 2)
  let version := header.getD 1 ""
  if version != "1" && version != "2" then
    throw s!"certificate, line {num}: unsupported version {version}"
  let (num, head) ← nextLine "instance" (some 4)
  let n ← number num (head.getD 1 "")
  let t ← number num (head.getD 2 "")
  let p ← number num (head.getD 3 "")
  let d ← numbers "d" n
  let dbar ← numbers "dbar" n
  let c ← numbers "c" n
  let (num, assume) ← nextLine "assume" none
  for a in assume.drop 1 do
    if !knownAssumptions.contains a then
      throw s!"certificate, line {num}: unknown assumption '{a}'"
  let (num, frontHead) ← nextLine "front" (some 2)
  let r ← number num (frontHead.getD 1 "")
  let front ← (List.range r).mapM fun _ => do
    let (num, toks) ← nextLine "" (some 2)
    return (← number num (toks.getD 0 ""), ← number num (toks.getD 1 ""))
  let fastest ← if version == "2" then do
      let (num, toks) ← nextLine "fastest" (some 2)
      match ← kind2 num (toks.getD 1 "") with
      | .forest => throw s!"certificate, line {num}: unknown fastest bound 'forest'"
      | k => pure k
    else pure .closed
  let plans ← (List.range r).mapM (plan n t p)
  let (num, gapHead) ← nextLine "lower-bounds" (some 2)
  let g ← number num (gapHead.getD 1 "")
  if version == "1" then
    let gaps ← (List.range g).mapM gap
    let _ ← nextLine "end" (some 1)
    if !(← get).isEmpty then throw "certificate: content after 'end'"
    return .v1 { n, t, p
                 d := fun i => d.getD i.val 0
                 dbar := fun i => dbar.getD i.val 0
                 c := fun i => c.getD i.val 0
                 assumptions := assume.drop 1
                 front, plans, gaps }
  else
    let gaps ← (List.range g).mapM (gap2 n)
    let _ ← nextLine "end" (some 1)
    if !(← get).isEmpty then throw "certificate: content after 'end'"
    return .v2 { n, t, p
                 d := fun i => d.getD i.val 0
                 dbar := fun i => dbar.getD i.val 0
                 c := fun i => c.getD i.val 0
                 assumptions := assume.drop 1
                 front, fastest, plans, gaps }

end Parse

/-- Parse a certificate of either version from its text. -/
def parseAnyCert (text : String) : Except String Parse.AnyCert :=
  (Parse.anyCert.run (Parse.tokenize text)).map Prod.fst

/-- Parse a version 1 certificate from its text. -/
def parseCert (text : String) : Except String Cert :=
  match parseAnyCert text with
  | .ok (.v1 C) => .ok C
  | .ok (.v2 _) => .error "certificate: version 2, expected version 1"
  | .error e => .error e

end ZenoFront
