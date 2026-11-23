import ZenoFront

/-!
# Axiom audit for `ZenoFront`

Run with `lake env lean scripts/CheckAxioms.lean` from `lean/`. It fails (non-zero exit) if any
declaration of a `ZenoFront` module depends on an axiom other than the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). In particular it rejects `sorryAx` (a `sorry`
anywhere in the dependency chain) and `Lean.ofReduceBool` (`native_decide`), so every theorem of
the library is checked by the kernel alone.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`ZenoFront).isPrefixOf mod do continue
    checked := checked + 1
    let axioms ← liftCoreM <| collectAxioms name
    let extra := axioms.filter (· ∉ allowedAxioms)
    unless extra.isEmpty do bad := bad.push (name, extra)
  if checked == 0 then
    throwError "no ZenoFront declaration found: is the library built?"
  unless bad.isEmpty do
    let lines := bad.toList.map fun (n, axs) => s!"  {n}: {axs.toList}"
    throwError (s!"{bad.size} declaration(s) use non-standard axioms:\n" ++
      String.intercalate "\n" lines)
  logInfo m!"axiom check passed: {checked} ZenoFront declarations, axioms ⊆ {allowedAxioms}"
