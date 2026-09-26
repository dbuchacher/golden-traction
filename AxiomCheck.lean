import Golden

/-!
# Every declaration uses only the standard axioms

Run with `lake env lean AxiomCheck.lean` after `lake build`. It walks every declaration in the `Golden`
module and fails if any depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
`sorry` is the axiom `sorryAx` and `native_decide` is `Lean.ofReduceBool`, so either would fail it.
Adapted from cott-lean's own check.
-/

open Lean Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#check_axioms_in " mod:ident : command => do
  let env ← getEnv
  let some i := env.header.moduleNames.idxOf? mod.getId | throwError "module {mod.getId} not loaded"
  let mut decls : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for c in env.header.moduleData[i]!.constNames do
    decls := decls + 1
    let axs ← collectAxioms c
    let extra := axs.filter (· ∉ standardAxioms)
    unless extra.isEmpty do bad := bad.push (c, extra)
  unless bad.isEmpty do
    throwError m!"{bad.size} declarations use a non-standard axiom: " ++
      m!"{bad.toList.map fun (c, axs) => m!"{c}: {axs.toList}"}"
  logInfo m!"{decls} declarations in {mod.getId}, all on the standard axioms"

#check_axioms_in Golden
