import GFNBounds

/-!
# The axiom sweep

`GFNBounds/Audit.lean` lists declarations by hand under `#print axioms`; a declaration left off
that list is not checked. This script sweeps **every** declaration of every `GFNBounds.*` module
and fails (a thrown `IO.userError`, hence a non-zero exit) if any depends on an axiom outside
`propext`, `Classical.choice`, `Quot.sound` — `sorryAx` included. Run by `make check` through
`lake env lean scripts/AxiomSweep.lean`, after the build.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0
  let mut mods := 0
  let mut bad : Array (Name × Array Name) := #[]
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless (`GFNBounds).isPrefixOf modName do continue
    mods := mods + 1
    for n in env.header.moduleData[idx]!.constNames do
      if (env.find? n).isSome then
        total := total + 1
        let axs ← collectAxioms n
        let extra := axs.filter (fun a => !(std.contains a))
        if !extra.isEmpty then bad := bad.push (n, extra)
  for (n, ax) in bad do IO.println s!"AXIOM SWEEP FAIL: {n} depends on {ax}"
  if !bad.isEmpty then
    throwError m!"axiom sweep: {bad.size} declaration(s) outside the standard axioms"
  IO.println s!"axiom sweep: {total} declarations in {mods} modules, all within propext/Classical.choice/Quot.sound"
